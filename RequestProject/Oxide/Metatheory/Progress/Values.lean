module
public import RequestProject.Oxide.Metatheory.Progress.Refine

/-!
# Progress, part 3: well-typed referents can be read and written

The lemma "Well-Formed References Evaluate to Well-Typed Values" of the paper,
the lemma "Place Expressions Reduce" and the corresponding facts for writes.
-/

@[expose] public section

namespace Oxide

variable {G : GlobalEnv}

/-! ### Lists of typed values -/

theorem HasTypeVs.get {Δ : TyEnv} {Θ : TempTy} {Γ : StackTy} {vs : List Value} {τs : List Ty}
    (h : HasTypeVs G Δ Θ Γ vs τs) {i : Nat} {v : Value} {τ : Ty} (hv : vs[i]? = some v)
    (hτ : τs[i]? = some τ) : ∃ Θ', HasTypeV G Δ Θ' Γ v τ := by
  induction vs generalizing Θ τs i with
  | nil => simp at hv
  | cons v' vs ih =>
    cases h with
    | vsCons _ _ _ _ _ τ' τs' h t =>
      cases i with
      | zero => simp at hv hτ; subst hv; subst hτ; exact ⟨_, h⟩
      | succ i => exact ih t (by simpa using hv) (by simpa using hτ)

theorem HasTypeVs.take {Δ : TyEnv} {Θ : TempTy} {Γ : StackTy} {vs : List Value}
    {τs : List Ty} (h : HasTypeVs G Δ Θ Γ vs τs) (i : Nat) :
    HasTypeVs G Δ Θ Γ (vs.take i) (τs.take i) := by
  induction vs generalizing Θ τs i with
  | nil => cases h; simpa using Typing.vsNil Δ Θ Γ
  | cons v vs ih =>
    cases h with
    | vsCons _ _ _ _ _ τ τs h t =>
      cases i with
      | zero => simpa using Typing.vsNil Δ Θ Γ
      | succ i => simpa using Typing.vsCons Δ Θ Γ v _ τ _ h (ih t i)

theorem HasTypeVs.drop {Δ : TyEnv} {Θ : TempTy} {Γ : StackTy} {vs : List Value}
    {τs : List Ty} (h : HasTypeVs G Δ Θ Γ vs τs) (i : Nat) :
    ∃ Θ', HasTypeVs G Δ Θ' Γ (vs.drop i) (τs.drop i) := by
  induction vs generalizing Θ τs i with
  | nil => cases h; exact ⟨Θ, by simpa using Typing.vsNil Δ Θ Γ⟩
  | cons v vs ih =>
    cases h with
    | vsCons _ _ _ _ _ τ τs h t =>
      cases i with
      | zero => exact ⟨Θ, by simpa using Typing.vsCons Δ Θ Γ v vs τ τs h t⟩
      | succ i => simpa using ih t i

theorem HasTypeVs.extract_replicate {Δ : TyEnv} {Θ : TempTy} {Γ : StackTy} {vs : List Value}
    {τ : Ty} (h : HasTypeVs G Δ Θ Γ vs (List.replicate vs.length τ)) (i j : Nat) :
    ∃ Θ', HasTypeVs G Δ Θ' Γ (vs.extract i j) (List.replicate (vs.extract i j).length τ) := by
  obtain ⟨Θ', h'⟩ := h.drop i
  have h'' := h'.take (j - i)
  refine ⟨Θ', ?_⟩
  rw [List.extract_eq_drop_take]
  convert h'' using 1
  simp [List.drop_replicate, List.take_replicate]

/-! ### Canonical forms with typing information -/

theorem HasTypeV.tuple_inv {Δ : TyEnv} {Θ : TempTy} {Γ : StackTy} {v : Value} {τs : List Ty}
    (h : HasTypeV G Δ Θ Γ v (.tuple τs)) :
    ∃ vs, v = .tuple vs ∧ HasTypeVs G Δ Θ Γ vs τs := by
  cases h with
  | vTuple _ _ _ vs _ h => exact ⟨vs, rfl, h⟩

theorem HasTypeV.array_inv {Δ : TyEnv} {Θ : TempTy} {Γ : StackTy} {v : Value} {τ : Ty}
    {n : Nat} (h : HasTypeV G Δ Θ Γ v (.array τ n)) :
    ∃ vs, v = .array vs ∧ vs.length = n ∧ HasTypeVs G Δ Θ Γ vs (List.replicate vs.length τ) := by
  cases h with
  | vArray _ _ _ vs _ h _ => exact ⟨vs, rfl, rfl, h⟩

theorem HasTypeV.slice_inv {Δ : TyEnv} {Θ : TempTy} {Γ : StackTy} {v : Value} {τ : Ty}
    (h : HasTypeV G Δ Θ Γ v (.slice τ)) :
    ∃ vs, v = .slice vs ∧ HasTypeVs G Δ Θ Γ vs (List.replicate vs.length τ) := by
  cases h with
  | vSlice _ _ _ vs _ h _ => exact ⟨vs, rfl, h⟩

theorem HasTypeV.ref_inv {Δ : TyEnv} {Θ : TempTy} {Γ : StackTy} {v : Value} {ρ : Region}
    {ω : Own} {τ : Ty} (h : HasTypeV G Δ Θ Γ v (.ref ρ ω τ)) :
    ∃ R, v = .ptr R ∧ RefTy Γ R τ := by
  cases h with
  | vPtr _ _ _ R _ _ _ _ hR _ _ _ => exact ⟨R, rfl, hR⟩

theorem HasTypeV.not_slice_of_SI {Δ : TyEnv} {Θ : TempTy} {Γ : StackTy} {ws : List Value}
    {τ : Ty} (h : HasTypeV G Δ Θ Γ (.slice ws) τ) (hsi : τ.SI) : False := by
  cases h with
  | vDead => cases hsi
  | vSlice => cases hsi

/-! ### Reading values along referent steps -/

theorem Value.readSteps_append (v : Value) (a b : List RStep) :
    v.readSteps (a ++ b) = (v.readSteps a).bind (·.readSteps b) := by
  induction a generalizing v with
  | nil => simp [Value.readSteps]
  | cons s a ih =>
    cases v <;> cases s <;> simp only [List.cons_append, Value.readSteps, Option.bind_none] <;>
      first
      | (split_ifs <;> simp [ih])
      | simp [ih, Option.bind_assoc]

theorem Value.readSteps_slice_last {v w : Value} {steps : List RStep} {a b : Nat}
    (h : v.readSteps (steps ++ [.slice a b]) = some w) : ∃ ws, w = .slice ws := by
  rw [Value.readSteps_append] at h
  cases h1 : v.readSteps steps with
  | none => simp [h1] at h
  | some u =>
    rw [h1] at h
    cases u <;> simp [Value.readSteps] at h <;> exact ⟨_, h.2.symm⟩

/-- **Well-formed references evaluate to well-typed values** (Lemma of the paper):
in a valid stack, a referent well-formed at type `τ` can be read, giving a value of
type `τ`; a referent ending in a slice step `[a..b]` reads a slice of length
`b - a`. -/
theorem RefTy.read {Γ : StackTy} {σ : Stack} (hσ : StoreValid G Γ σ) {R : Referent} {τ : Ty}
    (h : RefTy Γ R τ) :
    ∃ w Θ k, σ.read R = some w ∧ HasTypeV G {} Θ (Γ.drop k) w τ ∧
      ∀ steps a b, R.steps = steps ++ [.slice a b] → ∃ ws, w = .slice ws ∧ ws.length = b - a := by
  induction h with
  | id ℓ τ hv _ =>
    obtain ⟨v, k, hg, hv⟩ := hσ.lookup hv
    refine ⟨v, [], k, by simp [Stack.read, hg, Value.readSteps], hv, ?_⟩
    intro steps a b hs; simp at hs
  | proj R τs i τ _ hi ih =>
    obtain ⟨w, Θ, k, hr, hw, -⟩ := ih
    obtain ⟨vs, rfl, hvs⟩ := hw.tuple_inv
    have hlen := HasTypeVs.length_eq hvs
    have hi' : i < vs.length := by rw [hlen]; exact (List.getElem?_eq_some_iff.1 hi).1
    obtain ⟨Θ', hv⟩ := hvs.get (List.getElem?_eq_getElem hi') hi
    refine ⟨vs[i], Θ', k, ?_, hv, ?_⟩
    · simp only [Stack.read, Option.bind_eq_some_iff] at hr ⊢
      obtain ⟨u, hu, hu'⟩ := hr
      refine ⟨u, hu, ?_⟩
      rw [Value.readSteps_append, hu']
      simp [Value.readSteps, List.getElem?_eq_getElem hi']
    · intro steps a b hs
      have := congrArg List.getLast? hs
      simp at this
  | idxArray R τ n i _ hi ih =>
    obtain ⟨w, Θ, k, hr, hw, -⟩ := ih
    obtain ⟨vs, rfl, hlen, hvs⟩ := hw.array_inv
    have hi' : i < vs.length := by omega
    obtain ⟨Θ', hv⟩ := hvs.get (τ := τ) (List.getElem?_eq_getElem hi') (by simp [hi'])
    refine ⟨vs[i], Θ', k, ?_, hv, ?_⟩
    · simp only [Stack.read, Option.bind_eq_some_iff] at hr ⊢
      obtain ⟨u, hu, hu'⟩ := hr
      refine ⟨u, hu, ?_⟩
      rw [Value.readSteps_append, hu']
      simp [Value.readSteps, List.getElem?_eq_getElem hi']
    · intro steps a b hs
      have := congrArg List.getLast? hs
      simp at this
  | idxSlice root steps a b i τ _ hi ih =>
    obtain ⟨w, Θ, k, hr, hw, hsl⟩ := ih
    obtain ⟨ws, rfl, hlen⟩ := hsl steps a b rfl
    obtain ⟨_, hws, hvs⟩ := hw.slice_inv
    cases hws
    have hi' : i < ws.length := by omega
    obtain ⟨Θ', hv⟩ := hvs.get (τ := τ) (List.getElem?_eq_getElem hi') (by simp [hi'])
    refine ⟨ws[i], Θ', k, ?_, hv, ?_⟩
    · simp only [Stack.read, Option.bind_eq_some_iff] at hr ⊢
      obtain ⟨u, hu, hu'⟩ := hr
      refine ⟨u, hu, ?_⟩
      have e : steps ++ [RStep.slice a b, RStep.idx i] = (steps ++ [.slice a b]) ++ [.idx i] := by
        simp
      rw [e, Value.readSteps_append, hu']
      simp [Value.readSteps, List.getElem?_eq_getElem hi']
    · intro steps' a' b' hs
      have := congrArg List.getLast? hs
      simp at this
  | sliceArray R τ n i j _ hij hj ih =>
    obtain ⟨w, Θ, k, hr, hw, -⟩ := ih
    obtain ⟨vs, rfl, hlen, hvs⟩ := hw.array_inv
    obtain ⟨Θ', hvs'⟩ := hvs.extract_replicate i j
    refine ⟨.slice (vs.extract i j), Θ', k, ?_, ?_, ?_⟩
    · simp only [Stack.read, Option.bind_eq_some_iff] at hr ⊢
      obtain ⟨u, hu, hu'⟩ := hr
      refine ⟨u, hu, ?_⟩
      rw [Value.readSteps_append, hu']
      simp [Value.readSteps, hij, show j ≤ vs.length by omega]
    · exact Typing.vSlice _ _ _ _ τ hvs' (by
        cases hw with
        | vArray _ _ _ _ _ _ hsi => exact hsi)
    · intro steps a b hs
      have := congrArg List.getLast? hs
      simp at this
      obtain ⟨rfl, rfl⟩ := this
      exact ⟨_, rfl, by simp; omega⟩
  | sliceSlice root steps a b i j τ _ hij hj ih =>
    obtain ⟨w, Θ, k, hr, hw, hsl⟩ := ih
    obtain ⟨ws, rfl, hlen⟩ := hsl steps a b rfl
    obtain ⟨_, hws, hvs⟩ := hw.slice_inv
    cases hws
    obtain ⟨Θ', hvs'⟩ := hvs.extract_replicate i j
    refine ⟨.slice (ws.extract i j), Θ', k, ?_, ?_, ?_⟩
    · simp only [Stack.read, Option.bind_eq_some_iff] at hr ⊢
      obtain ⟨u, hu, hu'⟩ := hr
      refine ⟨u, hu, ?_⟩
      have e : steps ++ [RStep.slice a b, RStep.slice i j] =
          (steps ++ [.slice a b]) ++ [.slice i j] := by simp
      rw [e, Value.readSteps_append, hu']
      simp [Value.readSteps, hij, show j ≤ ws.length by omega]
    · exact Typing.vSlice _ _ _ _ τ hvs' (by
        cases hw with
        | vSlice _ _ _ _ _ _ hsi => exact hsi)
    · intro steps' a' b' hs
      have := congrArg List.getLast? hs
      simp at this
      obtain ⟨rfl, rfl⟩ := this
      exact ⟨_, rfl, by simp; omega⟩

end Oxide
