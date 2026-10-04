module
public import RequestProject.Oxide.Metatheory.Progress.Values

/-!
# Progress, part 4: place expressions reduce

Lemma "Place Expressions Reduce" of the paper: a well-typed place expression
evaluates to a referent at which a value of its type is stored; and the
corresponding facts for writes.
-/

@[expose] public section

namespace Oxide

variable {G : GlobalEnv}

theorem Stack.foldlM_placeStep_projs (σ : Stack) (R : Referent) (q : List Nat) :
    (q.map POp.proj).foldlM σ.placeStep R = some ⟨R.root, R.steps ++ q.map RStep.proj⟩ := by
  induction q generalizing R with
  | nil => simp
  | cons i q ih =>
    simp only [List.map_cons, List.foldlM_cons, Stack.placeStep]
    simp only [Option.bind_eq_bind, Option.bind_some]
    rw [ih]
    simp

/-- **Place expressions reduce** (Lemma of the paper): in a valid stack, a place
expression of type `τ` evaluates to a referent holding a value of type `τ`. -/
theorem PlaceTy.eval {Δ : TyEnv} {Γ : StackTy} {σ : Stack} (hσ : StoreValid G Γ σ) {ω : Own}
    {pa : APlaceExpr} {τ : Ty} {ρs : List Region} (h : PlaceTy Δ Γ ω pa τ ρs) :
    ∃ R w Θ k, pa.ops.foldlM σ.placeStep ⟨pa.root, []⟩ = some R ∧ σ.read R = some w ∧
      HasTypeV G {} Θ (Γ.drop k) w τ := by
  induction h with
  | var ℓ τ hv _ =>
    obtain ⟨v, k, hg, hv⟩ := hσ.lookup hv
    exact ⟨⟨ℓ, []⟩, v, [], k, rfl, by simp [Stack.read, hg, Value.readSteps], hv⟩
  | proj p τs i τ ρs _ hi ih =>
    obtain ⟨R, w, Θ, k, hR, hr, hw⟩ := ih
    obtain ⟨vs, rfl, hvs⟩ := hw.tuple_inv
    have hlen := HasTypeVs.length_eq hvs
    have hi' : i < vs.length := by rw [hlen]; exact (List.getElem?_eq_some_iff.1 hi).1
    obtain ⟨Θ', hv⟩ := hvs.get (List.getElem?_eq_getElem hi') hi
    refine ⟨⟨R.root, R.steps ++ [.proj i]⟩, vs[i], Θ', k, ?_, ?_, hv⟩
    · rw [List.foldlM_append, hR]; rfl
    · simp only [Stack.read, Option.bind_eq_some_iff] at hr ⊢
      obtain ⟨u, hu, hu'⟩ := hr
      refine ⟨u, hu, ?_⟩
      rw [Value.readSteps_append, hu']
      simp [Value.readSteps, List.getElem?_eq_getElem hi']
  | deref p ρ ω' τ ρs _ _ ih =>
    obtain ⟨R, w, Θ, k, hR, hr, hw⟩ := ih
    obtain ⟨R', rfl, hR'⟩ := hw.ref_inv
    obtain ⟨w', Θ', k', hr', hw', -⟩ := RefTy.read (hσ.drop k) hR'
    refine ⟨R', w', Θ', k + k', ?_, Stack.read_drop hr', by simpa [List.drop_drop] using hw'⟩
    rw [List.foldlM_append, hR]
    simp [Stack.placeStep, hr]

/-- Reading along a path of projections in a valid stack. -/
theorem HasTypeV.readPath {Δ : TyEnv} {Θ : TempTy} {Γ : StackTy} {v : Value} {τ : Ty}
    (h : HasTypeV G Δ Θ Γ v τ) {q : List Nat} {t : Ty} (hq : τ.atPath q = some t) :
    ∃ w Θ', v.readSteps (q.map RStep.proj) = some w ∧ HasTypeV G Δ Θ' Γ w t := by
  induction q generalizing v τ Θ with
  | nil => simp [Ty.atPath] at hq; subst hq; exact ⟨v, Θ, rfl, h⟩
  | cons i q ih =>
    cases τ with
    | tuple τs =>
      simp only [Ty.atPath] at hq
      cases h1 : τs[i]? with
      | none => simp [h1] at hq
      | some τi =>
        rw [h1] at hq
        obtain ⟨vs, rfl, hvs⟩ := h.tuple_inv
        have hlen := HasTypeVs.length_eq hvs
        have hi' : i < vs.length := by rw [hlen]; exact (List.getElem?_eq_some_iff.1 h1).1
        obtain ⟨Θ', hv⟩ := hvs.get (List.getElem?_eq_getElem hi') h1
        obtain ⟨w, Θ'', hw, hw'⟩ := ih hv hq
        exact ⟨w, Θ'', by simp [Value.readSteps, List.getElem?_eq_getElem hi', hw], hw'⟩
    | _ => simp [Ty.atPath] at hq

theorem StoreValid.readPlace {Γ : StackTy} {σ : Stack} (hσ : StoreValid G Γ σ) {π : APlace}
    {τ : Ty} (h : Γ.placeTy π = some τ) :
    ∃ w Θ k, σ.read ⟨π.root, π.path.map RStep.proj⟩ = some w ∧ HasTypeV G {} Θ (Γ.drop k) w τ := by
  simp only [StackTy.placeTy, Option.bind_eq_some_iff] at h
  obtain ⟨τx, hx, hp⟩ := h
  obtain ⟨v, k, hg, hv⟩ := hσ.lookup hx
  obtain ⟨w, Θ, hw, hw'⟩ := hv.readPath hp
  exact ⟨w, Θ, k, by simp [Stack.read, hg, hw], hw'⟩

/-! ### Writes -/

theorem Value.modifySteps_slice_len {xs : List Value} {steps : List RStep}
    {f : Value → Option Value} {r : Value} (h : (Value.slice xs).modifySteps steps f = some r)
    (hne : steps ≠ []) : ∃ ys, r = .slice ys ∧ ys.length = xs.length := by
  cases steps with
  | nil => exact absurd rfl hne
  | cons s rest =>
    cases s with
    | proj i => simp [Value.modifySteps] at h
    | idx i =>
      simp only [Value.modifySteps] at h
      split at h
      · simp only [Option.map_eq_some_iff] at h
        obtain ⟨_, _, rfl⟩ := h
        exact ⟨_, rfl, by simp⟩
      · simp at h
    | slice i j =>
      simp only [Value.modifySteps] at h
      split_ifs at h with hij
      split at h
      · split_ifs at h with hl
        cases h
        exact ⟨_, rfl, by simp; omega⟩
      · simp at h

/-- A write succeeds wherever a read succeeds, unless the write replaces a whole
slice (which no typing rule allows). -/
theorem Value.modifySteps_some {v w : Value} {steps : List RStep}
    (h : v.readSteps steps = some w)
    (hw : (∀ ws, w ≠ .slice ws) ∨ (∀ i j, RStep.slice i j ∉ steps)) (u : Value) :
    ∃ v', v.modifySteps steps (fun _ => some u) = some v' := by
  induction steps generalizing v with
  | nil => exact ⟨u, rfl⟩
  | cons s rest ih =>
    have hw' : (∀ ws, w ≠ .slice ws) ∨ (∀ i j, RStep.slice i j ∉ rest) := by
      rcases hw with hw | hw
      · exact .inl hw
      · exact .inr fun i j hm => hw i j (List.mem_cons_of_mem _ hm)
    cases v <;> cases s <;> simp only [Value.readSteps] at h
    all_goals first
      | (simp at h; done)
      | skip
    · -- tuple, proj
      rename_i vs i
      cases h1 : vs[i]? with
      | none => simp [h1] at h
      | some vi =>
        rw [h1] at h
        obtain ⟨v', hv'⟩ := ih (v := vi) (by simpa using h) hw'
        exact ⟨_, by simp [Value.modifySteps, h1, hv']; rfl⟩
    · -- array, idx
      rename_i vs i
      cases h1 : vs[i]? with
      | none => simp [h1] at h
      | some vi =>
        rw [h1] at h
        obtain ⟨v', hv'⟩ := ih (v := vi) (by simpa using h) hw'
        exact ⟨_, by simp [Value.modifySteps, h1, hv']; rfl⟩
    · -- array, slice
      rename_i vs i j
      split_ifs at h with hij
      cases rest with
      | nil =>
        simp [Value.readSteps] at h
        rcases hw with hw | hw
        · exact absurd h.symm (hw _)
        · exact absurd (List.mem_cons_self) (hw i j)
      | cons s' rest' =>
        obtain ⟨r, hr⟩ := ih (v := .slice (vs.extract i j)) h hw'
        obtain ⟨ys, rfl, hys⟩ := Value.modifySteps_slice_len hr (by simp)
        refine ⟨.array (vs.take i ++ ys ++ vs.drop j), ?_⟩
        simp only [Value.modifySteps, if_pos hij, hr]
        rw [if_pos (by simp at hys; omega)]
    · -- slice, idx
      rename_i vs i
      cases h1 : vs[i]? with
      | none => simp [h1] at h
      | some vi =>
        rw [h1] at h
        obtain ⟨v', hv'⟩ := ih (v := vi) (by simpa using h) hw'
        exact ⟨_, by simp [Value.modifySteps, h1, hv']; rfl⟩
    · -- slice, slice
      rename_i vs i j
      split_ifs at h with hij
      cases rest with
      | nil =>
        simp [Value.readSteps] at h
        rcases hw with hw | hw
        · exact absurd h.symm (hw _)
        · exact absurd (List.mem_cons_self) (hw i j)
      | cons s' rest' =>
        obtain ⟨r, hr⟩ := ih (v := .slice (vs.extract i j)) h hw'
        obtain ⟨ys, rfl, hys⟩ := Value.modifySteps_slice_len hr (by simp)
        refine ⟨.slice (vs.take i ++ ys ++ vs.drop j), ?_⟩
        simp only [Value.modifySteps, if_pos hij, hr]
        rw [if_pos (by simp at hys; omega)]

theorem Stack.write_some {σ : Stack} {R : Referent} {w : Value} (h : σ.read R = some w)
    (hw : (∀ ws, w ≠ .slice ws) ∨ (∀ i j, RStep.slice i j ∉ R.steps)) (u : Value) :
    ∃ σ', σ.write R u = some σ' := by
  simp only [Stack.read, Option.bind_eq_some_iff] at h
  obtain ⟨x, hx, hxw⟩ := h
  obtain ⟨x', hx'⟩ := Value.modifySteps_some hxw hw u
  exact ⟨_, by simp [Stack.write, hx, hx']; rfl⟩

end Oxide
