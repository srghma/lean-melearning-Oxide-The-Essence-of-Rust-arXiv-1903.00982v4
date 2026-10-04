module
public import RequestProject.Oxide.Metatheory.Progress.Places

/-!
# Progress, part 5: auxiliary facts for the main induction

Loan updates and region rewriting only change loan sets, so they produce
refinements; places of the stack typing evaluate in a valid stack; shape facts
relating the stack typing and the stack.
-/

@[expose] public section

namespace Oxide

variable {G : GlobalEnv}

/-! ### Loan updates and rewriting only change loans -/

theorem FrameTy.setRgnAt_ref (Φ : FrameTy) (j : Nat) (L : List Loan) :
    List.Forall₂ EntryRef (Φ.setRgnAt j L) Φ := by
  induction Φ generalizing j with
  | nil => exact .nil
  | cons e Φ ih =>
    cases e with
    | var τ => exact .cons (EntryRef.refl _) (ih j)
    | rgn L' =>
      cases j with
      | zero => exact .cons trivial (List.forall₂_same.2 fun e _ => EntryRef.refl e)
      | succ j => exact .cons trivial (ih j)

theorem Refines.setLoans (Γ : StackTy) (r : Nat) (L : List Loan) :
    Refines (Γ.setLoans r L) Γ := by
  induction Γ with
  | nil => exact .nil
  | cons Φ Γ ih =>
    simp only [StackTy.setLoans]
    split_ifs
    · exact .cons (FrameTy.setRgnAt_ref _ _ _) (Refines.refl Γ)
    · exact .cons (List.forall₂_same.2 fun e _ => EntryRef.refl e) ih

/-- The outlives judgments only change loan sets. -/
theorem OutlivesJ.refines {Δ : TyEnv} {Θ : TempTy} {μ : Mode} {F : OutlivesForm}
    (h : OutlivesJ Δ Θ μ F) :
    match F with
    | .one Γ _ _ Γ' => Refines Γ' Γ
    | .all Γ _ _ Γ' => Refines Γ' Γ := by
  induction h with
  | refl => exact Refines.refl _
  | trans _ _ _ _ _ _ _ _ _ ih₁ ih₂ => exact ih₂.trans ih₁
  | combine => exact Refines.setLoans _ _ _
  | combineUnrest => exact Refines.setLoans _ _ _
  | check => exact Refines.refl _
  | bothAbs => exact Refines.refl _
  | concAbs _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih => exact ih
  | absConc => exact Refines.refl _
  | allNil => exact Refines.refl _
  | allCons _ _ _ _ _ _ _ _ _ ih₁ ih₂ => exact ih₂.trans ih₁

/-- Region rewriting only changes loan sets. -/
theorem RewriteJ.refines {Δ : TyEnv} {Θ : TempTy} {μ : Mode} {F : RewriteForm}
    (h : RewriteJ Δ Θ μ F) :
    match F with
    | .one Γ _ _ Γ' => Refines Γ' Γ
    | .all Γ _ _ Γ' => Refines Γ' Γ := by
  induction h with
  | refl => exact Refines.refl _
  | trans _ _ _ _ _ _ _ _ ih₁ ih₂ => exact ih₂.trans ih₁
  | ref _ _ _ _ _ _ _ _ h₁ _ ih => exact ih.trans (OutlivesJ.refines h₁)
  | array _ _ _ _ _ _ ih => exact ih
  | slice _ _ _ _ _ ih => exact ih
  | tuple _ _ _ _ _ ih => exact ih
  | dead => exact Refines.refl _
  | allNil => exact Refines.refl _
  | allCons _ _ _ _ _ _ _ _ _ ih₁ ih₂ => exact ih₂.trans ih₁

theorem Rewrite.refines {Δ : TyEnv} {Θ : TempTy} {μ : Mode} {Γ Γ' : StackTy} {τ₁ τ₂ : Ty}
    (h : Rewrite Δ Θ μ Γ τ₁ τ₂ Γ') : Refines Γ' Γ := RewriteJ.refines h

/-! ### Places evaluate -/

theorem StoreValid.idxToLevel {Γ : StackTy} {σ : Stack} (h : StoreValid G Γ σ) (i : Nat) :
    Γ.idxToLevel i = σ.idxToLevel i := by
  cases h with
  | empty => rfl
  | frame Γ σ Φ ς h' hv =>
    have h1 := (FrameOK.numVars (G := G) hv).1
    have h2 := (StoreValid.size (StoreValid.frame Γ σ Φ ς h' hv)).1
    simp only [StackTy.idxToLevel, Stack.idxToLevel, h1, h2]

theorem evalPlace_eq {Γ Γ₀ : StackTy} {σ : Stack} (hR : Refines Γ Γ₀) (hσ : StoreValid G Γ₀ σ)
    {n : Nat} {p : PlaceExpr n} {pa : APlaceExpr} (hp : p.toAbs Γ = some pa) :
    pa.root = pa.root ∧ σ.evalPlace p = pa.ops.foldlM σ.placeStep ⟨pa.root, []⟩ := by
  refine ⟨rfl, ?_⟩
  simp only [PlaceExpr.toAbs, Option.map_eq_some_iff] at hp
  obtain ⟨ℓ, hℓ, rfl⟩ := hp
  rw [hR.idxToLevel, hσ.idxToLevel] at hℓ
  simp [Stack.evalPlace, hℓ]

/-- A place expression typed in a refinement of the stack typing evaluates. -/
theorem place_eval {Δ : TyEnv} {Γ Γ₀ : StackTy} {σ : Stack} (hR : Refines Γ Γ₀)
    (hσ : StoreValid G Γ₀ σ) {n : Nat} {p : PlaceExpr n} {pa : APlaceExpr} {ω : Own} {τ : Ty}
    {ρs : List Region} (hp : p.toAbs Γ = some pa) (htc : PlaceTy Δ Γ ω pa τ ρs) :
    ∃ R w Θ k, σ.evalPlace p = some R ∧ σ.read R = some w ∧
      HasTypeV G {} Θ (Γ₀.drop k) w τ := by
  obtain ⟨R, w, Θ, k, h1, h2, h3⟩ := PlaceTy.eval hσ (htc.refine hR)
  exact ⟨R, w, Θ, k, by rw [(evalPlace_eq hR hσ hp).2]; exact h1, h2, h3⟩

/-- A place (no dereference) of the stack typing evaluates to the referent of its path. -/
theorem place_eval_path {Γ Γ₀ : StackTy} {σ : Stack} (hR : Refines Γ Γ₀)
    (hσ : StoreValid G Γ₀ σ) {n : Nat} {p : PlaceExpr n} {π : APlace} {τ : Ty}
    (hp : p.toAbs Γ = some π.toExpr) (hty : Γ.placeTy π = some τ) :
    ∃ w τ₀ Θ k, σ.evalPlace p = some ⟨π.root, π.path.map RStep.proj⟩ ∧
      σ.read ⟨π.root, π.path.map RStep.proj⟩ = some w ∧ TyRef τ τ₀ ∧
      HasTypeV G {} Θ (Γ₀.drop k) w τ₀ := by
  obtain ⟨τ₀, h0, hr⟩ := hR.placeTy hty
  obtain ⟨w, Θ, k, h1, h2⟩ := hσ.readPlace h0
  refine ⟨w, τ₀, Θ, k, ?_, h1, hr, h2⟩
  rw [(evalPlace_eq hR hσ hp).2]
  simpa [APlace.toExpr] using Stack.foldlM_placeStep_projs σ ⟨π.root, []⟩ π.path

/-! ### Shapes -/

theorem topVal_some {Γ₀ : StackTy} {σ : Stack} (hσ : StoreValid G Γ₀ σ) {i ℓ : Nat}
    (h : Γ₀.idxToLevel i = some ℓ) : ∃ v, σ.topVal i = some v := by
  cases hσ with
  | empty => simp [StackTy.idxToLevel] at h
  | frame Γ σ Φ ς _ hv =>
    simp only [StackTy.idxToLevel] at h
    split_ifs at h with hi
    exact FrameOK.valAt_of_lt hv hi

theorem shape_cons {Γ Γ₀ : StackTy} {σ : Stack} (hR : Refines Γ Γ₀) (hσ : StoreValid G Γ₀ σ)
    {Φ : FrameTy} {Γ' : StackTy} (h : Γ = Φ :: Γ') : ∃ ς σ', σ = ς :: σ' := by
  subst h
  cases hR with
  | cons _ _ => exact hσ.cons_left

theorem shape_var {Γ Γ₀ : StackTy} {σ : Stack} (hR : Refines Γ Γ₀) (hσ : StoreValid G Γ₀ σ)
    {τ : Ty} {Φ : FrameTy} {Γ' : StackTy} (h : Γ = (.var τ :: Φ) :: Γ') :
    ∃ v ς σ', σ = (.val v :: ς) :: σ' := by
  subst h
  cases hR with
  | cons hΦ _ =>
    cases hΦ with
    | @cons _ e₀ _ _ he _ =>
      cases hσ with
      | frame _ σ' _ ς _ hv =>
        cases hv with
        | @cons _ s _ ς' hs _ =>
          cases e₀ <;> simp [EntryRef] at he
          cases s <;> simp [FrameOK] at hs
          exact ⟨_, _, _, rfl⟩

theorem shape_rgn {Γ Γ₀ : StackTy} {σ : Stack} (hR : Refines Γ Γ₀) (hσ : StoreValid G Γ₀ σ)
    {L : List Loan} {Φ : FrameTy} {Γ' : StackTy} (h : Γ = (.rgn L :: Φ) :: Γ') :
    ∃ ς σ', σ = (.rgn :: ς) :: σ' := by
  subst h
  cases hR with
  | cons hΦ _ =>
    cases hΦ with
    | @cons _ e₀ _ _ he _ =>
      cases hσ with
      | frame _ σ' _ ς _ hv =>
        cases hv with
        | @cons _ s _ ς' hs _ =>
          cases e₀ <;> simp [EntryRef] at he
          cases s <;> simp [FrameOK] at hs
          exact ⟨_, _, rfl⟩

/-! ### Types -/

theorem Ty.SI.tuple_inv {τs : List Ty} (h : Ty.SI (.tuple τs)) : ∀ τ ∈ τs, τ.SI := by
  cases h with
  | tuple _ h => exact h

theorem Ty.SI.array_inv {τ : Ty} {n : Nat} (h : Ty.SI (.array τ n)) : τ.SI := by
  cases h with
  | array _ _ h => exact h

theorem Ty.SI.not_slice {τ : Ty} (h : Ty.SI (.slice τ)) : False := by
  cases h

theorem RefTy.xi {Γ : StackTy} {R : Referent} {τ : Ty} (h : RefTy Γ R τ) : τ.XI := by
  induction h with
  | id _ _ _ hsi => exact .inl hsi
  | proj _ τs _ _ _ hi ih =>
    rcases ih with h | ⟨_, h, _⟩
    · exact .inl (h.tuple_inv _ (List.mem_of_getElem? hi))
    · cases h
  | idxArray _ _ _ _ _ _ ih =>
    rcases ih with h | ⟨_, h, _⟩
    · exact .inl h.array_inv
    · cases h
  | idxSlice _ _ _ _ _ _ _ _ ih =>
    rcases ih with h | ⟨_, h, h'⟩
    · exact h.not_slice.elim
    · cases h; exact .inl h'
  | sliceArray _ _ _ _ _ _ _ _ ih =>
    rcases ih with h | ⟨_, h, _⟩
    · exact .inr ⟨_, rfl, h.array_inv⟩
    · cases h
  | sliceSlice _ _ _ _ _ _ _ _ _ _ ih =>
    rcases ih with h | ⟨_, h, h'⟩
    · exact h.not_slice.elim
    · cases h; exact .inr ⟨_, rfl, h'⟩

/-- A referent of slice type ends with a slice step into an array or a slice. -/
theorem RefTy.slice_inv {Γ : StackTy} {R : Referent} {τ : Ty} (h : RefTy Γ R (.slice τ)) :
    ∃ R' i j, R = R'.snoc (.slice i j) ∧ i ≤ j ∧
      ((∃ n, RefTy Γ R' (.array τ n)) ∨ RefTy Γ R' (.slice τ)) := by
  generalize hτ : Ty.slice τ = τ' at h
  cases h with
  | id _ _ _ hsi => subst hτ; exact hsi.not_slice.elim
  | proj R τs i _ h hi =>
    subst hτ
    rcases h.xi with h' | ⟨_, h', _⟩
    · exact (h'.tuple_inv _ (List.mem_of_getElem? hi)).not_slice.elim
    · cases h'
  | idxArray R _ n i h _ =>
    subst hτ
    rcases h.xi with h' | ⟨_, h', _⟩
    · exact h'.array_inv.not_slice.elim
    · cases h'
  | idxSlice root steps a b i _ h _ =>
    subst hτ
    rcases h.xi with h' | ⟨_, h', h''⟩
    · exact h'.not_slice.elim
    · cases h'; exact h''.not_slice.elim
  | sliceArray R τ₀ n i j h hij _ =>
    cases hτ
    exact ⟨R, i, j, rfl, hij, .inl ⟨n, h⟩⟩
  | sliceSlice root steps a b i j τ₀ h hij _ =>
    cases hτ
    exact ⟨⟨root, steps ++ [.slice a b]⟩, i, j, by simp [Referent.snoc], hij, .inr h⟩

/-- Reading the base of a slice referent gives an array or a slice. -/
theorem RefTy.read_seq {Γ : StackTy} {σ : Stack} (hσ : StoreValid G Γ σ) {R : Referent} {τ : Ty}
    (h : (∃ n, RefTy Γ R (.array τ n)) ∨ RefTy Γ R (.slice τ)) :
    ∃ vs, σ.read R = some (.array vs) ∨ σ.read R = some (.slice vs) := by
  rcases h with ⟨n, h⟩ | h
  · obtain ⟨w, Θ, k, hr, hw, -⟩ := RefTy.read hσ h
    obtain ⟨vs, rfl, -⟩ := hw.array_inv
    exact ⟨vs, .inl hr⟩
  · obtain ⟨w, Θ, k, hr, hw, -⟩ := RefTy.read hσ h
    obtain ⟨vs, rfl, -⟩ := hw.slice_inv
    exact ⟨vs, .inr hr⟩

end Oxide
