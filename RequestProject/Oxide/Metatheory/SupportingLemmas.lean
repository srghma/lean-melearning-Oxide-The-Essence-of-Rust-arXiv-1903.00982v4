module
public import RequestProject.Oxide.Metatheory.Progress.Helpers

/-!
# Supporting lemmas from the paper's appendix (`proofs.tex`)

Lemmas of the paper's proof of preservation that hold in our formalization
independently of the problems with preservation itself:

* "Stack Validity is Preserved When Popping A Stack Frame" (`StoreValid.pop`);
* "Value Typing Fixed on Output Environments" (`HasType.val_output`) and
  "Values Change Environments in Limited Ways" (`HasType.val_refines`);
* "Type Computation is Preserved under Region Rewriting" (`PlaceTy.rewrite`) and the
  corresponding facts for referents (`RefTy.rewrite`), outlives (`PlaceTy.outlives`,
  `RefTy.outlives`) and garbage collection of loans (`PlaceTy.gcLoans`,
  `RefTy.gcLoans`): all of these only change loan sets (`LoanOnly`);
* "Type Computation is Preserved under Well-Typed Extensions" (`PlaceTy.push_var`)
  and the corresponding fact for referents (`RefTy.push_var`), together with the
  analogous facts for pushing a region (`PlaceTy.push_rgn`, `RefTy.push_rgn`).
-/

@[expose] public section

namespace Oxide

variable {G : GlobalEnv}

/-! ## Popping a frame and values -/

/-- "Stack Validity is Preserved When Popping A Stack Frame". -/
theorem StoreValid.pop {Γ : StackTy} {σ : Stack} {Φ : FrameTy} {ς : StackFrame}
    (h : StoreValid G (Φ :: Γ) (ς :: σ)) : StoreValid G Γ σ := by
  cases h with
  | frame _ _ _ _ h _ => exact h

/-- "Value Typing Fixed on Output Environments": a value typed by the expression
judgment is typed by the value judgment in the output stack typing. -/
theorem HasType.val_output {Δ : TyEnv} {Θ : TempTy} {Γ Γ' : StackTy} {n : Nat} {v : Value}
    {τ : Ty} (h : HasType G Δ Θ Γ (n := n) (.val v) τ Γ') : HasTypeV G Δ Θ Γ' v τ :=
  h.val_inv'.2

/-- "Values Change Environments in Limited Ways": typing a value can only kill places
of the stack typing (by `T-Drop`). -/
theorem HasType.val_refines {Δ : TyEnv} {Θ : TempTy} {Γ Γ' : StackTy} {n : Nat} {v : Value}
    {τ : Ty} (h : HasType G Δ Θ Γ (n := n) (.val v) τ Γ') : Refines Γ' Γ :=
  h.val_inv'.1

/-! ## Changes of loan sets -/

/-- Two frame entries that differ at most in their loan sets. -/
def EntrySame : FrameEntry → FrameEntry → Prop
  | .var τ, .var τ' => τ = τ'
  | .rgn _, .rgn _ => True
  | _, _ => False

/-- `LoanOnly Γ Γ'`: the stack typings have the same shape and the same variable
types; only loan sets may differ. -/
def LoanOnly (Γ Γ' : StackTy) : Prop := List.Forall₂ (List.Forall₂ EntrySame) Γ Γ'

theorem EntrySame.refl (e : FrameEntry) : EntrySame e e := by
  cases e <;> simp [EntrySame]

theorem EntrySame.symm {e e' : FrameEntry} (h : EntrySame e e') : EntrySame e' e := by
  cases e <;> cases e' <;> simp_all [EntrySame]

theorem EntrySame.trans {e₁ e₂ e₃ : FrameEntry} (h₁ : EntrySame e₁ e₂) (h₂ : EntrySame e₂ e₃) :
    EntrySame e₁ e₃ := by
  cases e₁ <;> cases e₂ <;> cases e₃ <;> simp_all [EntrySame]

theorem EntrySame.entryRef {e e' : FrameEntry} (h : EntrySame e e') : EntryRef e e' := by
  cases e <;> cases e' <;> simp_all [EntrySame, EntryRef]
  exact TyRef.refl _

theorem LoanOnly.refl (Γ : StackTy) : LoanOnly Γ Γ :=
  List.forall₂_same.2 fun _ _ => List.forall₂_same.2 fun e _ => EntrySame.refl e

theorem forall₂_symm' {α : Type} {R : α → α → Prop} (hs : ∀ {a b}, R a b → R b a)
    {l₁ l₂ : List α} (h : List.Forall₂ R l₁ l₂) : List.Forall₂ R l₂ l₁ := by
  induction h with
  | nil => exact .nil
  | cons hab _ ih => exact .cons (hs hab) ih

theorem LoanOnly.symm {Γ Γ' : StackTy} (h : LoanOnly Γ Γ') : LoanOnly Γ' Γ :=
  forall₂_symm' (R := List.Forall₂ EntrySame)
    (fun hΦ => forall₂_symm' (R := EntrySame) EntrySame.symm hΦ) h

theorem LoanOnly.trans {Γ₁ Γ₂ Γ₃ : StackTy} (h₁ : LoanOnly Γ₁ Γ₂) (h₂ : LoanOnly Γ₂ Γ₃) :
    LoanOnly Γ₁ Γ₃ :=
  forall₂_trans (R := List.Forall₂ EntrySame)
    (fun a b => forall₂_trans (R := EntrySame) EntrySame.trans a b) h₁ h₂

theorem LoanOnly.refines {Γ Γ' : StackTy} (h : LoanOnly Γ Γ') : Refines Γ Γ' :=
  h.imp fun _ _ hΦ => hΦ.imp fun _ _ he => he.entryRef

theorem FrameTy.setRgnAt_same (Φ : FrameTy) (j : Nat) (L : List Loan) :
    List.Forall₂ EntrySame (Φ.setRgnAt j L) Φ := by
  induction Φ generalizing j with
  | nil => exact .nil
  | cons e Φ ih =>
    cases e with
    | var τ => exact .cons (EntrySame.refl _) (ih j)
    | rgn L' =>
      cases j with
      | zero => exact .cons trivial (List.forall₂_same.2 fun e _ => EntrySame.refl e)
      | succ j => exact .cons trivial (ih j)

/-- Updating a loan set only changes loans. -/
theorem LoanOnly.setLoans (Γ : StackTy) (r : Nat) (L : List Loan) :
    LoanOnly (Γ.setLoans r L) Γ := by
  induction Γ with
  | nil => exact .nil
  | cons Φ Γ ih =>
    simp only [StackTy.setLoans]
    split_ifs
    · exact .cons (FrameTy.setRgnAt_same _ _ _) (LoanOnly.refl Γ)
    · exact .cons (List.forall₂_same.2 fun e _ => EntrySame.refl e) ih

/-- The outlives judgments only change loan sets. -/
theorem OutlivesJ.loanOnly {Δ : TyEnv} {Θ : TempTy} {μ : Mode} {F : OutlivesForm}
    (h : OutlivesJ Δ Θ μ F) :
    match F with
    | .one Γ _ _ Γ' => LoanOnly Γ Γ'
    | .all Γ _ _ Γ' => LoanOnly Γ Γ' := by
  induction h with
  | refl => exact LoanOnly.refl _
  | trans _ _ _ _ _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | combine => exact (LoanOnly.setLoans _ _ _).symm
  | combineUnrest => exact (LoanOnly.setLoans _ _ _).symm
  | check => exact LoanOnly.refl _
  | bothAbs => exact LoanOnly.refl _
  | concAbs _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih => exact ih
  | absConc => exact LoanOnly.refl _
  | allNil => exact LoanOnly.refl _
  | allCons _ _ _ _ _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Region rewriting only changes loan sets. -/
theorem RewriteJ.loanOnly {Δ : TyEnv} {Θ : TempTy} {μ : Mode} {F : RewriteForm}
    (h : RewriteJ Δ Θ μ F) :
    match F with
    | .one Γ _ _ Γ' => LoanOnly Γ Γ'
    | .all Γ _ _ Γ' => LoanOnly Γ Γ' := by
  induction h with
  | refl => exact LoanOnly.refl _
  | trans _ _ _ _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | ref _ _ _ _ _ _ _ _ h₁ _ ih => exact (OutlivesJ.loanOnly h₁).trans ih
  | array _ _ _ _ _ _ ih => exact ih
  | slice _ _ _ _ _ ih => exact ih
  | tuple _ _ _ _ _ ih => exact ih
  | dead => exact LoanOnly.refl _
  | allNil => exact LoanOnly.refl _
  | allCons _ _ _ _ _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem mapLoans_go_same (f : Nat → List Loan → List Loan) (base q : Nat) (Φ : FrameTy) (j : Nat) :
    List.Forall₂ EntrySame (StackTy.mapLoans.go f base q Φ j) Φ := by
  induction Φ generalizing j with
  | nil => exact .nil
  | cons e Φ ih =>
    cases e with
    | var τ => exact .cons rfl (ih j)
    | rgn L => exact .cons trivial (ih (j + 1))

/-- Mapping over the loan sets only changes loans. -/
theorem LoanOnly.mapLoans (f : Nat → List Loan → List Loan) (Γ : StackTy) :
    LoanOnly (Γ.mapLoans f) Γ := by
  induction Γ with
  | nil => exact .nil
  | cons Φ Γ ih => exact .cons (mapLoans_go_same _ _ _ _ _) ih

/-- Garbage collection of loans only changes loans. -/
theorem LoanOnly.gcLoans (Θ : TempTy) (Γ : StackTy) : LoanOnly (gcLoans Θ Γ) Γ :=
  LoanOnly.mapLoans _ _

/-- Type computation only depends on variable types. -/
theorem PlaceTy.loanOnly {Δ : TyEnv} {Γ Γ' : StackTy} (hΓ : LoanOnly Γ Γ') {ω : Own}
    {p : APlaceExpr} {τ : Ty} {ρs : List Region} (h : PlaceTy Δ Γ ω p τ ρs) :
    PlaceTy Δ Γ' ω p τ ρs := h.refine hΓ.refines

/-- Referent well-formedness only depends on variable types. -/
theorem RefTy.loanOnly {Γ Γ' : StackTy} (hΓ : LoanOnly Γ Γ') {R : Referent} {τ : Ty}
    (h : RefTy Γ R τ) : RefTy Γ' R τ := h.refine hΓ.refines

/-- "Type Computation is Preserved under Region Rewriting". -/
theorem PlaceTy.rewrite {Δ Δ' : TyEnv} {Θ : TempTy} {μ : Mode} {Γ Γ' : StackTy} {τ₁ τ₂ : Ty}
    (hr : Rewrite Δ' Θ μ Γ τ₁ τ₂ Γ') {ω : Own} {p : APlaceExpr} {τ : Ty} {ρs : List Region}
    (h : PlaceTy Δ Γ ω p τ ρs) : PlaceTy Δ Γ' ω p τ ρs :=
  h.loanOnly (RewriteJ.loanOnly hr)

/-- Referent well-formedness is preserved under region rewriting. -/
theorem RefTy.rewrite {Δ : TyEnv} {Θ : TempTy} {μ : Mode} {Γ Γ' : StackTy} {τ₁ τ₂ : Ty}
    (hr : Rewrite Δ Θ μ Γ τ₁ τ₂ Γ') {R : Referent} {τ : Ty} (h : RefTy Γ R τ) : RefTy Γ' R τ :=
  h.loanOnly (RewriteJ.loanOnly hr)

/-- Type computation is preserved by outlives judgments. -/
theorem PlaceTy.outlives {Δ Δ' : TyEnv} {Θ : TempTy} {μ : Mode} {Γ Γ' : StackTy}
    {ρ₁ ρ₂ : Region} (ho : Outlives Δ' Θ μ Γ ρ₁ ρ₂ Γ') {ω : Own} {p : APlaceExpr} {τ : Ty}
    {ρs : List Region} (h : PlaceTy Δ Γ ω p τ ρs) : PlaceTy Δ Γ' ω p τ ρs :=
  h.loanOnly (OutlivesJ.loanOnly ho)

/-- Referent well-formedness is preserved by outlives judgments. -/
theorem RefTy.outlives {Δ : TyEnv} {Θ : TempTy} {μ : Mode} {Γ Γ' : StackTy} {ρ₁ ρ₂ : Region}
    (ho : Outlives Δ Θ μ Γ ρ₁ ρ₂ Γ') {R : Referent} {τ : Ty} (h : RefTy Γ R τ) : RefTy Γ' R τ :=
  h.loanOnly (OutlivesJ.loanOnly ho)

/-- Type computation is preserved by garbage collection of loans. -/
theorem PlaceTy.gcLoans {Δ : TyEnv} {Θ : TempTy} {Γ : StackTy} {ω : Own} {p : APlaceExpr}
    {τ : Ty} {ρs : List Region} (h : PlaceTy Δ Γ ω p τ ρs) : PlaceTy Δ (gcLoans Θ Γ) ω p τ ρs :=
  h.loanOnly (LoanOnly.gcLoans Θ Γ).symm

/-- Referent well-formedness is preserved by garbage collection of loans. -/
theorem RefTy.gcLoans {Θ : TempTy} {Γ : StackTy} {R : Referent} {τ : Ty} (h : RefTy Γ R τ) :
    RefTy (gcLoans Θ Γ) R τ :=
  h.loanOnly (LoanOnly.gcLoans Θ Γ).symm

/-! ## Well-typed extensions -/

theorem FrameTy.numVars_cons_var (τ : Ty) (Φ : FrameTy) :
    FrameTy.numVars (.var τ :: Φ) = Φ.numVars + 1 := by
  simp [FrameTy.numVars]

theorem FrameTy.numVars_cons_rgn (L : List Loan) (Φ : FrameTy) :
    FrameTy.numVars (.rgn L :: Φ) = Φ.numVars := by
  simp [FrameTy.numVars]

/-- Pushing a variable on the top frame does not change the types of the existing
variables (which keep their levels). -/
theorem StackTy.varTy_push_var {Γ : StackTy} {ℓ : Nat} {τ : Ty} (hℓ : Γ.varTy ℓ = some τ)
    (τx : Ty) : (Γ.push (.var τx)).varTy ℓ = some τ := by
  cases Γ with
  | nil => simp [StackTy.varTy] at hℓ
  | cons Φ Γ =>
    simp only [StackTy.push, StackTy.varTy, FrameTy.numVars_cons_var] at hℓ ⊢
    by_cases h₁ : StackTy.numVars Γ ≤ ℓ
    · rw [if_pos h₁] at hℓ ⊢
      by_cases h₂ : ℓ - StackTy.numVars Γ < Φ.numVars
      · rw [if_pos h₂] at hℓ
        rw [if_pos (by omega)]
        have e : Φ.numVars + 1 - 1 - (ℓ - StackTy.numVars Γ) =
            (Φ.numVars - 1 - (ℓ - StackTy.numVars Γ)) + 1 := by omega
        rw [e]
        simpa [FrameTy.varAt] using hℓ
      · rw [if_neg h₂] at hℓ
        simp at hℓ
    · rw [if_neg h₁] at hℓ ⊢
      exact hℓ

/-- Pushing a region on the top frame does not change any variable type. -/
theorem StackTy.varTy_push_rgn (Γ : StackTy) (L : List Loan) (ℓ : Nat) :
    (Γ.push (.rgn L)).varTy ℓ = Γ.varTy ℓ := by
  cases Γ with
  | nil => simp [StackTy.push, StackTy.varTy, FrameTy.numVars]
  | cons Φ Γ => simp only [StackTy.push, StackTy.varTy, FrameTy.numVars_cons_rgn, FrameTy.varAt]

/-- "Type Computation is Preserved under Well-Typed Extensions". -/
theorem PlaceTy.push_var {Δ : TyEnv} {Γ : StackTy} {ω : Own} {p : APlaceExpr} {τ : Ty}
    {ρs : List Region} (h : PlaceTy Δ Γ ω p τ ρs) (τx : Ty) :
    PlaceTy Δ (Γ.push (.var τx)) ω p τ ρs := by
  induction h with
  | var ℓ τ hv hsi => exact .var ℓ τ (StackTy.varTy_push_var hv τx) hsi
  | proj p τs i τ ρs _ hi ih => exact .proj p τs i τ ρs ih hi
  | deref p ρ ω' τ ρs _ hle ih => exact .deref p ρ ω' τ ρs ih hle

/-- Referent well-formedness is preserved under well-typed extensions. -/
theorem RefTy.push_var {Γ : StackTy} {R : Referent} {τ : Ty} (h : RefTy Γ R τ) (τx : Ty) :
    RefTy (Γ.push (.var τx)) R τ := by
  induction h with
  | id ℓ τ hv hsi => exact .id ℓ τ (StackTy.varTy_push_var hv τx) hsi
  | proj R τs i τ _ hi ih => exact .proj R τs i τ ih hi
  | idxArray R τ n i _ hi ih => exact .idxArray R τ n i ih hi
  | idxSlice root steps a b i τ _ hi ih => exact .idxSlice root steps a b i τ ih hi
  | sliceArray R τ n i j _ hij hj ih => exact .sliceArray R τ n i j ih hij hj
  | sliceSlice root steps a b i j τ _ hij hj ih => exact .sliceSlice root steps a b i j τ ih hij hj

/-- Type computation is preserved when a region is pushed on the top frame. -/
theorem PlaceTy.push_rgn {Δ : TyEnv} {Γ : StackTy} {ω : Own} {p : APlaceExpr} {τ : Ty}
    {ρs : List Region} (h : PlaceTy Δ Γ ω p τ ρs) (L : List Loan) :
    PlaceTy Δ (Γ.push (.rgn L)) ω p τ ρs := by
  induction h with
  | var ℓ τ hv hsi => exact .var ℓ τ ((StackTy.varTy_push_rgn _ _ _).trans hv) hsi
  | proj p τs i τ ρs _ hi ih => exact .proj p τs i τ ρs ih hi
  | deref p ρ ω' τ ρs _ hle ih => exact .deref p ρ ω' τ ρs ih hle

/-- Referent well-formedness is preserved when a region is pushed on the top frame. -/
theorem RefTy.push_rgn {Γ : StackTy} {R : Referent} {τ : Ty} (h : RefTy Γ R τ) (L : List Loan) :
    RefTy (Γ.push (.rgn L)) R τ := by
  induction h with
  | id ℓ τ hv hsi => exact .id ℓ τ ((StackTy.varTy_push_rgn _ _ _).trans hv) hsi
  | proj R τs i τ _ hi ih => exact .proj R τs i τ ih hi
  | idxArray R τ n i _ hi ih => exact .idxArray R τ n i ih hi
  | idxSlice root steps a b i τ _ hi ih => exact .idxSlice root steps a b i τ ih hi
  | sliceArray R τ n i j _ hij hj ih => exact .sliceArray R τ n i j ih hij hj
  | sliceSlice root steps a b i j τ _ hij hj ih => exact .sliceSlice root steps a b i j τ ih hij hj

end Oxide
