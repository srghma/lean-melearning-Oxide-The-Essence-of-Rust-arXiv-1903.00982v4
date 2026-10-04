module
public import RequestProject.Oxide.Metatheory.Statements
public import Mathlib.Data.List.Forall2

/-!
# Progress, part 1: stacks satisfying stack typings

Basic facts about `StoreValid`: the shape of a valid stack matches the shape of
its stack typing, and variables of the stack typing are bound to values of
their type.
-/

@[expose] public section

namespace Oxide

variable {G : GlobalEnv}

theorem StoreValid.cons_inv {Γ : StackTy} {σ : Stack} {Φ : FrameTy} {ς : StackFrame}
    (h : StoreValid G (Φ :: Γ) (ς :: σ)) :
    StoreValid G Γ σ ∧ List.Forall₂ (FrameOK G (Φ :: Γ)) Φ ς := by
  cases h with
  | frame _ _ _ _ h hv => exact ⟨h, hv⟩

theorem StoreValid.nil_left {σ : Stack} (h : StoreValid G [] σ) : σ = [] := by
  cases h; rfl

theorem StoreValid.cons_left {Φ : FrameTy} {Γ : StackTy} {σ : Stack}
    (h : StoreValid G (Φ :: Γ) σ) : ∃ ς σ', σ = ς :: σ' := by
  cases h with
  | frame _ σ' _ ς _ _ => exact ⟨ς, σ', rfl⟩

theorem FrameOK.numVars {Γf : StackTy} {Φ : FrameTy} {ς : StackFrame}
    (h : List.Forall₂ (FrameOK G Γf) Φ ς) :
    Φ.numVars = ς.numVals ∧ Φ.numRgns = ς.numRgns := by
  induction h with
  | nil => exact ⟨rfl, rfl⟩
  | @cons e s Φ ς hes _ ih =>
    cases e <;> cases s <;> simp_all [FrameOK, FrameTy.numVars, FrameTy.numRgns,
      StackFrame.numVals, StackFrame.numRgns]

theorem FrameOK.varAt {Γf : StackTy} {Φ : FrameTy} {ς : StackFrame}
    (h : List.Forall₂ (FrameOK G Γf) Φ ς) {j : Nat} {τ : Ty} (hj : Φ.varAt j = some τ) :
    ∃ v, ς.valAt j = some v ∧ HasTypeV G {} [] Γf v τ := by
  induction h generalizing j with
  | nil => simp [FrameTy.varAt] at hj
  | @cons e s Φ ς hes _ ih =>
    cases e <;> cases s <;> simp only [FrameOK] at hes
    · cases j with
      | zero => simp [FrameTy.varAt] at hj; subst hj; exact ⟨_, rfl, hes⟩
      | succ j => simpa [FrameTy.varAt, StackFrame.valAt] using ih hj
    · simpa [FrameTy.varAt, StackFrame.valAt] using ih hj

theorem FrameTy.varAt_of_lt {Φ : FrameTy} {j : Nat} (h : j < Φ.numVars) :
    ∃ τ, Φ.varAt j = some τ := by
  induction Φ generalizing j with
  | nil => simp [FrameTy.numVars] at h
  | cons e Φ ih =>
    cases e with
    | var τ =>
      cases j with
      | zero => exact ⟨τ, rfl⟩
      | succ j =>
        simp [FrameTy.numVars] at h
        exact ih (by simpa [FrameTy.numVars] using h)
    | rgn L =>
      simp [FrameTy.numVars] at h
      exact ih (by simpa [FrameTy.numVars] using h)

theorem FrameOK.valAt_of_lt {Γf : StackTy} {Φ : FrameTy} {ς : StackFrame}
    (h : List.Forall₂ (FrameOK G Γf) Φ ς) {j : Nat} (hj : j < Φ.numVars) :
    ∃ v, ς.valAt j = some v := by
  obtain ⟨τ, hτ⟩ := FrameTy.varAt_of_lt hj
  obtain ⟨v, hv, _⟩ := FrameOK.varAt h hτ
  exact ⟨v, hv⟩

theorem StoreValid.size {Γ : StackTy} {σ : Stack} (h : StoreValid G Γ σ) :
    Γ.numVars = σ.size ∧ Γ.numRgns = σ.numRgns := by
  induction h with
  | empty => exact ⟨rfl, rfl⟩
  | frame Γ σ Φ ς _ hv ih =>
    have := FrameOK.numVars (G := G) hv
    simp_all [StackTy.numVars, StackTy.numRgns, Stack.size, Stack.numRgns]

theorem StoreValid.drop {Γ : StackTy} {σ : Stack} (h : StoreValid G Γ σ) (k : Nat) :
    StoreValid G (Γ.drop k) (σ.drop k) := by
  induction h generalizing k with
  | empty => simpa using StoreValid.empty
  | frame Γ σ Φ ς h hv ih =>
    cases k with
    | zero => exact StoreValid.frame Γ σ Φ ς h hv
    | succ k => simpa using ih k

theorem Stack.get?_lt {σ : Stack} {ℓ : Nat} {v : Value} (h : σ.get? ℓ = some v) :
    ℓ < σ.size := by
  induction σ with
  | nil => simp [Stack.get?] at h
  | cons ς σ ih =>
    simp only [Stack.get?] at h
    have e : Stack.size (ς :: σ) = ς.numVals + Stack.size σ := by
      simp [Stack.size]
    rw [e]
    split_ifs at h with h1 h2
    · omega
    · have := ih h
      omega

theorem Stack.get?_drop {σ : Stack} {k ℓ : Nat} {v : Value} (h : Stack.get? (σ.drop k) ℓ = some v) :
    σ.get? ℓ = some v := by
  induction σ generalizing k with
  | nil => simpa using h
  | cons ς σ ih =>
    cases k with
    | zero => simpa using h
    | succ k =>
      simp only [List.drop_succ_cons] at h
      have h' := ih h
      have := Stack.get?_lt h'
      simp only [Stack.get?]
      rw [if_neg (by omega)]
      exact h'

theorem Stack.read_drop {σ : Stack} {k : Nat} {R : Referent} {v : Value}
    (h : Stack.read (σ.drop k) R = some v) : σ.read R = some v := by
  unfold Stack.read at *
  cases hg : Stack.get? (σ.drop k) R.root with
  | none => simp [hg] at h
  | some w => rw [hg] at h; rw [Stack.get?_drop hg]; exact h

/-- Variables of the stack typing are bound in a valid stack to values of their
type (typed in a suffix of the stack typing). -/
theorem StoreValid.lookup {Γ : StackTy} {σ : Stack} (h : StoreValid G Γ σ) {ℓ : Nat} {τ : Ty}
    (hℓ : Γ.varTy ℓ = some τ) :
    ∃ v k, σ.get? ℓ = some v ∧ HasTypeV G {} [] (Γ.drop k) v τ := by
  induction h with
  | empty => simp [StackTy.varTy] at hℓ
  | frame Γ σ Φ ς h hv ih =>
    have hs := (StoreValid.size h).1
    have hf := (FrameOK.numVars (G := G) hv).1
    simp only [StackTy.varTy] at hℓ
    simp only [Stack.get?]
    split_ifs at hℓ with h1 h2
    · obtain ⟨v, hv1, hv2⟩ := FrameOK.varAt hv hℓ
      refine ⟨v, 0, ?_, by simpa using hv2⟩
      rw [if_pos (by omega), if_pos (by omega), ← hf, ← hs]
      exact hv1
    · obtain ⟨v, k, hv1, hv2⟩ := ih hℓ
      refine ⟨v, k + 1, ?_, by simpa using hv2⟩
      rw [if_neg (by omega)]
      exact hv1

end Oxide
