module
public import RequestProject.Oxide.Metatheory.Progress.Store

/-!
# Progress, part 2: refinement of stack typings by drops

`T-Drop` (and `T-Move`) replace types in the stack typing by dead types.  The
stack typing `Γ` an expression is checked in is therefore in general only a
*refinement* of the stack typing `Γ₀` satisfied by the stack: it has the same
shape, and its types are obtained from those of `Γ₀` by killing components.
Everything progress needs to know about live places is the same in `Γ` and `Γ₀`.
-/

@[expose] public section

namespace Oxide

variable {G : GlobalEnv}

/-- `TyRef τ τ₀`: `τ` is obtained from `τ₀` by replacing components by dead types. -/
inductive TyRef : Ty → Ty → Prop
  | refl (τ : Ty) : TyRef τ τ
  | dead (τ τ₀ : Ty) : TyRef (.dead τ) τ₀
  | tuple (τs τs₀ : List Ty) (hlen : τs.length = τs₀.length)
      (h : ∀ (i : Nat) (τ τ₀ : Ty), τs[i]? = some τ → τs₀[i]? = some τ₀ → TyRef τ τ₀) :
      TyRef (.tuple τs) (.tuple τs₀)

/-- Refinement of frame entries. -/
def EntryRef : FrameEntry → FrameEntry → Prop
  | .var τ, .var τ₀ => TyRef τ τ₀
  | .rgn _, .rgn _ => True
  | _, _ => False

/-- `Refines Γ Γ₀`: same shape, types refined by `TyRef` (loans are arbitrary). -/
def Refines (Γ Γ₀ : StackTy) : Prop := List.Forall₂ (List.Forall₂ EntryRef) Γ Γ₀

theorem TyRef.trans {τ₁ τ₂ τ₃ : Ty} (h₁ : TyRef τ₁ τ₂) (h₂ : TyRef τ₂ τ₃) : TyRef τ₁ τ₃ := by
  induction h₁ generalizing τ₃ with
  | refl => exact h₂
  | dead => exact .dead _ _
  | tuple τs τs₀ hlen h ih =>
    cases h₂ with
    | refl => exact .tuple τs τs₀ hlen h
    | tuple _ τs₁ hlen' h' =>
      refine .tuple τs τs₁ (hlen.trans hlen') fun i τ τ₁ hi hi₁ => ?_
      obtain ⟨τ₀, hτ₀⟩ : ∃ τ₀, τs₀[i]? = some τ₀ := by
        have : i < τs₀.length := by
          have := (List.getElem?_eq_some_iff.1 hi).1; omega
        exact ⟨_, List.getElem?_eq_getElem this⟩
      exact ih i τ τ₀ hi hτ₀ (h' i τ₀ τ₁ hτ₀ hi₁)

theorem EntryRef.refl (e : FrameEntry) : EntryRef e e := by
  cases e <;> simp [EntryRef, TyRef.refl]

theorem EntryRef.trans {e₁ e₂ e₃ : FrameEntry} (h₁ : EntryRef e₁ e₂) (h₂ : EntryRef e₂ e₃) :
    EntryRef e₁ e₃ := by
  cases e₁ <;> cases e₂ <;> cases e₃ <;> simp_all [EntryRef]
  exact h₁.trans h₂

theorem Refines.refl (Γ : StackTy) : Refines Γ Γ :=
  List.forall₂_same.2 fun _ _ => List.forall₂_same.2 fun e _ => EntryRef.refl e

theorem forall₂_trans {α : Type} {R : α → α → Prop}
    (htr : ∀ {a b c}, R a b → R b c → R a c) {l₁ l₂ l₃ : List α}
    (h₁ : List.Forall₂ R l₁ l₂) (h₂ : List.Forall₂ R l₂ l₃) : List.Forall₂ R l₁ l₃ := by
  induction h₁ generalizing l₃ with
  | nil => cases h₂; exact .nil
  | cons hab _ ih =>
    cases h₂ with
    | cons hbc t => exact .cons (htr hab hbc) (ih t)

theorem Refines.trans {Γ₁ Γ₂ Γ₃ : StackTy} (h₁ : Refines Γ₁ Γ₂) (h₂ : Refines Γ₂ Γ₃) :
    Refines Γ₁ Γ₃ :=
  forall₂_trans (R := List.Forall₂ EntryRef)
    (fun a b => forall₂_trans (R := EntryRef) EntryRef.trans a b) h₁ h₂

theorem TyRef.dead_left_SI {τ τ₀ : Ty} (h : TyRef τ τ₀) (hsi : τ.SI) : τ = τ₀ := by
  induction h with
  | refl => rfl
  | dead => cases hsi
  | tuple τs τs₀ hlen h ih =>
    cases hsi with
    | tuple _ hall =>
      congr 1
      apply List.ext_getElem? fun i => ?_
      cases h1 : τs[i]? with
      | none =>
        have : τs₀.length ≤ i := by rw [← hlen]; exact List.getElem?_eq_none_iff.1 h1
        exact (List.getElem?_eq_none_iff.2 this).symm
      | some τ =>
        have hi : i < τs₀.length := by rw [← hlen]; exact (List.getElem?_eq_some_iff.1 h1).1
        rw [List.getElem?_eq_getElem hi]
        exact congrArg some (ih i τ _ h1 (List.getElem?_eq_getElem hi)
          (hall τ (List.mem_of_getElem? h1)))

theorem TyRef.atPath {τ τ₀ : Ty} (h : TyRef τ τ₀) {q : List Nat} {t : Ty}
    (hq : τ.atPath q = some t) : ∃ t₀, τ₀.atPath q = some t₀ ∧ TyRef t t₀ := by
  induction q generalizing τ τ₀ with
  | nil => simp [Ty.atPath] at hq; subst hq; exact ⟨τ₀, rfl, h⟩
  | cons i q ih =>
    cases h with
    | refl => exact ⟨t, hq, .refl _⟩
    | dead => simp [Ty.atPath] at hq
    | tuple τs τs₀ hlen h =>
      simp only [Ty.atPath] at hq ⊢
      cases h1 : τs[i]? with
      | none => simp [h1] at hq
      | some τi =>
        rw [h1] at hq
        have hi : i < τs₀.length := by rw [← hlen]; exact (List.getElem?_eq_some_iff.1 h1).1
        rw [List.getElem?_eq_getElem hi]
        exact ih (h i τi _ h1 (List.getElem?_eq_getElem hi)) hq

theorem TyRef.setPath_dead {τ τ' t : Ty} {q : List Nat} (h : τ.setPath q (.dead t) = some τ') :
    TyRef τ' τ := by
  induction q generalizing τ τ' with
  | nil => simp [Ty.setPath] at h; subst h; exact .dead _ _
  | cons i q ih =>
    cases τ with
    | tuple τs =>
      simp only [Ty.setPath] at h
      cases h1 : τs[i]? with
      | none => simp [h1] at h
      | some τi =>
        rw [h1] at h
        simp only [Option.map_eq_some_iff] at h
        obtain ⟨τi', hτi', rfl⟩ := h
        refine .tuple _ _ (by simp) fun j a b ha hb => ?_
        by_cases hij : j = i
        · subst hij
          rw [List.getElem?_set_self (List.getElem?_eq_some_iff.1 h1).1] at ha
          cases ha
          rw [h1] at hb; cases hb
          exact ih hτi'
        · rw [List.getElem?_set_ne (Ne.symm hij)] at ha
          rw [ha] at hb; cases hb
          exact .refl _
    | _ => simp [Ty.setPath] at h

/-! ### Frames -/

theorem EntryRef.frame_numVars {Φ Φ₀ : FrameTy} (h : List.Forall₂ EntryRef Φ Φ₀) :
    Φ.numVars = Φ₀.numVars ∧ Φ.numRgns = Φ₀.numRgns := by
  induction h with
  | nil => exact ⟨rfl, rfl⟩
  | @cons a b Φ Φ₀ hab _ ih =>
    cases a <;> cases b <;> simp_all [EntryRef, FrameTy.numVars, FrameTy.numRgns]

theorem EntryRef.frame_varAt {Φ Φ₀ : FrameTy} (h : List.Forall₂ EntryRef Φ Φ₀) {j : Nat}
    {τ : Ty} (hj : Φ.varAt j = some τ) : ∃ τ₀, Φ₀.varAt j = some τ₀ ∧ TyRef τ τ₀ := by
  induction h generalizing j with
  | nil => simp [FrameTy.varAt] at hj
  | @cons a b Φ Φ₀ hab _ ih =>
    cases a <;> cases b <;> simp only [EntryRef] at hab
    · cases j with
      | zero => simp [FrameTy.varAt] at hj ⊢; subst hj; exact hab
      | succ j => simpa [FrameTy.varAt] using ih hj
    · simpa [FrameTy.varAt] using ih hj

theorem EntryRef.frame_setVarAt {Φ : FrameTy} {j : Nat} {τ τ' : Ty} (hj : Φ.varAt j = some τ)
    (hr : TyRef τ' τ) : List.Forall₂ EntryRef (Φ.setVarAt j τ') Φ := by
  induction Φ generalizing j with
  | nil => simp [FrameTy.varAt] at hj
  | cons e Φ ih =>
    cases e with
    | var σ =>
      cases j with
      | zero =>
        simp [FrameTy.varAt] at hj; subst hj
        exact .cons hr (List.forall₂_same.2 fun e _ => EntryRef.refl e)
      | succ j => exact .cons (EntryRef.refl _) (ih (by simpa [FrameTy.varAt] using hj))
    | rgn L => exact .cons (EntryRef.refl _) (ih (by simpa [FrameTy.varAt] using hj))

/-! ### Stack typings -/

theorem Refines.numVars {Γ Γ₀ : StackTy} (h : Refines Γ Γ₀) :
    Γ.numVars = Γ₀.numVars ∧ Γ.numRgns = Γ₀.numRgns := by
  induction h with
  | nil => exact ⟨rfl, rfl⟩
  | cons hΦ _ ih =>
    have := EntryRef.frame_numVars hΦ
    simp_all [StackTy.numVars, StackTy.numRgns]

theorem Refines.idxToLevel {Γ Γ₀ : StackTy} (h : Refines Γ Γ₀) (i : Nat) :
    Γ.idxToLevel i = Γ₀.idxToLevel i := by
  cases h with
  | nil => rfl
  | cons hΦ hΓ =>
    have h1 := EntryRef.frame_numVars hΦ
    have h2 := Refines.numVars (List.Forall₂.cons hΦ hΓ)
    simp only [StackTy.idxToLevel, h1.1, h2.1]

theorem Refines.varTy {Γ Γ₀ : StackTy} (h : Refines Γ Γ₀) {ℓ : Nat} {τ : Ty}
    (hℓ : Γ.varTy ℓ = some τ) : ∃ τ₀, Γ₀.varTy ℓ = some τ₀ ∧ TyRef τ τ₀ := by
  induction h with
  | nil => simp [StackTy.varTy] at hℓ
  | @cons Φ Φ₀ Γ Γ₀ hΦ hΓ ih =>
    have h1 := EntryRef.frame_numVars hΦ
    have h2 := Refines.numVars hΓ
    simp only [StackTy.varTy, h1.1, h2.1] at hℓ ⊢
    split_ifs at hℓ ⊢
    · exact EntryRef.frame_varAt hΦ hℓ
    · exact ih hℓ

theorem Refines.placeTy {Γ Γ₀ : StackTy} (h : Refines Γ Γ₀) {π : APlace} {τ : Ty}
    (hπ : Γ.placeTy π = some τ) : ∃ τ₀, Γ₀.placeTy π = some τ₀ ∧ TyRef τ τ₀ := by
  simp only [StackTy.placeTy, Option.bind_eq_some_iff] at hπ ⊢
  obtain ⟨τx, hx, hp⟩ := hπ
  obtain ⟨τx₀, hx₀, hr⟩ := h.varTy hx
  obtain ⟨t₀, ht₀, hr'⟩ := hr.atPath hp
  exact ⟨t₀, ⟨τx₀, hx₀, ht₀⟩, hr'⟩

theorem Refines.setVarTy {Γ : StackTy} {ℓ : Nat} {τ τ' : Ty} (hℓ : Γ.varTy ℓ = some τ)
    (hr : TyRef τ' τ) : Refines (Γ.setVarTy ℓ τ') Γ := by
  induction Γ with
  | nil => simp [StackTy.varTy] at hℓ
  | cons Φ Γ ih =>
    simp only [StackTy.varTy] at hℓ
    simp only [StackTy.setVarTy]
    split_ifs at hℓ ⊢ with h1 h2
    · exact .cons (EntryRef.frame_setVarAt hℓ hr) (Refines.refl Γ)
    · exact .cons (List.forall₂_same.2 fun e _ => EntryRef.refl e) (ih hℓ)

theorem Refines.setPlaceTy_dead {Γ Γd : StackTy} {π : APlace} {t : Ty}
    (hd : Γ.setPlaceTy π (.dead t) = some Γd) : Refines Γd Γ := by
  simp only [StackTy.setPlaceTy, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hd
  obtain ⟨τx, hx, τx', hx', rfl⟩ := hd
  exact Refines.setVarTy hx (TyRef.setPath_dead hx')

theorem Refines.nil_iff {Γ Γ₀ : StackTy} (h : Refines Γ Γ₀) : Γ = [] ↔ Γ₀ = [] := by
  cases h <;> simp

/-- Place typing only depends on live (sized and initialized) types, which are
preserved by refinement. -/
theorem PlaceTy.refine {Δ : TyEnv} {Γ Γ₀ : StackTy} (hΓ : Refines Γ Γ₀) {ω : Own}
    {p : APlaceExpr} {τ : Ty} {ρs : List Region} (h : PlaceTy Δ Γ ω p τ ρs) :
    PlaceTy Δ Γ₀ ω p τ ρs := by
  induction h with
  | var ℓ τ hv hsi =>
    obtain ⟨τ₀, hτ₀, hr⟩ := hΓ.varTy hv
    have e := hr.dead_left_SI hsi
    subst e
    exact .var ℓ τ hτ₀ hsi
  | proj p τs i τ ρs _ hi ih => exact .proj p τs i τ ρs ih hi
  | deref p ρ ω' τ ρs _ hle ih => exact .deref p ρ ω' τ ρs ih hle

/-- Referent typing is preserved by refinement. -/
theorem RefTy.refine {Γ Γ₀ : StackTy} (hΓ : Refines Γ Γ₀) {R : Referent} {τ : Ty}
    (h : RefTy Γ R τ) : RefTy Γ₀ R τ := by
  induction h with
  | id ℓ τ hv hsi =>
    obtain ⟨τ₀, hτ₀, hr⟩ := hΓ.varTy hv
    have e := hr.dead_left_SI hsi
    subst e
    exact .id ℓ τ hτ₀ hsi
  | proj R τs i τ _ hi ih => exact .proj R τs i τ ih hi
  | idxArray R τ n i _ hi ih => exact .idxArray R τ n i ih hi
  | idxSlice root steps a b i τ _ hi ih => exact .idxSlice root steps a b i τ ih hi
  | sliceArray R τ n i j _ hij hj ih => exact .sliceArray R τ n i j ih hij hj
  | sliceSlice root steps a b i j τ _ hij hj ih => exact .sliceSlice root steps a b i j τ ih hij hj

/-! ### Values typed by the expression judgment -/

/-- A value typed by the expression typing judgment: its output stack typing
refines the input one (only drops can happen), and the value is typed in it. -/
theorem HasType.val_inv' {Δ : TyEnv} {Θ : TempTy} {Γ Γ' : StackTy} {n : Nat} {v : Value}
    {τ : Ty} (h : HasType G Δ Θ Γ (n := n) (.val v) τ Γ') :
    Refines Γ' Γ ∧ HasTypeV G Δ Θ Γ' v τ := by
  change Typing G (TyJ.expr Δ Θ Γ (Term.val v : Term n) τ Γ') at h
  generalize hJ : TyJ.expr Δ Θ Γ (Term.val v : Term n) τ Γ' = J at h
  induction h generalizing Γ with
  | val => cases hJ; exact ⟨Refines.refl _, by assumption⟩
  | drop _ _ _ _ _ _ _ _ _ _ _ hd _ ih =>
    cases hJ
    obtain ⟨h1, h2⟩ := ih rfl
    exact ⟨h1.trans (Refines.setPlaceTy_dead hd), h2⟩
  | _ => cases hJ

end Oxide
