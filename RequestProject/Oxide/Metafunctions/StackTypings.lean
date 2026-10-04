module

public import RequestProject.Oxide.Metafunctions.Places
public import RequestProject.Oxide.Syntax.Environments

/-!
# Oxide metafunctions, part 4: stack typings

Appendix C of the paper: type lookup and update at places in a stack typing,
`explode`, `regions(Γ, Θ)`, garbage collection of loans (`gc-loans`), the union
`Γ₁ ⋓ Γ₂`, `Γ ⊖ p`, and the side conditions used by the region-based alias
management of §3.4 and the borrowing rules of §3.5.  Also the captured frame of
a closure (`T-Closure`).
-/

@[expose] public section

namespace Oxide

namespace StackTy

variable {S : Ctx}

/-- `Γ(π)`: the (maybe-dead) type at a place. -/
def placeTy (Γ : StackTy S) (π : APlace S) : Option (MTy S) := (Γ.varTy π.root).atPath π.path

/-- The type at a place, if it is fully initialized. -/
def placeTyI (Γ : StackTy S) (π : APlace S) : Option (Ty S) := (Γ.placeTy π).bind MTy.toTy?

/-- `Γ[π ↦ τ]`: type update at a place. -/
def setPlaceTy (Γ : StackTy S) (π : APlace S) (τ : MTy S) : Option (StackTy S) :=
  ((Γ.varTy π.root).setPath π.path τ).map (Γ.setVarTy π.root)

/-- The codomain of `Γ` restricted to variables. -/
def cod (Γ : StackTy S) : List (MTy S) := Γ.slots.varTys.map Prod.snd

/-- `explode(Γ)`: all exploded initialized bindings of the stack typing. -/
def explode (Γ : StackTy S) : List (APlace S × Ty S) :=
  Γ.slots.varTys.flatMap fun p => p.2.explode ⟨p.1, []⟩

/-- All region bindings `r ↦ {ℓ̄}`. -/
def rgns (Γ : StackTy S) : List (In .rgn S × List (Loan S)) := Γ.slots.rgnLoans

/-- `places(Γ)`: the innermost places of all loans. -/
def places (Γ : StackTy S) : List (APlace S) :=
  Γ.rgns.flatMap fun p => p.2.map fun l => l.pe.base

/-- `Γ ⊖ p`: remove all loans of the form `p°[p]`. -/
def rsub (Γ : StackTy S) (p : APlaceExpr S) : StackTy S :=
  Γ.mapLoans fun _ L => L.filter fun l => !decide (p.IsPrefix l.pe)

end StackTy

/-- `regions(Γ, Θ)`: the region bindings of `Γ` together with the (anonymous)
regions of the frames captured by closure types occurring in `Γ` or `Θ`. -/
def regionsOf {S : Ctx} (Γ : StackTy S) (Θ : TempTy S) : List (Option (In .rgn S) × List (Loan S)) :=
  Γ.rgns.map (fun r => (some r.1, r.2)) ++
    ((Γ.cod.flatMap MTy.closureLoans) ++ (Θ.flatMap Ty.closureLoans)).map fun L => (none, L)

/-- The concrete regions occurring in the types of `Θ` and `Γ`. -/
def usedRgns {S : Ctx} (Θ : TempTy S) (Γ : StackTy S) : List (In .rgn S) :=
  Θ.flatMap Ty.frgns ++ Γ.cod.flatMap MTy.frgns

/-- `gc-loans_Θ(Γ)`: empty the loan sets of all regions that occur in no type of
`Θ` or `Γ`. -/
def gcLoans {S : Ctx} (Θ : TempTy S) (Γ : StackTy S) : StackTy S :=
  Γ.mapLoans fun r L => if r ∈ usedRgns Θ Γ then L else []

open Classical in
/-- `Γ₁ ⋓ Γ₂` on the entries: same variable types, loan sets are united. -/
noncomputable def SlotTys.union {Γ : Ctx} : {S : Ctx} → SlotTys Γ S → SlotTys Γ S → Option (SlotTys Γ S)
  | _, .nil, .nil => some .nil
  | _, .var τ₁ a, .var τ₂ b => if τ₁ = τ₂ then (SlotTys.union a b).map (.var τ₁) else none
  | _, .rgn L₁ a, .rgn L₂ b => (SlotTys.union a b).map (.rgn (L₁ ∪ L₂))
  | _, .frame a, .frame b => (SlotTys.union a b).map .frame
  | _, .fvar a, .fvar b => (SlotTys.union a b).map .fvar
  | _, .abs a, .abs b => (SlotTys.union a b).map .abs
  | _, .tvar a, .tvar b => (SlotTys.union a b).map .tvar

open Classical in
/-- `Γ₁ ⋓ Γ₂` on stack typings. -/
noncomputable def StackTy.union {S : Ctx} (Γ₁ Γ₂ : StackTy S) : Option (StackTy S) :=
  if Γ₁.outlives = Γ₂.outlives then (Γ₁.slots.union Γ₂.slots).map fun s => ⟨s, Γ₁.outlives⟩
  else none

/-- `r is unique to π in Γ`. -/
def RgnUniqueTo {S : Ctx} (r : In .rgn S) (π : APlace S) (Γ : StackTy S) : Prop :=
  ∀ π' r' ω' τ', (π', Ty.ref (.conc r') ω' τ') ∈ Γ.explode → π = π' ∨ r ≠ r'

/-- `Γ ⊢ r rnrb`: the region `r` is not reborrowed. -/
def NotReborrowed {S : Ctx} (Γ : StackTy S) (r : In .rgn S) : Prop :=
  ∀ π ω τ, (π, Ty.ref (.conc r) ω τ) ∈ Γ.explode →
    ¬ ∃ r' L, (r', L) ∈ Γ.rgns ∧ (⟨ω, π.derefExpr⟩ : Loan S) ∈ L

/-- Regions mentioned in the signatures of function types occurring in `Γ` or `Θ`. -/
def closureSigRgns {S : Ctx} (Θ : TempTy S) (Γ : StackTy S) : List (List (In .rgn S)) :=
  Γ.cod.flatMap MTy.sigRgns ++ Θ.flatMap Ty.sigRgns

/-- `Γ; Θ ⊢ r rnic`: region `r` is not in a closure's signature. -/
def NotInClosure {S : Ctx} (Θ : TempTy S) (Γ : StackTy S) (r : In .rgn S) : Prop :=
  ∀ s ∈ closureSigRgns Θ Γ, r ∉ s

/-- `Γ; Θ ⊢ {r̄} clrs`: the closure restriction. -/
def ClosRestriction {S : Ctx} (Θ : TempTy S) (Γ : StackTy S) (rs : List (In .rgn S)) : Prop :=
  ∀ s ∈ closureSigRgns Θ Γ, (∀ r ∈ rs, r ∈ s) ∨ (∀ r ∈ rs, r ∉ s)

/-- `r₁ occurs before r₂ in Γ` (`OC-*`): `r₁` is bound before (deeper than) `r₂`. -/
def OccursBefore {S : Ctx} (r₁ r₂ : In .rgn S) : Prop := r₂.toNat < r₁.toNat

/-! ## Closures -/

/-- Build a frame typing of shape `f` from its variable types and loan sets (fails
if `f` contains entries other than variables and regions). -/
def FrameTy.build {T : Ctx} : (f : Ctx) → (In .var f → Option (Ty T)) → (In .rgn f → List (Loan T)) →
    Option (FrameTy T f)
  | [], _, _ => some .nil
  | .var :: f, gv, gr => do
      pure (.var (← gv .here) (← FrameTy.build f (fun j => gv j.there) (fun j => gr j.there)))
  | .rgn :: f, gv, gr =>
      (FrameTy.build f (fun j => gv j.there) (fun j => gr j.there)).map (.rgn (gr .here))
  | _ :: _, _, _ => none

/-- The frame captured by a closure (`Φ_c` of `T-Closure`): the types of the
selected variables and the loan sets of the selected regions, where the selected
entries now refer to their copies in the captured frame. -/
def capturedFrame {S f : Ctx} (Γ : StackTy S) (s : Sel f S) : Option (FrameTy (f ++ .frame :: S) f) :=
  FrameTy.build f (fun j => ((Γ.varTy (s.renF j)).toTy?).map (Ty.rename s.inv))
    (fun j => (Γ.loans (s.renF j)).map (Loan.rename s.inv))

/-- Captured variables of non-copyable type become dead (`T-Closure`). -/
def killNC {S f : Ctx} (Γ : StackTy S) (s : Sel f S) : StackTy S :=
  s.selVars.foldl (fun Γ x => match (Γ.varTy x).toTy? with
    | some τ => if τ.noncopyable then Γ.setVarTy x (.dead τ) else Γ
    | none => Γ) Γ

end Oxide
