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

/-- Convert the path of a place into a typed path into the declared type of its
root (the only point where an out-of-range projection is detected). -/
def resolve (Γ : StackTy S) (π : APlace S) : Option (TyPath (Γ.varTy π.root).ty) :=
  TyPath.ofList _ π.path

/-- `Γ(π)`: the (maybe-dead) type at a place. -/
def placeTy (Γ : StackTy S) (π : APlace S) : Option (MTy S) :=
  (Γ.resolve π).map (Γ.varTy π.root).st.get

/-- The type at a place, if it is fully initialized. -/
def placeTyI (Γ : StackTy S) (π : APlace S) : Option (Ty S) := (Γ.placeTy π).bind MTy.toTy?

/-- `Γ[π ↦ τ]`: type update at a place. -/
def setPlaceTy (Γ : StackTy S) (π : APlace S) (τ : MTy S) : Option (StackTy S) :=
  (Γ.resolve π).map fun p => Γ.setVarTy π.root ((Γ.varTy π.root).st.set p τ)

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
def rsub (Γ : StackTy S) (p : APExpr S) : StackTy S :=
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

namespace Cap
variable {S : Ctx}

/-- The first captured copy of a variable. -/
def findVar : {f : Ctx} → Cap S f → In .var S → Option (In .var f)
  | _, .nil, _ => none
  | _, .var x c, y => if x.toIn = y then some .here else (c.findVar y).map .there
  | _, .rgn _ c, y => (c.findVar y).map .there

/-- The first captured copy of a region. -/
def findRgn : {f : Ctx} → Cap S f → In .rgn S → Option (In .rgn f)
  | _, .nil, _ => none
  | _, .var _ c, r => (c.findRgn r).map .there
  | _, .rgn r' c, r => if r' = r then some .here else (c.findRgn r).map .there

/-- The renaming sending each captured entry of `S` to its copy in the captured
frame `f`, and every other entry past the new frame boundary. -/
def inv {f : Ctx} (c : Cap S f) : TRen S (f ++ .frame :: S) := ⟨fun {b} _ i =>
  match b, i with
  | .var, i => match c.findVar i with
    | some j => j.inlL
    | none => In.weakenL f (.there i)
  | .rgn, i => match c.findRgn i with
    | some j => j.inlL
    | none => In.weakenL f (.there i)
  | _, i => In.weakenL f (.there i)⟩

/-- The frame typing of a captured frame: the types of the captured variables and
the loan sets of the captured regions, renamed by `ρ`. -/
def frameTy {T : Ctx} (Γ : StackTy S) (ρ : TRen S T) : {f : Ctx} → Cap S f → Option (FrameTy T f)
  | _, .nil => some .nil
  | _, .var x c => do
      pure (.var (← ((Γ.varTy x.toIn).toTy?).map (Ty.rename ρ)) (← frameTy Γ ρ c))
  | _, .rgn r c => (frameTy Γ ρ c).map (.rgn ((Γ.loans r).map (Loan.rename ρ)))

end Cap

/-- The frame captured by a closure (`Φ_c` of `T-Closure`): the types of the
captured variables and the loan sets of the captured regions, where the captured
entries now refer to their copies in the captured frame. -/
def capturedFrame {S f : Ctx} (Γ : StackTy S) (c : Cap S f) : Option (FrameTy (f ++ .frame :: S) f) :=
  c.frameTy Γ c.inv

/-- Captured variables of non-copyable type become dead (`T-Closure`). -/
def killNC {S f : Ctx} (Γ : StackTy S) (c : Cap S f) : StackTy S :=
  c.vars.foldl (fun Γ x => match (Γ.varTy x.toIn).toTy? with
    | some τ => if τ.noncopyable then Γ.setVarTy x.toIn (.dead τ) else Γ
    | none => Γ) Γ

end Oxide
