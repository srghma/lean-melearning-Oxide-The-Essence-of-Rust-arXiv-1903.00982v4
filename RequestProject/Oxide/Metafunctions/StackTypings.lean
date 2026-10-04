module

public import RequestProject.Oxide.Metafunctions.Places

/-!
# Oxide metafunctions, part 3: frame and stack typings

Appendix C of the paper: type lookup and update at places in a stack typing,
`explode`, garbage collection of loans (`gc-loans`), `Γ ⊖ p`, and the
side conditions used by the region-based alias management of §3.4 and the
borrowing rules of §3.5.
-/

@[expose] public section

namespace Oxide

namespace FrameTy
/-- Variable types of a frame, most recent first. -/
def varTys (Φ : FrameTy) : List Ty := Φ.filterMap fun | .var τ => some τ | .rgn _ => none
/-- Loan sets of the region entries of a frame, most recent first. -/
def rgnLoans (Φ : FrameTy) : List (List Loan) := Φ.filterMap fun | .rgn L => some L | .var _ => none
/-- The type of the `j`-th most recent variable of the frame. -/
def varAt : FrameTy → Nat → Option Ty
  | [], _ => none
  | .var τ :: _, 0 => some τ
  | .var _ :: Φ, j + 1 => varAt Φ j
  | .rgn _ :: Φ, j => varAt Φ j
/-- Update the type of the `j`-th most recent variable of the frame. -/
def setVarAt : FrameTy → Nat → Ty → FrameTy
  | [], _, _ => []
  | .var _ :: Φ, 0, τ => .var τ :: Φ
  | .var σ :: Φ, j + 1, τ => .var σ :: setVarAt Φ j τ
  | .rgn L :: Φ, j, τ => .rgn L :: setVarAt Φ j τ
/-- The loans of the `j`-th most recent region of the frame. -/
def rgnAt : FrameTy → Nat → Option (List Loan)
  | [], _ => none
  | .rgn L :: _, 0 => some L
  | .rgn _ :: Φ, j + 1 => rgnAt Φ j
  | .var _ :: Φ, j => rgnAt Φ j
/-- Update the loans of the `j`-th most recent region of the frame. -/
def setRgnAt : FrameTy → Nat → List Loan → FrameTy
  | [], _, _ => []
  | .rgn _ :: Φ, 0, L => .rgn L :: Φ
  | .rgn L' :: Φ, j + 1, L => .rgn L' :: setRgnAt Φ j L
  | .var τ :: Φ, j, L => .var τ :: setRgnAt Φ j L
end FrameTy

namespace StackTy
/-- Total number of variables. -/
def numVars (Γ : StackTy) : Nat := (Γ.map FrameTy.numVars).sum
/-- Total number of regions. -/
def numRgns (Γ : StackTy) : Nat := (Γ.map FrameTy.numRgns).sum
/-- The level of the variable with de Bruijn index `i` (relative to the top frame). -/
def idxToLevel (Γ : StackTy) (i : Nat) : Option Nat :=
  match Γ with
  | [] => none
  | Φ :: _ => if i < Φ.numVars then some (Γ.numVars - 1 - i) else none
/-- `Γ(x)`: the type of the variable at level `ℓ`. -/
def varTy : StackTy → Nat → Option Ty
  | [], _ => none
  | Φ :: Γ, ℓ =>
      if numVars Γ ≤ ℓ then
        (if ℓ - numVars Γ < Φ.numVars then Φ.varAt (Φ.numVars - 1 - (ℓ - numVars Γ)) else none)
      else varTy Γ ℓ
/-- `Γ[x ↦ τ]` for the variable at level `ℓ`. -/
def setVarTy : StackTy → Nat → Ty → StackTy
  | [], _, _ => []
  | Φ :: Γ, ℓ, τ =>
      if numVars Γ ≤ ℓ then Φ.setVarAt (Φ.numVars - 1 - (ℓ - numVars Γ)) τ :: Γ
      else Φ :: setVarTy Γ ℓ τ
/-- `Γ(r)`: the loan set of the region at level `ℓ`. -/
def loans? : StackTy → Nat → Option (List Loan)
  | [], _ => none
  | Φ :: Γ, ℓ =>
      if numRgns Γ ≤ ℓ then
        (if ℓ - numRgns Γ < Φ.numRgns then Φ.rgnAt (Φ.numRgns - 1 - (ℓ - numRgns Γ)) else none)
      else loans? Γ ℓ
/-- `Γ[r ↦ {ℓ̄}]` for the region at level `ℓ`. -/
def setLoans : StackTy → Nat → List Loan → StackTy
  | [], _, _ => []
  | Φ :: Γ, ℓ, L =>
      if numRgns Γ ≤ ℓ then Φ.setRgnAt (Φ.numRgns - 1 - (ℓ - numRgns Γ)) L :: Γ
      else Φ :: setLoans Γ ℓ L
/-- `r ∈ dom(Γ)`. -/
def HasRgn (Γ : StackTy) (ℓ : Nat) : Prop := ∃ L, Γ.loans? ℓ = some L
/-- `Γ(π)`: type lookup at a place. -/
def placeTy (Γ : StackTy) (π : APlace) : Option Ty := (Γ.varTy π.root).bind (·.atPath π.path)
/-- `Γ[π ↦ τ]`: type update at a place. -/
def setPlaceTy (Γ : StackTy) (π : APlace) (τ : Ty) : Option StackTy := do
  let τx ← Γ.varTy π.root
  let τx' ← τx.setPath π.path τ
  pure (Γ.setVarTy π.root τx')
/-- `Γ, e`: extend the top frame (an empty stack typing is treated as one empty frame). -/
def push (Γ : StackTy) (e : FrameEntry) : StackTy :=
  match Γ with
  | [] => [[e]]
  | Φ :: Γ => (e :: Φ) :: Γ
/-- All variable types, indexed by level (oldest first). -/
def allVarTys (Γ : StackTy) : List Ty := (Γ.reverse.map fun Φ => Φ.varTys.reverse).flatten
/-- All loan sets, indexed by region level (oldest first). -/
def allLoans (Γ : StackTy) : List (List Loan) := (Γ.reverse.map fun Φ => Φ.rgnLoans.reverse).flatten
/-- All region bindings `r ↦ {ℓ̄}` with their levels. -/
def rgns (Γ : StackTy) : List (Nat × List Loan) := Γ.allLoans.mapIdx fun ℓ L => (ℓ, L)
/-- The codomain of `Γ` restricted to variables. -/
def cod (Γ : StackTy) : List Ty := Γ.allVarTys
/-- Apply a function to every region binding (given its level). -/
def mapLoans (f : Nat → List Loan → List Loan) : StackTy → StackTy
  | [] => []
  | Φ :: Γ =>
      let base := numRgns Γ
      let q := Φ.numRgns
      let rec go : FrameTy → Nat → FrameTy
        | [], _ => []
        | .rgn L :: Φ', j => .rgn (f (base + q - 1 - j) L) :: go Φ' (j + 1)
        | .var τ :: Φ', j => .var τ :: go Φ' j
      go Φ 0 :: mapLoans f Γ
end StackTy

/-- `explode(π : τ)`: tuples are split into their components. -/
def Ty.explode (π : APlace) : Ty → List (APlace × Ty)
  | .tuple τs => (τs.attach.mapIdx fun i ⟨τ, _⟩ => τ.explode ⟨π.root, π.path ++ [i]⟩).flatten
  | τ => [(π, τ)]

/-- `explode(Γ)`: all exploded bindings of the stack typing. -/
def StackTy.explode (Γ : StackTy) : List (APlace × Ty) :=
  (Γ.allVarTys.mapIdx fun ℓ τ => τ.explode ⟨ℓ, []⟩).flatten

/-- `regions(Γ, Θ)`: the region bindings of `Γ` (with their level) together with
those of the frames captured by closure types occurring in `Γ` or `Θ` (which are
anonymous copies, hence without level). -/
def regionsOf (Γ : StackTy) (Θ : TempTy) : List (Option Nat × List Loan) :=
  Γ.rgns.map (fun r => (some r.1, r.2)) ++
    ((Γ.cod ++ Θ).flatMap fun τ => (τ.closureFrames.map FrameTy.rgnLoans).flatten).map
      fun L => (none, L)

/-- `gc-loans_Θ(Γ)`: empty the loan sets of all regions that occur in no type of
`Θ` or `Γ`. -/
def gcLoans (Θ : TempTy) (Γ : StackTy) : StackTy :=
  let used : List Nat := (Θ ++ Γ.cod).flatMap Ty.frgns
  Γ.mapLoans fun ℓ L => if ℓ ∈ used then L else []

open Classical in
/-- `Φ₁ ⋓ Φ₂` on frames: same variables and types, loan sets are united. -/
noncomputable def FrameTy.union : FrameTy → FrameTy → Option FrameTy
  | [], [] => some []
  | .var τ₁ :: Φ₁, .var τ₂ :: Φ₂ =>
      if τ₁ = τ₂ then (FrameTy.union Φ₁ Φ₂).map (.var τ₁ :: ·) else none
  | .rgn L₁ :: Φ₁, .rgn L₂ :: Φ₂ => (FrameTy.union Φ₁ Φ₂).map (.rgn (L₁ ∪ L₂) :: ·)
  | _, _ => none

/-- `Γ₁ ⋓ Γ₂` on stack typings. -/
noncomputable def StackTy.union : StackTy → StackTy → Option StackTy
  | [], [] => some []
  | Φ₁ :: Γ₁, Φ₂ :: Γ₂ => do
      let Φ ← FrameTy.union Φ₁ Φ₂
      let Γ ← StackTy.union Γ₁ Γ₂
      pure (Φ :: Γ)
  | _, _ => none

/-- `Γ ⊖ p`: remove all loans of the form `p°[p]`. -/
def StackTy.rsub (Γ : StackTy) (p : APlaceExpr) : StackTy :=
  Γ.mapLoans fun _ L => L.filter fun l => !decide (p.IsPrefix l.pe)

/-- `r is unique to π in Γ`. -/
def RgnUniqueTo (r : Nat) (π : APlace) (Γ : StackTy) : Prop :=
  ∀ π' r' ω' τ', (π', Ty.ref (.conc r') ω' τ') ∈ Γ.explode → π = π' ∨ r ≠ r'

/-- `Γ ⊢ r rnrb`: the region `r` is not reborrowed. -/
def NotReborrowed (Γ : StackTy) (r : Nat) : Prop :=
  ∀ π ω τ, (π, Ty.ref (.conc r) ω τ) ∈ Γ.explode →
    ¬ ∃ r' L, (r', L) ∈ Γ.rgns ∧ (⟨ω, π.derefExpr⟩ : Loan) ∈ L

/-- Regions mentioned in the signatures of function types occurring in `Γ` or `Θ`. -/
def closureSigRgns (Θ : TempTy) (Γ : StackTy) : List (List Nat) :=
  (Γ.cod ++ Θ).flatMap fun τ => τ.fnTypes.map fun (ps, r, _) => Ty.frgnsL ps ++ r.frgns

/-- `Γ; Θ ⊢ r rnic`: region `r` is not in a closure's signature. -/
def NotInClosure (Θ : TempTy) (Γ : StackTy) (r : Nat) : Prop :=
  ∀ s ∈ closureSigRgns Θ Γ, r ∉ s

/-- `Γ; Θ ⊢ {r̄} clrs`: the closure restriction. -/
def ClosRestriction (Θ : TempTy) (Γ : StackTy) (rs : List Nat) : Prop :=
  ∀ s ∈ closureSigRgns Θ Γ, (∀ r ∈ rs, r ∈ s) ∨ (∀ r ∈ rs, r ∉ s)

/-- `r₁ occurs before r₂ in Γ` (`OC-*`): with levels this simply means that `r₁`
is older than `r₂` (and `r₂` is bound). -/
def OccursBefore (r₁ r₂ : Nat) (Γ : StackTy) : Prop := r₁ < r₂ ∧ r₂ < Γ.numRgns

/-- `places(Γ)`: the innermost places of all loans. -/
def StackTy.places (Γ : StackTy) : List APlace :=
  Γ.rgns.flatMap fun (_, L) => L.map fun l => l.pe.base

end Oxide
