module

public import RequestProject.Oxide.Syntax.Types

/-!
# Oxide syntax, part 3: environments for typechecking

Paper §3.3 ("Environments for Typechecking"), Figure "Environments in Oxide":
frame typings `Φ`, stack typings `Γ`, temporary typings `Θ` and type environments
`Δ`.  Global environments `Σ` are defined with terms (`Syntax/Terms.lean`) since
function definitions contain their bodies.
-/

@[expose] public section

namespace Oxide

/-- Frame typings `Φ` (most recent entry first). -/
abbrev FrameTy := List FrameEntry

/-- Stack typings `Γ ::= • | Γ ‡ Φ` (top frame first). -/
abbrev StackTy := List FrameTy

/-- Temporary (continuation) typings `Θ`. -/
abbrev TempTy := List Ty

/-- Type environments `Δ`: the number of frame variables, abstract regions and
type variables in scope, and the outlives constraints `ϱ₁ :> ϱ₂` (pairs of
abstract-region indices). -/
structure TyEnv where
  nfrm : Nat := 0
  nrgn : Nat := 0
  nty : Nat := 0
  outlives : List (Nat × Nat) := []
  deriving DecidableEq, Repr, Inhabited

/-- Extend `Δ` with the binders `φ̄ : FRM, ϱ̄ : RGN, ᾱ : TYPE` and the bounds `ϱ₁ :> ϱ₂`
of a polymorphic signature (existing region indices are shifted). -/
def TyEnv.extend (Δ : TyEnv) (nφ nϱ nα : Nat) (bounds : List (Nat × Nat)) : TyEnv :=
  { nfrm := Δ.nfrm + nφ, nrgn := Δ.nrgn + nϱ, nty := Δ.nty + nα,
    outlives := bounds ++ Δ.outlives.map fun b => (b.1 + nϱ, b.2 + nϱ) }

end Oxide
