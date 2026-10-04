module

public import RequestProject.Oxide.Metafunctions.Types

/-!
# Oxide metafunctions, part 3: places

Appendix C of the paper (`places.tex`): prefixes, disjointness and decomposition
of places and place expressions (§3.1, "Places and Place Expressions").
-/

@[expose] public section

namespace Oxide

variable {Γ : Ctx}

/-- The innermost place of a place expression: root and leading projections
(`p = p°[π]` with `π` maximal). -/
def APlaceExpr.base (p : APlaceExpr Γ) : APlace Γ :=
  ⟨p.root, (p.ops.takeWhile (· != POp.deref)).filterMap fun
    | .proj i => some i
    | .deref => none⟩

/-- `π₁` is a prefix of `π₂`. -/
def APlace.IsPrefix (π₁ π₂ : APlace Γ) : Prop := π₁.root = π₂.root ∧ π₁.path <+: π₂.path

/-- `π₁ # π₂`: disjointness of places. -/
def APlace.Disjoint (π₁ π₂ : APlace Γ) : Prop := ¬ π₁.IsPrefix π₂ ∧ ¬ π₂.IsPrefix π₁

/-- `p₁ # p₂` on place expressions: their innermost places are disjoint. -/
def APlaceExpr.Disjoint (p₁ p₂ : APlaceExpr Γ) : Prop := p₁.base.Disjoint p₂.base

/-- `p' = p°[p]` for some context `p°`. -/
def APlaceExpr.IsPrefix (p p' : APlaceExpr Γ) : Prop := p.root = p'.root ∧ p.ops <+: p'.ops

instance (p p' : APlaceExpr Γ) : Decidable (p.IsPrefix p') := by
  unfold APlaceExpr.IsPrefix; infer_instance

/-- The place expression `*π`. -/
def APlace.derefExpr (π : APlace Γ) : APlaceExpr Γ := ⟨π.root, π.path.map POp.proj ++ [.deref]⟩

/-- The innermost dereferenced place of a place expression, if any:
`p = p°[*π]`, returned as `(π, p°)`. -/
def APlaceExpr.splitDeref (p : APlaceExpr Γ) : Option (APlace Γ × List POp) :=
  if POp.deref ∈ p.ops then
    some (p.base, (p.ops.dropWhile (· != POp.deref)).drop 1)
  else none

/-- The innermost place `π` of a referent `𝓡 = 𝓡°[π]`. -/
def Referent.base (R : Referent Γ) : APlace Γ :=
  ⟨R.root, (R.steps.takeWhile fun | .proj _ => true | _ => false).filterMap fun
    | .proj i => some i
    | _ => none⟩

end Oxide
