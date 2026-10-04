module

public import RequestProject.Oxide.Metafunctions.Types

/-!
# Oxide metafunctions, part 2: places

Appendix C of the paper (`places.tex`): prefixes, disjointness and decomposition
of places and place expressions (§3.1, "Places and Place Expressions").
-/

@[expose] public section

namespace Oxide

/-- The innermost place of a place expression: root and leading projections
(`p = p°[π]` with `π` maximal). -/
def APlaceExpr.base (p : APlaceExpr) : APlace :=
  ⟨p.root, (p.ops.takeWhile (· != POp.deref)).filterMap fun
    | .proj i => some i
    | .deref => none⟩

/-- `π₁` is a prefix of `π₂`. -/
def APlace.IsPrefix (π₁ π₂ : APlace) : Prop := π₁.root = π₂.root ∧ π₁.path <+: π₂.path

/-- `π₁ # π₂`: disjointness ("relevance") of places. -/
def APlace.Disjoint (π₁ π₂ : APlace) : Prop := ¬ π₁.IsPrefix π₂ ∧ ¬ π₂.IsPrefix π₁

/-- `p₁ # p₂` on place expressions: their innermost places are disjoint. -/
def APlaceExpr.Disjoint (p₁ p₂ : APlaceExpr) : Prop := p₁.base.Disjoint p₂.base

/-- `p' = p°[p]` for some context `p°` (i.e. `p` is a "prefix" of `p'`). -/
def APlaceExpr.IsPrefix (p p' : APlaceExpr) : Prop := p.root = p'.root ∧ p.ops <+: p'.ops

instance (p p' : APlaceExpr) : Decidable (p.IsPrefix p') := by
  unfold APlaceExpr.IsPrefix; infer_instance

/-- The place expression `*π`. -/
def APlace.derefExpr (π : APlace) : APlaceExpr := ⟨π.root, π.path.map POp.proj ++ [.deref]⟩

/-- The innermost dereferenced place of a place expression, if any:
`p = p°[*π]`, returned as `(π, p°)`. -/
def APlaceExpr.splitDeref (p : APlaceExpr) : Option (APlace × List POp) :=
  if POp.deref ∈ p.ops then
    some (p.base, (p.ops.dropWhile (· != POp.deref)).drop 1)
  else none

end Oxide
