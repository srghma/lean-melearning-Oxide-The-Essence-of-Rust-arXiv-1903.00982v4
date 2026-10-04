module

public import RequestProject.Oxide.Metafunctions.Types

/-!
# Oxide metafunctions, part 3: places

Appendix C of the paper (`places.tex`): prefixes, disjointness and decomposition
of places and place expressions (§3.1, "Places and Place Expressions").  Since
place expressions are structured by their dereferences, the decompositions
`p = p°[π]` and `p = p°[*π]` are plain recursions.
-/

@[expose] public section

namespace Oxide

variable {Γ : Ctx}

/-- The innermost place of a place expression (`p = p°[π]` with `π` maximal). -/
def APExpr.base : APExpr Γ → APlace Γ
  | .place π => π
  | .deref p _ => p.base

/-- `π₁` is a prefix of `π₂`. -/
def APlace.IsPrefix (π₁ π₂ : APlace Γ) : Prop := π₁.root = π₂.root ∧ π₁.path <+: π₂.path

/-- `π₁ # π₂`: disjointness of places. -/
def APlace.Disjoint (π₁ π₂ : APlace Γ) : Prop := ¬ π₁.IsPrefix π₂ ∧ ¬ π₂.IsPrefix π₁

/-- `p₁ # p₂` on place expressions: their innermost places are disjoint. -/
def APExpr.Disjoint (p₁ p₂ : APExpr Γ) : Prop := p₁.base.Disjoint p₂.base

/-- Whether `p' = p°[p]` for some context `p°`. -/
def APExpr.isPrefixOf (p : APExpr Γ) : APExpr Γ → Bool
  | .place π' => match p with
    | .place π => π.root == π'.root && π.path.isPrefixOf π'.path
    | .deref _ _ => false
  | .deref p'' q => p.isPrefixOf p'' || match p with
    | .deref p₀ q₀ => p₀ == p'' && q₀.isPrefixOf q
    | .place _ => false

/-- `p' = p°[p]` for some context `p°`. -/
def APExpr.IsPrefix (p p' : APExpr Γ) : Prop := p.isPrefixOf p' = true

instance (p p' : APExpr Γ) : Decidable (p.IsPrefix p') := by
  unfold APExpr.IsPrefix; infer_instance

/-- The innermost dereferenced place of a place expression, if any:
`p = p°[*π]`, returned as `(π, p°)`. -/
def APExpr.splitDeref : APExpr Γ → Option (APlace Γ × PCtx)
  | .place _ => none
  | .deref (.place π) q => some (π, ⟨q, []⟩)
  | .deref p q => (p.splitDeref).map fun (π, c) => (π, { c with groups := c.groups ++ [q] })

end Oxide
