module

public import RequestProject.Oxide.Metafunctions.StackTypings

/-!
# Region-based alias management: place typing and ownership safety

Paper §3.4 ("Region-Based Alias Management"), Figure "Ownership Safety in Oxide";
appendix B.3 ("Ownership Safety").

Type computation for place expressions (`TC-*`, used by ownership safety and by
the typing rules) and the ownership-safety judgment `Δ; Γ; Θ ⊢_ω p ⇒ {ℓ̄}`
(`O-*`).  The paper's `Δ` is part of the stack typing `Γ`.
-/

@[expose] public section

namespace Oxide

/-! ## Type computation for place expressions (`TC-*`) -/

/-- `Δ; Γ ⊢_ω p : τ^XI, {ρ̄}`: the place expression `p` has type `τ` in an `ω`
context, passing through the regions `ρ̄`. -/
inductive PlaceTy {S : Ctx} (Γ : StackTy S) (ω : Own) : APlaceExpr S → XTy S → List (Region S) → Prop
  /-- `TC-Var` -/
  | var (x : In .var S) (τ : Ty S) (h : (Γ.varTy x).toTy? = some τ) : PlaceTy Γ ω ⟨x, []⟩ (.sized τ) []
  /-- `TC-Proj` -/
  | proj (p : APlaceExpr S) (k : Nat) (τs : Fin k → Ty S) (i : Nat) (hi : i < k) (ρs : List (Region S))
      (h : PlaceTy Γ ω p (.sized (.tuple k τs)) ρs) :
      PlaceTy Γ ω ⟨p.root, p.ops ++ [.proj i]⟩ (.sized (τs ⟨i, hi⟩)) ρs
  /-- `TC-Deref` -/
  | deref (p : APlaceExpr S) (ρ : Region S) (ω' : Own) (τ : XTy S) (ρs : List (Region S))
      (h : PlaceTy Γ ω p (.sized (.ref ρ ω' τ)) ρs) (hle : Own.Le ω ω') :
      PlaceTy Γ ω ⟨p.root, p.ops ++ [.deref]⟩ τ (ρs ++ [ρ])

/-! ## Ownership safety (`O-*`) -/

/-- The common side condition of the ownership safety rules: for every region
`r' ↦ {ℓ̄}` in `regions(Γ, Θ)`, either no conflicting loan of `r'` overlaps
`target`, or `r'` is a region of the stack typing that is only held by references
at excluded places (the anonymous regions of closure frames are never in the
second case). -/
def SafeCond {S : Ctx} (Θ : TempTy S) (Γ : StackTy S) (ω : Own) (excl : List (APlace S))
    (target : APlaceExpr S) : Prop :=
  ∀ r' L, (r', L) ∈ regionsOf Γ Θ →
    (∀ l ∈ L, (ω = .uniq ∨ l.own = .uniq) → l.pe.Disjoint target) ∨
    (∃ r, r' = some r ∧
      (∃ π' ω' τ', (π', Ty.ref (.conc r) ω' τ') ∈ Γ.explode) ∧
      (∀ τ ∈ Θ, r ∉ τ.frgns) ∧
      (∀ π' ω' τ', (π', Ty.ref (.conc r) ω' τ') ∈ Γ.explode → π' ∈ excl))

/-- The places excluded when reborrowing through loans `ℓ̄`: the innermost
dereferenced place `π_j` of every loan `ω p_j` with `p_j = p°_j[*π_j]`. -/
def exclOf {S : Ctx} (L : List (Loan S)) : List (APlace S) :=
  L.filterMap fun l => l.pe.splitDeref.map (·.1)

/-- `Δ; Γ; Θ ⊢^{π̄}_ω p ⇒ {ℓ̄}`: it is safe to use `p` `ω`-ly (with reborrow
exclusion list `π̄`), and `p` may point to any of the loans `ℓ̄`. -/
inductive OwnSafe {S : Ctx} (Θ : TempTy S) (Γ : StackTy S) (ω : Own) :
    List (APlace S) → APlaceExpr S → List (Loan S) → Prop
  /-- `O-SafePlace` -/
  | place (excl : List (APlace S)) (π : APlace S) (h : SafeCond Θ Γ ω excl π.toExpr) :
      OwnSafe Θ Γ ω excl π.toExpr [⟨ω, π.toExpr⟩]
  /-- `O-Deref` -/
  | deref (excl : List (APlace S)) (π : APlace S) (ctx : List POp) (r : In .rgn S) (ωπ : Own)
      (τπ : XTy S) (outs : List (List (Loan S)))
      (hπ : Γ.placeTyI π = some (.ref (.conc r) ωπ τπ))
      (hle : Own.Le ω ωπ)
      (hlen : outs.length = (Γ.loans r).length)
      (hrec : ∀ lo ∈ (Γ.loans r).zip outs,
        OwnSafe Θ Γ ω (excl ++ exclOf (Γ.loans r) ++ [π]) (APlaceExpr.plug ctx lo.1.pe) lo.2)
      (hsafe : SafeCond Θ Γ ω (excl ++ exclOf (Γ.loans r) ++ [π]) (APlaceExpr.plug ctx π.derefExpr)) :
      OwnSafe Θ Γ ω excl (APlaceExpr.plug ctx π.derefExpr)
        (outs.flatten ++ [⟨ω, APlaceExpr.plug ctx π.derefExpr⟩])
  /-- `O-DerefAbs` -/
  | derefAbs (excl : List (APlace S)) (π : APlace S) (ctx : List POp) (ϱ : In .abs S) (ωπ : Own)
      (τπ τ : XTy S) (ρs : List (Region S))
      (hπ : Γ.placeTyI π = some (.ref (.abs ϱ) ωπ τπ))
      (htc : PlaceTy Γ ω (APlaceExpr.plug ctx π.derefExpr) τ ρs)
      (hle : Own.Le ω ωπ)
      (hsafe : SafeCond Θ Γ ω (excl ++ [π]) (APlaceExpr.plug ctx π.derefExpr)) :
      OwnSafe Θ Γ ω excl (APlaceExpr.plug ctx π.derefExpr) [⟨ω, APlaceExpr.plug ctx π.derefExpr⟩]

end Oxide
