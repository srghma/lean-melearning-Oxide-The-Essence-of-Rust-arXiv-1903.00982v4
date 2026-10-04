module

public import RequestProject.Oxide.Metafunctions.Terms

/-!
# Region-based alias management: place typing and ownership safety

Paper §3.4 ("Region-Based Alias Management"), Figure "Ownership Safety in Oxide";
appendix B.3 ("Ownership Safety").

Type computation for place expressions (`TC-*`, used by ownership safety and
by the typing rules) and the ownership-safety judgment
`Δ; Γ ⊢_ω p ⇒ {ℓ̄}` (`O-*`).

Metavariable sorts of the paper (`τ^SI`, `τ^XI`, `τ^SD`, `τ^SX`) are turned into
explicit premises using the predicates `Ty.SI`, `Ty.XI`, `Ty.SD`, `Ty.SX`.
-/

@[expose] public section

namespace Oxide

/-! ## Type computation for place expressions (`TC-*`) -/

/-- `Δ; Γ ⊢_ω p : τ, {ρ̄}`: the place expression `p` has type `τ` in an `ω`
context, passing through the regions `ρ̄`. -/
inductive PlaceTy (Δ : TyEnv) (Γ : StackTy) (ω : Own) : APlaceExpr → Ty → List Region → Prop
  | var (ℓ : Nat) (τ : Ty) (h : Γ.varTy ℓ = some τ) (hsi : τ.SI) : PlaceTy Δ Γ ω ⟨ℓ, []⟩ τ []
  | proj (p : APlaceExpr) (τs : List Ty) (i : Nat) (τ : Ty) (ρs : List Region)
      (h : PlaceTy Δ Γ ω p (.tuple τs) ρs) (hi : τs[i]? = some τ) :
      PlaceTy Δ Γ ω ⟨p.root, p.ops ++ [.proj i]⟩ τ ρs
  | deref (p : APlaceExpr) (ρ : Region) (ω' : Own) (τ : Ty) (ρs : List Region)
      (h : PlaceTy Δ Γ ω p (.ref ρ ω' τ) ρs) (hle : Own.Le ω ω') :
      PlaceTy Δ Γ ω ⟨p.root, p.ops ++ [.deref]⟩ τ (ρs ++ [ρ])

/-! ## Ownership safety (`O-*`) -/

/-- The common side condition of the ownership safety rules: for every region
`r' ↦ {ℓ̄}` in `regions(Γ, Θ)`, either no conflicting loan of `r'` overlaps
`target`, or `r'` is a region of the stack typing (with level `ℓ`) that is only held
by references at excluded places (the anonymous regions of closure frames are
never in the second case). -/
def SafeCond (Θ : TempTy) (Γ : StackTy) (ω : Own) (excl : List APlace)
    (target : APlaceExpr) : Prop :=
  ∀ r' L, (r', L) ∈ regionsOf Γ Θ →
    (∀ l ∈ L, (ω = .uniq ∨ l.own = .uniq) → l.pe.Disjoint target) ∨
    (∃ ℓ, r' = some ℓ ∧
      (∃ π' ω' τ', (π', Ty.ref (.conc ℓ) ω' τ') ∈ Γ.explode) ∧
      (∀ τ ∈ Θ, ℓ ∉ τ.frgns) ∧
      (∀ π' ω' τ', (π', Ty.ref (.conc ℓ) ω' τ') ∈ Γ.explode → π' ∈ excl))

/-- The places excluded when reborrowing through loans `ℓ̄`: the innermost
dereferenced place `π_j` of every loan `ω p_j` with `p_j = p°_j[*π_j]`. -/
def exclOf (L : List Loan) : List APlace := L.filterMap fun l => l.pe.splitDeref.map (·.1)

/-- `Δ; Γ; Θ ⊢^{π̄}_ω p ⇒ {ℓ̄}`: it is safe to use `p` `ω`-ly (with reborrow
exclusion list `π̄`), and `p` may point to any of the loans `ℓ̄`. -/
inductive OwnSafe (Δ : TyEnv) (Θ : TempTy) (Γ : StackTy) (ω : Own) :
    List APlace → APlaceExpr → List Loan → Prop
  /-- `O-SafePlace` -/
  | place (excl : List APlace) (π : APlace) (h : SafeCond Θ Γ ω excl π.toExpr) :
      OwnSafe Δ Θ Γ ω excl π.toExpr [⟨ω, π.toExpr⟩]
  /-- `O-Deref` -/
  | deref (excl : List APlace) (π : APlace) (ctx : List POp) (r : Nat) (ωπ : Own)
      (τπ : Ty) (L : List Loan) (outs : List (List Loan))
      (hπ : Γ.placeTy π = some (.ref (.conc r) ωπ τπ))
      (hr : Γ.loans? r = some L)
      (hle : Own.Le ω ωπ)
      (hlen : outs.length = L.length)
      (hrec : ∀ lo ∈ L.zip outs,
        OwnSafe Δ Θ Γ ω (excl ++ exclOf L ++ [π]) (APlaceExpr.plug ctx lo.1.pe) lo.2)
      (hsafe : SafeCond Θ Γ ω (excl ++ exclOf L ++ [π]) (APlaceExpr.plug ctx π.derefExpr)) :
      OwnSafe Δ Θ Γ ω excl (APlaceExpr.plug ctx π.derefExpr)
        (outs.flatten ++ [⟨ω, APlaceExpr.plug ctx π.derefExpr⟩])
  /-- `O-DerefAbs` -/
  | derefAbs (excl : List APlace) (π : APlace) (ctx : List POp) (ϱ : Nat) (ωπ : Own)
      (τπ τ : Ty) (ρs : List Region)
      (hπ : Γ.placeTy π = some (.ref (.abs ϱ) ωπ τπ))
      (htc : PlaceTy Δ Γ ω (APlaceExpr.plug ctx π.derefExpr) τ ρs)
      (hle : Own.Le ω ωπ)
      (hsafe : SafeCond Θ Γ ω (excl ++ [π]) (APlaceExpr.plug ctx π.derefExpr)) :
      OwnSafe Δ Θ Γ ω excl (APlaceExpr.plug ctx π.derefExpr)
        [⟨ω, APlaceExpr.plug ctx π.derefExpr⟩]

end Oxide
