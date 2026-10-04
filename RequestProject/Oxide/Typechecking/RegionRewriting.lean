module

public import RequestProject.Oxide.AliasManagement.OwnershipSafety

/-!
# Typechecking, part 1: region rewriting and outlives

Paper §3.5 ("Typechecking Oxide Programs"), paragraph "Region Rewriting and
Outlives" and Figure "Region Rewriting and Outlives Relations in Oxide";
appendix B.2 ("Region Rewriting & Outlives Relations").
-/

@[expose] public section

namespace Oxide

/-- Region rewriting modes `μ ::= + | ⊞ | =`. -/
inductive Mode where
  | combine
  | combineUnrest
  | noop
  deriving DecidableEq, Repr

/-! ## Outlives and region rewriting -/

/-- The forms of the outlives judgments: a single constraint `ρ₁ :> ρ₂`, or a list
of constraints `ρ₁ :> ϱ, …, ρₙ :> ϱ` with a common abstract right-hand side. -/
inductive OutlivesForm where
  | one (Γ : StackTy) (ρ₁ ρ₂ : Region) (Γ' : StackTy)
  | all (Γ : StackTy) (ρs : List Region) (ϱ : Nat) (Γ' : StackTy)

/-- The outlives judgments (`OL-*`), as a single inductive family indexed by the
form of the judgment (see `Outlives` and `OutlivesAll` below). -/
inductive OutlivesJ (Δ : TyEnv) (Θ : TempTy) : Mode → OutlivesForm → Prop
  | refl (μ : Mode) (Γ : StackTy) (ρ : Region) : OutlivesJ Δ Θ μ (.one Γ ρ ρ Γ)
  | trans (μ : Mode) (Γ Γ' Γ'' : StackTy) (ϱ₁ ϱ₂ ϱ₃ : Nat)
      (h₁ : OutlivesJ Δ Θ μ (.one Γ (.abs ϱ₁) (.abs ϱ₂) Γ'))
      (h₂ : OutlivesJ Δ Θ μ (.one Γ' (.abs ϱ₂) (.abs ϱ₃) Γ'')) :
      OutlivesJ Δ Θ μ (.one Γ (.abs ϱ₁) (.abs ϱ₃) Γ'')
  /-- `OL-CombineConcrete` -/
  | combine (Γ : StackTy) (r₁ r₂ : Nat) (L₁ L₂ : List Loan)
      (hnrb₁ : NotReborrowed Γ r₁) (hnrb₂ : NotReborrowed Γ r₂)
      (hclrs : ClosRestriction Θ Γ [r₁, r₂]) (hob : OccursBefore r₁ r₂ Γ)
      (h₁ : Γ.loans? r₁ = some L₁) (h₂ : Γ.loans? r₂ = some L₂) :
      OutlivesJ Δ Θ .combine (.one Γ (.conc r₁) (.conc r₂) (Γ.setLoans r₂ (L₁ ∪ L₂)))
  /-- `OL-CombineConcreteUnrestricted` -/
  | combineUnrest (Γ : StackTy) (r₁ r₂ : Nat) (L₁ L₂ : List Loan)
      (hnrb₁ : NotReborrowed Γ r₁) (hnrb₂ : NotReborrowed Γ r₂)
      (hob : OccursBefore r₁ r₂ Γ)
      (h₁ : Γ.loans? r₁ = some L₁) (h₂ : Γ.loans? r₂ = some L₂) :
      OutlivesJ Δ Θ .combineUnrest (.one Γ (.conc r₁) (.conc r₂) (Γ.setLoans r₂ (L₁ ∪ L₂)))
  /-- `OL-CheckConcrete` -/
  | check (Γ : StackTy) (r₁ r₂ : Nat)
      (hnrb₁ : NotReborrowed Γ r₁) (hnrb₂ : NotReborrowed Γ r₂)
      (hob : OccursBefore r₁ r₂ Γ) :
      OutlivesJ Δ Θ .noop (.one Γ (.conc r₁) (.conc r₂) Γ)
  /-- `OL-BothAbstract` -/
  | bothAbs (μ : Mode) (Γ : StackTy) (ϱ₁ ϱ₂ : Nat)
      (h₁ : ϱ₁ < Δ.nrgn) (h₂ : ϱ₂ < Δ.nrgn) (h : (ϱ₁, ϱ₂) ∈ Δ.outlives) :
      OutlivesJ Δ Θ μ (.one Γ (.abs ϱ₁) (.abs ϱ₂) Γ)
  /-- `OL-ConcreteAbstract` -/
  | concAbs (μ : Mode) (Γ Γ' : StackTy) (r ϱ : Nat) (L : List Loan)
      (ρss : List (List Region))
      (hL : Γ.loans? r = some L) (hne : L ≠ [])
      (hnp : ∀ l ∈ L, ¬ l.pe.IsPlace)
      (hlen : ρss.length = L.length)
      (htc : ∀ lρ ∈ L.zip ρss, ∃ τ, PlaceTy Δ Γ .shrd lρ.1.pe τ lρ.2)
      (hϱ : ϱ < Δ.nrgn)
      (hall : OutlivesJ Δ Θ μ (.all Γ ρss.flatten ϱ Γ')) :
      OutlivesJ Δ Θ μ (.one Γ (.conc r) (.abs ϱ) Γ')
  /-- `OL-AbstractConcrete` -/
  | absConc (μ : Mode) (Γ : StackTy) (ϱ r : Nat)
      (hϱ : ϱ < Δ.nrgn) (hr : Γ.HasRgn r) :
      OutlivesJ Δ Θ μ (.one Γ (.abs ϱ) (.conc r) Γ)
  /-- no constraints -/
  | allNil (μ : Mode) (Γ : StackTy) (ϱ : Nat) : OutlivesJ Δ Θ μ (.all Γ [] ϱ Γ)
  /-- `ρ :> ϱ` followed by the remaining constraints, threading the stack typing -/
  | allCons (μ : Mode) (Γ Γ' Γ'' : StackTy) (ρ : Region) (ρs : List Region) (ϱ : Nat)
      (h : OutlivesJ Δ Θ μ (.one Γ ρ (.abs ϱ) Γ')) (t : OutlivesJ Δ Θ μ (.all Γ' ρs ϱ Γ'')) :
      OutlivesJ Δ Θ μ (.all Γ (ρ :: ρs) ϱ Γ'')

/-- `Δ; Γ; Θ ⊢^μ ρ₁ :> ρ₂ ⊣ Γ'`: `ρ₁` outlives `ρ₂`, rewriting `Γ` according to `μ`. -/
abbrev Outlives (Δ : TyEnv) (Θ : TempTy) (μ : Mode) (Γ : StackTy) (ρ₁ ρ₂ : Region)
    (Γ' : StackTy) : Prop := OutlivesJ Δ Θ μ (.one Γ ρ₁ ρ₂ Γ')

/-- `ρ₁ :> ϱ, …, ρₙ :> ϱ`, threading the stack typing. -/
abbrev OutlivesAll (Δ : TyEnv) (Θ : TempTy) (μ : Mode) (Γ : StackTy) (ρs : List Region)
    (ϱ : Nat) (Γ' : StackTy) : Prop := OutlivesJ Δ Θ μ (.all Γ ρs ϱ Γ')

/-- `Δ; Γ; Θ ⊢ ρ̄₁ :> ρ̄₂ ⊣ Γ'` (`OL-Bounds`). -/
inductive OutlivesMany (Δ : TyEnv) (Θ : TempTy) (μ : Mode) :
    StackTy → List (Region × Region) → StackTy → Prop
  | nil (Γ : StackTy) : OutlivesMany Δ Θ μ Γ [] Γ
  | cons (Γ Γ' Γ'' : StackTy) (ρ₁ ρ₂ : Region) (rest : List (Region × Region))
      (h : Outlives Δ Θ μ Γ ρ₁ ρ₂ Γ') (t : OutlivesMany Δ Θ μ Γ' rest Γ'') :
      OutlivesMany Δ Θ μ Γ ((ρ₁, ρ₂) :: rest) Γ''

/-- The forms of the rewriting judgments: a single type, or a list of types. -/
inductive RewriteForm where
  | one (Γ : StackTy) (τ₁ τ₂ : Ty) (Γ' : StackTy)
  | all (Γ : StackTy) (τs₁ τs₂ : List Ty) (Γ' : StackTy)

/-- The region rewriting judgments (`RR-*`), as a single inductive family indexed
by the form of the judgment (see `Rewrite` and `RewriteAll` below). -/
inductive RewriteJ (Δ : TyEnv) (Θ : TempTy) : Mode → RewriteForm → Prop
  | refl (μ : Mode) (Γ : StackTy) (τ : Ty) : RewriteJ Δ Θ μ (.one Γ τ τ Γ)
  | trans (μ : Mode) (Γ Γ' Γ'' : StackTy) (τ₁ τ₂ τ₃ : Ty)
      (h₁ : RewriteJ Δ Θ μ (.one Γ τ₁ τ₂ Γ')) (h₂ : RewriteJ Δ Θ μ (.one Γ' τ₂ τ₃ Γ'')) :
      RewriteJ Δ Θ μ (.one Γ τ₁ τ₃ Γ'')
  /-- `RR-Reference` -/
  | ref (μ : Mode) (Γ Γ' Γ'' : StackTy) (ρ₁ ρ₂ : Region) (ω : Own) (τ₁ τ₂ : Ty)
      (h₁ : Outlives Δ Θ μ Γ ρ₁ ρ₂ Γ') (h₂ : RewriteJ Δ Θ μ (.one Γ' τ₁ τ₂ Γ'')) :
      RewriteJ Δ Θ μ (.one Γ (.ref ρ₁ ω τ₁) (.ref ρ₂ ω τ₂) Γ'')
  /-- `RR-Array` -/
  | array (μ : Mode) (Γ Γ' : StackTy) (τ₁ τ₂ : Ty) (n : Nat)
      (h : RewriteJ Δ Θ μ (.one Γ τ₁ τ₂ Γ')) :
      RewriteJ Δ Θ μ (.one Γ (.array τ₁ n) (.array τ₂ n) Γ')
  /-- `RR-Slice` -/
  | slice (μ : Mode) (Γ Γ' : StackTy) (τ₁ τ₂ : Ty)
      (h : RewriteJ Δ Θ μ (.one Γ τ₁ τ₂ Γ')) :
      RewriteJ Δ Θ μ (.one Γ (.slice τ₁) (.slice τ₂) Γ')
  /-- `RR-Tuple` -/
  | tuple (μ : Mode) (Γ Γ' : StackTy) (τs τs' : List Ty)
      (h : RewriteJ Δ Θ μ (.all Γ τs τs' Γ')) :
      RewriteJ Δ Θ μ (.one Γ (.tuple τs) (.tuple τs') Γ')
  /-- `RR-Dead` -/
  | dead (μ : Mode) (Γ Γ' : StackTy) (τ₁ τ₂ : Ty) (hsi₁ : τ₁.SI) (hsi₂ : τ₂.SI)
      (h : RewriteJ Δ Θ μ (.one Γ τ₁ τ₂ Γ')) : RewriteJ Δ Θ μ (.one Γ τ₁ (.dead τ₂) Γ)
  /-- empty lists -/
  | allNil (μ : Mode) (Γ : StackTy) : RewriteJ Δ Θ μ (.all Γ [] [] Γ)
  /-- componentwise rewriting, threading the stack typing -/
  | allCons (μ : Mode) (Γ Γ' Γ'' : StackTy) (τ τ' : Ty) (τs τs' : List Ty)
      (h : RewriteJ Δ Θ μ (.one Γ τ τ' Γ')) (t : RewriteJ Δ Θ μ (.all Γ' τs τs' Γ'')) :
      RewriteJ Δ Θ μ (.all Γ (τ :: τs) (τ' :: τs') Γ'')

/-- `Δ; Γ; Θ ⊢^μ τ₁ ⇝ τ₂ ⊣ Γ'`: terms at type `τ₁` can be rewritten according to
`μ` at type `τ₂`. -/
abbrev Rewrite (Δ : TyEnv) (Θ : TempTy) (μ : Mode) (Γ : StackTy) (τ₁ τ₂ : Ty)
    (Γ' : StackTy) : Prop := RewriteJ Δ Θ μ (.one Γ τ₁ τ₂ Γ')

/-- Componentwise rewriting of lists of types, threading the stack typing. -/
abbrev RewriteAll (Δ : TyEnv) (Θ : TempTy) (μ : Mode) (Γ : StackTy) (τs₁ τs₂ : List Ty)
    (Γ' : StackTy) : Prop := RewriteJ Δ Θ μ (.all Γ τs₁ τs₂ Γ')

end Oxide
