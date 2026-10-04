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

/-! ## Outlives -/

/-- The forms of the outlives judgments: a single constraint `ρ₁ :> ρ₂`, or a list
of constraints `ρ₁ :> ϱ, …, ρₙ :> ϱ` with a common abstract right-hand side. -/
inductive OutlivesForm (S : Ctx) where
  | one (Γ : StackTy S) (ρ₁ ρ₂ : Region S) (Γ' : StackTy S)
  | all (Γ : StackTy S) (ρs : List (Region S)) (ϱ : In .abs S) (Γ' : StackTy S)

/-- The outlives judgments (`OL-*`). -/
inductive OutlivesJ {S : Ctx} (Θ : TempTy S) : Mode → OutlivesForm S → Prop
  | refl (μ : Mode) (Γ : StackTy S) (ρ : Region S) : OutlivesJ Θ μ (.one Γ ρ ρ Γ)
  | trans (μ : Mode) (Γ Γ' Γ'' : StackTy S) (ϱ₁ ϱ₂ ϱ₃ : In .abs S)
      (h₁ : OutlivesJ Θ μ (.one Γ (.abs ϱ₁) (.abs ϱ₂) Γ'))
      (h₂ : OutlivesJ Θ μ (.one Γ' (.abs ϱ₂) (.abs ϱ₃) Γ'')) :
      OutlivesJ Θ μ (.one Γ (.abs ϱ₁) (.abs ϱ₃) Γ'')
  /-- `OL-CombineConcrete` -/
  | combine (Γ : StackTy S) (r₁ r₂ : In .rgn S)
      (hnrb₁ : NotReborrowed Γ r₁) (hnrb₂ : NotReborrowed Γ r₂)
      (hclrs : ClosRestriction Θ Γ [r₁, r₂]) (hob : OccursBefore r₁ r₂) :
      OutlivesJ Θ .combine (.one Γ (.conc r₁) (.conc r₂) (Γ.setLoans r₂ (Γ.loans r₁ ∪ Γ.loans r₂)))
  /-- `OL-CombineConcreteUnrestricted` -/
  | combineUnrest (Γ : StackTy S) (r₁ r₂ : In .rgn S)
      (hnrb₁ : NotReborrowed Γ r₁) (hnrb₂ : NotReborrowed Γ r₂) (hob : OccursBefore r₁ r₂) :
      OutlivesJ Θ .combineUnrest
        (.one Γ (.conc r₁) (.conc r₂) (Γ.setLoans r₂ (Γ.loans r₁ ∪ Γ.loans r₂)))
  /-- `OL-CheckConcrete` -/
  | check (Γ : StackTy S) (r₁ r₂ : In .rgn S)
      (hnrb₁ : NotReborrowed Γ r₁) (hnrb₂ : NotReborrowed Γ r₂) (hob : OccursBefore r₁ r₂) :
      OutlivesJ Θ .noop (.one Γ (.conc r₁) (.conc r₂) Γ)
  /-- `OL-BothAbstract` -/
  | bothAbs (μ : Mode) (Γ : StackTy S) (ϱ₁ ϱ₂ : In .abs S) (h : (ϱ₁, ϱ₂) ∈ Γ.outlives) :
      OutlivesJ Θ μ (.one Γ (.abs ϱ₁) (.abs ϱ₂) Γ)
  /-- `OL-ConcreteAbstract` -/
  | concAbs (μ : Mode) (Γ Γ' : StackTy S) (r : In .rgn S) (ϱ : In .abs S)
      (ρss : List (List (Region S)))
      (hne : Γ.loans r ≠ [])
      (hnp : ∀ l ∈ Γ.loans r, ¬ l.pe.IsPlace)
      (hlen : ρss.length = (Γ.loans r).length)
      (htc : ∀ lρ ∈ (Γ.loans r).zip ρss, ∃ τ, PlaceTy Γ .shrd lρ.1.pe τ lρ.2)
      (hall : OutlivesJ Θ μ (.all Γ ρss.flatten ϱ Γ')) :
      OutlivesJ Θ μ (.one Γ (.conc r) (.abs ϱ) Γ')
  /-- `OL-AbstractConcrete` -/
  | absConc (μ : Mode) (Γ : StackTy S) (ϱ : In .abs S) (r : In .rgn S) :
      OutlivesJ Θ μ (.one Γ (.abs ϱ) (.conc r) Γ)
  /-- no constraints -/
  | allNil (μ : Mode) (Γ : StackTy S) (ϱ : In .abs S) : OutlivesJ Θ μ (.all Γ [] ϱ Γ)
  /-- `ρ :> ϱ` followed by the remaining constraints, threading the stack typing -/
  | allCons (μ : Mode) (Γ Γ' Γ'' : StackTy S) (ρ : Region S) (ρs : List (Region S)) (ϱ : In .abs S)
      (h : OutlivesJ Θ μ (.one Γ ρ (.abs ϱ) Γ')) (t : OutlivesJ Θ μ (.all Γ' ρs ϱ Γ'')) :
      OutlivesJ Θ μ (.all Γ (ρ :: ρs) ϱ Γ'')

/-- `Δ; Γ; Θ ⊢^μ ρ₁ :> ρ₂ ⊣ Γ'`. -/
abbrev Outlives {S : Ctx} (Θ : TempTy S) (μ : Mode) (Γ : StackTy S) (ρ₁ ρ₂ : Region S)
    (Γ' : StackTy S) : Prop := OutlivesJ Θ μ (.one Γ ρ₁ ρ₂ Γ')

/-- `Δ; Γ; Θ ⊢ ρ̄₁ :> ρ̄₂ ⊣ Γ'` (`OL-Bounds`). -/
inductive OutlivesMany {S : Ctx} (Θ : TempTy S) (μ : Mode) :
    StackTy S → List (Region S × Region S) → StackTy S → Prop
  | nil (Γ : StackTy S) : OutlivesMany Θ μ Γ [] Γ
  | cons (Γ Γ' Γ'' : StackTy S) (ρ₁ ρ₂ : Region S) (rest : List (Region S × Region S))
      (h : Outlives Θ μ Γ ρ₁ ρ₂ Γ') (t : OutlivesMany Θ μ Γ' rest Γ'') :
      OutlivesMany Θ μ Γ ((ρ₁, ρ₂) :: rest) Γ''

/-! ## Region rewriting -/

/-- The forms of the rewriting judgments: sized types, maybe-unsized types, a sized
type into a maybe-dead type (`RR-Dead`), and lists of these. -/
inductive RewriteForm (S : Ctx) where
  | ty (Γ : StackTy S) (τ₁ τ₂ : Ty S) (Γ' : StackTy S)
  | xty (Γ : StackTy S) (τ₁ τ₂ : XTy S) (Γ' : StackTy S)
  | mty (Γ : StackTy S) (τ₁ : Ty S) (τ₂ : MTy S) (Γ' : StackTy S)
  | all (Γ : StackTy S) (τs₁ τs₂ : List (Ty S)) (Γ' : StackTy S)
  | allM (Γ : StackTy S) (τs₁ : List (Ty S)) (τs₂ : List (MTy S)) (Γ' : StackTy S)

/-- The region rewriting judgments (`RR-*`). -/
inductive RewriteJ {S : Ctx} (Θ : TempTy S) : Mode → RewriteForm S → Prop
  | refl (μ : Mode) (Γ : StackTy S) (τ : Ty S) : RewriteJ Θ μ (.ty Γ τ τ Γ)
  | trans (μ : Mode) (Γ Γ' Γ'' : StackTy S) (τ₁ τ₂ τ₃ : Ty S)
      (h₁ : RewriteJ Θ μ (.ty Γ τ₁ τ₂ Γ')) (h₂ : RewriteJ Θ μ (.ty Γ' τ₂ τ₃ Γ'')) :
      RewriteJ Θ μ (.ty Γ τ₁ τ₃ Γ'')
  /-- `RR-Reference` -/
  | ref (μ : Mode) (Γ Γ' Γ'' : StackTy S) (ρ₁ ρ₂ : Region S) (ω : Own) (τ₁ τ₂ : XTy S)
      (h₁ : Outlives Θ μ Γ ρ₁ ρ₂ Γ') (h₂ : RewriteJ Θ μ (.xty Γ' τ₁ τ₂ Γ'')) :
      RewriteJ Θ μ (.ty Γ (.ref ρ₁ ω τ₁) (.ref ρ₂ ω τ₂) Γ'')
  /-- `RR-Array` -/
  | array (μ : Mode) (Γ Γ' : StackTy S) (τ₁ τ₂ : Ty S) (n : Nat)
      (h : RewriteJ Θ μ (.ty Γ τ₁ τ₂ Γ')) :
      RewriteJ Θ μ (.ty Γ (.array τ₁ n) (.array τ₂ n) Γ')
  /-- `RR-Tuple` -/
  | tuple (μ : Mode) (Γ Γ' : StackTy S) (k : Nat) (τs τs' : Fin k → Ty S)
      (h : RewriteJ Θ μ (.all Γ (List.ofFn τs) (List.ofFn τs') Γ')) :
      RewriteJ Θ μ (.ty Γ (.tuple k τs) (.tuple k τs') Γ')
  /-- sized types are maybe-unsized types -/
  | sized (μ : Mode) (Γ Γ' : StackTy S) (τ₁ τ₂ : Ty S) (h : RewriteJ Θ μ (.ty Γ τ₁ τ₂ Γ')) :
      RewriteJ Θ μ (.xty Γ (.sized τ₁) (.sized τ₂) Γ')
  /-- `RR-Slice` -/
  | slice (μ : Mode) (Γ Γ' : StackTy S) (τ₁ τ₂ : Ty S) (h : RewriteJ Θ μ (.ty Γ τ₁ τ₂ Γ')) :
      RewriteJ Θ μ (.xty Γ (.slice τ₁) (.slice τ₂) Γ')
  /-- initialized targets -/
  | init (μ : Mode) (Γ Γ' : StackTy S) (τ₁ τ₂ : Ty S) (h : RewriteJ Θ μ (.ty Γ τ₁ τ₂ Γ')) :
      RewriteJ Θ μ (.mty Γ τ₁ (.init τ₂) Γ')
  /-- `RR-Dead` -/
  | dead (μ : Mode) (Γ Γ' : StackTy S) (τ₁ τ₂ : Ty S) (h : RewriteJ Θ μ (.ty Γ τ₁ τ₂ Γ')) :
      RewriteJ Θ μ (.mty Γ τ₁ (.dead τ₂) Γ)
  /-- partially dead tuple targets -/
  | mtuple (μ : Mode) (Γ Γ' : StackTy S) (k : Nat) (τs : Fin k → Ty S) (ms : Fin k → MTy S)
      (h : RewriteJ Θ μ (.allM Γ (List.ofFn τs) (List.ofFn ms) Γ')) :
      RewriteJ Θ μ (.mty Γ (.tuple k τs) (.tuple k ms) Γ')
  | allNil (μ : Mode) (Γ : StackTy S) : RewriteJ Θ μ (.all Γ [] [] Γ)
  | allCons (μ : Mode) (Γ Γ' Γ'' : StackTy S) (τ τ' : Ty S) (τs τs' : List (Ty S))
      (h : RewriteJ Θ μ (.ty Γ τ τ' Γ')) (t : RewriteJ Θ μ (.all Γ' τs τs' Γ'')) :
      RewriteJ Θ μ (.all Γ (τ :: τs) (τ' :: τs') Γ'')
  | allMNil (μ : Mode) (Γ : StackTy S) : RewriteJ Θ μ (.allM Γ [] [] Γ)
  | allMCons (μ : Mode) (Γ Γ' Γ'' : StackTy S) (τ : Ty S) (m : MTy S) (τs : List (Ty S))
      (ms : List (MTy S))
      (h : RewriteJ Θ μ (.mty Γ τ m Γ')) (t : RewriteJ Θ μ (.allM Γ' τs ms Γ'')) :
      RewriteJ Θ μ (.allM Γ (τ :: τs) (m :: ms) Γ'')

/-- `Δ; Γ; Θ ⊢^μ τ₁ ⇝ τ₂ ⊣ Γ'`: terms at type `τ₁` can be rewritten according to
`μ` at type `τ₂`. -/
abbrev Rewrite {S : Ctx} (Θ : TempTy S) (μ : Mode) (Γ : StackTy S) (τ₁ τ₂ : Ty S)
    (Γ' : StackTy S) : Prop := RewriteJ Θ μ (.ty Γ τ₁ τ₂ Γ')

/-- Rewriting into a maybe-dead type (the target of an assignment). -/
abbrev RewriteM {S : Ctx} (Θ : TempTy S) (μ : Mode) (Γ : StackTy S) (τ₁ : Ty S) (τ₂ : MTy S)
    (Γ' : StackTy S) : Prop := RewriteJ Θ μ (.mty Γ τ₁ τ₂ Γ')

end Oxide
