module

public import RequestProject.Oxide.Syntax.Places

/-!
# Oxide syntax, part 2: types

Paper §3.2 ("Types in Oxide"), Figure "Type Syntax of Oxide"; appendix A.

Frame expressions and frame entries (paper §3.3) are defined here as well, since
they are mutually inductive with types (a closure type records its captured
environment).
-/

@[expose] public section

namespace Oxide

/-- Base types `bool | u32 | unit`. -/
inductive BaseTy where
  | bool
  | u32
  | unit
  deriving DecidableEq, Repr, Inhabited

mutual
/-- Oxide types.  A single datatype covers all the syntactic categories of the
paper (sized/maybe-unsized, initialized/dead); the categories are carved out by
the predicates below. -/
inductive Ty where
  /-- base types -/
  | base (b : BaseTy)
  /-- type variables `α` (de Bruijn index) -/
  | tvar (i : Nat)
  /-- references `&ρ ω τ` -/
  | ref (ρ : Region) (ω : Own) (τ : Ty)
  /-- arrays `[τ; n]` -/
  | array (τ : Ty) (n : Nat)
  /-- slices `[τ]` (unsized) -/
  | slice (τ : Ty)
  /-- tuples `(τ₁, …, τₙ)` -/
  | tuple (τs : List Ty)
  /-- binary sums `Either<τ₁, τ₂>` -/
  | sum (τ₁ τ₂ : Ty)
  /-- function types `∀<φ̄, ϱ̄, ᾱ>(τ₁, …, τₙ) →^Φ τ_r where ϱ₁ : ϱ₂, …`, binding
  `nφ` frame variables, `nϱ` abstract regions and `nα` type variables (indices
  `0 … n-1` of each sort in `params`, `ret`, `env`); the bounds are pairs of
  abstract-region indices -/
  | fn (nφ nϱ nα : Nat) (params : List Ty) (ret : Ty) (env : FrameExpr)
      (bounds : List (Nat × Nat))
  /-- dead types `τ^†` -/
  | dead (τ : Ty)
/-- Frame expressions `Φ ::= φ | Φ_frame` (frame variables are de Bruijn indices).
In a frame occurring inside a type (the captured environment of a closure), the
types of the variable entries refer to the frame's own region entries with
`Region.bound j` (`j`-th most recent region entry of the frame). -/
inductive FrameExpr where
  | var (i : Nat)
  | frame (Φ : List FrameEntry)
/-- Entries of a frame typing: a (nameless) variable binding `x : τ` or a
(nameless) region binding `r ↦ {ℓ̄}`.  Frames are listed most recent entry
first. -/
inductive FrameEntry where
  | var (τ : Ty)
  | rgn (loans : List Loan)
end

instance : Inhabited Ty := ⟨.base .unit⟩
instance : Inhabited FrameExpr := ⟨.frame []⟩

namespace Ty
def bool : Ty := .base .bool
def u32 : Ty := .base .u32
def unit : Ty := .base .unit
/-- A closure type `(τ₁, …, τₙ) →^Φ τ_r` (no quantifiers, no bounds). -/
def closure (params : List Ty) (ret : Ty) (Φ : FrameExpr) : Ty := .fn 0 0 0 params ret Φ []
end Ty

end Oxide
