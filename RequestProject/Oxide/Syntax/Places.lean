module

public import Mathlib.Data.List.Basic
public import Mathlib.Order.Basic

/-!
# Oxide syntax, part 1: ownership qualifiers, regions, places and loans

Paper §3.1 ("The Syntax of Oxide"), paragraphs "Places and Place Expressions" and
"Annotations for References"; appendix A ("Oxide Syntax").

This is the first file of the formalization; the general representation choices
(de Bruijn indices and levels) are explained here.

## Representation choices

* **Term variables use de Bruijn indices.**  `Term n` is the type of Oxide
  expressions with (at most) `n` free term variables, so `Term 0` is the type of
  closed expressions.  Binders (`let`, `for`, `match` arms, closure parameters)
  extend the scope (`Term (n+1)`, `Term (n + k)`).  Index `0` is the most recently
  bound variable.
* Since Oxide's stack is *ordered*, index `i` of a term in focus denotes the
  `i`-th most recent binding of the *top stack frame* (both at runtime and in the
  stack typing).  Pointers (referents) and loans, which may point into older stack
  frames, use absolute **de Bruijn levels** (positions counted from the bottom of
  the whole stack).  Levels are stable when the stack grows or shrinks above them.
* Type-level binders are also nameless.  A function type
  `∀<φ̄, ϱ̄, ᾱ>(…) → …` records only how many frame variables, abstract regions and
  type variables it binds; occurrences are de Bruijn indices (one index space per
  sort).  The type environment `Δ` is correspondingly just a count per sort plus
  the outlives constraints.
* Concrete regions are bound by `letrgn { e }` (index `Region.bound 0` in `e`).
  When the region is introduced (statically by `T-LetRegion`, dynamically by
  `E-LetRegion`) the binder is *opened* with a de Bruijn level `Region.conc ℓ`
  designating the region's entry in the stack typing (locally nameless style).
  Closure values and closure types bind their captured regions in the same way.
* Only global function names remain strings (they are the keys of `Σ`).
* Runtime values form a separate syntactic class `Value` that is embedded into
  terms with `Term.val`.  Consequently the constants `()`, `n`, `true`, `false`
  and function names are written as values.
* Lists of terms inside `Term n` use the auxiliary inductive `Terms n` (Lean does
  not allow `List (Term n)` as a nested occurrence of an indexed family).
-/

@[expose] public section

namespace Oxide

/-- Ownership qualifiers `ω ::= shrd | uniq`. -/
inductive Own where
  | shrd
  | uniq
  deriving DecidableEq, Repr, Inhabited

/-- The ordering on ownership qualifiers (`QO-Refl`, `QO-ShrdUniq`). -/
inductive Own.Le : Own → Own → Prop where
  | refl (ω : Own) : Own.Le ω ω
  | shrdUniq : Own.Le .shrd .uniq

instance : DecidableRel Own.Le := fun a b =>
  match a, b with
  | .shrd, .shrd => isTrue (.refl _)
  | .uniq, .uniq => isTrue (.refl _)
  | .shrd, .uniq => isTrue .shrdUniq
  | .uniq, .shrd => isFalse (by intro h; cases h)

/-- Regions `ρ ::= ϱ | r`.
* `abs i`: the abstract region with de Bruijn index `i` (bound by a function type
  or function definition),
* `bound i`: a concrete region bound by the `i`-th enclosing `letrgn` (or region
  captured by a closure),
* `conc ℓ`: the concrete region whose entry in the stack typing has level `ℓ`. -/
inductive Region where
  | abs (i : Nat)
  | bound (i : Nat)
  | conc (ℓ : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- One step of a place expression: a dereference `*·` or a projection `·.i`. -/
inductive POp where
  | deref
  | proj (i : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- Place expressions `p ::= x | *p | p.n` as they occur in terms, with a de Bruijn
index as root.  `ops` lists the operations from the innermost (applied first to
the root) to the outermost. -/
structure PlaceExpr (n : Nat) where
  root : Fin n
  ops : List POp
  deriving DecidableEq, Repr

/-- Absolute place expressions, whose root is a de Bruijn *level*.  These are used
in loans `ω p` stored in the stack typing. -/
structure APlaceExpr where
  root : Nat
  ops : List POp
  deriving DecidableEq, Repr, Inhabited

/-- Absolute places `π = x.q` (no dereferences): a level and a path of projections. -/
structure APlace where
  root : Nat
  path : List Nat
  deriving DecidableEq, Repr, Inhabited

/-- A place seen as a place expression. -/
def APlace.toExpr (π : APlace) : APlaceExpr := ⟨π.root, π.path.map POp.proj⟩

/-- `p` is a place, i.e. contains no dereference. -/
def APlaceExpr.IsPlace (p : APlaceExpr) : Prop := POp.deref ∉ p.ops

/-- Plugging a place expression into a place-expression context `p°[p']`; the
context is given by its list of (outer) operations. -/
def APlaceExpr.plug (ctx : List POp) (p : APlaceExpr) : APlaceExpr := ⟨p.root, p.ops ++ ctx⟩

/-- Loans `ℓ ::= ω p`. -/
structure Loan where
  own : Own
  pe : APlaceExpr
  deriving DecidableEq, Repr, Inhabited

end Oxide
