module

public import RequestProject.Oxide.Syntax.Terms

/-!
# Proposal prototype, part 1: scopes, variables and renamings

This file and the other files in `Proposal/` are a self-contained prototype of
the redesign described in `Proposal/PROPOSAL.md`.  The rest of the
formalization does not use them.

A *scope* `Γ : Ctx` is the list of the sorts of all binders in scope, most
recent first.  It is the erasure of the paper's `Δ` (frame variables, abstract
regions, type variables) together with the shape of the stack typing `Γ`/stack
`σ` (variables, concrete regions and frame boundaries).  A plain `Term n` is the
special case `Γ = [.var, …, .var]`.

Variables are typed de Bruijn indices: `In b Γ` is a position of `Γ` holding a
binder of sort `b`, so an index can never be out of range or point at a binder
of the wrong sort.  Term variables (`TVar Γ`) can in addition only reach the
*top frame*: they cannot cross a `.frame` boundary.
-/

@[expose] public section

namespace Oxide.Scoped

/-- Sorts of binders. -/
inductive Bnd where
  /-- frame variable `φ` (bound by a function signature) -/
  | fvar
  /-- abstract region `ϱ` (bound by a function signature) -/
  | abs
  /-- type variable `α` (bound by a function signature) -/
  | tvar
  /-- term variable / stack slot `x` (bound by `let`, `for`, `match`, parameters) -/
  | var
  /-- concrete region `r` (bound by `letrgn`) / region marker on the stack -/
  | rgn
  /-- frame boundary (pushed by a function or closure call, i.e. `framed`) -/
  | frame
  deriving DecidableEq, Repr

/-- Scopes: binder sorts, most recent first. -/
abbrev Ctx := List Bnd

/-- `k` term-variable binders (closure and function parameters). -/
abbrev vars (k : Nat) : Ctx := List.replicate k .var

/-- `In b Γ`: a typed de Bruijn index pointing at a binder of sort `b` in `Γ`.
It may cross frame boundaries (regions, type-level binders, loans and pointers
may refer to older frames). -/
inductive In (b : Bnd) : Ctx → Type where
  | here {Γ : Ctx} : In b (b :: Γ)
  | there {Γ : Ctx} {c : Bnd} (i : In b Γ) : In b (c :: Γ)
  deriving DecidableEq, Repr

/-- Term variables: positions holding a `.var` binder in the top frame.  There is
no constructor skipping a `.frame` (or a type-level binder), so a term can only
mention the variables of its own frame. -/
inductive TVar : Ctx → Type where
  | here {Γ : Ctx} : TVar (.var :: Γ)
  | skipVar {Γ : Ctx} (i : TVar Γ) : TVar (.var :: Γ)
  | skipRgn {Γ : Ctx} (i : TVar Γ) : TVar (.rgn :: Γ)
  deriving DecidableEq, Repr

/-- Forget that a term variable is in the top frame. -/
def TVar.toIn : {Γ : Ctx} → TVar Γ → In .var Γ
  | _, .here => .here
  | _, .skipVar i => .there i.toIn
  | _, .skipRgn i => .there i.toIn

/-- The empty scope has no variables of any sort. -/
def In.elimNil {b : Bnd} {α : Sort _} (i : In b []) : α := nomatch i

/-- The index of the `i`-th binder (`i < k`) among `k` binders of sort `b`. -/
def In.ofFin {b : Bnd} : {k : Nat} → Fin k → (Γ : Ctx) → In b (List.replicate k b ++ Γ)
  | _ + 1, ⟨0, _⟩, _ => .here
  | k + 1, ⟨i + 1, h⟩, Γ => .there (In.ofFin (k := k) ⟨i, by omega⟩ Γ)

/-- Weaken an index by a prefix of binders. -/
def In.weakenL {b : Bnd} {Γ : Ctx} : (cs : Ctx) → In b Γ → In b (cs ++ Γ)
  | [], i => i
  | _ :: cs, i => .there (In.weakenL cs i)

/-! ## Renamings -/

/-- Type-level renamings: maps on indices of every sort.  These act on types,
regions, loans and values (which never mention term variables). -/
structure TRen (Γ Δ : Ctx) where
  ren : {b : Bnd} → In b Γ → In b Δ

/-- Renamings of terms: additionally map top-frame term variables. -/
structure Ren (Γ Δ : Ctx) extends TRen Γ Δ where
  tvar : TVar Γ → TVar Δ

/-- Lift a type-level renaming under one binder. -/
def TRen.lift {Γ Δ : Ctx} (ρ : TRen Γ Δ) (c : Bnd) : TRen (c :: Γ) (c :: Δ) where
  ren := fun
    | .here => .here
    | .there i => .there (ρ.ren i)

/-- Lift a type-level renaming under a list of binders. -/
def TRen.liftN {Γ Δ : Ctx} (ρ : TRen Γ Δ) : (cs : Ctx) → TRen (cs ++ Γ) (cs ++ Δ)
  | [] => ρ
  | c :: cs => (ρ.liftN cs).lift c

/-- Weakening by one binder of any sort. -/
def TRen.wk (Γ : Ctx) (c : Bnd) : TRen Γ (c :: Γ) where
  ren := .there

/-- Weakening by a prefix of binders. -/
def TRen.wkL (Γ : Ctx) (cs : Ctx) : TRen Γ (cs ++ Γ) where
  ren := In.weakenL cs

/-- Lift a map on top-frame variables under one binder.  Under a `.frame` binder
(or a type-level binder) there are no top-frame variables from outside, which is
why the map is total for every `c`. -/
def TVar.lift {Γ Δ : Ctx} {c : Bnd} (f : TVar Γ → TVar Δ) : TVar (c :: Γ) → TVar (c :: Δ)
  | .here => .here
  | .skipVar i => .skipVar (f i)
  | .skipRgn i => .skipRgn (f i)

/-- Lift a term renaming under one binder. -/
def Ren.lift {Γ Δ : Ctx} (ρ : Ren Γ Δ) (c : Bnd) : Ren (c :: Γ) (c :: Δ) :=
  { ρ.toTRen.lift c with tvar := TVar.lift ρ.tvar }

/-- Lift a term renaming under a list of binders. -/
def Ren.liftN {Γ Δ : Ctx} (ρ : Ren Γ Δ) : (cs : Ctx) → Ren (cs ++ Γ) (cs ++ Δ)
  | [] => ρ
  | c :: cs => (ρ.liftN cs).lift c

/-- Enter a new frame: a type-level renaming becomes a term renaming, since the
term variables of the new frame do not include any outer one. -/
def TRen.enterFrame {Γ Δ : Ctx} (ρ : TRen Γ Δ) : Ren (.frame :: Γ) (.frame :: Δ) :=
  { ρ.lift .frame with tvar := fun i => nomatch i }

/-- Weakening of terms by a variable binder.  (Terms cannot be weakened by a
`.frame` binder: the new frame hides their variables.) -/
def Ren.wkVar (Γ : Ctx) : Ren Γ (.var :: Γ) := { TRen.wk Γ .var with tvar := .skipVar }

/-- Weakening of terms by a region binder. -/
def Ren.wkRgn (Γ : Ctx) : Ren Γ (.rgn :: Γ) := { TRen.wk Γ .rgn with tvar := .skipRgn }

end Oxide.Scoped
