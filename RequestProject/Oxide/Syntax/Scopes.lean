module

public import Mathlib.Data.List.Basic
public import Mathlib.Order.Basic

/-!
# Oxide syntax, part 0: scopes, typed de Bruijn indices and renamings

This is the first file of the formalization.  Every syntactic class of Oxide
(types, terms, values, stack typings, stacks, continuations) is indexed by a
*scope* `Γ : Ctx`: the list of the sorts of all binders in scope, most recent
first.  The sorts are

* `fvar`  — frame variables `φ` (bound by a polymorphic signature),
* `abs`   — abstract regions `ϱ` (bound by a polymorphic signature),
* `tvar`  — type variables `α` (bound by a polymorphic signature),
* `var`   — term variables / stack slots `x` (bound by `let`, `for`, `match` and
  parameters),
* `rgn`   — concrete regions `r` (bound by `letrgn`; region markers on the stack),
* `frame` — frame boundaries `‡` (pushed by a function or closure call).

Variables are *typed* de Bruijn indices: `In b Γ` points at a binder of sort `b`
in `Γ`, so an index can never be out of range or point at a binder of the wrong
sort.  Term variables (`TVar Γ`) in addition can only reach the *top frame*: no
constructor crosses a `.frame` boundary.  A closed program is a `Term sig []`, and
the plain `Term n` of a calculus with only term variables is the special case
`Γ = vars n`.

Renamings (`TRen`, `Ren`) and partial renamings (`PRen`, `PRenT`, used to
*strengthen*, i.e. pop binders) act on indices.  Runtime scopes (`Ctx.Runtime`)
contain only variables, concrete regions and frame boundaries.  Frame boundaries are never
referred to, so renamings only have to act on the five *indexable* sorts
(`Bnd.Idx`).
-/

@[expose] public section

namespace Oxide

/-- Sorts of binders. -/
inductive Bnd where
  /-- frame variable `φ` -/
  | fvar
  /-- abstract region `ϱ` -/
  | abs
  /-- type variable `α` -/
  | tvar
  /-- term variable / stack slot `x` -/
  | var
  /-- concrete region `r` / region marker on the stack -/
  | rgn
  /-- frame boundary `‡` -/
  | frame
  deriving DecidableEq, Repr

/-- The sorts that can be referred to by an index (all but frame boundaries). -/
class Bnd.Idx (b : Bnd) : Prop where
  ne : b ≠ .frame

instance : Bnd.Idx .fvar := ⟨by decide⟩
instance : Bnd.Idx .abs := ⟨by decide⟩
instance : Bnd.Idx .tvar := ⟨by decide⟩
instance : Bnd.Idx .var := ⟨by decide⟩
instance : Bnd.Idx .rgn := ⟨by decide⟩

/-- Scopes: binder sorts, most recent first. -/
abbrev Ctx := List Bnd

/-- `k` term-variable binders (closure and function parameters; parameter `i` is
the `i`-th most recent binder). -/
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

namespace In

variable {b : Bnd}

/-- The position of an index (`0` = most recent binder). -/
def toNat {Γ : Ctx} : In b Γ → Nat
  | .here => 0
  | .there i => i.toNat + 1

/-- The empty scope has no binders. -/
def elimNil {α : Sort _} (i : In b []) : α := nomatch i

/-- The index of the `i`-th binder among `k` binders of sort `b`. -/
def ofFin : {k : Nat} → Fin k → (Γ : Ctx) → In b (List.replicate k b ++ Γ)
  | _ + 1, ⟨0, _⟩, _ => .here
  | k + 1, ⟨i + 1, h⟩, Γ => .there (In.ofFin (k := k) ⟨i, by omega⟩ Γ)

/-- Weaken an index by a prefix of binders. -/
def weakenL {Γ : Ctx} : (cs : Ctx) → In b Γ → In b (cs ++ Γ)
  | [], i => i
  | _ :: cs, i => .there (In.weakenL cs i)

/-- Embed an index into a prefix of a scope. -/
def inlL {Γ : Ctx} : {cs : Ctx} → In b cs → In b (cs ++ Γ)
  | _, .here => .here
  | _, .there i => .there i.inlL

/-- Split an index into a scope `cs ++ Γ`. -/
def split {Γ : Ctx} : (cs : Ctx) → In b (cs ++ Γ) → In b cs ⊕ In b Γ
  | [], i => .inr i
  | _ :: _, .here => .inl .here
  | _ :: cs, .there i => (In.split cs i).map .there id

/-- Indices never point at a frame boundary. -/
def dropFrame : {b : Bnd} → [Bnd.Idx b] → {Γ : Ctx} → In b (.frame :: Γ) → In b Γ
  | _, _, _, .there m => m
  | .frame, inst, _, .here => absurd rfl inst.ne

/-- An index into `List.replicate k c` has sort `c`. -/
theorem sort_of_replicate : {k : Nat} → {c : Bnd} → In b (List.replicate k c) → b = c
  | _ + 1, _, .here => rfl
  | _ + 1, _, .there i => sort_of_replicate i

/-- The position of an index into `List.replicate k b`. -/
def toFin : {k : Nat} → In b (List.replicate k b) → Fin k
  | _ + 1, .here => ⟨0, by omega⟩
  | _ + 1, .there i => (toFin i).succ

end In

namespace TVar

/-- Forget that a term variable is in the top frame. -/
def toIn : {Γ : Ctx} → TVar Γ → In .var Γ
  | _, .here => .here
  | _, .skipVar i => .there i.toIn
  | _, .skipRgn i => .there i.toIn

/-- The `i`-th of `k` parameters. -/
def ofFin : {k : Nat} → Fin k → (Γ : Ctx) → TVar (vars k ++ Γ)
  | _ + 1, ⟨0, _⟩, _ => .here
  | k + 1, ⟨i + 1, h⟩, Γ => .skipVar (TVar.ofFin (k := k) ⟨i, by omega⟩ Γ)

/-- A top-frame variable of a scope `f ++ ‡ :: Γ` lives in `f`. -/
def toInL {Γ : Ctx} : (f : Ctx) → TVar (f ++ .frame :: Γ) → In .var f
  | [], i => nomatch i
  | .var :: _, .here => .here
  | .var :: f, .skipVar i => .there (toInL f i)
  | .rgn :: f, .skipRgn i => .there (toInL f i)

end TVar

/-! ## Renamings -/

/-- Type-level renamings: maps on indices of every indexable sort.  These act on
types, regions, loans and values (which never mention term variables). -/
structure TRen (Γ Δ : Ctx) where
  ren : {b : Bnd} → [Bnd.Idx b] → In b Γ → In b Δ

/-- Renamings of terms: additionally map top-frame term variables. -/
structure Ren (Γ Δ : Ctx) extends TRen Γ Δ where
  tvar : TVar Γ → TVar Δ

namespace TRen

/-- The identity renaming. -/
def id (Γ : Ctx) : TRen Γ Γ := ⟨fun i => i⟩

/-- Composition of renamings. -/
def comp {Γ Δ Ε : Ctx} (ρ₁ : TRen Γ Δ) (ρ₂ : TRen Δ Ε) : TRen Γ Ε := ⟨fun i => ρ₂.ren (ρ₁.ren i)⟩

/-- Lift a renaming under one binder. -/
def lift {Γ Δ : Ctx} (ρ : TRen Γ Δ) (c : Bnd) : TRen (c :: Γ) (c :: Δ) where
  ren := fun
    | .here => .here
    | .there i => .there (ρ.ren i)

/-- Lift a renaming under a list of binders. -/
def liftN {Γ Δ : Ctx} (ρ : TRen Γ Δ) : (cs : Ctx) → TRen (cs ++ Γ) (cs ++ Δ)
  | [] => ρ
  | c :: cs => (ρ.liftN cs).lift c

/-- Weakening by one binder of any sort. -/
def wk (Γ : Ctx) (c : Bnd) : TRen Γ (c :: Γ) := ⟨.there⟩

/-- Weakening by a prefix of binders. -/
def wkL (Γ : Ctx) (cs : Ctx) : TRen Γ (cs ++ Γ) := ⟨In.weakenL cs⟩

/-- Enter a new frame: a type-level renaming becomes a term renaming, since the
new frame does not see any outer term variable. -/
def enterFrame {Γ Δ : Ctx} (ρ : TRen Γ Δ) : Ren (.frame :: Γ) (.frame :: Δ) :=
  { ρ.lift .frame with tvar := fun i => nomatch i }

/-- Weakening by a pushed frame of shape `f`. -/
def wkFrame (f S : Ctx) : TRen S (f ++ .frame :: S) := ⟨fun i => In.weakenL f (.there i)⟩

/-- Weakening by a pushed frame of shape `f` holding `k` parameters on top. -/
def frameRen (k : Nat) (f S : Ctx) : TRen S (vars k ++ (f ++ .frame :: S)) :=
  ⟨fun i => In.weakenL (vars k) ((wkFrame f S).ren i)⟩

end TRen

/-- Lift a map on top-frame variables under one binder. -/
def TVar.lift {Γ Δ : Ctx} {c : Bnd} (f : TVar Γ → TVar Δ) : TVar (c :: Γ) → TVar (c :: Δ)
  | .here => .here
  | .skipVar i => .skipVar (f i)
  | .skipRgn i => .skipRgn (f i)

namespace Ren

/-- The identity renaming. -/
def id (Γ : Ctx) : Ren Γ Γ := { TRen.id Γ with tvar := fun i => i }

/-- Lift a term renaming under one binder. -/
def lift {Γ Δ : Ctx} (ρ : Ren Γ Δ) (c : Bnd) : Ren (c :: Γ) (c :: Δ) :=
  { ρ.toTRen.lift c with tvar := TVar.lift ρ.tvar }

/-- Lift a term renaming under a list of binders. -/
def liftN {Γ Δ : Ctx} (ρ : Ren Γ Δ) : (cs : Ctx) → Ren (cs ++ Γ) (cs ++ Δ)
  | [] => ρ
  | c :: cs => (ρ.liftN cs).lift c

/-- Weakening of terms by a variable binder.  (Terms cannot be weakened by a
`.frame` binder: the new frame hides their variables.) -/
def wkVar (Γ : Ctx) : Ren Γ (.var :: Γ) := { TRen.wk Γ .var with tvar := .skipVar }

/-- Weakening of terms by a region binder. -/
def wkRgn (Γ : Ctx) : Ren Γ (.rgn :: Γ) := { TRen.wk Γ .rgn with tvar := .skipRgn }

end Ren

/-! ## Partial renamings (strengthening) -/

/-- Partial type-level renamings.  Removing a binder from a scope (popping a stack
slot, a region or a frame) is a partial renaming: it fails exactly on the removed
binders. -/
structure PRen (Γ Δ : Ctx) where
  ren : {b : Bnd} → [Bnd.Idx b] → In b Γ → Option (In b Δ)

/-- Partial renamings of terms. -/
structure PRenT (Γ Δ : Ctx) extends PRen Γ Δ where
  tvar : TVar Γ → Option (TVar Δ)

namespace PRen

/-- Lift a partial renaming under one binder. -/
def lift {Γ Δ : Ctx} (ρ : PRen Γ Δ) (c : Bnd) : PRen (c :: Γ) (c :: Δ) where
  ren := fun
    | .here => some .here
    | .there i => (ρ.ren i).map .there

/-- Lift a partial renaming under a list of binders. -/
def liftN {Γ Δ : Ctx} (ρ : PRen Γ Δ) : (cs : Ctx) → PRen (cs ++ Γ) (cs ++ Δ)
  | [] => ρ
  | c :: cs => (ρ.liftN cs).lift c

/-- Drop the most recent binder. -/
def drop (Γ : Ctx) (c : Bnd) : PRen (c :: Γ) Γ where
  ren := fun
    | .here => none
    | .there i => some i

/-- Drop a prefix of binders. -/
def dropL : (cs : Ctx) → (Γ : Ctx) → PRen (cs ++ Γ) Γ
  | [], _ => ⟨some⟩
  | _ :: cs, Γ => ⟨fun
    | .here => none
    | .there i => (PRen.dropL cs Γ).ren i⟩

/-- Composition of partial renamings. -/
def comp {Γ Δ Ε : Ctx} (ρ₁ : PRen Γ Δ) (ρ₂ : PRen Δ Ε) : PRen Γ Ε := ⟨fun i => (ρ₁.ren i).bind ρ₂.ren⟩

/-- Pop a frame of shape `f` holding `k` parameters on top. -/
def popFrameK (k : Nat) (f S : Ctx) : PRen (vars k ++ (f ++ .frame :: S)) S :=
  (dropL (vars k) _).comp ((dropL f _).comp (dropL [.frame] S))

/-- Enter a new frame. -/
def enterFrame {Γ Δ : Ctx} (ρ : PRen Γ Δ) : PRenT (.frame :: Γ) (.frame :: Δ) :=
  { ρ.lift .frame with tvar := fun i => nomatch i }

end PRen

namespace PRenT

/-- Lift a partial term renaming under one binder. -/
def lift {Γ Δ : Ctx} (ρ : PRenT Γ Δ) (c : Bnd) : PRenT (c :: Γ) (c :: Δ) :=
  { ρ.toPRen.lift c with
    tvar := fun
      | .here => some .here
      | .skipVar i => (ρ.tvar i).map .skipVar
      | .skipRgn i => (ρ.tvar i).map .skipRgn }

/-- Lift a partial term renaming under a list of binders. -/
def liftN {Γ Δ : Ctx} (ρ : PRenT Γ Δ) : (cs : Ctx) → PRenT (cs ++ Γ) (cs ++ Δ)
  | [] => ρ
  | c :: cs => (ρ.liftN cs).lift c

end PRenT

/-- A list as a vector of its elements. -/
def listFin {α : Type} (l : List α) : Fin l.length → α := l.get

/-- Sequence a vector of optional values. -/
def optFin {α : Type} : {k : Nat} → (Fin k → Option α) → Option (Fin k → α)
  | 0, _ => some Fin.elim0
  | _ + 1, f => do
    let a ← f 0
    let r ← optFin fun i => f i.succ
    pure (Fin.cases a r)

/-! ## Runtime scopes

At runtime a scope only contains term variables, concrete regions and frame
boundaries: the type-level binders (`fvar`, `abs`, `tvar`) of a polymorphic
signature are substituted away when a function is called. -/

/-- The sorts that exist at runtime. -/
def Bnd.IsRuntime : Bnd → Prop
  | .var | .rgn | .frame => True
  | .fvar | .abs | .tvar => False

instance : DecidablePred Bnd.IsRuntime := fun b => by cases b <;> unfold Bnd.IsRuntime <;> infer_instance

/-- A runtime scope: only variables, concrete regions and frame boundaries. -/
def Ctx.Runtime (S : Ctx) : Prop := ∀ b ∈ S, b.IsRuntime

end Oxide
