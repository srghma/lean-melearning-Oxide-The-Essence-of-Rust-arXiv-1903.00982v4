module

public import RequestProject.Oxide.Syntax.Scopes

/-!
# Oxide syntax, part 1: ownership qualifiers, places, loans and referents

Paper §3.1 ("The Syntax of Oxide"), paragraphs "Places and Place Expressions" and
"Annotations for References"; the referents of §3.6; appendix A.

**Place expressions are structured by their dereferences.**  In the paper a place
expression `p ::= x | *p | p.n` is always a place `π = x.q` (a variable and a path
of projections) followed by groups "dereference, then projections".  This is
exactly the shape of the inductive types below:

* `APlace Γ` / `TPlace Γ` — places `x.q` (no dereference);
* `APExpr Γ` / `PExpr Γ` — `place π` or `deref p q` (that is, `(*p).q`).

So "the innermost place", "the innermost dereferenced place", "`p` is a place"
and plugging a place expression into a context are plain pattern matches and
recursions, and a term that needs a *place* (a move, an assignment target that is
a place) can simply take a `TPlace`.

There are two flavours of roots:

* `TPlace Γ`, `PExpr Γ`, as written in terms: rooted at a *top-frame* variable
  (`TVar Γ`);
* `APlace Γ`, `APExpr Γ`, as found in loans: rooted at a variable of *any* frame
  (`In .var Γ`), since a region of an older frame may hold a loan to a newer
  variable.

Referents (pointer targets) are structured the same way: a place, followed by
indexing and slicing steps; a slice is given by its *start and length*, so there
is no side condition `n₁ ≤ n₂`.

Projection indices stay natural numbers in the syntax: whether `.n` is valid
depends on the type of what is projected, which is not part of the scope.  They
are converted once, by the typing rules, into paths indexed by a type
(`TyPath`, `Syntax/Types.lean`) and by the machine into paths indexed by a value
(`VPath`, `Metafunctions/Stacks.lean`).
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

/-! ## Places and place expressions -/

/-- Places `π = x.q` (no dereferences) rooted at a variable of any frame. -/
structure APlace (Γ : Ctx) where
  root : In .var Γ
  path : List Nat
  deriving DecidableEq, Repr

/-- Places `π = x.q` as written in terms: rooted at a variable of the top frame. -/
structure TPlace (Γ : Ctx) where
  root : TVar Γ
  path : List Nat
  deriving DecidableEq, Repr

/-- Place expressions (in loans): a place, or `(*p).q`. -/
inductive APExpr (Γ : Ctx) where
  | place (π : APlace Γ)
  /-- `(*p).q` -/
  | deref (p : APExpr Γ) (q : List Nat)
  deriving DecidableEq, Repr

/-- Place expressions as written in terms: a place, or `(*p).q`. -/
inductive PExpr (Γ : Ctx) where
  | place (π : TPlace Γ)
  /-- `(*p).q` -/
  | deref (p : PExpr Γ) (q : List Nat)
  deriving DecidableEq, Repr

namespace APlace
variable {Γ : Ctx}

/-- `π.q'` -/
def append (π : APlace Γ) (q : List Nat) : APlace Γ := ⟨π.root, π.path ++ q⟩

/-- A place seen as a place expression. -/
def toExpr (π : APlace Γ) : APExpr Γ := .place π

/-- The place expression `*π`. -/
def derefExpr (π : APlace Γ) : APExpr Γ := .deref (.place π) []

end APlace

/-- A term-level place as an absolute one. -/
def TPlace.toAbs {Γ : Ctx} (π : TPlace Γ) : APlace Γ := ⟨π.root.toIn, π.path⟩

/-- A term-level place expression as an absolute one. -/
def PExpr.toAbs {Γ : Ctx} : PExpr Γ → APExpr Γ
  | .place π => .place π.toAbs
  | .deref p q => .deref p.toAbs q

namespace APExpr
variable {Γ : Ctx}

/-- The root variable. -/
def root : APExpr Γ → In .var Γ
  | .place π => π.root
  | .deref p _ => p.root

/-- `p` is a place, i.e. contains no dereference. -/
def IsPlace : APExpr Γ → Prop
  | .place _ => True
  | .deref _ _ => False

instance : DecidablePred (@IsPlace Γ) := fun p => by cases p <;> unfold IsPlace <;> infer_instance

/-- `p.q'`: extend the last group of projections. -/
def append : APExpr Γ → List Nat → APExpr Γ
  | .place π, q' => .place (π.append q')
  | .deref p q, q' => .deref p (q ++ q')

end APExpr

/-- Place-expression contexts `p°`: what follows the hole, i.e. projections
continuing the plugged expression, then further groups "dereference, then
projections" (innermost first). -/
structure PCtx where
  path : List Nat := []
  groups : List (List Nat) := []
  deriving DecidableEq, Repr

/-- Plugging a place expression into a context `p°[p']`. -/
def APExpr.plug {Γ : Ctx} (c : PCtx) (p : APExpr Γ) : APExpr Γ :=
  c.groups.foldl (fun p q => .deref p q) (p.append c.path)

/-- Loans `ℓ ::= ω p`. -/
structure Loan (Γ : Ctx) where
  own : Own
  pe : APExpr Γ
  deriving DecidableEq, Repr

/-! ## Constants -/

/-- Base types `bool | u32 | unit`. -/
inductive BaseTy where
  | bool
  | u32
  | unit
  deriving DecidableEq, Repr, Inhabited

/-- Constants `c ::= () | n | true | false`, indexed by their base type, so that a
literal carries its type.  Unsigned integers are 32-bit (`UInt32`). -/
inductive Prim : BaseTy → Type where
  | unit : Prim .unit
  | num (n : UInt32) : Prim .u32
  | bool (b : Bool) : Prim .bool
  deriving DecidableEq, Repr

/-! ## Referents -/

/-- Referents `𝓡 ::= x | 𝓡.n | 𝓡[n] | 𝓡[n₁..n₂]`: abstract memory addresses whose
root is a stack slot (of any frame), structured like place expressions: a place,
then indexing steps (each followed by projections) and slicing steps.  A slice is
given by its start and its length. -/
inductive Referent (Γ : Ctx) where
  | place (π : APlace Γ)
  /-- `𝓡[i].q` -/
  | index (R : Referent Γ) (i : Nat) (q : List Nat)
  /-- `𝓡[start .. start + len]` -/
  | slice (R : Referent Γ) (start len : Nat)
  deriving DecidableEq, Repr

namespace Referent
variable {Γ : Ctx}

/-- The root stack slot. -/
def root : Referent Γ → In .var Γ
  | .place π => π.root
  | .index R _ _ => R.root
  | .slice R _ _ => R.root

/-- The innermost place `π` of a referent `𝓡 = 𝓡°[π]`. -/
def base : Referent Γ → APlace Γ
  | .place π => π
  | .index R _ _ => R.base
  | .slice R _ _ => R.base

/-- `𝓡.q`: projections (impossible after a slice, which is unsized). -/
def projs : Referent Γ → List Nat → Option (Referent Γ)
  | .place π, q => some (.place (π.append q))
  | .index R i q', q => some (.index R i (q' ++ q))
  | .slice _ _ _, [] => none
  | .slice _ _ _, _ :: _ => none

end Referent

/-! ## Renaming -/

def APlace.rename {Γ Δ : Ctx} (ρ : TRen Γ Δ) (π : APlace Γ) : APlace Δ := ⟨ρ.ren π.root, π.path⟩

def APExpr.rename {Γ Δ : Ctx} (ρ : TRen Γ Δ) : APExpr Γ → APExpr Δ
  | .place π => .place (π.rename ρ)
  | .deref p q => .deref (p.rename ρ) q

def Loan.rename {Γ Δ : Ctx} (ρ : TRen Γ Δ) (l : Loan Γ) : Loan Δ := ⟨l.own, l.pe.rename ρ⟩

def TPlace.rename {Γ Δ : Ctx} (ρ : Ren Γ Δ) (π : TPlace Γ) : TPlace Δ := ⟨ρ.tvar π.root, π.path⟩

def PExpr.rename {Γ Δ : Ctx} (ρ : Ren Γ Δ) : PExpr Γ → PExpr Δ
  | .place π => .place (π.rename ρ)
  | .deref p q => .deref (p.rename ρ) q

def Referent.rename {Γ Δ : Ctx} (ρ : TRen Γ Δ) : Referent Γ → Referent Δ
  | .place π => .place (π.rename ρ)
  | .index R i q => .index (R.rename ρ) i q
  | .slice R a l => .slice (R.rename ρ) a l

def APlace.prename {Γ Δ : Ctx} (ρ : PRen Γ Δ) (π : APlace Γ) : Option (APlace Δ) :=
  (ρ.ren π.root).map fun r => ⟨r, π.path⟩

def APExpr.prename {Γ Δ : Ctx} (ρ : PRen Γ Δ) : APExpr Γ → Option (APExpr Δ)
  | .place π => (π.prename ρ).map .place
  | .deref p q => (p.prename ρ).map (.deref · q)

def Loan.prename {Γ Δ : Ctx} (ρ : PRen Γ Δ) (l : Loan Γ) : Option (Loan Δ) :=
  (l.pe.prename ρ).map fun pe => ⟨l.own, pe⟩

def TPlace.prename {Γ Δ : Ctx} (ρ : PRenT Γ Δ) (π : TPlace Γ) : Option (TPlace Δ) :=
  (ρ.tvar π.root).map fun r => ⟨r, π.path⟩

def PExpr.prename {Γ Δ : Ctx} (ρ : PRenT Γ Δ) : PExpr Γ → Option (PExpr Δ)
  | .place π => (π.prename ρ).map .place
  | .deref p q => (p.prename ρ).map (.deref · q)

def Referent.prename {Γ Δ : Ctx} (ρ : PRen Γ Δ) : Referent Γ → Option (Referent Δ)
  | .place π => (π.prename ρ).map .place
  | .index R i q => (R.prename ρ).map (.index · i q)
  | .slice R a l => (R.prename ρ).map (.slice · a l)

end Oxide
