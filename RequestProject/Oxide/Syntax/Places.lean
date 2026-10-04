module

public import RequestProject.Oxide.Syntax.Scopes

/-!
# Oxide syntax, part 1: ownership qualifiers, places, loans and referents

Paper §3.1 ("The Syntax of Oxide"), paragraphs "Places and Place Expressions" and
"Annotations for References"; the referents of §3.6; appendix A.

Place expressions come in two flavours:

* `PlaceExpr Γ`, as written in terms: rooted at a *top-frame* variable
  (`TVar Γ`);
* `APlaceExpr Γ`, as found in loans: rooted at a variable of *any* frame
  (`In .var Γ`), since a region of an older frame may hold a loan to a newer
  variable.

Referents (pointer targets) are rooted at a stack slot `In .var Γ` of any frame.
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

/-- One step of a place expression: a dereference `*·` or a projection `·.i`. -/
inductive POp where
  | deref
  | proj (i : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- Place expressions `p ::= x | *p | p.n` as written in terms: the root is a
variable of the top frame; `ops` lists the operations from the innermost (applied
first to the root) to the outermost. -/
structure PlaceExpr (Γ : Ctx) where
  root : TVar Γ
  ops : List POp
  deriving DecidableEq, Repr

/-- Absolute place expressions (in loans): the root is a variable of any frame. -/
structure APlaceExpr (Γ : Ctx) where
  root : In .var Γ
  ops : List POp
  deriving DecidableEq, Repr

/-- Places `π = x.q` (no dereferences): a variable and a path of projections. -/
structure APlace (Γ : Ctx) where
  root : In .var Γ
  path : List Nat
  deriving DecidableEq, Repr

/-- A place seen as a place expression. -/
def APlace.toExpr {Γ : Ctx} (π : APlace Γ) : APlaceExpr Γ := ⟨π.root, π.path.map POp.proj⟩

/-- A term-level place expression as an absolute one. -/
def PlaceExpr.toAbs {Γ : Ctx} (p : PlaceExpr Γ) : APlaceExpr Γ := ⟨p.root.toIn, p.ops⟩

/-- `p` is a place, i.e. contains no dereference. -/
def APlaceExpr.IsPlace {Γ : Ctx} (p : APlaceExpr Γ) : Prop := POp.deref ∉ p.ops

/-- Plugging a place expression into a place-expression context `p°[p']`; the
context is given by its list of (outer) operations. -/
def APlaceExpr.plug {Γ : Ctx} (ctx : List POp) (p : APlaceExpr Γ) : APlaceExpr Γ :=
  ⟨p.root, p.ops ++ ctx⟩

/-- Loans `ℓ ::= ω p`. -/
structure Loan (Γ : Ctx) where
  own : Own
  pe : APlaceExpr Γ
  deriving DecidableEq, Repr

/-- Constants `c ::= () | n | true | false` (unsigned integers are natural
numbers). -/
inductive Prim where
  | unit
  | num (n : Nat)
  | bool (b : Bool)
  deriving DecidableEq, Repr, Inhabited

/-- Steps of a referent: projection `.n`, indexing `[n]` and slicing `[n₁..n₂]`
(half-open interval `[n₁, n₂)`). -/
inductive RStep where
  | proj (i : Nat)
  | idx (i : Nat)
  | slice (i j : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- Referents `𝓡 ::= x | 𝓡.n | 𝓡[n] | 𝓡[n₁..n₂]`: abstract memory addresses whose
root is a stack slot (of any frame).  Steps are listed innermost first. -/
structure Referent (Γ : Ctx) where
  root : In .var Γ
  steps : List RStep
  deriving DecidableEq, Repr

/-- The referent `𝓡` extended by one step. -/
def Referent.snoc {Γ : Ctx} (R : Referent Γ) (s : RStep) : Referent Γ := ⟨R.root, R.steps ++ [s]⟩

/-! ## Renaming -/

def APlaceExpr.rename {Γ Δ : Ctx} (ρ : TRen Γ Δ) (p : APlaceExpr Γ) : APlaceExpr Δ :=
  ⟨ρ.ren p.root, p.ops⟩

def Loan.rename {Γ Δ : Ctx} (ρ : TRen Γ Δ) (l : Loan Γ) : Loan Δ := ⟨l.own, l.pe.rename ρ⟩

def PlaceExpr.rename {Γ Δ : Ctx} (ρ : Ren Γ Δ) (p : PlaceExpr Γ) : PlaceExpr Δ :=
  ⟨ρ.tvar p.root, p.ops⟩

def Referent.rename {Γ Δ : Ctx} (ρ : TRen Γ Δ) (R : Referent Γ) : Referent Δ :=
  ⟨ρ.ren R.root, R.steps⟩

def APlace.rename {Γ Δ : Ctx} (ρ : TRen Γ Δ) (π : APlace Γ) : APlace Δ := ⟨ρ.ren π.root, π.path⟩

def Loan.prename {Γ Δ : Ctx} (ρ : PRen Γ Δ) (l : Loan Γ) : Option (Loan Δ) :=
  (ρ.ren l.pe.root).map fun r => ⟨l.own, ⟨r, l.pe.ops⟩⟩

def PlaceExpr.prename {Γ Δ : Ctx} (ρ : PRenT Γ Δ) (p : PlaceExpr Γ) : Option (PlaceExpr Δ) :=
  (ρ.tvar p.root).map fun r => ⟨r, p.ops⟩

def Referent.prename {Γ Δ : Ctx} (ρ : PRen Γ Δ) (R : Referent Γ) : Option (Referent Δ) :=
  (ρ.ren R.root).map fun r => ⟨r, R.steps⟩

end Oxide
