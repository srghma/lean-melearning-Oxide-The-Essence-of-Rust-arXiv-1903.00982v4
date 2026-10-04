module

public import RequestProject.Oxide.Proposal.Scopes

/-!
# Proposal prototype, part 2: well-scoped, well-sorted types

`Ty Γ` is indexed by the scope `Γ`, so every region, type variable, frame
variable and loan in a type is in scope by construction.  The paper's sorts of
types are separate families instead of predicates:

* `Ty Γ`   — sized, initialized types `τ^SI`;
* `XTy Γ`  — maybe-unsized types `τ^XI` (what a reference may point to);
* `MTy Γ`  — maybe-dead types `τ^SX` (what the stack typing records for a
  variable, possibly partially moved).

So `&ρ ω [τ]` is well formed but `[[τ]]` (an array of slices), `(τ†, u32)` as a
`let` annotation or a dead closure parameter cannot even be written.
-/

@[expose] public section

namespace Oxide.Scoped

open Oxide (Own POp BaseTy)

/-- The binders of a polymorphic signature `<φ̄, ϱ̄, ᾱ>`. -/
structure Binders where
  nφ : Nat := 0
  nϱ : Nat := 0
  nα : Nat := 0
  deriving DecidableEq, Repr

/-- The scope extension made by the binders `<φ̄, ϱ̄, ᾱ>` (most recent first). -/
abbrev Binders.ctx (b : Binders) : Ctx :=
  List.replicate b.nα .tvar ++ (List.replicate b.nϱ .abs ++ List.replicate b.nφ .fvar)

/-- Regions `ρ ::= ϱ | r`: an abstract region or a concrete region, both
in scope.  (There is no separate "opened" form: `letrgn` simply binds a `.rgn`.) -/
inductive Region (Γ : Ctx) where
  | abs (i : In .abs Γ)
  | conc (r : In .rgn Γ)
  deriving DecidableEq, Repr

/-- Absolute place expressions (roots of loans): a variable of *any* frame. -/
structure APlaceExpr (Γ : Ctx) where
  root : In .var Γ
  ops : List POp
  deriving DecidableEq, Repr

/-- Loans `ω p`. -/
structure Loan (Γ : Ctx) where
  own : Own
  pe : APlaceExpr Γ
  deriving DecidableEq, Repr

mutual
/-- Sized, initialized types `τ^SI`. -/
inductive Ty : Ctx → Type where
  | base {Γ : Ctx} (b : BaseTy) : Ty Γ
  | tvar {Γ : Ctx} (α : In .tvar Γ) : Ty Γ
  /-- `&ρ ω τ^XI` -/
  | ref {Γ : Ctx} (ρ : Region Γ) (ω : Own) (τ : XTy Γ) : Ty Γ
  /-- `[τ; n]` -/
  | array {Γ : Ctx} (τ : Ty Γ) (n : Nat) : Ty Γ
  /-- `(τ₁, …, τ_k)`: the arity is part of the data, no list needed -/
  | tuple {Γ : Ctx} (k : Nat) (τs : Fin k → Ty Γ) : Ty Γ
  /-- `Either<τ₁, τ₂>` -/
  | sum {Γ : Ctx} (τ₁ τ₂ : Ty Γ) : Ty Γ
  /-- `∀<φ̄, ϱ̄, ᾱ>(τ₁, …, τ_k) →^Φ τ_r where ϱᵢ : ϱⱼ`: the signature, the
  captured environment and the return type live in the extended scope; the
  bounds can only name the bound abstract regions. -/
  | fn {Γ : Ctx} (b : Binders) (k : Nat) (params : Fin k → Ty (b.ctx ++ Γ))
      (ret : Ty (b.ctx ++ Γ)) (env : FrameExpr (b.ctx ++ Γ)) (bounds : List (Fin b.nϱ × Fin b.nϱ)) :
      Ty Γ
/-- Maybe-unsized types `τ^XI`. -/
inductive XTy : Ctx → Type where
  | sized {Γ : Ctx} (τ : Ty Γ) : XTy Γ
  /-- `[τ]` -/
  | slice {Γ : Ctx} (τ : Ty Γ) : XTy Γ
/-- Frame expressions `Φ ::= φ | Φ_frame`.  A literal frame of shape `f` is
typed in the scope where that frame has been pushed (`f ++ .frame :: Γ`), so its
types may mention the frame's own regions. -/
inductive FrameExpr : Ctx → Type where
  | var {Γ : Ctx} (φ : In .fvar Γ) : FrameExpr Γ
  | frame {Γ : Ctx} (f : Ctx) (Φ : FrameTy (f ++ .frame :: Γ) f) : FrameExpr Γ
/-- `FrameTy Γ f`: a frame typing for a frame of shape `f`, all of whose types
and loans live in scope `Γ`.  Only `.var` and `.rgn` entries can be built, so a
frame shape never contains type-level binders or frame boundaries. -/
inductive FrameTy : Ctx → Ctx → Type where
  | nil {Γ : Ctx} : FrameTy Γ []
  | var {Γ f : Ctx} (τ : Ty Γ) (Φ : FrameTy Γ f) : FrameTy Γ (.var :: f)
  | rgn {Γ f : Ctx} (loans : List (Loan Γ)) (Φ : FrameTy Γ f) : FrameTy Γ (.rgn :: f)
end

/-- Maybe-dead types `τ^SX`: what the stack typing records for a variable. -/
inductive MTy (Γ : Ctx) where
  | init (τ : Ty Γ)
  /-- `τ†` -/
  | dead (τ : Ty Γ)
  /-- partially moved tuples -/
  | tuple (k : Nat) (τs : Fin k → MTy Γ)

namespace Ty
def bool {Γ : Ctx} : Ty Γ := .base .bool
def u32 {Γ : Ctx} : Ty Γ := .base .u32
def unit {Γ : Ctx} : Ty Γ := .base .unit
end Ty

/-! ## Renaming -/

def Region.rename {Γ Δ : Ctx} (ρ : TRen Γ Δ) : Region Γ → Region Δ
  | .abs i => .abs (ρ.ren i)
  | .conc r => .conc (ρ.ren r)

def Loan.rename {Γ Δ : Ctx} (ρ : TRen Γ Δ) (l : Loan Γ) : Loan Δ :=
  ⟨l.own, ⟨ρ.ren l.pe.root, l.pe.ops⟩⟩

mutual
def Ty.rename {Γ Δ : Ctx} (ρ : TRen Γ Δ) : Ty Γ → Ty Δ
  | .base b => .base b
  | .tvar α => .tvar (ρ.ren α)
  | .ref r ω τ => .ref (r.rename ρ) ω (τ.rename ρ)
  | .array τ n => .array (τ.rename ρ) n
  | .tuple k τs => .tuple k fun i => (τs i).rename ρ
  | .sum τ₁ τ₂ => .sum (τ₁.rename ρ) (τ₂.rename ρ)
  | .fn b k ps ret env bs =>
      .fn b k (fun i => (ps i).rename (ρ.liftN b.ctx)) (ret.rename (ρ.liftN b.ctx))
        (env.rename (ρ.liftN b.ctx)) bs
def XTy.rename {Γ Δ : Ctx} (ρ : TRen Γ Δ) : XTy Γ → XTy Δ
  | .sized τ => .sized (τ.rename ρ)
  | .slice τ => .slice (τ.rename ρ)
def FrameExpr.rename {Γ Δ : Ctx} (ρ : TRen Γ Δ) : FrameExpr Γ → FrameExpr Δ
  | .var φ => .var (ρ.ren φ)
  | .frame f Φ => .frame f (Φ.rename ((ρ.lift .frame).liftN f))
def FrameTy.rename {Γ Δ : Ctx} (ρ : TRen Γ Δ) : {f : Ctx} → FrameTy Γ f → FrameTy Δ f
  | _, .nil => .nil
  | _, .var τ Φ => .var (τ.rename ρ) (Φ.rename ρ)
  | _, .rgn L Φ => .rgn (L.map (Loan.rename ρ)) (Φ.rename ρ)
end

def MTy.rename {Γ Δ : Ctx} (ρ : TRen Γ Δ) : MTy Γ → MTy Δ
  | .init τ => .init (τ.rename ρ)
  | .dead τ => .dead (τ.rename ρ)
  | .tuple k τs => .tuple k fun i => (τs i).rename ρ

/-- Weakening of a type by one binder (of any sort, including `.frame`). -/
abbrev Ty.wk {Γ : Ctx} (c : Bnd) (τ : Ty Γ) : Ty (c :: Γ) := τ.rename (TRen.wk Γ c)

end Oxide.Scoped
