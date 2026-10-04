module

public import RequestProject.Oxide.Syntax.Places

/-!
# Oxide syntax, part 2: types

Paper §3.2 ("Types in Oxide"), Figure "Type Syntax of Oxide"; appendix A.  Frame
expressions and frame typings (paper §3.3) are defined here as well, since they
are mutually inductive with types (a closure type records its captured frame).

`Ty Γ` is indexed by the scope `Γ`, so every region, type variable, frame
variable and loan in a type is in scope by construction.  The paper's *sorts* of
types are separate families instead of predicates on one datatype:

* `Ty Γ`  — sized, initialized types `τ^SI`;
* `XTy Γ` — maybe-unsized types `τ^XI` (what a reference may point to);
* `MTy Γ` — maybe-dead types `τ^SX` (what the stack typing records for a
  variable, possibly partially moved).

So an array of slices `[[τ]; n]`, a dead `let` annotation or a slice as a
closure parameter cannot even be written.
-/

@[expose] public section

namespace Oxide

/-- Base types `bool | u32 | unit`. -/
inductive BaseTy where
  | bool
  | u32
  | unit
  deriving DecidableEq, Repr, Inhabited

/-- The binders of a polymorphic signature `<φ̄, ϱ̄, ᾱ>`. -/
structure Binders where
  nφ : Nat := 0
  nϱ : Nat := 0
  nα : Nat := 0
  deriving DecidableEq, Repr

/-- The scope extension made by the binders `<φ̄, ϱ̄, ᾱ>` (most recent first):
the `i`-th type variable is the `i`-th binder, then come the abstract regions and
the frame variables. -/
abbrev Binders.ctx (b : Binders) : Ctx :=
  List.replicate b.nα .tvar ++ (List.replicate b.nϱ .abs ++ List.replicate b.nφ .fvar)

/-- The `i`-th abstract region bound by a signature. -/
def Binders.absIdx {Γ : Ctx} (b : Binders) (i : Fin b.nϱ) : In .abs (b.ctx ++ Γ) :=
  In.inlL (In.weakenL (List.replicate b.nα .tvar) (In.ofFin i (List.replicate b.nφ .fvar)))

/-- Regions `ρ ::= ϱ | r`: an abstract region or a concrete region, both in
scope.  (`letrgn` simply binds a `.rgn`; there is no "opened" form.) -/
inductive Region (Γ : Ctx) where
  | abs (i : In .abs Γ)
  | conc (r : In .rgn Γ)
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
  /-- `(τ₁, …, τ_k)` -/
  | tuple {Γ : Ctx} (k : Nat) (τs : Fin k → Ty Γ) : Ty Γ
  /-- `Either<τ₁, τ₂>` -/
  | sum {Γ : Ctx} (τ₁ τ₂ : Ty Γ) : Ty Γ
  /-- `∀<φ̄, ϱ̄, ᾱ>(τ₁, …, τ_k) →^Φ τ_r where ϱᵢ : ϱⱼ`: the parameters, the
  captured environment and the return type live in the extended scope; the bounds
  can only name the bound abstract regions.  Closure types have no binders. -/
  | fn {Γ : Ctx} (b : Binders) (k : Nat) (params : Fin k → Ty (b.ctx ++ Γ))
      (ret : Ty (b.ctx ++ Γ)) (env : FrameExpr (b.ctx ++ Γ))
      (bounds : List (Fin b.nϱ × Fin b.nϱ)) : Ty Γ
/-- Maybe-unsized types `τ^XI`. -/
inductive XTy : Ctx → Type where
  | sized {Γ : Ctx} (τ : Ty Γ) : XTy Γ
  /-- `[τ]` -/
  | slice {Γ : Ctx} (τ : Ty Γ) : XTy Γ
/-- Frame expressions `Φ ::= φ | Φ_frame`.  A literal frame of shape `f` is typed
in the scope where that frame has been pushed (`f ++ ‡ :: Γ`), so its types may
mention the frame's own regions. -/
inductive FrameExpr : Ctx → Type where
  | var {Γ : Ctx} (φ : In .fvar Γ) : FrameExpr Γ
  | frame {Γ : Ctx} (f : Ctx) (Φ : FrameTy (f ++ .frame :: Γ) f) : FrameExpr Γ
/-- `FrameTy Γ f`: a frame typing for a frame of shape `f`, all of whose types
and loans live in scope `Γ`.  Only `.var` and `.rgn` entries exist. -/
inductive FrameTy : Ctx → Ctx → Type where
  | nil {Γ : Ctx} : FrameTy Γ []
  | var {Γ f : Ctx} (τ : Ty Γ) (Φ : FrameTy Γ f) : FrameTy Γ (.var :: f)
  | rgn {Γ f : Ctx} (loans : List (Loan Γ)) (Φ : FrameTy Γ f) : FrameTy Γ (.rgn :: f)
end

/-- Maybe-dead types `τ^SX`: what the stack typing records for a variable.  As
in the paper's grammar, a fully initialized tuple has two representations
(`init (tuple …)` and `tuple (init …)`); `MTy.toTy?` identifies them. -/
inductive MTy (Γ : Ctx) where
  | init (τ : Ty Γ)
  /-- `τ†` -/
  | dead (τ : Ty Γ)
  /-- partially moved tuples -/
  | tuple (k : Nat) (τs : Fin k → MTy Γ)

instance {Γ : Ctx} : Inhabited (Ty Γ) := ⟨.base .unit⟩

namespace Ty
def bool {Γ : Ctx} : Ty Γ := .base .bool
def u32 {Γ : Ctx} : Ty Γ := .base .u32
def unit {Γ : Ctx} : Ty Γ := .base .unit

/-- A closure type `(τ₁, …, τ_k) →^Φ τ_r` (no binders, no bounds). -/
def closure {Γ : Ctx} (k : Nat) (ps : Fin k → Ty Γ) (ret : Ty Γ) (env : FrameExpr Γ) : Ty Γ :=
  .fn {} k ps ret env []
end Ty

/-- The empty frame expression. -/
def FrameExpr.empty {Γ : Ctx} : FrameExpr Γ := .frame [] .nil

/-! ## Renaming -/

def Region.rename {Γ Δ : Ctx} (ρ : TRen Γ Δ) : Region Γ → Region Δ
  | .abs i => .abs (ρ.ren i)
  | .conc r => .conc (ρ.ren r)

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

/-- Weakening of a type by one binder. -/
abbrev Ty.wk {Γ : Ctx} (c : Bnd) (τ : Ty Γ) : Ty (c :: Γ) := τ.rename (TRen.wk Γ c)

/-- Weakening of a type by a prefix of binders. -/
abbrev Ty.wkL {Γ : Ctx} (cs : Ctx) (τ : Ty Γ) : Ty (cs ++ Γ) := τ.rename (TRen.wkL Γ cs)

/-! ## Strengthening (partial renaming) -/

def Region.prename {Γ Δ : Ctx} (ρ : PRen Γ Δ) : Region Γ → Option (Region Δ)
  | .abs i => (ρ.ren i).map .abs
  | .conc r => (ρ.ren r).map .conc

mutual
def Ty.prename {Γ Δ : Ctx} (ρ : PRen Γ Δ) : Ty Γ → Option (Ty Δ)
  | .base b => some (.base b)
  | .tvar α => (ρ.ren α).map .tvar
  | .ref r ω τ => do pure (.ref (← r.prename ρ) ω (← τ.prename ρ))
  | .array τ n => do pure (.array (← τ.prename ρ) n)
  | .tuple k τs => do pure (.tuple k (← optFin fun i => (τs i).prename ρ))
  | .sum τ₁ τ₂ => do pure (.sum (← τ₁.prename ρ) (← τ₂.prename ρ))
  | .fn b k ps ret env bs => do
      pure (.fn b k (← optFin fun i => (ps i).prename (ρ.liftN b.ctx))
        (← ret.prename (ρ.liftN b.ctx)) (← env.prename (ρ.liftN b.ctx)) bs)
def XTy.prename {Γ Δ : Ctx} (ρ : PRen Γ Δ) : XTy Γ → Option (XTy Δ)
  | .sized τ => (τ.prename ρ).map .sized
  | .slice τ => (τ.prename ρ).map .slice
def FrameExpr.prename {Γ Δ : Ctx} (ρ : PRen Γ Δ) : FrameExpr Γ → Option (FrameExpr Δ)
  | .var φ => (ρ.ren φ).map .var
  | .frame f Φ => (Φ.prename ((ρ.lift .frame).liftN f)).map (.frame f)
def FrameTy.prename {Γ Δ : Ctx} (ρ : PRen Γ Δ) : {f : Ctx} → FrameTy Γ f → Option (FrameTy Δ f)
  | _, .nil => some .nil
  | _, .var τ Φ => do pure (.var (← τ.prename ρ) (← Φ.prename ρ))
  | _, .rgn L Φ => do pure (.rgn (← L.mapM (Loan.prename ρ)) (← Φ.prename ρ))
end

def MTy.prename {Γ Δ : Ctx} (ρ : PRen Γ Δ) : MTy Γ → Option (MTy Δ)
  | .init τ => (τ.prename ρ).map .init
  | .dead τ => (τ.prename ρ).map .dead
  | .tuple k τs => (optFin fun i => (τs i).prename ρ).map (.tuple k)

end Oxide
