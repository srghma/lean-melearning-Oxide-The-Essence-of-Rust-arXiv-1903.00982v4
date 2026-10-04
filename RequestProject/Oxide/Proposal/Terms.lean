module

public import RequestProject.Oxide.Proposal.Types

/-!
# Proposal prototype, part 3: well-scoped terms, values and functions

`Term Γ` is indexed by the scope `Γ`.  Compared to the current `Term n`:

* all type annotations are `Ty Γ` (sized and in scope), so `let`, closure
  parameters and `Left`/`Right` annotations are well sorted by construction;
* borrows take a concrete region `In .rgn Γ` (the typing rules never accept an
  abstract or unbound region there);
* `letrgn` binds a `.rgn` (no `Region.bound` / opening needed);
* closures, tuples, arrays and calls carry their arity, with the components as
  `Fin k → _` (no `params.length = k` side condition, no auxiliary `Terms`);
* a call carries the binders `b` it instantiates, with exactly `b.nφ` frames,
  `b.nϱ` regions and `b.nα` types;
* the runtime forms have exact scopes: `framed f e` runs `e` in a new frame of
  shape `f`, `shift`/`shiftRgn` pop the binder their body has;
* values live in the same scope (pointers are typed indices into the stack), and
  a closure value's body is scoped by its captured frame.

A closed program is a `Term []`.
-/

@[expose] public section

namespace Oxide.Scoped

open Oxide (Own POp Prim RStep)

/-- Place expressions in terms: rooted at a variable of the top frame. -/
structure PlaceExpr (Γ : Ctx) where
  root : TVar Γ
  ops : List POp
  deriving DecidableEq, Repr

/-- Referents (pointer targets): rooted at a variable of any frame. -/
structure Referent (Γ : Ctx) where
  root : In .var Γ
  steps : List RStep
  deriving DecidableEq, Repr

mutual
/-- Oxide expressions in scope `Γ`. -/
inductive Term : Ctx → Type where
  | val {Γ : Ctx} (v : Value Γ) : Term Γ
  | place {Γ : Ctx} (p : PlaceExpr Γ) : Term Γ
  /-- `&r ω p` -/
  | borrow {Γ : Ctx} (r : In .rgn Γ) (ω : Own) (p : PlaceExpr Γ) : Term Γ
  /-- `&r ω p[e]` -/
  | borrowIdx {Γ : Ctx} (r : In .rgn Γ) (ω : Own) (p : PlaceExpr Γ) (e : Term Γ) : Term Γ
  /-- `&r ω p[e₁..e₂]` -/
  | borrowSlice {Γ : Ctx} (r : In .rgn Γ) (ω : Own) (p : PlaceExpr Γ) (e₁ e₂ : Term Γ) : Term Γ
  /-- `p[e]` -/
  | index {Γ : Ctx} (p : PlaceExpr Γ) (e : Term Γ) : Term Γ
  /-- `p := e` -/
  | assign {Γ : Ctx} (p : PlaceExpr Γ) (e : Term Γ) : Term Γ
  /-- `letrgn<r> { e }` -/
  | letrgn {Γ : Ctx} (e : Term (.rgn :: Γ)) : Term Γ
  /-- `let x : τ = e₁; e₂` -/
  | letE {Γ : Ctx} (τ : Ty Γ) (e₁ : Term Γ) (e₂ : Term (.var :: Γ)) : Term Γ
  | seq {Γ : Ctx} (e₁ e₂ : Term Γ) : Term Γ
  /-- `|x₁ : τ₁, …, x_k : τ_k| → τ_r { e }` -/
  | closure {Γ : Ctx} (k : Nat) (params : Fin k → Ty Γ) (ret : Ty Γ) (body : Term (vars k ++ Γ)) :
      Term Γ
  /-- `e_f::<Φ̄, ρ̄, τ̄>(e₁, …, e_k)` -/
  | app {Γ : Ctx} (f : Term Γ) (b : Binders) (Φs : Fin b.nφ → FrameExpr Γ)
      (ρs : Fin b.nϱ → Region Γ) (τs : Fin b.nα → Ty Γ) (k : Nat) (args : Fin k → Term Γ) : Term Γ
  | ite {Γ : Ctx} (e₁ e₂ e₃ : Term Γ) : Term Γ
  | tuple {Γ : Ctx} (k : Nat) (es : Fin k → Term Γ) : Term Γ
  | array {Γ : Ctx} (k : Nat) (es : Fin k → Term Γ) : Term Γ
  | forE {Γ : Ctx} (e₁ : Term Γ) (e₂ : Term (.var :: Γ)) : Term Γ
  | whileE {Γ : Ctx} (e₁ e₂ : Term Γ) : Term Γ
  | abort {Γ : Ctx} (msg : String) : Term Γ
  | inl {Γ : Ctx} (τ₁ τ₂ : Ty Γ) (e : Term Γ) : Term Γ
  | inr {Γ : Ctx} (τ₁ τ₂ : Ty Γ) (e : Term Γ) : Term Γ
  | matchE {Γ : Ctx} (e : Term Γ) (e₁ e₂ : Term (.var :: Γ)) : Term Γ
  /-- runtime: `framed e`, running `e` in a freshly pushed frame of shape `f` -/
  | framed {Γ : Ctx} (f : Ctx) (e : Term (f ++ .frame :: Γ)) : Term Γ
  /-- runtime: `shift e`, popping the variable bound in `e` -/
  | shift {Γ : Ctx} (e : Term (.var :: Γ)) : Term Γ
  /-- runtime: `shiftprov e`, popping the region bound in `e` -/
  | shiftRgn {Γ : Ctx} (e : Term (.rgn :: Γ)) : Term Γ
/-- Values in scope `Γ`. -/
inductive Value : Ctx → Type where
  | prim {Γ : Ctx} (c : Prim) : Value Γ
  | fn {Γ : Ctx} (f : String) : Value Γ
  | dead {Γ : Ctx} : Value Γ
  | tuple {Γ : Ctx} (k : Nat) (vs : Fin k → Value Γ) : Value Γ
  | array {Γ : Ctx} (k : Nat) (vs : Fin k → Value Γ) : Value Γ
  | slice {Γ : Ctx} (k : Nat) (vs : Fin k → Value Γ) : Value Γ
  /-- `ptr 𝓡`: the root is a stack slot in scope -/
  | ptr {Γ : Ctx} (R : Referent Γ) : Value Γ
  /-- `⟨ς, |x̄ : τ̄| → τ_r { e }⟩`: the captured frame `env` has shape `f`; the
  body runs in a new frame holding the parameters on top of `f`. -/
  | closure {Γ : Ctx} (f : Ctx) (env : Env Γ f) (k : Nat) (params : Fin k → Ty Γ) (ret : Ty Γ)
      (body : Term (vars k ++ (f ++ .frame :: Γ))) : Value Γ
  | inl {Γ : Ctx} (τ₁ τ₂ : Ty Γ) (v : Value Γ) : Value Γ
  | inr {Γ : Ctx} (τ₁ τ₂ : Ty Γ) (v : Value Γ) : Value Γ
/-- `Env Γ f`: values for the `.var` slots of a frame of shape `f`, in scope `Γ`. -/
inductive Env : Ctx → Ctx → Type where
  | nil {Γ : Ctx} : Env Γ []
  | var {Γ f : Ctx} (v : Value Γ) (ε : Env Γ f) : Env Γ (.var :: f)
  | rgn {Γ f : Ctx} (ε : Env Γ f) : Env Γ (.rgn :: f)
end

/-- Closed programs. -/
abbrev Program := Term []

/-! ## Renaming -/

def PlaceExpr.rename {Γ Δ : Ctx} (ρ : Ren Γ Δ) (p : PlaceExpr Γ) : PlaceExpr Δ :=
  ⟨ρ.tvar p.root, p.ops⟩

def Referent.rename {Γ Δ : Ctx} (ρ : TRen Γ Δ) (R : Referent Γ) : Referent Δ :=
  ⟨ρ.ren R.root, R.steps⟩

mutual
def Term.rename {Γ Δ : Ctx} (ρ : Ren Γ Δ) : Term Γ → Term Δ
  | .val v => .val (v.rename ρ.toTRen)
  | .place p => .place (p.rename ρ)
  | .borrow r ω p => .borrow (ρ.ren r) ω (p.rename ρ)
  | .borrowIdx r ω p e => .borrowIdx (ρ.ren r) ω (p.rename ρ) (e.rename ρ)
  | .borrowSlice r ω p e₁ e₂ => .borrowSlice (ρ.ren r) ω (p.rename ρ) (e₁.rename ρ) (e₂.rename ρ)
  | .index p e => .index (p.rename ρ) (e.rename ρ)
  | .assign p e => .assign (p.rename ρ) (e.rename ρ)
  | .letrgn e => .letrgn (e.rename (ρ.lift .rgn))
  | .letE τ e₁ e₂ => .letE (τ.rename ρ.toTRen) (e₁.rename ρ) (e₂.rename (ρ.lift .var))
  | .seq e₁ e₂ => .seq (e₁.rename ρ) (e₂.rename ρ)
  | .closure k ps r body =>
      .closure k (fun i => (ps i).rename ρ.toTRen) (r.rename ρ.toTRen) (body.rename (ρ.liftN (vars k)))
  | .app f b Φs ρs τs k args =>
      .app (f.rename ρ) b (fun i => (Φs i).rename ρ.toTRen) (fun i => (ρs i).rename ρ.toTRen)
        (fun i => (τs i).rename ρ.toTRen) k (fun i => (args i).rename ρ)
  | .ite e₁ e₂ e₃ => .ite (e₁.rename ρ) (e₂.rename ρ) (e₃.rename ρ)
  | .tuple k es => .tuple k fun i => (es i).rename ρ
  | .array k es => .array k fun i => (es i).rename ρ
  | .forE e₁ e₂ => .forE (e₁.rename ρ) (e₂.rename (ρ.lift .var))
  | .whileE e₁ e₂ => .whileE (e₁.rename ρ) (e₂.rename ρ)
  | .abort s => .abort s
  | .inl τ₁ τ₂ e => .inl (τ₁.rename ρ.toTRen) (τ₂.rename ρ.toTRen) (e.rename ρ)
  | .inr τ₁ τ₂ e => .inr (τ₁.rename ρ.toTRen) (τ₂.rename ρ.toTRen) (e.rename ρ)
  | .matchE e e₁ e₂ => .matchE (e.rename ρ) (e₁.rename (ρ.lift .var)) (e₂.rename (ρ.lift .var))
  | .framed f e => .framed f (e.rename (ρ.toTRen.enterFrame.liftN f))
  | .shift e => .shift (e.rename (ρ.lift .var))
  | .shiftRgn e => .shiftRgn (e.rename (ρ.lift .rgn))
def Value.rename {Γ Δ : Ctx} (ρ : TRen Γ Δ) : Value Γ → Value Δ
  | .prim c => .prim c
  | .fn f => .fn f
  | .dead => .dead
  | .tuple k vs => .tuple k fun i => (vs i).rename ρ
  | .array k vs => .array k fun i => (vs i).rename ρ
  | .slice k vs => .slice k fun i => (vs i).rename ρ
  | .ptr R => .ptr (R.rename ρ)
  | .closure f env k ps r body =>
      .closure f (env.rename ρ) k (fun i => (ps i).rename ρ) (r.rename ρ)
        (body.rename ((ρ.enterFrame.liftN f).liftN (vars k)))
  | .inl τ₁ τ₂ v => .inl (τ₁.rename ρ) (τ₂.rename ρ) (v.rename ρ)
  | .inr τ₁ τ₂ v => .inr (τ₁.rename ρ) (τ₂.rename ρ) (v.rename ρ)
def Env.rename {Γ Δ : Ctx} (ρ : TRen Γ Δ) : {f : Ctx} → Env Γ f → Env Δ f
  | _, .nil => .nil
  | _, .var v ε => .var (v.rename ρ) (ε.rename ρ)
  | _, .rgn ε => .rgn (ε.rename ρ)
end

/-! ## Global functions -/

/-- Global function definitions `fn f<φ̄, ϱ̄, ᾱ>(x₁ : τ₁, …, x_k : τ_k) → τ_r
where ϱᵢ : ϱⱼ { e }`.  The signature is closed except for its own binders; the
body runs in its own frame holding the parameters. -/
structure FnDef where
  name : String
  binders : Binders
  k : Nat
  params : Fin k → Ty binders.ctx
  ret : Ty binders.ctx
  bounds : List (Fin binders.nϱ × Fin binders.nϱ)
  body : Term (vars k ++ .frame :: binders.ctx)

/-- Global environments `Σ`. -/
abbrev GlobalEnv := List FnDef

end Oxide.Scoped
