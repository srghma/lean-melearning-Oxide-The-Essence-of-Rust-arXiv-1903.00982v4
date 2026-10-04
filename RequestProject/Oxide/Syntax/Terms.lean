module

public import RequestProject.Oxide.Syntax.Types

/-!
# Oxide syntax, part 3: terms, values and global environments

Paper §3.1 ("The Syntax of Oxide"), Figure "Term Syntax of Oxide"; the values,
referents and pointers come from §3.6, Figure "Oxide Syntax Extensions for
Dynamics"; appendix A.

`Term Γ` is indexed by the scope `Γ`:

* all type annotations are `Ty Γ` (sized and in scope), so `let`, closure
  parameters and `Left`/`Right` annotations are well sorted by construction;
* borrows take a concrete region `In .rgn Γ` (the typing rules never accept an
  abstract region there);
* `letrgn` binds a `.rgn`, `let`/`for`/`match` bind a `.var`;
* closures, tuples, arrays and calls carry their arity, with the components as
  `Fin k → _`;
* a call carries the binders `b` it instantiates, with exactly `b.nφ` frames,
  `b.nϱ` regions and `b.nα` types;
* values live in the same scope (pointers are typed indices into the stack), and
  a closure value's body is scoped by its captured frame.

There are no runtime forms (`framed`, `shift`): the operational semantics is an
abstract machine whose continuation records the frames and bindings to pop
(`OperationalSemantics/Machine.lean`).  A closed program is a `Term []`.

Closure and function parameters: parameter `i` (counting from `0` in the order in
which the parameters are written) is the `i`-th most recent binder of the body.
-/

@[expose] public section

namespace Oxide

mutual
/-- Oxide expressions in scope `Γ`. -/
inductive Term : Ctx → Type where
  /-- values (constants, function names; at runtime any value) -/
  | val {Γ : Ctx} (v : Value Γ) : Term Γ
  /-- use of a place expression (move or copy) -/
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
  /-- `e₁; e₂` -/
  | seq {Γ : Ctx} (e₁ e₂ : Term Γ) : Term Γ
  /-- `|x₁ : τ₁, …, x_k : τ_k| → τ_r { e }`: the body sees the parameters on top of
  the current frame (whose variables it captures) -/
  | closure {Γ : Ctx} (k : Nat) (params : Fin k → Ty Γ) (ret : Ty Γ) (body : Term (vars k ++ Γ)) :
      Term Γ
  /-- `e_f::<Φ̄, ρ̄, τ̄>(e₁, …, e_k)` -/
  | app {Γ : Ctx} (f : Term Γ) (b : Binders) (Φs : Fin b.nφ → FrameExpr Γ)
      (ρs : Fin b.nϱ → Region Γ) (τs : Fin b.nα → Ty Γ) (k : Nat) (args : Fin k → Term Γ) : Term Γ
  /-- `if e₁ { e₂ } else { e₃ }` -/
  | ite {Γ : Ctx} (e₁ e₂ e₃ : Term Γ) : Term Γ
  /-- `(e₁, …, e_k)` -/
  | tuple {Γ : Ctx} (k : Nat) (es : Fin k → Term Γ) : Term Γ
  /-- `[e₁, …, e_k]` -/
  | array {Γ : Ctx} (k : Nat) (es : Fin k → Term Γ) : Term Γ
  /-- `for x in e₁ { e₂ }` -/
  | forE {Γ : Ctx} (e₁ : Term Γ) (e₂ : Term (.var :: Γ)) : Term Γ
  /-- `while e₁ { e₂ }` -/
  | whileE {Γ : Ctx} (e₁ e₂ : Term Γ) : Term Γ
  /-- `abort!(str)` -/
  | abort {Γ : Ctx} (msg : String) : Term Γ
  /-- `Left::<τ₁, τ₂>(e)` -/
  | inl {Γ : Ctx} (τ₁ τ₂ : Ty Γ) (e : Term Γ) : Term Γ
  /-- `Right::<τ₁, τ₂>(e)` -/
  | inr {Γ : Ctx} (τ₁ τ₂ : Ty Γ) (e : Term Γ) : Term Γ
  /-- `match e { Left(x₁) => e₁, Right(x₂) => e₂ }` -/
  | matchE {Γ : Ctx} (e : Term Γ) (e₁ e₂ : Term (.var :: Γ)) : Term Γ
/-- Values in scope `Γ`. -/
inductive Value : Ctx → Type where
  /-- constants -/
  | prim {Γ : Ctx} (c : Prim) : Value Γ
  /-- global function names `f` -/
  | fn {Γ : Ctx} (f : String) : Value Γ
  /-- the dead value -/
  | dead {Γ : Ctx} : Value Γ
  /-- tuples -/
  | tuple {Γ : Ctx} (k : Nat) (vs : Fin k → Value Γ) : Value Γ
  /-- arrays -/
  | array {Γ : Ctx} (k : Nat) (vs : Fin k → Value Γ) : Value Γ
  /-- dynamically sized slices `|v₁, …, v_k|` -/
  | slice {Γ : Ctx} (k : Nat) (vs : Fin k → Value Γ) : Value Γ
  /-- `ptr 𝓡`: the root is a stack slot in scope -/
  | ptr {Γ : Ctx} (R : Referent Γ) : Value Γ
  /-- `⟨ς, |x̄ : τ̄| → τ_r { e }⟩`: the captured frame `env` has shape `f`; the
  body runs in a new frame holding the parameters on top of `f`. -/
  | closure {Γ : Ctx} (f : Ctx) (env : Env Γ f) (k : Nat) (params : Fin k → Ty Γ) (ret : Ty Γ)
      (body : Term (vars k ++ (f ++ .frame :: Γ))) : Value Γ
  /-- left injection -/
  | inl {Γ : Ctx} (τ₁ τ₂ : Ty Γ) (v : Value Γ) : Value Γ
  /-- right injection -/
  | inr {Γ : Ctx} (τ₁ τ₂ : Ty Γ) (v : Value Γ) : Value Γ
/-- `Env Γ f`: values for the `.var` slots of a frame of shape `f`, in scope `Γ`. -/
inductive Env : Ctx → Ctx → Type where
  | nil {Γ : Ctx} : Env Γ []
  | var {Γ f : Ctx} (v : Value Γ) (ε : Env Γ f) : Env Γ (.var :: f)
  | rgn {Γ f : Ctx} (ε : Env Γ f) : Env Γ (.rgn :: f)
end

instance {Γ : Ctx} : Inhabited (Value Γ) := ⟨.prim .unit⟩
instance {Γ : Ctx} : Inhabited (Term Γ) := ⟨.val default⟩

/-- Closed programs. -/
abbrev Program := Term []

namespace Value
def unit {Γ : Ctx} : Value Γ := .prim .unit
def num {Γ : Ctx} (k : Nat) : Value Γ := .prim (.num k)
def tt {Γ : Ctx} : Value Γ := .prim (.bool true)
def ff {Γ : Ctx} : Value Γ := .prim (.bool false)
end Value

/-! ## Renaming -/

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
      .closure k (fun i => (ps i).rename ρ.toTRen) (r.rename ρ.toTRen)
        (body.rename (ρ.liftN (vars k)))
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

/-- Weakening of a value by one binder. -/
abbrev Value.wk {Γ : Ctx} (c : Bnd) (v : Value Γ) : Value (c :: Γ) := v.rename (TRen.wk Γ c)

/-! ## Strengthening -/

mutual
def Term.prename {Γ Δ : Ctx} (ρ : PRenT Γ Δ) : Term Γ → Option (Term Δ)
  | .val v => (v.prename ρ.toPRen).map .val
  | .place p => (p.prename ρ).map .place
  | .borrow r ω p => do pure (.borrow (← ρ.ren r) ω (← p.prename ρ))
  | .borrowIdx r ω p e => do pure (.borrowIdx (← ρ.ren r) ω (← p.prename ρ) (← e.prename ρ))
  | .borrowSlice r ω p e₁ e₂ => do
      pure (.borrowSlice (← ρ.ren r) ω (← p.prename ρ) (← e₁.prename ρ) (← e₂.prename ρ))
  | .index p e => do pure (.index (← p.prename ρ) (← e.prename ρ))
  | .assign p e => do pure (.assign (← p.prename ρ) (← e.prename ρ))
  | .letrgn e => (e.prename (ρ.lift .rgn)).map .letrgn
  | .letE τ e₁ e₂ => do
      pure (.letE (← τ.prename ρ.toPRen) (← e₁.prename ρ) (← e₂.prename (ρ.lift .var)))
  | .seq e₁ e₂ => do pure (.seq (← e₁.prename ρ) (← e₂.prename ρ))
  | .closure k ps r body => do
      pure (.closure k (← optFin fun i => (ps i).prename ρ.toPRen) (← r.prename ρ.toPRen)
        (← body.prename (ρ.liftN (vars k))))
  | .app f b Φs ρs τs k args => do
      pure (.app (← f.prename ρ) b (← optFin fun i => (Φs i).prename ρ.toPRen)
        (← optFin fun i => (ρs i).prename ρ.toPRen) (← optFin fun i => (τs i).prename ρ.toPRen) k
        (← optFin fun i => (args i).prename ρ))
  | .ite e₁ e₂ e₃ => do pure (.ite (← e₁.prename ρ) (← e₂.prename ρ) (← e₃.prename ρ))
  | .tuple k es => (optFin fun i => (es i).prename ρ).map (.tuple k)
  | .array k es => (optFin fun i => (es i).prename ρ).map (.array k)
  | .forE e₁ e₂ => do pure (.forE (← e₁.prename ρ) (← e₂.prename (ρ.lift .var)))
  | .whileE e₁ e₂ => do pure (.whileE (← e₁.prename ρ) (← e₂.prename ρ))
  | .abort s => some (.abort s)
  | .inl τ₁ τ₂ e => do pure (.inl (← τ₁.prename ρ.toPRen) (← τ₂.prename ρ.toPRen) (← e.prename ρ))
  | .inr τ₁ τ₂ e => do pure (.inr (← τ₁.prename ρ.toPRen) (← τ₂.prename ρ.toPRen) (← e.prename ρ))
  | .matchE e e₁ e₂ => do
      pure (.matchE (← e.prename ρ) (← e₁.prename (ρ.lift .var)) (← e₂.prename (ρ.lift .var)))
def Value.prename {Γ Δ : Ctx} (ρ : PRen Γ Δ) : Value Γ → Option (Value Δ)
  | .prim c => some (.prim c)
  | .fn f => some (.fn f)
  | .dead => some .dead
  | .tuple k vs => (optFin fun i => (vs i).prename ρ).map (.tuple k)
  | .array k vs => (optFin fun i => (vs i).prename ρ).map (.array k)
  | .slice k vs => (optFin fun i => (vs i).prename ρ).map (.slice k)
  | .ptr R => (R.prename ρ).map .ptr
  | .closure f env k ps r body => do
      pure (.closure f (← env.prename ρ) k (← optFin fun i => (ps i).prename ρ) (← r.prename ρ)
        (← body.prename ((ρ.enterFrame.liftN f).liftN (vars k))))
  | .inl τ₁ τ₂ v => do pure (.inl (← τ₁.prename ρ) (← τ₂.prename ρ) (← v.prename ρ))
  | .inr τ₁ τ₂ v => do pure (.inr (← τ₁.prename ρ) (← τ₂.prename ρ) (← v.prename ρ))
def Env.prename {Γ Δ : Ctx} (ρ : PRen Γ Δ) : {f : Ctx} → Env Γ f → Option (Env Δ f)
  | _, .nil => some .nil
  | _, .var v ε => do pure (.var (← v.prename ρ) (← ε.prename ρ))
  | _, .rgn ε => (ε.prename ρ).map .rgn
end

/-- Strengthening that never fails: the parts of a value that mention a removed
binder (pointers into it, closures mentioning it) are replaced by `dead`.  Used
for the values left on the stack when a binder is popped: a slot whose type is
(partially) dead may legitimately hold such garbage. -/
def Value.prenameD {Γ Δ : Ctx} (ρ : PRen Γ Δ) : Value Γ → Value Δ
  | .prim c => .prim c
  | .fn f => .fn f
  | .dead => .dead
  | .tuple k vs => .tuple k fun i => (vs i).prenameD ρ
  | .array k vs => .array k fun i => (vs i).prenameD ρ
  | .slice k vs => .slice k fun i => (vs i).prenameD ρ
  | .inl τ₁ τ₂ v => match τ₁.prename ρ, τ₂.prename ρ with
    | some τ₁', some τ₂' => .inl τ₁' τ₂' (v.prenameD ρ)
    | _, _ => .dead
  | .inr τ₁ τ₂ v => match τ₁.prename ρ, τ₂.prename ρ with
    | some τ₁', some τ₂' => .inr τ₁' τ₂' (v.prenameD ρ)
    | _, _ => .dead
  | v => (v.prename ρ).getD .dead

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

/-- Look up a global function. -/
def GlobalEnv.lookup (G : GlobalEnv) (f : String) : Option FnDef := G.find? (·.name == f)

end Oxide
