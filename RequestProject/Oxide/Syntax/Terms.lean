module

public import RequestProject.Oxide.Syntax.TypeSubst

/-!
# Oxide syntax, part 4: terms, values and global environments

Paper §3.1 ("The Syntax of Oxide"), Figure "Term Syntax of Oxide"; the values,
referents and pointers come from §3.6, Figure "Oxide Syntax Extensions for
Dynamics"; appendix A.

Terms are in **A-normal form**: every operand is an atom (`Atom`: a value, a move
or a copy), every intermediate result is named by a `let`, and a term (`Term`) is
a sequence of `let x : τ = c;` and `c;` ending with a computation `c` (`Comp`).
See the section "Terms and values (A-normal form)" below.

`Term sig Γ` (like `Comp sig Γ` and `Atom sig Γ`) is indexed by the scope `Γ` and
parametrized by the *global signature* `sig`, the list of the types of the
declared global functions:

* all type annotations are `Ty Γ` (sized and in scope), so `let`, closure
  parameters and `Left`/`Right` annotations are well sorted by construction;
* borrows take a concrete region `In .rgn Γ`;
* `letrgn` binds a `.rgn`, `let`/`for`/`match` bind a `.var`;
* **every use of a place says whether it moves or copies**, as `Operand::Move` and
  `Operand::Copy` do in Rust's MIR: the atom `move π` takes a *place* `π` (no
  dereference can be moved out of), `copy p` any place expression;
* **a closure is written in its own scope**: its body sees its parameters, its
  captured frame `f` (each captured entry says which variable or region of the
  current frame it copies, `Cap`) and the outer binders `o` it may mention, given
  by an explicit substitution `θ : Inst o Γ`.  Its parameter and return types live
  in `o` as well.  So a closure body can only mention what its type and its
  captures make available;
* a call carries the binders `b` it instantiates and its type arguments
  `TArgs b Γ`;
* tuples, arrays and calls carry their arity, with the components as `Fin k → _`;
* constants carry their base type (`Prim b`), and `u32` literals are `UInt32`;
* **a global function is an index into the signature** (`FnIdx sig`), so it always
  exists, and the global environment (`GlobalEnv sig`) has exactly one body per
  declared function, typed against the whole signature (so functions may be
  mutually recursive).

There are no runtime forms (`framed`, `shift`): the operational semantics is an
abstract machine whose continuation records the frames and bindings to pop
(`OperationalSemantics/Machine.lean`).  A closed program is a `Term sig []`.

Closure and function parameters: parameter `i` (counting from `0` in the order in
which the parameters are written) is the `i`-th most recent binder of the body.
-/

@[expose] public section

namespace Oxide

/-! ## Global signatures -/

/-- The signature of a global function `fn f<φ̄, ϱ̄, ᾱ>(x₁ : τ₁, …, x_k : τ_k) → τ_r
where ϱᵢ : ϱⱼ`: closed except for its own binders.  The name is only a label. -/
structure FnSig where
  name : String
  binders : Binders
  k : Nat
  params : Fin k → Ty binders.ctx
  ret : Ty binders.ctx
  bounds : List (Fin binders.nϱ × Fin binders.nϱ)

/-- Global signatures: the declared global functions. -/
abbrev Sig := List FnSig

/-- Global function names: indices into a signature. -/
inductive FnIdx : Sig → Type where
  | here {s : FnSig} {sig : Sig} : FnIdx (s :: sig)
  | there {s : FnSig} {sig : Sig} (f : FnIdx sig) : FnIdx (s :: sig)
  deriving DecidableEq, Repr

/-- The signature of a global function (total). -/
def FnIdx.get : {sig : Sig} → FnIdx sig → FnSig
  | s :: _, .here => s
  | _ :: _, .there f => f.get

/-- The type of a global function (in any scope). -/
def FnSig.ty {Γ : Ctx} (d : FnSig) : Ty Γ :=
  .fn d.binders d.k (fun i => (d.params i).rename (TRen.inlL _ Γ))
    ((d.ret).rename (TRen.inlL _ Γ)) .empty d.bounds

/-- The scope in which the body of a global function is written: its parameters in
a new frame above its binders. -/
abbrev FnSig.bodyCtx (d : FnSig) : Ctx := vars d.k ++ .frame :: d.binders.ctx

/-! ## Captures -/

/-- `Cap Γ f`: what a closure captures, as a frame of shape `f`: for each variable
of the frame the variable of the current frame it copies, for each region the
region whose loans it records. -/
inductive Cap (Γ : Ctx) : Ctx → Type where
  | nil : Cap Γ []
  | var {f : Ctx} (x : TVar Γ) (c : Cap Γ f) : Cap Γ (.var :: f)
  | rgn {f : Ctx} (r : In .rgn Γ) (c : Cap Γ f) : Cap Γ (.rgn :: f)

namespace Cap

def rename {Γ Δ : Ctx} (ρ : Ren Γ Δ) : {f : Ctx} → Cap Γ f → Cap Δ f
  | _, .nil => .nil
  | _, .var x c => .var (ρ.tvar x) (c.rename ρ)
  | _, .rgn r c => .rgn (ρ.ren r) (c.rename ρ)

def prename {Γ Δ : Ctx} (ρ : PRenT Γ Δ) : {f : Ctx} → Cap Γ f → Option (Cap Δ f)
  | _, .nil => some .nil
  | _, .var x c => do pure (.var (← ρ.tvar x) (← c.prename ρ))
  | _, .rgn r c => do pure (.rgn (← ρ.ren r) (← c.prename ρ))

/-- The captured variables. -/
def vars {Γ : Ctx} : {f : Ctx} → Cap Γ f → List (TVar Γ)
  | _, .nil => []
  | _, .var x c => x :: c.vars
  | _, .rgn _ c => c.vars

/-- The captured regions. -/
def rgns {Γ : Ctx} : {f : Ctx} → Cap Γ f → List (In .rgn Γ)
  | _, .nil => []
  | _, .var _ c => c.rgns
  | _, .rgn r c => r :: c.rgns

/-- A capture list names each variable and each region at most once.  `T-Closure`
requires this: a variable captured twice would give two copies of a non-copyable
value (for example two `&uniq` references to the same place) in the closure's
frame, while the enclosing stack typing kills the original only once. -/
def Nodup {Γ : Ctx} {f : Ctx} (c : Cap Γ f) : Prop := c.vars.Nodup ∧ c.rgns.Nodup

instance {Γ : Ctx} {f : Ctx} (c : Cap Γ f) : Decidable c.Nodup := by
  unfold Nodup; infer_instance

end Cap

/-! ## Terms and values (A-normal form)

Terms are in **A-normal form**: every operand of an operation is an *atom*
(`Atom`: a value, a move out of a place or a copy out of a place expression), and
every intermediate result is named by a `let`.  The grammar has three levels:

* `Atom`: operands `a ::= v | move π | copy p`;
* `Comp`: computations, i.e. a single operation on atoms (a borrow, an index, an
  assignment, a call, a tuple, …) or a control construct (`letrgn`, `if`, `for`,
  `while`, `match`) whose blocks are terms; the scrutinee of `if`, `for` and
  `match` is an atom;
* `Term`: a sequence of `let x : τ = c;` and `c;` ending with a computation
  `c` (`Term.ret c`).

The right-hand side of a `let` is a computation, never a `let` or a sequence, so
`let`s never nest to the left.  Control constructs are computations, so they may
be bound by a `let` (`let x : τ = if a { e₁ } else { e₂ }; e`): this is the usual
relaxation of A-normal form for languages with blocks (strict A-normal form would
need join points).  The condition of `while` is a term, since it is re-evaluated
on each iteration. -/

mutual
/-- Atoms (operands) in scope `Γ`: values, moves and copies.  Evaluating an atom
does not involve any further evaluation. -/
inductive Atom (sig : Sig) : Ctx → Type where
  /-- values (constants, function names; at runtime any value) -/
  | val {Γ : Ctx} (v : Value sig Γ) : Atom sig Γ
  /-- move out of a place `π` -/
  | move {Γ : Ctx} (π : TPlace Γ) : Atom sig Γ
  /-- copy out of a place expression `p` -/
  | copy {Γ : Ctx} (p : PExpr Γ) : Atom sig Γ
/-- Computations in scope `Γ`: one operation whose operands are atoms, or a control
construct whose blocks are terms. -/
inductive Comp (sig : Sig) : Ctx → Type where
  /-- an atom -/
  | atom {Γ : Ctx} (a : Atom sig Γ) : Comp sig Γ
  /-- `&r ω p` -/
  | borrow {Γ : Ctx} (r : In .rgn Γ) (ω : Own) (p : PExpr Γ) : Comp sig Γ
  /-- `&r ω p[a]` -/
  | borrowIdx {Γ : Ctx} (r : In .rgn Γ) (ω : Own) (p : PExpr Γ) (a : Atom sig Γ) : Comp sig Γ
  /-- `&r ω p[a₁..a₂]` -/
  | borrowSlice {Γ : Ctx} (r : In .rgn Γ) (ω : Own) (p : PExpr Γ) (a₁ a₂ : Atom sig Γ) : Comp sig Γ
  /-- `p[a]` -/
  | index {Γ : Ctx} (p : PExpr Γ) (a : Atom sig Γ) : Comp sig Γ
  /-- `p := a` -/
  | assign {Γ : Ctx} (p : PExpr Γ) (a : Atom sig Γ) : Comp sig Γ
  /-- `|x₁ : τ₁, …, x_k : τ_k| → τ_r { e }`, capturing the frame `f` given by `c`;
  the body, the parameter types and the return type are written in the closure's
  own scope, whose outer binders `o` stand for the entries `θ`. -/
  | closure {Γ : Ctx} (f : Ctx) (c : Cap Γ f) (o : Ctx) (θ : Inst o Γ) (k : Nat)
      (params : Fin k → Ty o) (ret : Ty o) (body : Term sig (vars k ++ (f ++ .frame :: o))) :
      Comp sig Γ
  /-- `a_f::<Φ̄, ρ̄, τ̄>(a₁, …, a_k)` -/
  | app {Γ : Ctx} (f : Atom sig Γ) (b : Binders) (θ : TArgs b Γ) (k : Nat)
      (args : Fin k → Atom sig Γ) : Comp sig Γ
  /-- `(a₁, …, a_k)` -/
  | tuple {Γ : Ctx} (k : Nat) (as : Fin k → Atom sig Γ) : Comp sig Γ
  /-- `[a₁, …, a_k]` -/
  | array {Γ : Ctx} (k : Nat) (as : Fin k → Atom sig Γ) : Comp sig Γ
  /-- `Left::<τ₁, τ₂>(a)` -/
  | inl {Γ : Ctx} (τ₁ τ₂ : Ty Γ) (a : Atom sig Γ) : Comp sig Γ
  /-- `Right::<τ₁, τ₂>(a)` -/
  | inr {Γ : Ctx} (τ₁ τ₂ : Ty Γ) (a : Atom sig Γ) : Comp sig Γ
  /-- `abort!(str)` -/
  | abort {Γ : Ctx} (msg : String) : Comp sig Γ
  /-- `letrgn<r> { e }` -/
  | letrgn {Γ : Ctx} (e : Term sig (.rgn :: Γ)) : Comp sig Γ
  /-- `if a { e₁ } else { e₂ }` -/
  | ite {Γ : Ctx} (a : Atom sig Γ) (e₁ e₂ : Term sig Γ) : Comp sig Γ
  /-- `for x in a { e }` -/
  | forE {Γ : Ctx} (a : Atom sig Γ) (e : Term sig (.var :: Γ)) : Comp sig Γ
  /-- `while e₁ { e₂ }` (the condition `e₁` is re-evaluated at each iteration) -/
  | whileE {Γ : Ctx} (e₁ e₂ : Term sig Γ) : Comp sig Γ
  /-- `match a { Left(x₁) => e₁, Right(x₂) => e₂ }` -/
  | matchE {Γ : Ctx} (a : Atom sig Γ) (e₁ e₂ : Term sig (.var :: Γ)) : Comp sig Γ
/-- Oxide expressions in A-normal form, in scope `Γ`: a sequence of bindings and
statements ending with a computation. -/
inductive Term (sig : Sig) : Ctx → Type where
  /-- the computation `c`, whose value is the value of the term -/
  | ret {Γ : Ctx} (c : Comp sig Γ) : Term sig Γ
  /-- `let x : τ = c; e` -/
  | letE {Γ : Ctx} (τ : Ty Γ) (c : Comp sig Γ) (e : Term sig (.var :: Γ)) : Term sig Γ
  /-- `c; e` -/
  | seq {Γ : Ctx} (c : Comp sig Γ) (e : Term sig Γ) : Term sig Γ
/-- Values in scope `Γ`. -/
inductive Value (sig : Sig) : Ctx → Type where
  /-- constants, with their base type -/
  | prim {Γ : Ctx} {b : BaseTy} (c : Prim b) : Value sig Γ
  /-- global functions -/
  | fn {Γ : Ctx} (f : FnIdx sig) : Value sig Γ
  /-- the dead value -/
  | dead {Γ : Ctx} : Value sig Γ
  /-- tuples -/
  | tuple {Γ : Ctx} (k : Nat) (vs : Fin k → Value sig Γ) : Value sig Γ
  /-- arrays -/
  | array {Γ : Ctx} (k : Nat) (vs : Fin k → Value sig Γ) : Value sig Γ
  /-- dynamically sized slices `|v₁, …, v_k|` -/
  | slice {Γ : Ctx} (k : Nat) (vs : Fin k → Value sig Γ) : Value sig Γ
  /-- `ptr 𝓡`: the root is a stack slot in scope -/
  | ptr {Γ : Ctx} (R : Referent Γ) : Value sig Γ
  /-- `⟨ς, |x̄ : τ̄| → τ_r { e }⟩`: the captured frame `env` has shape `f`; the body
  is written in the closure's own scope (as for closure terms). -/
  | closure {Γ : Ctx} (f : Ctx) (env : Env sig Γ f) (o : Ctx) (θ : Inst o Γ) (k : Nat)
      (params : Fin k → Ty o) (ret : Ty o) (body : Term sig (vars k ++ (f ++ .frame :: o))) :
      Value sig Γ
  /-- left injection -/
  | inl {Γ : Ctx} (τ₁ τ₂ : Ty Γ) (v : Value sig Γ) : Value sig Γ
  /-- right injection -/
  | inr {Γ : Ctx} (τ₁ τ₂ : Ty Γ) (v : Value sig Γ) : Value sig Γ
/-- `Env Γ f`: values for the `.var` slots of a frame of shape `f`, in scope `Γ`. -/
inductive Env (sig : Sig) : Ctx → Ctx → Type where
  | nil {Γ : Ctx} : Env sig Γ []
  | var {Γ f : Ctx} (v : Value sig Γ) (ε : Env sig Γ f) : Env sig Γ (.var :: f)
  | rgn {Γ f : Ctx} (ε : Env sig Γ f) : Env sig Γ (.rgn :: f)
end

variable {sig : Sig}

instance {Γ : Ctx} : Inhabited (Value sig Γ) := ⟨.prim .unit⟩

/-- The term consisting of a value (the result of a finished computation). -/
abbrev Term.val {Γ : Ctx} (v : Value sig Γ) : Term sig Γ := .ret (.atom (.val v))

/-- The term `abort!(str)`. -/
abbrev Term.abort {Γ : Ctx} (msg : String) : Term sig Γ := .ret (.abort msg)

instance {Γ : Ctx} : Inhabited (Term sig Γ) := ⟨.val default⟩

/-- Closed programs. -/
abbrev Program (sig : Sig) := Term sig []

namespace Value
def unit {Γ : Ctx} : Value sig Γ := .prim .unit
def num {Γ : Ctx} (n : UInt32) : Value sig Γ := .prim (.num n)
def tt {Γ : Ctx} : Value sig Γ := .prim (.bool true)
def ff {Γ : Ctx} : Value sig Γ := .prim (.bool false)
end Value

/-! ## Renaming -/

mutual
def Atom.rename {Γ Δ : Ctx} (ρ : Ren Γ Δ) : Atom sig Γ → Atom sig Δ
  | .val v => .val (v.rename ρ.toTRen)
  | .move π => .move (π.rename ρ)
  | .copy p => .copy (p.rename ρ)
def Comp.rename {Γ Δ : Ctx} (ρ : Ren Γ Δ) : Comp sig Γ → Comp sig Δ
  | .atom a => .atom (a.rename ρ)
  | .borrow r ω p => .borrow (ρ.ren r) ω (p.rename ρ)
  | .borrowIdx r ω p a => .borrowIdx (ρ.ren r) ω (p.rename ρ) (a.rename ρ)
  | .borrowSlice r ω p a₁ a₂ => .borrowSlice (ρ.ren r) ω (p.rename ρ) (a₁.rename ρ) (a₂.rename ρ)
  | .index p a => .index (p.rename ρ) (a.rename ρ)
  | .assign p a => .assign (p.rename ρ) (a.rename ρ)
  | .closure f c o θ k ps r body => .closure f (c.rename ρ) o (θ.rename ρ.toTRen) k ps r body
  | .app f b θ k args => .app (f.rename ρ) b (θ.rename ρ.toTRen) k (fun i => (args i).rename ρ)
  | .tuple k as => .tuple k fun i => (as i).rename ρ
  | .array k as => .array k fun i => (as i).rename ρ
  | .inl τ₁ τ₂ a => .inl (τ₁.rename ρ.toTRen) (τ₂.rename ρ.toTRen) (a.rename ρ)
  | .inr τ₁ τ₂ a => .inr (τ₁.rename ρ.toTRen) (τ₂.rename ρ.toTRen) (a.rename ρ)
  | .abort s => .abort s
  | .letrgn e => .letrgn (e.rename (ρ.lift .rgn))
  | .ite a e₁ e₂ => .ite (a.rename ρ) (e₁.rename ρ) (e₂.rename ρ)
  | .forE a e => .forE (a.rename ρ) (e.rename (ρ.lift .var))
  | .whileE e₁ e₂ => .whileE (e₁.rename ρ) (e₂.rename ρ)
  | .matchE a e₁ e₂ => .matchE (a.rename ρ) (e₁.rename (ρ.lift .var)) (e₂.rename (ρ.lift .var))
def Term.rename {Γ Δ : Ctx} (ρ : Ren Γ Δ) : Term sig Γ → Term sig Δ
  | .ret c => .ret (c.rename ρ)
  | .letE τ c e => .letE (τ.rename ρ.toTRen) (c.rename ρ) (e.rename (ρ.lift .var))
  | .seq c e => .seq (c.rename ρ) (e.rename ρ)
def Value.rename {Γ Δ : Ctx} (ρ : TRen Γ Δ) : Value sig Γ → Value sig Δ
  | .prim c => .prim c
  | .fn f => .fn f
  | .dead => .dead
  | .tuple k vs => .tuple k fun i => (vs i).rename ρ
  | .array k vs => .array k fun i => (vs i).rename ρ
  | .slice k vs => .slice k fun i => (vs i).rename ρ
  | .ptr R => .ptr (R.rename ρ)
  | .closure f env o θ k ps r body => .closure f (env.rename ρ) o (θ.rename ρ) k ps r body
  | .inl τ₁ τ₂ v => .inl (τ₁.rename ρ) (τ₂.rename ρ) (v.rename ρ)
  | .inr τ₁ τ₂ v => .inr (τ₁.rename ρ) (τ₂.rename ρ) (v.rename ρ)
def Env.rename {Γ Δ : Ctx} (ρ : TRen Γ Δ) : {f : Ctx} → Env sig Γ f → Env sig Δ f
  | _, .nil => .nil
  | _, .var v ε => .var (v.rename ρ) (ε.rename ρ)
  | _, .rgn ε => .rgn (ε.rename ρ)
end

/-- Weakening of a value by one binder. -/
abbrev Value.wk {Γ : Ctx} (c : Bnd) (v : Value sig Γ) : Value sig (c :: Γ) := v.rename (TRen.wk Γ c)

/-! ## Strengthening -/

mutual
def Atom.prename {Γ Δ : Ctx} (ρ : PRenT Γ Δ) : Atom sig Γ → Option (Atom sig Δ)
  | .val v => (v.prename ρ.toPRen).map .val
  | .move π => (π.prename ρ).map .move
  | .copy p => (p.prename ρ).map .copy
def Comp.prename {Γ Δ : Ctx} (ρ : PRenT Γ Δ) : Comp sig Γ → Option (Comp sig Δ)
  | .atom a => (a.prename ρ).map .atom
  | .borrow r ω p => do pure (.borrow (← ρ.ren r) ω (← p.prename ρ))
  | .borrowIdx r ω p a => do pure (.borrowIdx (← ρ.ren r) ω (← p.prename ρ) (← a.prename ρ))
  | .borrowSlice r ω p a₁ a₂ => do
      pure (.borrowSlice (← ρ.ren r) ω (← p.prename ρ) (← a₁.prename ρ) (← a₂.prename ρ))
  | .index p a => do pure (.index (← p.prename ρ) (← a.prename ρ))
  | .assign p a => do pure (.assign (← p.prename ρ) (← a.prename ρ))
  | .closure f c o θ k ps r body => do
      pure (.closure f (← c.prename ρ) o (← θ.prename ρ.toPRen) k ps r body)
  | .app f b θ k args => do
      pure (.app (← f.prename ρ) b (← θ.prename ρ.toPRen) k (← optFin fun i => (args i).prename ρ))
  | .tuple k as => (optFin fun i => (as i).prename ρ).map (.tuple k)
  | .array k as => (optFin fun i => (as i).prename ρ).map (.array k)
  | .inl τ₁ τ₂ a => do pure (.inl (← τ₁.prename ρ.toPRen) (← τ₂.prename ρ.toPRen) (← a.prename ρ))
  | .inr τ₁ τ₂ a => do pure (.inr (← τ₁.prename ρ.toPRen) (← τ₂.prename ρ.toPRen) (← a.prename ρ))
  | .abort s => some (.abort s)
  | .letrgn e => (e.prename (ρ.lift .rgn)).map .letrgn
  | .ite a e₁ e₂ => do pure (.ite (← a.prename ρ) (← e₁.prename ρ) (← e₂.prename ρ))
  | .forE a e => do pure (.forE (← a.prename ρ) (← e.prename (ρ.lift .var)))
  | .whileE e₁ e₂ => do pure (.whileE (← e₁.prename ρ) (← e₂.prename ρ))
  | .matchE a e₁ e₂ => do
      pure (.matchE (← a.prename ρ) (← e₁.prename (ρ.lift .var)) (← e₂.prename (ρ.lift .var)))
def Term.prename {Γ Δ : Ctx} (ρ : PRenT Γ Δ) : Term sig Γ → Option (Term sig Δ)
  | .ret c => (c.prename ρ).map .ret
  | .letE τ c e => do
      pure (.letE (← τ.prename ρ.toPRen) (← c.prename ρ) (← e.prename (ρ.lift .var)))
  | .seq c e => do pure (.seq (← c.prename ρ) (← e.prename ρ))
def Value.prename {Γ Δ : Ctx} (ρ : PRen Γ Δ) : Value sig Γ → Option (Value sig Δ)
  | .prim c => some (.prim c)
  | .fn f => some (.fn f)
  | .dead => some .dead
  | .tuple k vs => (optFin fun i => (vs i).prename ρ).map (.tuple k)
  | .array k vs => (optFin fun i => (vs i).prename ρ).map (.array k)
  | .slice k vs => (optFin fun i => (vs i).prename ρ).map (.slice k)
  | .ptr R => (R.prename ρ).map .ptr
  | .closure f env o θ k ps r body => do
      pure (.closure f (← env.prename ρ) o (← θ.prename ρ) k ps r body)
  | .inl τ₁ τ₂ v => do pure (.inl (← τ₁.prename ρ) (← τ₂.prename ρ) (← v.prename ρ))
  | .inr τ₁ τ₂ v => do pure (.inr (← τ₁.prename ρ) (← τ₂.prename ρ) (← v.prename ρ))
def Env.prename {Γ Δ : Ctx} (ρ : PRen Γ Δ) : {f : Ctx} → Env sig Γ f → Option (Env sig Δ f)
  | _, .nil => some .nil
  | _, .var v ε => do pure (.var (← v.prename ρ) (← ε.prename ρ))
  | _, .rgn ε => (ε.prename ρ).map .rgn
end

/-- Strengthening that never fails: the parts of a value that mention a removed
binder (pointers into it, closures mentioning it) are replaced by `dead`.  Used
for the values left on the stack when a binder is popped: a slot whose type is
(partially) dead may legitimately hold such garbage. -/
def Value.prenameD {Γ Δ : Ctx} (ρ : PRen Γ Δ) : Value sig Γ → Value sig Δ
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

/-! ## Global environments -/

/-- `Defs sig ss`: one body for each function of the list `ss`, each written in its
own scope and typed against the whole signature `sig`. -/
inductive Defs (sig : Sig) : Sig → Type where
  | nil : Defs sig []
  | cons {s : FnSig} {ss : Sig} (body : Term sig s.bodyCtx) (ds : Defs sig ss) : Defs sig (s :: ss)

/-- Global environments `Σ`: exactly one body per declared function. -/
abbrev GlobalEnv (sig : Sig) := Defs sig sig

/-- The body of a global function (total). -/
def Defs.get : {ss : Sig} → Defs sig ss → (f : FnIdx ss) → Term sig f.get.bodyCtx
  | _, .cons b _, .here => b
  | _, .cons _ ds, .there f => ds.get f

/-- The body of a global function (total). -/
abbrev GlobalEnv.body (G : GlobalEnv sig) (f : FnIdx sig) : Term sig f.get.bodyCtx := G.get f

/-- A global function definition: a signature and a body written against the
global signature `sig`. -/
structure FnDef (sig : Sig) where
  fsig : FnSig
  body : Term sig fsig.bodyCtx

end Oxide
