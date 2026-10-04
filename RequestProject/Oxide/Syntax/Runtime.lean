module

public import RequestProject.Oxide.Syntax.Terms

/-!
# Oxide syntax, part 5: runtime stacks, continuations and configurations

Paper §3.6 ("Operational Semantics"), Figure "Oxide Syntax Extensions for
Dynamics": stack frames `ς` and stacks `σ`.  The paper's runtime terms `framed e`
and `shift e` and its evaluation contexts `𝒞` are replaced by the continuations
of an abstract machine (`Cont`): a continuation records the work left to do
around the expression in focus, including the bindings and frames to pop.

* A stack `Stack S` has exactly one slot per binder of `S`: a value for each
  variable, a marker for each concrete region and each frame boundary.  Every
  value may point anywhere in the stack (also to newer slots), so all values live
  in the scope of the whole stack.
* A continuation `Cont S` expects a value in scope `S`.  The frames `popVar`,
  `popRgn` and `popFrame` change the scope: they pop the binders their inner
  continuation does not see.
* A configuration `⟨S, σ, e, κ⟩` has a stack, an expression in focus and a
  continuation, all in the same scope `S`.
-/

@[expose] public section

namespace Oxide

/-- `Slots Γ S`: the contents of stack slots of shape `S`, all values living in
scope `Γ`.  Only `.var`, `.rgn` and `.frame` entries exist at runtime (a stack
never contains unsubstituted type-level binders). -/
inductive Slots (Γ : Ctx) : Ctx → Type where
  | nil : Slots Γ []
  | var {S : Ctx} (v : Value Γ) (σ : Slots Γ S) : Slots Γ (.var :: S)
  | rgn {S : Ctx} (σ : Slots Γ S) : Slots Γ (.rgn :: S)
  | frame {S : Ctx} (σ : Slots Γ S) : Slots Γ (.frame :: S)

/-- Stacks `σ`. -/
abbrev Stack (S : Ctx) := Slots S S

/-- Continuations (the paper's evaluation contexts, made explicit, together with
the pending pops of `shift`, `shiftprov` and `framed`). -/
inductive Cont : Ctx → Type where
  /-- the end of the program -/
  | halt {S : Ctx} : Cont S
  /-- `&r ω p[□]` -/
  | borrowIdx {S : Ctx} (r : In .rgn S) (ω : Own) (p : PlaceExpr S) (κ : Cont S) : Cont S
  /-- `&r ω p[□..e₂]` -/
  | borrowSlice₁ {S : Ctx} (r : In .rgn S) (ω : Own) (p : PlaceExpr S) (e₂ : Term S) (κ : Cont S) :
      Cont S
  /-- `&r ω p[v..□]` -/
  | borrowSlice₂ {S : Ctx} (r : In .rgn S) (ω : Own) (p : PlaceExpr S) (v : Value S) (κ : Cont S) :
      Cont S
  /-- `p[□]` -/
  | index {S : Ctx} (p : PlaceExpr S) (κ : Cont S) : Cont S
  /-- `p := □` -/
  | assign {S : Ctx} (p : PlaceExpr S) (κ : Cont S) : Cont S
  /-- `let x : τ = □; e₂` -/
  | letE {S : Ctx} (τ : Ty S) (e₂ : Term (.var :: S)) (κ : Cont S) : Cont S
  /-- `□; e₂` -/
  | seq {S : Ctx} (e₂ : Term S) (κ : Cont S) : Cont S
  /-- `□::<Φ̄, ρ̄, τ̄>(e₁, …, e_k)` -/
  | appFn {S : Ctx} (b : Binders) (Φs : Fin b.nφ → FrameExpr S) (ρs : Fin b.nϱ → Region S)
      (τs : Fin b.nα → Ty S) (k : Nat) (args : Fin k → Term S) (κ : Cont S) : Cont S
  /-- `v_f::<Φ̄, ρ̄, τ̄>(v₁, …, vᵢ, □, eᵢ₊₂, …)` -/
  | appArg {S : Ctx} (f : Value S) (b : Binders) (Φs : Fin b.nφ → FrameExpr S)
      (ρs : Fin b.nϱ → Region S) (τs : Fin b.nα → Ty S) (done : List (Value S))
      (rest : List (Term S)) (κ : Cont S) : Cont S
  /-- `if □ { e₂ } else { e₃ }` -/
  | ite {S : Ctx} (e₂ e₃ : Term S) (κ : Cont S) : Cont S
  /-- `for x in □ { e₂ }` -/
  | forE {S : Ctx} (e₂ : Term (.var :: S)) (κ : Cont S) : Cont S
  /-- `(v₁, …, vᵢ, □, eᵢ₊₂, …)` -/
  | tuple {S : Ctx} (done : List (Value S)) (rest : List (Term S)) (κ : Cont S) : Cont S
  /-- `[v₁, …, vᵢ, □, eᵢ₊₂, …]` -/
  | array {S : Ctx} (done : List (Value S)) (rest : List (Term S)) (κ : Cont S) : Cont S
  /-- `Left::<τ₁, τ₂>(□)` -/
  | inl {S : Ctx} (τ₁ τ₂ : Ty S) (κ : Cont S) : Cont S
  /-- `Right::<τ₁, τ₂>(□)` -/
  | inr {S : Ctx} (τ₁ τ₂ : Ty S) (κ : Cont S) : Cont S
  /-- `match □ { Left(x) => e₁, Right(y) => e₂ }` -/
  | matchE {S : Ctx} (e₁ e₂ : Term (.var :: S)) (κ : Cont S) : Cont S
  /-- `shift □`: pop the most recent variable -/
  | popVar {S : Ctx} (κ : Cont S) : Cont (.var :: S)
  /-- `shiftprov □`: pop the most recent region -/
  | popRgn {S : Ctx} (κ : Cont S) : Cont (.rgn :: S)
  /-- `framed □`: pop a frame of shape `f` holding `k` parameters on top -/
  | popFrame {S : Ctx} (k : Nat) (f : Ctx) (κ : Cont S) : Cont (vars k ++ (f ++ .frame :: S))

/-- Configurations `(σ; e)` of the abstract machine, with their continuation. -/
structure Config where
  S : Ctx
  stack : Stack S
  focus : Term S
  cont : Cont S

/-- The initial configuration of a closed program. -/
def Config.init (e : Program) : Config := ⟨[], .nil, e, .halt⟩

end Oxide
