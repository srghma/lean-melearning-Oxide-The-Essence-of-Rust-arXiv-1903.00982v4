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
* A configuration `⟨S, σ, e, κ⟩` has a stack, a term in focus and a
  continuation, all in the same scope `S`.  A finished computation is the term
  `Term.val v`.
-/

@[expose] public section

namespace Oxide

/-- `Slots Γ S`: the contents of stack slots of shape `S`, all values living in
scope `Γ`.  Only `.var`, `.rgn` and `.frame` entries exist at runtime: there is no
case for type-level binders, so a stack over a scope containing one is empty
(`Slots.runtime`). -/
inductive Slots (sig : Sig) (Γ : Ctx) : Ctx → Type where
  | nil : Slots sig Γ []
  | var {S : Ctx} (v : Value sig Γ) (σ : Slots sig Γ S) : Slots sig Γ (.var :: S)
  | rgn {S : Ctx} (σ : Slots sig Γ S) : Slots sig Γ (.rgn :: S)
  | frame {S : Ctx} (σ : Slots sig Γ S) : Slots sig Γ (.frame :: S)

/-- Stacks `σ`. -/
abbrev Stack (sig : Sig) (S : Ctx) := Slots sig S S

/-- Stacks only exist over runtime scopes (variables, concrete regions and frame
boundaries). -/
theorem Slots.runtime {sig : Sig} {Γ : Ctx} : {S : Ctx} → Slots sig Γ S → S.Runtime
  | _, .nil => fun _ h => nomatch h
  | _, .var _ σ => fun b h => by
      rcases List.mem_cons.mp h with rfl | h
      · trivial
      · exact σ.runtime b h
  | _, .rgn σ => fun b h => by
      rcases List.mem_cons.mp h with rfl | h
      · trivial
      · exact σ.runtime b h
  | _, .frame σ => fun b h => by
      rcases List.mem_cons.mp h with rfl | h
      · trivial
      · exact σ.runtime b h

/-- Continuations (the paper's evaluation contexts, made explicit, together with
the pending pops of `shift`, `shiftprov` and `framed`).  Since terms are in
A-normal form, the operands of an operation are atoms, which are evaluated in a
single step: the only work left to do around a computation is the rest of a
sequence of bindings, the next iteration of a `while` loop, and the pops. -/
inductive Cont (sig : Sig) : Ctx → Type where
  /-- the end of the program -/
  | halt {S : Ctx} : Cont sig S
  /-- `let x : τ = □; e` -/
  | letE {S : Ctx} (τ : Ty S) (e : Term sig (.var :: S)) (κ : Cont sig S) : Cont sig S
  /-- `□; e` -/
  | seq {S : Ctx} (e : Term sig S) (κ : Cont sig S) : Cont sig S
  /-- `while □ { e₂ }`, where `□` is the current evaluation of the condition `e₁` -/
  | whileE {S : Ctx} (e₁ e₂ : Term sig S) (κ : Cont sig S) : Cont sig S
  /-- `shift □`: pop the most recent variable -/
  | popVar {S : Ctx} (κ : Cont sig S) : Cont sig (.var :: S)
  /-- `shiftprov □`: pop the most recent region -/
  | popRgn {S : Ctx} (κ : Cont sig S) : Cont sig (.rgn :: S)
  /-- `framed □`: pop a frame of shape `f` holding `k` parameters on top -/
  | popFrame {S : Ctx} (k : Nat) (f : Ctx) (κ : Cont sig S) : Cont sig (vars k ++ (f ++ .frame :: S))

/-- Configurations `(σ; e)` of the abstract machine, with their continuation. -/
structure Config (sig : Sig) where
  S : Ctx
  stack : Stack sig S
  focus : Term sig S
  cont : Cont sig S

/-- The scope of a configuration is a runtime scope. -/
theorem Config.runtime {sig : Sig} (c : Config sig) : c.S.Runtime := c.stack.runtime

/-- The initial configuration of a closed program. -/
def Config.init {sig : Sig} (e : Program sig) : Config sig := ⟨[], .nil, e, .halt⟩

end Oxide
