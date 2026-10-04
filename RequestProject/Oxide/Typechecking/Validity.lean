module

public import RequestProject.Oxide.Typechecking.Typing
public import RequestProject.Oxide.Metafunctions.Stacks

/-!
# Typechecking, part 3: stack validity and well-formed global environments

Appendix B.1 ("Well-Formedness Judgments") and B.5 ("Additional Judgments") of
the paper: stack validity `Σ ⊢ σ : Γ` (used in the statements of §3.7) and
well-formedness of global function definitions and global environments `Σ`.

Since the stack and the stack typing are indexed by the same scope, stack
validity is simply: every slot holds a value of the (maybe-dead) type recorded
for it.
-/

@[expose] public section

namespace Oxide

/-- `Σ ⊢ σ : Γ` (`WF-StackEmpty`, `WF-StackFrame`): every value of the stack has
the type attributed to it by the stack typing. -/
def StoreValid (G : GlobalEnv) {S : Ctx} (Γ : StackTy S) (σ : Stack S) : Prop :=
  ∀ x : In .var S, HasTypeM G Γ (σ.get x) (Γ.varTy x)

/-- The stack typing in which the body of a global function is checked: its
binders and bounds, a frame boundary, and the parameters. -/
def FnDef.bodyTy (d : FnDef) : StackTy (vars d.k ++ .frame :: d.binders.ctx) :=
  ((StackTy.ofBinders d.binders d.bounds).pushFrame (f := []) .nil).pushVars
    fun i => (d.params i).rename (TRen.wkFrame [] _)

/-- `Σ ⊢ fn f … { e }` (`WF-FunctionDefinition`): the body has a type that can be
rewritten into the return type, and its frame can be popped. -/
def FnDefWF (G : GlobalEnv) (d : FnDef) : Prop :=
  ∃ τf Γo Γo', HasType G [] d.bodyTy d.body τf Γo ∧
    Rewrite [] .combine Γo τf (d.ret.rename (TRen.frameRen d.k [] _)) Γo' ∧
    ((gcLoans [d.ret.rename (TRen.frameRen d.k [] _)] Γo').popFrame d.k []).isSome

/-- `⊢ Σ` (`WF-GlobalEnv`). -/
def GlobalWF (G : GlobalEnv) : Prop := ∀ d ∈ G, FnDefWF G d

end Oxide
