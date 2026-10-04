module

public import RequestProject.Oxide.Typechecking.Typing

/-!
# Typechecking, part 3: stack validity and well-formed environments

Appendix B.1 ("Well-Formedness Judgments") and B.5 ("Additional Judgments") of
the paper: stack validity `Σ ⊢ σ : Γ` (used in the statements of §3.7),
temporaries, and well-formedness of type environments, global function
definitions and global environments `Σ`.
-/

@[expose] public section

namespace Oxide

/-! ## Stack validity, temporaries and well-formed environments -/

/-- Alignment of an entry of a frame typing with an entry of a stack frame: a
variable binding `x : τ` corresponds to a value of type `τ` (typed in the stack
typing `Γf` of the frame and the frames below it), a region binding to a region
marker. -/
def FrameOK (G : GlobalEnv) (Γf : StackTy) : FrameEntry → StackEntry → Prop
  | .var τ, .val v => HasTypeV G {} [] Γf v τ
  | .rgn _, .rgn => True
  | _, _ => False

/-- `Σ ⊢ σ : Γ` (`WF-StackEmpty`, `WF-StackFrame`): every value of the stack has
the type attributed to it by the stack typing. -/
inductive StoreValid (G : GlobalEnv) : StackTy → Stack → Prop
  | empty : StoreValid G [] []
  | frame (Γ : StackTy) (σ : Stack) (Φ : FrameTy) (ς : StackFrame)
      (h : StoreValid G Γ σ) (hv : List.Forall₂ (FrameOK G (Φ :: Γ)) Φ ς) :
      StoreValid G (Φ :: Γ) (ς :: σ)

/-- `Σ; Γ ⊢ v̄ : Θ` (`WF-Temporaries`). -/
def TempValid (G : GlobalEnv) (Γ : StackTy) (vs : List Value) (Θ : TempTy) : Prop :=
  vs.length = Θ.length ∧
    ∀ (i : Nat) (v : Value) (τ : Ty), vs[i]? = some v → Θ[i]? = some τ →
      HasTypeV G {} (Θ.take i) Γ v τ

/-- `⊢ Δ` (`WF-TVar*`): outlives constraints only mention bound regions. -/
def TyEnvWF (Δ : TyEnv) : Prop := ∀ b ∈ Δ.outlives, b.1 < Δ.nrgn ∧ b.2 < Δ.nrgn

/-- `Σ; Δ; Γ ⊢ Θ` (`WF-TemporaryTyping`). -/
def TempWF (G : GlobalEnv) (Δ : TyEnv) (Γ : StackTy) (Θ : TempTy) : Prop :=
  ∀ τ ∈ Θ, TyWF G Δ Γ τ ∧
    ∀ r ∈ τ.frgns, ¬ ∃ τb ∈ Γ.cod, r ∈ τb.frgns ∧ Γ.loans? r = some []

/-- `Σ ⊢ fn f … { e }` (`WF-FunctionDefinition`). -/
def FnDefWF (G : GlobalEnv) (d : FnDef) : Prop :=
  (∀ b ∈ d.bounds, b.1 < d.nϱ ∧ b.2 < d.nϱ) ∧
    ∃ τf Γ', HasType G (({} : TyEnv).extend d.nφ d.nϱ d.nα d.bounds) []
        [d.params.reverse.map FrameEntry.var] d.body τf Γ' ∧
      Rewrite (({} : TyEnv).extend d.nφ d.nϱ d.nα d.bounds) [] .combine [] τf d.ret []

/-- `⊢ Σ` (`WF-GlobalEnv`). -/
def GlobalWF (G : GlobalEnv) : Prop := ∀ d ∈ G, FnDefWF G d

/-- `⊢ Σ; Δ; Γ; Θ` (`WF-Environments`). -/
def CtxWF (G : GlobalEnv) (Δ : TyEnv) (Γ : StackTy) (Θ : TempTy) : Prop :=
  GlobalWF G ∧ TyEnvWF Δ ∧ StackWF G Δ Γ ∧ TempWF G Δ Γ Θ

end Oxide
