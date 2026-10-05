module

public import RequestProject.Oxide.Typechecking.Validity

/-!
# Typechecking, part 4: continuations and configurations

The paper types runtime terms `framed e`, `shift e` and evaluation contexts as
ordinary expressions.  With the abstract machine, the work left to do is a
continuation instead, and it gets its own judgment:
`ContOK sig Θ Γ τ κ` says that plugging a value of type `τ`, produced with output
stack typing `Γ` by a term typed under the temporaries `Θ`, into `κ` gives a
well-typed program.  Since terms are in A-normal form, the only continuation
frames are the rest of a sequence of bindings (`T-Let`, `T-Seq`), the rest of a
`while` loop (`T-While`) and the pops.  Each rule is the corresponding typing
rule with its first premise (the computation now in focus) removed.  The
frames `popVar`, `popRgn` and `popFrame` check, like `T-Let`, `T-LetRegion` and
`T-Closure`, that the result type and the stack typing can be strengthened past
the popped binders.

A configuration is well typed (`ConfigTyped`) if its stack is valid for some
stack typing, its focus is well typed in it, and its continuation accepts the
result.
-/

@[expose] public section

namespace Oxide

/-- The judgment for continuations. -/
inductive ContOK (sig : Sig) : {S : Ctx} → TempTy S → StackTy S → Ty S → Cont sig S → Prop
  /-- the end of the program accepts any value -/
  | halt {S : Ctx} (Θ : TempTy S) (Γ : StackTy S) (τ : Ty S) : ContOK sig Θ Γ τ .halt
  /-- `T-Let` -/
  | letE {S : Ctx} (Θ : TempTy S) (Γ Γ₁' Γ' : StackTy S) (Γ₂ : StackTy (.var :: S))
      (τ τa τr : Ty S) (τ₂ : Ty (.var :: S)) (e : Term sig (.var :: S)) (κ : Cont sig S)
      (hr : Rewrite Θ .combine Γ τ τa Γ₁')
      (hnrb : ∀ r ∈ τa.frgns, NotReborrowed Γ₁' r)
      (h₂ : HasType sig (Θ.rename (TRen.wk S .var))
        (gcLoans (Θ.rename (TRen.wk S .var)) (Γ₁'.pushVar (.init (τa.wk .var)))) e τ₂ Γ₂)
      (hdead : (Γ₂.varTy .here).IsDead)
      (hpop : (gcLoans (τ₂ :: Θ.rename (TRen.wk S .var)) Γ₂).popL [.var] = some Γ')
      (hτ : τ₂.prename (PRen.drop S .var) = some τr)
      (hκ : ContOK sig Θ Γ' τr κ) :
      ContOK sig Θ Γ τ (.letE τa e κ)
  /-- `T-Seq` -/
  | seq {S : Ctx} (Θ : TempTy S) (Γ Γ₂ : StackTy S) (τ τ₂ : Ty S) (e : Term sig S) (κ : Cont sig S)
      (h₂ : HasType sig Θ (gcLoans Θ Γ) e τ₂ Γ₂) (hκ : ContOK sig Θ Γ₂ τ₂ κ) :
      ContOK sig Θ Γ τ (.seq e κ)
  /-- `T-While`, after the evaluation of the condition -/
  | whileE {S : Ctx} (Θ : TempTy S) (Γ Γ₂ : StackTy S) (e₁ e₂ : Term sig S) (κ : Cont sig S)
      (h₂ : HasType sig Θ Γ e₂ Ty.unit Γ₂)
      (h₁' : HasType sig Θ Γ₂ e₁ Ty.bool Γ₂) (h₂' : HasType sig Θ Γ₂ e₂ Ty.unit Γ₂)
      (hκ : ContOK sig Θ Γ₂ Ty.unit κ) :
      ContOK sig Θ Γ Ty.bool (.whileE e₁ e₂ κ)
  /-- the end of the scope of a variable (`T-Shift`) -/
  | popVar {S : Ctx} (Θ : TempTy S) (Γ : StackTy (.var :: S)) (Γ' : StackTy S) (τ : Ty (.var :: S))
      (τ' : Ty S) (κ : Cont sig S)
      (hpop : (gcLoans (τ :: Θ.rename (TRen.wk S .var)) Γ).popL [.var] = some Γ')
      (hτ : τ.prename (PRen.drop S .var) = some τ')
      (hκ : ContOK sig Θ Γ' τ' κ) :
      ContOK sig (Θ.rename (TRen.wk S .var)) Γ τ (.popVar κ)
  /-- the end of the scope of a region -/
  | popRgn {S : Ctx} (Θ : TempTy S) (Γ : StackTy (.rgn :: S)) (Γ' : StackTy S) (τ : Ty (.rgn :: S))
      (τ' : Ty S) (κ : Cont sig S)
      (hpop : (gcLoans (τ :: Θ.rename (TRen.wk S .rgn)) Γ).popL [.rgn] = some Γ')
      (hτ : τ.prename (PRen.drop S .rgn) = some τ')
      (hκ : ContOK sig Θ Γ' τ' κ) :
      ContOK sig (Θ.rename (TRen.wk S .rgn)) Γ τ (.popRgn κ)
  /-- the end of a call (`T-Framed`, with the no-escape condition) -/
  | popFrame {S : Ctx} (k : Nat) (f : Ctx) (Θ : TempTy S) (Γ : StackTy (vars k ++ (f ++ .frame :: S)))
      (Γ' : StackTy S) (τ : Ty (vars k ++ (f ++ .frame :: S))) (τ' : Ty S) (κ : Cont sig S)
      (hpop : (gcLoans (τ :: Θ.rename (TRen.frameRen k f S)) Γ).popFrame k f = some Γ')
      (hτ : τ.prename (PRen.popFrameK k f S) = some τ')
      (hκ : ContOK sig Θ Γ' τ' κ) :
      ContOK sig (Θ.rename (TRen.frameRen k f S)) Γ τ (.popFrame k f κ)

/-- A configuration is well typed: its stack is valid for some stack typing, its
focus is well typed, and its continuation accepts the result. -/
def ConfigTyped (sig : Sig) (c : Config sig) : Prop :=
  ∃ (Θ : TempTy c.S) (Γ : StackTy c.S) (τ : Ty c.S) (Γ' : StackTy c.S),
    StoreValid Γ c.stack ∧ HasType sig Θ Γ c.focus τ Γ' ∧ ContOK sig Θ Γ' τ c.cont

end Oxide
