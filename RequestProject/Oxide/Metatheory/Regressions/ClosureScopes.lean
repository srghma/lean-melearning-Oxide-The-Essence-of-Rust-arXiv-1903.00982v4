module

public import RequestProject.Oxide.Metatheory.Statements

/-!
# Regression: a closure body can only mention what its type makes available

With scope-indexed syntax, popping a binder strengthens the result value past the
binder, and this fails if the value still mentions it.  In the previous version
of this formalization a closure body was written in the full enclosing scope, so
it could mention a region in a type annotation without that region appearing in
the closure's type.  The program

  `letrgn<r> { || -> () { Right::<&r shrd (), ()>(()); () } }`

was well typed, but popping `r` got stuck on the closure value; that refuted
progress and type safety.

Now a closure is written in its own scope: its parameters, its captured frame,
and outer binders `o` standing for explicit entries `θ : Inst o Γ`.  The body
above mentions `r`, so `r` must be an outer binder of the closure, and the typing
rules `T-Closure` and `T-ClosureValue` require every binder reachable through
`θ` to occur in the closure's type (`Inst.Covered`).  The type `() → ()` does not
mention `r`, so:

* the closure term is not well typed in any stack typing (`tp_closure_untyped`),
  hence neither is the program (`tp_prog_untyped`);
* the closure value is not well typed either (`tp_closure_value_untyped`), so the
  configuration that used to be stuck is not well typed (`tp_stuck_untyped`).
-/

@[expose] public section

namespace Oxide

variable {sig : Sig}

/-- No parameter types. -/
def noTys {S : Ctx} : Fin 0 → Ty S := fun i => i.elim0

/-- The body `Right::<&r shrd (), ()>(()); ()` of the closure, in the closure's own
scope `[‡, r]`: no parameters, an empty captured frame, and the outer binder `r`. -/
def tpBody : Term sig (vars 0 ++ ([] ++ .frame :: [.rgn])) :=
  .seq (.inr (.ref (.conc (.there .here)) .shrd (.sized Ty.unit)) Ty.unit (.val Value.unit))
    (.val Value.unit)

/-- The entries of the closure's outer binders: its `r` is the enclosing `r`. -/
def tpInst : Inst [.rgn] [.rgn] := .cons (b := .rgn) (.here : In .rgn [.rgn]) .nil

/-- The closure `|| -> () { Right::<&r shrd (), ()>(()); () }` in the scope `[r]`. -/
def tpClosure : Term sig [.rgn] := .closure [] .nil [.rgn] tpInst 0 noTys Ty.unit tpBody

/-- The program `letrgn<r> { || -> () { Right::<&r shrd (), ()>(()); () } }`. -/
def tpProg : Program sig := .letrgn tpClosure

/-- The closure's entries cannot be strengthened past `r`, although its type
`() → ()` (with an empty captured frame) can: the coverage condition fails. -/
theorem tp_not_covered {Φc : FrameTy ([] ++ .frame :: [.rgn]) []} :
    ¬ tpInst.Covered (tpInst.closureTy (k := 0) noTys Ty.unit (.frame [] Φc)) := by
  intro h
  cases Φc
  have := h [] (PRen.drop [] .rgn) (by
    simp [Inst.closureTy, Ty.closure, Ty.prename, FrameExpr.prename, FrameTy.prename, optFin,
      Ty.subst, Ty.unit])
  simp [tpInst, Inst.prename, Entry.prename, PRen.drop] at this

/-- The closure term is not well typed, in any stack typing. -/
theorem tp_closure_untyped {Θ : TempTy [.rgn]} {Γ Γ' : StackTy [.rgn]} {τ : Ty [.rgn]} :
    ¬ HasType sig Θ Γ tpClosure τ Γ' := by
  intro h
  change Typing sig (TyJ.expr Θ Γ tpClosure τ Γ') at h
  generalize hJ : TyJ.expr Θ Γ tpClosure τ Γ' = J at h
  induction h generalizing Γ with
  | drop _ _ _ _ _ _ _ _ _ _ _ ih => cases hJ; exact ih rfl
  | closure _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcov =>
      cases hJ
      exact tp_not_covered hcov
  | _ => cases hJ

/-- The program `letrgn<r> { || -> () { Right::<&r shrd (), ()>(()); () } }` is not
well typed. -/
theorem tp_prog_untyped {τ : Ty []} {Γ' : StackTy []} :
    ¬ HasType sig [] StackTy.empty tpProg τ Γ' := by
  intro h
  change Typing sig (TyJ.expr [] StackTy.empty tpProg τ Γ') at h
  generalize hJ : TyJ.expr [] StackTy.empty tpProg τ Γ' = J at h
  induction h with
  | drop _ _ _ _ π _ _ _ _ _ _ _ => cases hJ; exact π.root.elimNil
  | letrgn _ _ _ _ _ _ _ h =>
      cases hJ
      exact tp_closure_untyped h
  | _ => cases hJ

/-- The closure value (with the empty captured frame) in the scope `[r]`. -/
def tpClosureVal : Value sig [.rgn] := .closure [] .nil [.rgn] tpInst 0 noTys Ty.unit tpBody

/-- The closure value is not well typed. -/
theorem tp_closure_value_untyped {Θ : TempTy [.rgn]} {Γ : StackTy [.rgn]} {τ : Ty [.rgn]} :
    ¬ HasTypeV sig Θ Γ tpClosureVal τ := by
  intro h
  cases h with
  | vClosure _ _ _ _ _ _ _ _ _ _ _ _ _ hcov => exact tp_not_covered hcov

/-- The configuration that used to be stuck (the closure value in focus, `r` on the
stack, and the continuation "pop `r`, then halt") is not well typed. -/
def tpStuck : Config sig := ⟨[.rgn], .rgn .nil, .val tpClosureVal, .popRgn .halt⟩

theorem tp_stuck_untyped : ¬ ConfigTyped sig (tpStuck (sig := sig)) := by
  rintro ⟨Θ, Γ, τ, Γ', -, ht, -⟩
  obtain ⟨Γ₀, hv⟩ := HasType.val_inv ht
  exact tp_closure_value_untyped hv

end Oxide
