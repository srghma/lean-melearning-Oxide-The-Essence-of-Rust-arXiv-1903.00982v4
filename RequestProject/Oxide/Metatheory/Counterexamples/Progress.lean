module

public import RequestProject.Oxide.Metatheory.Statements

/-!
# Progress does not hold for the scoped rules as they stand

With scope-indexed syntax, popping a binder (`popVar`, `popRgn`, `popFrame`)
strengthens the result value past the binder, and this fails if the value still
mentions it.  The typing rules check that the *type* of the result and the
remaining stack typing do not mention the popped binder, but a closure value can
mention a region in its body without that region appearing in its type: like the
paper's `T-Closure`, `T-ClosureValue` puts no constraint on the regions that
occur in type annotations inside the body.

The configuration `tpStuck` has a region `r` on the stack, the continuation
"pop `r`, then halt", and in focus the closure value

  `⟨•, || -> () { Right::<&r shrd (), ()>(()); () }⟩`

whose type `() → ()` (with the empty captured frame) does not mention `r`.  It
is well typed (`tp_typed`), but the closure's body cannot be strengthened past
`r`, so the machine is stuck (`tp_stuck`).  Hence `¬ Progress G` for every `G`
(`not_progress`).

With named regions, as in the paper, the body would simply keep mentioning a
region that no longer exists, which is harmless at runtime since annotations are
never evaluated.  A repair is to require (in `T-Closure` and `T-ClosureValue`)
that the regions of the enclosing scope occurring in a closure body also occur
in the closure's type or are captured by it.
-/

@[expose] public section

namespace Oxide

variable {G : GlobalEnv}

/-- No parameter types. -/
def noTys {S : Ctx} : Fin 0 → Ty S := fun i => i.elim0

/-- The body `Right::<&r shrd (), ()>(()); ()` of the closure, in the scope
`[‡, r]` (an empty captured frame above the region `r`). -/
def tpBody : Term (vars 0 ++ ([] ++ [.frame, .rgn])) :=
  .seq (.inr (.ref (.conc (.there .here)) .shrd (.sized Ty.unit)) Ty.unit (.val Value.unit))
    (.val Value.unit)

/-- The closure value `⟨•, || -> () { Right::<&r shrd (), ()>(()); () }⟩`. -/
def tpClosure : Value [.rgn] := .closure [] .nil 0 noTys Ty.unit tpBody

/-- Its type `() → ()`, with the empty captured frame. -/
def tpTy : Ty [.rgn] := Ty.closure 0 noTys Ty.unit (.frame [] .nil)

/-- The stack typing `r ↦ {}`. -/
def tpΓ : StackTy [.rgn] := ⟨.rgn [] .nil, []⟩

/-- The stuck configuration: the closure value in focus, the region `r` on the
stack, and the continuation "pop `r`, then halt". -/
def tpStuck : Config := ⟨[.rgn], .rgn .nil, .val tpClosure, .popRgn .halt⟩

/-- The closure value has type `() → ()`. -/
theorem tp_closure_typed : HasTypeV G [] tpΓ tpClosure tpTy := by
  refine Typing.vClosure [] tpΓ [] .nil 0 noTys Ty.unit tpBody .nil
    (gcLoans (TempTy.rename (TRen.frameRen 0 [] [.rgn]) []) (closureBodyTy tpΓ .nil noTys))
    (Typing.envNil _ _) ?_ ?_
  · exact Typing.seq _ _ _ _ _ _ _ _
      (Typing.inr _ _ _ _ _ _ (Typing.val _ _ _ _ (Typing.vUnit _ _)))
      (Typing.val _ _ _ _ (Typing.vUnit _ _))
  · rfl

/-- The configuration `tpStuck` is well typed. -/
theorem tp_typed : ConfigTyped G tpStuck := by
  refine ⟨[], tpΓ, tpTy, tpΓ, ?_, Typing.val _ _ _ _ tp_closure_typed, ?_⟩
  · intro x
    cases x with
    | there x => exact x.elimNil
  · exact ContOK.popRgn [] tpΓ StackTy.empty tpTy (Ty.closure 0 noTys Ty.unit (.frame [] .nil)) .halt
      rfl rfl (.halt _ _ _)

/-- The closure value cannot be strengthened past `r`: its body mentions `r`. -/
theorem tp_closure_prename : tpClosure.prename (PRen.drop [] .rgn) = none := by
  simp [tpClosure, tpBody, Value.prename, Term.prename, Ty.prename, Region.prename,
    PRen.enterFrame, PRenT.liftN, PRen.lift, PRen.drop]

/-- A value in focus followed by `popRgn`, which cannot be strengthened past the
popped region. -/
def Cont.popRgnBlocked : {S : Ctx} → Cont S → Term S → Bool
  | _, .popRgn (S := S) _, .val v => (v.prename (PRen.drop S .rgn)).isNone
  | _, _, _ => false

/-- A configuration whose focus and continuation are as in `Cont.popRgnBlocked`. -/
def Config.popRgnBlocked (c : Config) : Bool := Cont.popRgnBlocked c.cont c.focus

/-- Such configurations do not step. -/
theorem Step.not_popRgnBlocked {c c' : Config} (h : Step G c c') : c.popRgnBlocked = false := by
  cases h <;> first | rfl | simp_all [Config.popRgnBlocked, Cont.popRgnBlocked]

/-- The configuration `tpStuck` is stuck. -/
theorem tp_stuck : ¬ tpStuck.IsFinal ∧ ∀ c', ¬ Step G tpStuck c' := by
  refine ⟨?_, fun c' h => ?_⟩
  · rintro (⟨v, -, h⟩ | ⟨s, h⟩) <;> cases h
  · have := Step.not_popRgnBlocked h
    simp [tpStuck, Config.popRgnBlocked, Cont.popRgnBlocked, tp_closure_prename] at this

/-- **Progress (`Progress`) is false** for every global environment: the well-typed
configuration `tpStuck` is neither final nor able to step. -/
theorem not_progress : ¬ Progress G := fun h =>
  (h tpStuck tp_typed).elim (tp_stuck (G := G)).1 fun ⟨c', hs⟩ => (tp_stuck (G := G)).2 c' hs

/-! ## The stuck configuration is reachable from a well-typed program

The machine reaches `tpStuck` from the closed program

  `letrgn<r> { || -> () { Right::<&r shrd (), ()>(()); () } }`

when the closure does not capture `r` (the capture selection of `E-Closure`,
like that of `T-Closure`, may leave out entries of the current frame), so the
program also refutes type safety, independently of the `E-Move` counterexample
of `Counterexamples/TypeSafety.lean`. -/

/-- The closure's body as written, in the scope `[r]`. -/
def tpSrcBody : Term (vars 0 ++ [.rgn]) :=
  .seq (.inr (.ref (.conc .here) .shrd (.sized Ty.unit)) Ty.unit (.val Value.unit)) (.val Value.unit)

/-- The program `letrgn<r> { || -> () { Right::<&r shrd (), ()>(()); () } }`. -/
def tpProg : Program := .letrgn (.closure 0 noTys Ty.unit tpSrcBody)

/-- The capture selection that leaves `r` out. -/
def tpSel : Sel [] [.rgn] := .skipRgn .nil

theorem tp_body_rename : tpSrcBody = tpBody.rename (tpSel.ren.liftN (vars 0)) := rfl

/-- The program is well typed. -/
theorem tp_prog_typed : ∃ τ Γ', HasType G [] StackTy.empty tpProg τ Γ' := by
  refine ⟨_, _, Typing.letrgn [] StackTy.empty StackTy.empty tpΓ _ tpTy
    (Ty.closure 0 noTys Ty.unit (.frame [] .nil)) ?h rfl rfl⟩
  case h =>
    refine Typing.closure [] tpΓ tpΓ 0 noTys Ty.unit tpSrcBody [] tpSel tpBody .nil
      (gcLoans (TempTy.rename (TRen.frameRen 0 [] [.rgn]) []) (closureBodyTy tpΓ .nil noTys))
      tp_body_rename rfl (by simp [Sel.selRgns, tpSel]) (by simp [Ty.frgns, Ty.unit]) ?_ rfl
    exact Typing.seq _ _ _ _ _ _ _ _
      (Typing.inr _ _ _ _ _ _ (Typing.val _ _ _ _ (Typing.vUnit _ _)))
      (Typing.val _ _ _ _ (Typing.vUnit _ _))

/-- The program reaches `tpStuck`. -/
theorem tp_steps : Steps G (Config.init tpProg) tpStuck := by
  refine .step _ _ _ (Step.letrgn _ _ _) ?_
  refine .step _ _ _ (Step.closure _ 0 noTys Ty.unit tpSrcBody _ [] tpSel tpBody .nil
    tp_body_rename rfl) ?_
  exact .refl _

/-- **Type safety (`TypeSafety`) is false** for every global environment, also
because of closure bodies mentioning regions that their types do not mention. -/
theorem not_type_safety_scope : ¬ TypeSafety G := by
  intro h
  obtain ⟨τ, Γ', ht⟩ := tp_prog_typed (G := G)
  rcases h tpProg τ Γ' ht tpStuck tp_steps with hf | ⟨c', hs⟩
  · exact (tp_stuck (G := G)).1 hf
  · exact (tp_stuck (G := G)).2 c' hs

end Oxide
