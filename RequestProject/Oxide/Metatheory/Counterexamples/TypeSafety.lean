module
public import RequestProject.Oxide.Metatheory.Counterexamples.Preservation

/-!
# Type safety, as stated in the paper, does not hold

The theorem "Type Safety" of the paper (formalized as `TypeSafety`: every
configuration reachable from a well-typed closed program run on the empty stack is
final or can step) is false.

The paper's rules `E-Move` and `E-Copy` both apply to a place `π`: `E-Move` has no
side condition requiring the type of `π` to be non-copyable (that distinction is
only made by the typing rules `T-Move`/`T-Copy`).  In the well-typed program

  `let x : bool = true; x; if x { () } else { () }`

the first use of `x` (typed by `T-Copy`) may therefore step by `E-Move`, which
overwrites `x` with `dead`.  The second use then copies `dead`, and
`if dead { () } else { () }` is stuck (`not_type_safety`).

Since every configuration that progress applies to steps, the stuck configuration
is not well typed; so restricting preservation to reachable configurations does not
make it true (`ts_reachable_not_typable`; see also `Metatheory/Counterexamples/Reachability.lean`).
-/

@[expose] public section

namespace Oxide

variable {G : GlobalEnv}

/-- `x`, the variable with de Bruijn index 0. -/
def tsX : PlaceExpr 1 := ⟨0, []⟩

/-- The branch `if x { () } else { () }`. -/
def tsIte : Term 1 := .ite (.place tsX) (.val Value.unit) (.val Value.unit)

/-- The program `let x : bool = true; x; if x { () } else { () }`. -/
def tsProg : Term 0 := .letE Ty.bool (.val Value.tt) (.seq (.place tsX) tsIte)

/-- The stack typing with one frame containing `x : bool`. -/
def tsΓ : StackTy := [[.var Ty.bool]]

/-- The stack typing with one frame containing `x : bool†`. -/
def tsΓd : StackTy := [[.var (.dead Ty.bool)]]

theorem ts_copy_x : HasType G {} [] tsΓ (.place tsX) Ty.bool tsΓ := by
  refine Typing.copy {} [] tsΓ tsX ⟨0, []⟩ [⟨.shrd, ⟨0, []⟩⟩] Ty.bool [] rfl ?_ ?_ (.base _)
    (by simp [Ty.copyable, Ty.noncopyable, Ty.bool])
  · refine OwnSafe.place (π := ⟨0, []⟩) [] ?_
    intro r' L h
    simp [regionsOf, tsΓ, StackTy.rgns, StackTy.allLoans, StackTy.cod, StackTy.allVarTys,
      FrameTy.rgnLoans, FrameTy.varTys, Ty.closureFrames, Ty.bool, Ty.fnTypes] at h
  · exact PlaceTy.var 0 Ty.bool rfl (.base _)

theorem ts_unit_drop : HasType G {} [] tsΓ (n := 1) (.val Value.unit) Ty.unit tsΓd :=
  Typing.drop {} [] tsΓ tsΓd tsΓd ⟨0, []⟩ Ty.bool Ty.unit _ rfl (.base _) rfl
    (Typing.val _ _ _ _ _ (Typing.vUnit _ _ _))

theorem ts_ite : HasType G {} [] tsΓ tsIte Ty.unit tsΓd := by
  refine Typing.ite {} [] tsΓ tsΓ tsΓd tsΓd tsΓd tsΓd tsΓd _ _ _ Ty.unit Ty.unit Ty.unit
    ts_copy_x ts_unit_drop ts_unit_drop (.inl rfl) (.base _) (.base _) (.base _)
    (.refl _ _ _) (.refl _ _ _) ?_
  simp [tsΓd, StackTy.union, FrameTy.union]

/-- The program `let x : bool = true; x; if x { () } else { () }` is well typed. -/
theorem ts_typed : HasType G {} [] [] tsProg Ty.unit [[]] := by
  refine Typing.letE {} [] [] [] [] [] [] Ty.bool Ty.bool Ty.unit (.dead Ty.bool) _ _
    (Typing.val _ _ _ _ _ (Typing.vBool _ _ _ true)) (.base _) (.base _) (.refl _ _ _)
    (by simp [Ty.bool, Ty.frgns]) ?_ (.base _) (.dead _ (.base _))
  have hgc : gcLoans [] (StackTy.push [] (.var Ty.bool)) = tsΓ := rfl
  rw [hgc]
  refine Typing.seq {} [] tsΓ tsΓ tsΓd _ _ Ty.bool Ty.unit ts_copy_x (.base _) ?_ (.base _)
  have hgc' : gcLoans [] tsΓ = tsΓ := rfl
  rw [hgc']
  exact ts_ite

/-- The stuck configuration reached by moving the copyable `x` with `E-Move`. -/
def tsStuck : Term 0 := .shift (.ite (.val Value.dead) (.val Value.unit) (.val Value.unit))

/-- The stack of the stuck configuration. -/
def tsStuckσ : Stack := [[.val .dead]]

/-- The program reaches the stuck configuration: `E-Move` may be applied to the
copyable variable `x` (the dynamics do not distinguish moves from copies), so the
second use of `x` reads `dead`. -/
theorem ts_steps : Steps G [] tsProg tsStuckσ tsStuck := by
  refine Steps.step _ [[.val Value.tt]] _ _ (.shift (.seq (.place tsX) tsIte)) _
    (Step.letE [] Ty.bool Value.tt _) ?_
  refine Steps.step _ tsStuckσ _ _ (.shift (.seq (.val Value.tt) tsIte)) _
    (Step.ctx .shift _ _ _ _ (Step.ctx (.seq tsIte) _ _ _ _
      (Step.move _ _ tsX ⟨0, []⟩ Value.tt (by simp [tsX]) rfl rfl rfl))) ?_
  refine Steps.step _ tsStuckσ _ _ (.shift tsIte) _
    (Step.ctx .shift _ _ _ _ (Step.seq _ _ _)) ?_
  refine Steps.step _ tsStuckσ _ _ tsStuck _
    (Step.ctx .shift _ _ tsIte _ (Step.ctx (.ite (.val Value.unit) (.val Value.unit)) _ _ _ _
      (Step.copy _ tsX ⟨0, []⟩ Value.dead rfl rfl))) ?_
  exact Steps.refl _ _

/-- Whether a term is a value. -/
def Term.isValB {n : Nat} : Term n → Bool
  | .val _ => true
  | _ => false

/-- Plugging into an evaluation context never yields a value. -/
theorem ECtx.plug_isValB {m n : Nat} (C : ECtx m n) (e : Term m) : (C.plug e).isValB = false := by
  cases C <;> rfl

/-- Values do not step. -/
theorem Step.isValB {σ σ' : Stack} {n : Nat} {e e' : Term n}
    (h : Step G σ e σ' e') : e.isValB = false := by
  induction h <;> first | rfl | exact ECtx.plug_isValB _ _

/-- Whether a value is a boolean constant. -/
def Value.isBoolB : Value → Bool
  | .prim (.bool _) => true
  | _ => false

/-- A syntactic class of stuck terms: `if v { … } else { … }` where `v` is a
value that is not a boolean, possibly below `shift` and `shiftprov`. -/
def Term.stuckB {n : Nat} : Term n → Bool
  | .ite (.val v) _ _ => !v.isBoolB
  | .shift e => e.stuckB
  | .shiftRgn e => e.stuckB
  | _ => false

/-- Terms of the class `Term.stuckB` do not step. -/
theorem Step.stuckB {σ σ' : Stack} {n : Nat} {e e' : Term n}
    (h : Step G σ e σ' e') : e.stuckB = false := by
  induction h with
  | ctx C σ σ' e e' h ih =>
    have hv := Step.isValB h
    cases C <;> first
      | rfl
      | exact ih
      | (cases e <;> simp_all [ECtx.plug, Term.isValB, Term.stuckB])
  | ctxAbort C => cases C <;> rfl
  | _ => rfl

/-- A configuration whose term is in the class `Term.stuckB` is stuck. -/
theorem stuck_of_stuckB {σ : Stack} {n : Nat} {e : Term n} (he : e.stuckB = true) :
    ¬ e.IsFinal ∧ ∀ σ' e', ¬ Step G σ e σ' e' := by
  refine ⟨?_, fun σ' e' h => by simp [Step.stuckB h] at he⟩
  rintro (⟨v, rfl⟩ | ⟨s, rfl⟩) <;> simp [Term.stuckB] at he

/-- The configuration `(tsStuckσ; tsStuck)` is stuck. -/
theorem ts_stuck : ¬ tsStuck.IsFinal ∧ ∀ σ'' e'', ¬ Step G tsStuckσ tsStuck σ'' e'' :=
  stuck_of_stuckB rfl

/-- **Type safety, as stated in the paper (`TypeSafety`), is false** for every
global environment, in particular for well-formed ones such as `[]`. -/
theorem not_type_safety : ¬ TypeSafety G := by
  intro h
  rcases h tsProg Ty.unit [[]] ts_typed tsStuckσ tsStuck ts_steps with hf | ⟨σ'', e'', hs⟩
  · exact (ts_stuck (G := G)).1 hf
  · exact (ts_stuck (G := G)).2 σ'' e'' hs

/-- A configuration reached from a well-typed closed program run on the empty stack
need not be well typed: no stack typing makes `(tsStuckσ; tsStuck)` well typed and
satisfied by its stack.  Hence restricting `Preservation` to configurations
reachable from closed programs does not make it true; the dynamics has to be
changed as well (see `Oxide.StepC`). -/
theorem ts_reachable_not_typable :
    Steps G [] tsProg tsStuckσ tsStuck ∧
    ∀ (Θ : TempTy) (Γ Γ' : StackTy) (τ : Ty),
      ¬ (HasType G {} Θ Γ tsStuck τ Γ' ∧ StoreValid G Γ tsStuckσ) := by
  refine ⟨ts_steps, fun Θ Γ Γ' τ ⟨ht, hσ⟩ => ?_⟩
  rcases progress_aux ht Γ tsStuckσ (Refines.refl Γ) hσ with hf | ⟨σ'', e'', hs⟩
  · exact (ts_stuck (G := G)).1 hf
  · exact (ts_stuck (G := G)).2 σ'' e'' hs

end Oxide
