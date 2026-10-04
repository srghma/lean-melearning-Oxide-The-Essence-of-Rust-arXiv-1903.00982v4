module

public import RequestProject.Oxide.Metatheory.Statements

/-!
# Type safety and preservation, as stated in the paper, do not hold

The paper's rules `E-Move` and `E-Copy` both apply to a place `π`: `E-Move` has
no side condition requiring the type of `π` to be non-copyable (that distinction
is only made by the typing rules `T-Move`/`T-Copy`).  In the well-typed program

  `let x : bool = true; x; if x { () } else { () }`

the first use of `x` (typed by `T-Copy`) may therefore step by `E-Move`, which
overwrites `x` with `dead`.  The second use then copies `dead`, and
`if dead { () } else { () }` is stuck (`not_type_safety`).

The stuck configuration has the dead value in focus, and the dead value has no
type; so no stack typing makes it well typed, and preservation fails too
(`not_preservation`).  Scoping plays no role in this counterexample.
-/

@[expose] public section

namespace Oxide

variable {G : GlobalEnv}

/-- `x`, the variable bound by the `let`. -/
def tsX : PlaceExpr [.var] := ⟨.here, []⟩

/-- The branch `if x { () } else { () }`. -/
def tsIte : Term [.var] := .ite (.place tsX) (.val Value.unit) (.val Value.unit)

/-- The program `let x : bool = true; x; if x { () } else { () }`. -/
def tsProg : Program := .letE Ty.bool (.val Value.tt) (.seq (.place tsX) tsIte)

/-- The stack typing `x : bool`. -/
def tsΓ : StackTy [.var] := ⟨.var (.init Ty.bool) .nil, []⟩

/-- The stack typing `x : bool†`. -/
def tsΓd : StackTy [.var] := ⟨.var (.dead Ty.bool) .nil, []⟩

theorem ts_copy_x : HasType G [] tsΓ (.place tsX) Ty.bool tsΓ := by
  refine Typing.copy [] tsΓ tsX [⟨.shrd, ⟨.here, []⟩⟩] Ty.bool [] ?_ (PlaceTy.var .here Ty.bool rfl) rfl
  refine OwnSafe.place (π := ⟨.here, []⟩) [] ?_
  intro r' L h
  simp [regionsOf, tsΓ, StackTy.rgns, StackTy.cod, SlotTys.rgnLoans, SlotTys.varTys, MTy.closureLoans,
    Ty.closureLoans, Ty.bool] at h

theorem ts_unit_drop : HasType G [] tsΓ (.val Value.unit) Ty.unit tsΓd :=
  Typing.drop [] tsΓ tsΓd tsΓd ⟨.here, []⟩ Ty.bool Ty.unit _ rfl rfl
    (Typing.val _ _ _ _ (Typing.vUnit _ _))

theorem ts_ite : HasType G [] tsΓ tsIte Ty.unit tsΓd := by
  refine Typing.ite [] tsΓ tsΓ tsΓd tsΓd tsΓd tsΓd tsΓd _ _ _ Ty.unit Ty.unit Ty.unit
    ts_copy_x ts_unit_drop ts_unit_drop (.inl rfl) (.refl _ _ _) (.refl _ _ _) ?_
  simp [tsΓd, StackTy.union, SlotTys.union]

/-- The program `let x : bool = true; x; if x { () } else { () }` is well typed. -/
theorem ts_typed : HasType G [] StackTy.empty tsProg Ty.unit StackTy.empty := by
  refine Typing.letE [] StackTy.empty StackTy.empty StackTy.empty StackTy.empty tsΓd Ty.bool Ty.bool
    Ty.unit Ty.unit _ _ (Typing.val _ _ _ _ (Typing.vBool _ _ true)) (.refl _ _ _)
    (by simp [Ty.bool, Ty.frgns]) ?_ trivial rfl rfl
  refine Typing.seq [] tsΓ tsΓ tsΓd _ _ Ty.bool Ty.unit ts_copy_x ?_
  exact ts_ite

/-- The stack of the stuck configuration: `x ↦ dead`. -/
def tsStuckσ : Stack [.var] := .var .dead .nil

/-- The stuck configuration reached by moving the copyable `x` with `E-Move`. -/
def tsStuck : Config := ⟨[.var], tsStuckσ, .val .dead, .ite (.val Value.unit) (.val Value.unit) (.popVar .halt)⟩

/-- The program reaches the stuck configuration: `E-Move` may be applied to the
copyable variable `x` (the dynamics do not distinguish moves from copies), so the
second use of `x` reads `dead`. -/
theorem ts_steps : Steps G (Config.init tsProg) tsStuck := by
  refine .step _ _ _ (Step.letPush _ _ _ _ _) ?_
  refine .step _ _ _ (Step.letE _ _ _ _ _) ?_
  refine .step _ _ _ (Step.seqPush _ _ _ _) ?_
  refine .step _ ⟨[.var], tsStuckσ, .val Value.tt, _⟩ _
    (Step.move _ _ tsX _ ⟨.here, []⟩ Value.tt (by simp [tsX]) rfl rfl rfl) ?_
  refine .step _ _ _ (Step.seq _ _ _ _) ?_
  refine .step _ _ _ (Step.itePush _ _ _ _ _) ?_
  refine .step _ _ _ (Step.copy _ tsX _ ⟨.here, []⟩ .dead rfl rfl) ?_
  exact .refl _

/-- A configuration with the dead value in focus, consumed by a conditional,
does not step. -/
theorem Step.not_dead_ite {c c' : Config} (h : Step G c c') (hf : c.focus = .val .dead)
    {e₁ e₂ : Term c.S} {κ : Cont c.S} (hk : c.cont = .ite e₁ e₂ κ) : False := by
  cases h <;> simp_all [Value.tt, Value.ff]

/-- The configuration `tsStuck` is stuck. -/
theorem ts_stuck : ¬ tsStuck.IsFinal ∧ ∀ c', ¬ Step G tsStuck c' := by
  refine ⟨?_, fun c' h => ?_⟩
  swap
  · exact Step.not_dead_ite h rfl rfl
  rintro (⟨v, -, h⟩ | ⟨s, h⟩) <;> cases h

/-- **Type safety, as stated in the paper (`TypeSafety`), is false** for every
global environment, in particular for well-formed ones such as `[]`. -/
theorem not_type_safety : ¬ TypeSafety G := by
  intro h
  rcases h tsProg Ty.unit StackTy.empty ts_typed tsStuck ts_steps with hf | ⟨c', hs⟩
  · exact (ts_stuck (G := G)).1 hf
  · exact (ts_stuck (G := G)).2 c' hs

/-- The stuck configuration is not well typed: its focus is the dead value. -/
theorem ts_stuck_untyped : ¬ ConfigTyped G tsStuck := by
  rintro ⟨Θ, Γ, τ, Γ', -, ht, -⟩
  obtain ⟨Γ₀, hv⟩ := HasType.val_inv ht
  exact hv.not_dead

/-- **Preservation (`Preservation`) is false** for every global environment: the
well-typed program `tsProg` reaches the ill-typed configuration `tsStuck`. -/
theorem not_preservation : ¬ Preservation G := fun h =>
  ts_stuck_untyped (ts_steps.preserve h (ConfigTyped.init ts_typed))

end Oxide
