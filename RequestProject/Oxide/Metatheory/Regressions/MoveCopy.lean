module

public import RequestProject.Oxide.Metatheory.Statements

/-!
# Regression: moves and copies are distinguished by the syntax

In the paper (and in the previous version of this formalization) `E-Move` and
`E-Copy` both applied to a place: `E-Move` had no side condition requiring the
place to be non-copyable, a distinction only made by the typing rules
`T-Move`/`T-Copy`.  In the well-typed program

  `let x : bool = true; x; if x { () } else { () }`

the first use of `x` (typed by `T-Copy`) could therefore step by `E-Move`, which
overwrote `x` with `dead`, and the program got stuck on `if dead { … }`.  That
refuted type safety and preservation.

Now every use of a place says whether it moves or copies (`Atom.move`,
`Atom.copy`, as `Operand::Move`/`Operand::Copy` in Rust's MIR), `T-Copy` requires a
copyable type, and `E-Move` only applies to `move`.  The program is written

  `let x : bool = true; copy x; if copy x { () } else { () }`

It is still well typed (`ts_typed`), a `copy` step never changes the stack
(`Step.copy_inv`), and the program runs to its final value (`ts_runs`).
-/

@[expose] public section

namespace Oxide

variable {sig : Sig}

/-- `x`, the variable bound by the `let`. -/
def tsX : PExpr [.var] := .place ⟨.here, []⟩

/-- The branch `if copy x { () } else { () }`. -/
def tsIte : Comp sig [.var] := .ite (.copy tsX) (.val Value.unit) (.val Value.unit)

/-- The program `let x : bool = true; copy x; if copy x { () } else { () }` (already
in A-normal form). -/
def tsProg : Program sig := .letE Ty.bool (.atom (.val Value.tt)) (.seq (.atom (.copy tsX)) (.ret tsIte))

/-- The stack typing `x : bool`. -/
def tsΓ : StackTy [.var] := ⟨.var (.init Ty.bool) .nil, []⟩

/-- The stack typing `x : bool†`. -/
def tsΓd : StackTy [.var] := ⟨.var (.dead Ty.bool) .nil, []⟩

theorem ts_copy_x : HasTypeA sig [] tsΓ (.copy tsX) Ty.bool tsΓ := by
  refine Typing.copy [] tsΓ tsX [⟨.shrd, .place ⟨.here, []⟩⟩] Ty.bool [] ?_
    (PlaceTy.place ⟨.here, []⟩ Ty.bool rfl) rfl
  refine OwnSafe.place (π := ⟨.here, []⟩) [] ?_
  intro r' L h
  simp [regionsOf, tsΓ, StackTy.rgns, StackTy.cod, SlotTys.rgnLoans, SlotTys.varTys, MTy.closureLoans,
    Ty.closureLoans, Ty.bool, MTy.init] at h

theorem ts_unit_drop : HasType sig [] tsΓ (.val Value.unit) Ty.unit tsΓd :=
  Typing.ret _ _ _ _ _ <| Typing.drop [] tsΓ tsΓd tsΓd ⟨.here, []⟩ Ty.bool Ty.unit _ rfl rfl
    (Typing.atom _ _ _ _ _ (Typing.val _ _ _ _ (Typing.vPrim _ _ .unit)))

theorem ts_ite : HasTypeC sig [] tsΓ tsIte Ty.unit tsΓd := by
  refine Typing.ite [] tsΓ tsΓ tsΓd tsΓd tsΓd tsΓd tsΓd _ _ _ Ty.unit Ty.unit Ty.unit
    ts_copy_x ts_unit_drop ts_unit_drop (.inl rfl) (.refl _ _ _) (.refl _ _ _) ?_
  simp [tsΓd, StackTy.union, SlotTys.union]

/-- The program `let x : bool = true; copy x; if copy x { () } else { () }` is well
typed. -/
theorem ts_typed : HasType sig [] StackTy.empty tsProg Ty.unit StackTy.empty := by
  refine Typing.letE [] StackTy.empty StackTy.empty StackTy.empty StackTy.empty tsΓd Ty.bool Ty.bool
    Ty.unit Ty.unit _ _ (Typing.atom _ _ _ _ _ (Typing.val _ _ _ _ (Typing.vPrim _ _ (.bool true))))
    (.refl _ _ _) (by simp [Ty.bool, Ty.frgns]) ?_ rfl rfl rfl
  exact Typing.seq [] tsΓ tsΓ tsΓd _ _ Ty.bool Ty.unit (Typing.atom _ _ _ _ _ ts_copy_x)
    (Typing.ret _ _ _ _ _ ts_ite)

/-- Evaluating a `copy` atom never changes the stack: it only reads. -/
theorem EvalAtom.copy_inv {S : Ctx} {σ σ' : Stack sig S} {p : PExpr S} {v : Value sig S}
    (h : EvalAtom σ (.copy p) v σ') : σ' = σ := by
  cases h
  rfl

/-- A `copy` step never changes the stack: it only reads. -/
theorem Step.copy_inv {G : GlobalEnv sig} {S : Ctx} {σ : Stack sig S} {p : PExpr S} {κ : Cont sig S}
    {c' : Config sig} (h : Step G ⟨S, σ, .ret (.atom (.copy p)), κ⟩ c') :
    ∃ v, c' = ⟨S, σ, .val v, κ⟩ := by
  cases h
  exact ⟨_, rfl⟩

/-- The program runs to its final value `()`. -/
theorem ts_runs (G : GlobalEnv sig) :
    Steps G (Config.init tsProg) ⟨[], .nil, .val Value.unit, .halt⟩ := by
  refine .step _ _ _ (Step.letPush _ _ _ _ _) ?_
  refine .step _ _ _ (Step.letE _ _ _ _ _) ?_
  refine .step _ _ _ (Step.seqPush _ _ _ _) ?_
  refine .step _ _ _ (Step.copy _ tsX _ (.place ⟨.here, []⟩) Value.tt rfl rfl) ?_
  refine .step _ _ _ (Step.seq _ _ _ _) ?_
  refine .step _ _ _ (Step.iteTrue _ _ _ _ _ _ (EvalAtom.copy _ tsX (.place ⟨.here, []⟩) _ rfl rfl)) ?_
  refine .step _ _ _ (Step.popVar _ _ Value.unit _ rfl) ?_
  exact .refl _

theorem ts_final : (⟨[], .nil, .val Value.unit, .halt⟩ : Config sig).IsFinal := .inl ⟨_, rfl, rfl⟩

end Oxide
