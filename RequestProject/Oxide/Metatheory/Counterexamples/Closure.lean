module
public import RequestProject.Oxide.Metatheory.Counterexamples.TypeSafety

/-!
# A second counterexample to type safety: closures returning dangling pointers

This counterexample does not use `E-Move`.  In

  `letrgn<'r> { let x : bool = true;
                let p : &'r shrd bool = (|| -> &'r shrd bool { &'r shrd x })();
                if *p { () } else { () } }`

`T-Closure` checks the body in a stack typing whose top frame holds the closure's
own copy `x'` of the captured `x`; `T-Borrow` accepts `&'r shrd x'` since `'r` has
no loans and occurs in no closure signature of that stack typing, and the result
type `&'r shrd bool` is exactly the closure's return type.  At runtime the pointer
designates `x'` by its de Bruijn level; `E-Framed` pops the closure's frame, and
after `p` is pushed that level designates `p` itself.  So `*p` reads a pointer
where a boolean is expected and the `if` is stuck (`not_type_safety_closure`).

With the paper's named variables, the pointer `ptr x` would designate the outer
`x` after the pop; the failure comes from representing referents (and loans) by
de Bruijn levels.
-/

@[expose] public section

namespace Oxide

variable {G : GlobalEnv}

/-- `&r shrd bool` for the region bound by the enclosing `letrgn`. -/
def ccTyB : Ty := .ref (.bound 0) .shrd Ty.bool
/-- `&r shrd bool` once the region is opened at level `0`. -/
def ccTy : Ty := .ref (.conc 0) .shrd Ty.bool

/-- The closure `|| -> &r shrd bool { &r shrd x }` (before opening). -/
def ccCloB : Term 1 := .closure 0 [] ccTyB (.borrow (.bound 0) .shrd ⟨0, []⟩)
/-- The closure body, once the region is opened. -/
def ccBody : Term (1 + 0) := .borrow (.conc 0) .shrd ⟨0, []⟩
/-- The closure, once the region is opened. -/
def ccClo : Term 1 := .closure 0 [] ccTy ccBody

/-- `if *p { () } else { () }`. -/
def ccIte : Term 2 := .ite (.place ⟨0, [.deref]⟩) (.val Value.unit) (.val Value.unit)

/-- The program
`letrgn<r> { let x : bool = true; let p : &r shrd bool = (|| -> &r shrd bool { &r shrd x })(); if *p { () } else { () } }`. -/
def ccProg : Term 0 :=
  .letrgn (.letE Ty.bool (.val Value.tt)
    (.letE ccTyB (.app ccCloB [] [] [] .nil) ccIte))

/-- The body of `letrgn`, once the region is opened. -/
def ccBodyO : Term 0 :=
  .letE Ty.bool (.val Value.tt) (.letE ccTy (.app ccClo [] [] [] .nil) ccIte)

theorem cc_open : (Term.letE Ty.bool (.val Value.tt)
    (.letE ccTyB (.app ccCloB [] [] [] .nil) ccIte) : Term 0).openRgns [0] = ccBodyO := rfl

/-- The closure value. -/
def ccCloV : Value := .closure 1 0 0 [Value.tt] [] ccTy ccBody

/-- The final (stuck) term. -/
def ccStuck : Term 0 :=
  .shiftRgn (.shift (.shift (.ite (.val (.ptr ⟨1, []⟩)) (.val Value.unit) (.val Value.unit))))

/-- The final stack. -/
def ccStuckσ : Stack := [[.val (.ptr ⟨1, []⟩), .val Value.tt, .rgn]]

theorem cc_steps : Steps G [] ccProg ccStuckσ ccStuck := by
  refine Steps.step _ [[.rgn]] _ _ (.shiftRgn ccBodyO) _ (Step.letrgn [] _) ?_
  refine Steps.step _ [[.val Value.tt, .rgn]] _ _
    (.shiftRgn (.shift (.letE ccTy (.app ccClo [] [] [] .nil) ccIte))) _
    (Step.ctx .shiftRgn _ _ _ _ (Step.letE _ _ _ _)) ?_
  refine Steps.step _ [[.val Value.tt, .rgn]] _ _
    (.shiftRgn (.shift (.letE ccTy (.app (.val ccCloV) [] [] [] .nil) ccIte))) _
    (Step.ctx .shiftRgn _ _ _ _ (Step.ctx .shift _ _ _ _ (Step.ctx (.letE ccTy ccIte) _ _ _ _
      (Step.ctx (.appFn [] [] [] .nil) _ _ _ _
        (Step.closure _ 0 [] ccTy ccBody 1 id ccBody [Value.tt] [] rfl
          (fun i j h => by omega) (fun ⟨0, _⟩ => rfl) List.nodup_nil
          (fun r => by simp [ccBody, Term.frgns, Region.frgns, ccTy, Ty.frgns, Ty.frgnsL]; omega)
          rfl (fun ⟨0, _⟩ => rfl)))))) ?_
  refine Steps.step _ [[.val Value.tt], [.val Value.tt, .rgn]] _ _
    (.shiftRgn (.shift (.letE ccTy (.framed 1 ccBody) ccIte))) _
    (Step.ctx .shiftRgn _ _ _ _ (Step.ctx .shift _ _ _ _ (Step.ctx (.letE ccTy ccIte) _ _ _ _
      (Step.appClosure _ 1 0 0 [Value.tt] [] ccTy ccBody [] [] [] [] rfl)))) ?_
  refine Steps.step _ [[.val Value.tt], [.val Value.tt, .rgn]] _ _
    (.shiftRgn (.shift (.letE ccTy (.framed 1 (.val (.ptr ⟨1, []⟩))) ccIte))) _
    (Step.ctx .shiftRgn _ _ _ _ (Step.ctx .shift _ _ _ _ (Step.ctx (.letE ccTy ccIte) _ _ _ _
      (Step.ctx (.framed 1) _ _ _ _
        (Step.borrow _ (.conc 0) .shrd ⟨0, []⟩ ⟨1, []⟩ Value.tt rfl rfl))))) ?_
  refine Steps.step _ [[.val Value.tt, .rgn]] _ _
    (.shiftRgn (.shift (.letE ccTy (.val (.ptr ⟨1, []⟩)) ccIte))) _
    (Step.ctx .shiftRgn _ _ _ _ (Step.ctx .shift _ _ _ _ (Step.ctx (.letE ccTy ccIte) _ _ _ _
      (Step.framed _ _ 1 _)))) ?_
  refine Steps.step _ ccStuckσ _ _ (.shiftRgn (.shift (.shift ccIte))) _
    (Step.ctx .shiftRgn _ _ _ _ (Step.ctx .shift _ _ _ _ (Step.letE _ _ _ _))) ?_
  refine Steps.step _ ccStuckσ _ _ ccStuck _
    (Step.ctx .shiftRgn _ _ _ _ (Step.ctx .shift _ _ _ _ (Step.ctx .shift _ _ ccIte _
      (Step.ctx (.ite (.val Value.unit) (.val Value.unit)) _ _ _ _
        (Step.copy _ ⟨0, [.deref]⟩ ⟨1, []⟩ (.ptr ⟨1, []⟩) rfl rfl))))) ?_
  exact Steps.refl _ _


/-- The loan `shrd x'` created by the closure body, where `x'` (level `1`) is the
copy of `x` in the closure's frame. -/
def ccLoan : Loan := ⟨.shrd, ⟨1, []⟩⟩

def ccΓ1 : StackTy := [[.var Ty.bool, .rgn []]]
def ccΓb : StackTy := [[.var Ty.bool], [.var Ty.bool, .rgn []]]
def ccΓ2 : StackTy := [[.var Ty.bool, .rgn [ccLoan]]]
def ccΓ3 : StackTy := [[.var ccTy, .var Ty.bool, .rgn [ccLoan]]]
def ccΓ3d : StackTy := [[.var (.dead ccTy), .var Ty.bool, .rgn [ccLoan]]]
def ccΓ4 : StackTy := [[.var (.dead ccTy), .var (.dead Ty.bool), .rgn [ccLoan]]]

theorem cc_body_typed :
    HasType G {} [] ccΓb ccBody ccTy ([.var Ty.bool] :: ccΓ2) := by
  have := Typing.borrow (G := G) {} [] ccΓb 0 .shrd (⟨0, []⟩ : PlaceExpr (1 + 0)) ⟨1, []⟩
    [ccLoan] Ty.bool [] rfl rfl ?_ ?_ (PlaceTy.var 1 Ty.bool rfl (.base _)) (.inl (.base _))
  · exact this
  · intro s hs
    simp [closureSigRgns, ccΓb, StackTy.cod, StackTy.allVarTys, FrameTy.varTys, Ty.fnTypes,
      Ty.bool] at hs
  · refine OwnSafe.place (π := ⟨1, []⟩) [] ?_
    intro r' L h
    left
    simp [regionsOf, ccΓb, StackTy.rgns, StackTy.allLoans, StackTy.cod, StackTy.allVarTys,
      FrameTy.rgnLoans, FrameTy.varTys, Ty.closureFrames, Ty.bool, Ty.fnTypes] at h
    obtain ⟨-, rfl⟩ := h
    simp

theorem cc_clo_typed :
    HasType G {} [] ccΓ1 ccClo (Ty.closure [] ccTy (.frame [.var Ty.bool])) ccΓ2 := by
  refine Typing.closure {} [] ccΓ1 0 [] ccTy ccBody 1 id ccBody [(0, Ty.bool)] []
    [.var Ty.bool] [.var Ty.bool] ccΓ2 rfl (by simp) (.ref _ _ _ (.base _)) rfl
    (fun i j h => by omega) (fun ⟨0, _⟩ => rfl) rfl (fun ⟨0, _⟩ => ⟨0, Ty.bool, rfl, rfl, rfl⟩)
    List.nodup_nil
    (fun r => by simp [ccBody, Term.frgns, Region.frgns, ccTy, Ty.frgns, Ty.frgnsL]; omega)
    (by simp) rfl ?_ ?_
  · intro r hr
    simp [ccTy, Ty.frgns, Ty.frgnsL, Ty.bool] at hr
    subst hr
    rfl
  · have h1 : (FrameTy.openAt ccΓ1.numRgns (List.map FrameEntry.var ([] : List Ty).reverse ++
        [FrameEntry.var Ty.bool]) :: killNC ccΓ1 [(0, Ty.bool)]) = ccΓb := by
      simp [FrameTy.openAt, killNC, Ty.noncopyable, Ty.bool, ccΓ1, ccΓb, Ty.openRgns, Ty.map]
    have h2 : Term.openRgns (newLevels ccΓ1.numRgns ([] : List Nat).length) ccBody = ccBody := rfl
    rw [h1, h2]
    exact cc_body_typed

theorem cc_safe (excl : List APlace) (target : APlaceExpr) :
    SafeCond [] ccΓ3 .shrd excl target := by
  intro r' L h
  left
  simp [regionsOf, ccΓ3, StackTy.rgns, StackTy.allLoans, StackTy.cod, StackTy.allVarTys,
    FrameTy.rgnLoans, FrameTy.varTys, Ty.closureFrames, Ty.bool, Ty.fnTypes, ccTy] at h
  obtain ⟨-, rfl⟩ := h
  simp [ccLoan]

theorem cc_deref_typed : HasType G {} [] ccΓ3 (.place ⟨0, [.deref]⟩ : Term 2) Ty.bool ccΓ3 := by
  refine Typing.copy {} [] ccΓ3 ⟨0, [.deref]⟩ (APlaceExpr.plug [] (APlace.derefExpr ⟨1, []⟩))
    ([[⟨.shrd, ⟨1, []⟩⟩]].flatten ++ [⟨.shrd, APlaceExpr.plug [] (APlace.derefExpr ⟨1, []⟩)⟩])
    Ty.bool [.conc 0] rfl ?_ ?_ (.base _) (by simp [Ty.copyable, Ty.noncopyable, Ty.bool])
  · refine OwnSafe.deref [] ⟨1, []⟩ [] 0 .shrd Ty.bool [ccLoan] [[⟨.shrd, ⟨1, []⟩⟩]] rfl rfl
      (.refl _) rfl ?_ (cc_safe _ _)
    intro lo hlo
    simp at hlo
    subst hlo
    exact OwnSafe.place (π := ⟨1, []⟩) _ (cc_safe _ _)
  · exact PlaceTy.deref ⟨1, []⟩ (.conc 0) .shrd Ty.bool [] (PlaceTy.var 1 ccTy rfl
      (.ref _ _ _ (.base _))) (.refl _)

theorem cc_unit_typed : HasType G {} [] ccΓ3 (n := 2) (.val Value.unit) Ty.unit ccΓ4 :=
  Typing.drop {} [] ccΓ3 ccΓ3d ccΓ4 ⟨1, []⟩ ccTy Ty.unit _ rfl (.ref _ _ _ (.base _)) rfl
    (Typing.drop {} [] ccΓ3d ccΓ4 ccΓ4 ⟨0, []⟩ Ty.bool Ty.unit _ rfl (.base _) rfl
      (Typing.val _ _ _ _ _ (Typing.vUnit _ _ _)))

theorem cc_ite_typed : HasType G {} [] ccΓ3 ccIte Ty.unit ccΓ4 := by
  refine Typing.ite {} [] ccΓ3 ccΓ3 ccΓ4 ccΓ4 ccΓ4 ccΓ4 ccΓ4 _ _ _ Ty.unit Ty.unit Ty.unit
    cc_deref_typed cc_unit_typed cc_unit_typed (.inl rfl) (.base _) (.base _) (.base _)
    (.refl _ _ _) (.refl _ _ _) ?_
  simp [ccΓ4, StackTy.union, FrameTy.union]


theorem cc_stuck : ¬ ccStuck.IsFinal ∧ ∀ σ'' e'', ¬ Step G ccStuckσ ccStuck σ'' e'' :=
  stuck_of_stuckB rfl

theorem cc_inner_typed : HasType G {} [] ccΓ1
    (.letE ccTy (.app ccClo [] [] [] .nil) ccIte) Ty.unit [[.var (.dead Ty.bool), .rgn [ccLoan]]] := by
  refine Typing.letE {} [] ccΓ1 ccΓ2 ccΓ2 [.var (.dead Ty.bool), .rgn [ccLoan]] [] ccTy ccTy
    Ty.unit (.dead ccTy) _ _ ?_ (.ref _ _ _ (.base _)) (.ref _ _ _ (.base _)) (.refl _ _ _) ?_ ?_
    (.base _) (.dead _ (.ref _ _ _ (.base _)))
  · exact Typing.appClosure {} [] ccΓ1 ccΓ2 ccΓ2 ccClo .nil [] ccTy _ cc_clo_typed
      (Typing.argsRwNil _ _ _) (by simp)
  · intro r hr π ω τ hmem
    simp [ccΓ2, StackTy.explode, StackTy.allVarTys, FrameTy.varTys, Ty.explode, Ty.bool] at hmem
  · have h : gcLoans [] (ccΓ2.push (.var ccTy)) = ccΓ3 := by
      simp [gcLoans, ccΓ2, ccΓ3, StackTy.push, StackTy.mapLoans, StackTy.mapLoans.go,
        StackTy.cod, StackTy.allVarTys, FrameTy.varTys, ccTy, Ty.frgns, Ty.bool, StackTy.numRgns,
        FrameTy.numRgns]
    rw [h]
    exact cc_ite_typed

/-- The program `ccProg` is well typed. -/
theorem cc_typed : HasType G {} [] [] ccProg Ty.unit [[]] := by
  refine Typing.letrgn {} [] [] [] [] [ccLoan] _ Ty.unit ?_ (.base _) (by simp [Ty.unit, Ty.frgns])
  have h0 : StackTy.numRgns [] = 0 := rfl
  rw [h0, cc_open]
  refine Typing.letE {} [] [[.rgn []]] [[.rgn []]] [[.rgn []]] [.rgn [ccLoan]] [] Ty.bool Ty.bool
    Ty.unit (.dead Ty.bool) _ _ (Typing.val _ _ _ _ _ (Typing.vBool _ _ _ true)) (.base _) (.base _)
    (.refl _ _ _) (by simp [Ty.bool, Ty.frgns]) ?_ (.base _) (.dead _ (.base _))
  have h : gcLoans [] (StackTy.push [[.rgn []]] (.var Ty.bool)) = ccΓ1 := by
    simp [gcLoans, ccΓ1, StackTy.push, StackTy.mapLoans, StackTy.mapLoans.go]
  rw [h]
  exact cc_inner_typed

/-- **Closures can return dangling pointers.**  Type safety (`TypeSafety`) fails even
without using `E-Move`: the closure body borrows its own copy of the captured
variable `x` into the enclosing region `r`.  With de Bruijn levels, the resulting
pointer designates a slot of the closure's frame, which `E-Framed` pops; after `p`
is pushed, the dangling pointer designates `p` itself, so `*p` reads a pointer where
a boolean is expected. -/
theorem not_type_safety_closure : ¬ TypeSafety G := by
  intro h
  rcases h ccProg Ty.unit [[]] cc_typed ccStuckσ ccStuck cc_steps with hf | ⟨σ'', e'', hs⟩
  · exact (cc_stuck (G := G)).1 hf
  · exact (cc_stuck (G := G)).2 σ'' e'' hs

end Oxide
