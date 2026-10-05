module

public import RequestProject.Oxide.Metatheory.Regressions.ClosureScopes

/-!
# Regression: a closure may not capture the same variable twice

A closure term lists the variables of the current frame that it copies into its
captured frame (`Cap`).  Nothing in the syntax prevents the list from naming the
same variable twice.  Before the fix, `T-Closure` then gave *both* copies the type
of that variable, even when it is not copyable, and `killNC` killed the original
only once.

Concretely, with a global function

  `fn dup<ϱ>(y : &ϱ uniq u32) -> () { let f : τ_f = || -> () { body }; f() }`

whose closure captures `y` twice, as `c₁` and `c₂` (`dcCap`), the body

  `letrgn<r₁> { letrgn<r₂> {`
  `  let a : &r₁ uniq u32 = &r₁ uniq *c₁;`
  `  let b : &r₂ uniq u32 = &r₂ uniq *c₂;`
  `  *b := 2; *a := 1; () } }`

holds two *simultaneously live* unique borrows `a` and `b` of the same location
`*y`, and `b` is written while `a` is still used afterwards: exactly what the
borrow checker must reject.  It type checks (`dcBody_typed`): the loan
`uniq *c₁` of `r₁` and the place `*c₂` have different roots, so ownership safety
sees them as disjoint.  At runtime both slots hold the pointer stored in `y`
(`dc_env_aliases`).  Before the fix the closure term was well typed: every premise
of `T-Closure` other than the one the fix adds holds (`dc_closure_other_premises`).

**Fix.** `T-Closure` now requires the capture list to be duplicate-free
(`Cap.Nodup`).  `dcCap` is not (`dcCap_not_nodup`), so the closure term is not
well typed in any stack typing (`dc_closure_untyped`), the function is not well
formed (`dc_fn_not_wf`), and neither is a global environment containing it
(`dcG_not_wf`).  The `[OXIDE| … ]` syntax always produced duplicate-free capture
lists.
-/

@[expose] public section

namespace Oxide

variable {sig : Sig}

/-- `&ϱ uniq u32` in the signature scope `[ϱ]`. -/
def dcRefTy : Ty [.abs] := .ref (.abs .here) .uniq (.sized Ty.u32)

/-- The signature `fn dup<ϱ>(y : &ϱ uniq u32) -> ()`. -/
def dcSig : FnSig where
  name := "dup"
  binders := { nϱ := 1 }
  k := 1
  params := fun _ => dcRefTy
  ret := Ty.unit
  bounds := []

/-- The capture list `[y, y]`: the parameter `y` is captured twice. -/
def dcCap : Cap dcSig.bodyCtx [.var, .var] := .var .here (.var .here .nil)

/-- `*x` for a variable `x`. -/
def dcDeref {Γ : Ctx} (x : TVar Γ) : PExpr Γ := .deref (.place ⟨x, []⟩) []

/-- The closure body in its own scope `[c₁, c₂, ‡]`:
`letrgn<r₁> { letrgn<r₂> { let a : &r₁ uniq u32 = &r₁ uniq *c₁;
  let b : &r₂ uniq u32 = &r₂ uniq *c₂; *b := 2; *a := 1; () } }`. -/
def dcBody : Term sig (vars 0 ++ ([.var, .var] ++ .frame :: [])) :=
  .ret <| .letrgn <| .ret <| .letrgn <|
    .letE (.ref (.conc (.there .here)) .uniq (.sized Ty.u32))
      (.borrow (.there .here) .uniq (dcDeref (.skipRgn (.skipRgn .here)))) <|
    .letE (.ref (.conc (.there .here)) .uniq (.sized Ty.u32))
      (.borrow (.there .here) .uniq (dcDeref (.skipVar (.skipRgn (.skipRgn (.skipVar .here)))))) <|
    .seq (.assign (dcDeref .here) (.val (Value.num 2))) <|
    .seq (.assign (dcDeref (.skipVar .here)) (.val (Value.num 1))) <|
    .val Value.unit

/-- The closure `|| -> () { … }` capturing `y` twice. -/
def dcClosure : Comp sig dcSig.bodyCtx := .closure [.var, .var] dcCap [] .nil 0 noTys Ty.unit dcBody

/-- The opened closure body, in scope `[c₁, c₂, ‡, y, ‡, ϱ]`. -/
def dcBodyOpen : Term sig (vars 0 ++ ([.var, .var] ++ .frame :: dcSig.bodyCtx)) :=
  .ret <| .letrgn <| .ret <| .letrgn <|
    .letE (.ref (.conc (.there .here)) .uniq (.sized Ty.u32))
      (.borrow (.there .here) .uniq (dcDeref (.skipRgn (.skipRgn .here)))) <|
    .letE (.ref (.conc (.there .here)) .uniq (.sized Ty.u32))
      (.borrow (.there .here) .uniq (dcDeref (.skipVar (.skipRgn (.skipRgn (.skipVar .here)))))) <|
    .seq (.assign (dcDeref .here) (.val (Value.num 2))) <|
    .seq (.assign (dcDeref (.skipVar .here)) (.val (Value.num 1))) <|
    .val Value.unit

/-- Opening the body (with no outer binders) only re-indexes it. -/
theorem dcBody_open :
    (dcBody (sig := sig)).openBody (Inst.nil : Inst [] dcSig.bodyCtx).toTSub = dcBodyOpen := rfl

/-- The scope of the opened closure body: `[c₁, c₂, ‡, y, ‡, ϱ]`. -/
abbrev dcB : Ctx := vars 0 ++ ([.var, .var] ++ .frame :: dcSig.bodyCtx)

/-- `ϱ` in the scope of the opened closure body. -/
def dcϱ : In .abs dcB := .there (.there (.there (.there (.there .here))))

/-- `&ϱ uniq u32` in the scope of the opened closure body. -/
def dcRefB : Ty dcB := .ref (.abs dcϱ) .uniq (.sized Ty.u32)

/-- The body of `dup` in A-normal form: create the closure, bind it to `f`, and call
it: `let f : (() →^Φ ()) = || -> () { … }; f()`, where the captured frame `Φ` gives
both copies the type `&ϱ uniq u32`. -/
def dcFnBody : Term sig dcSig.bodyCtx :=
  .letE (Ty.closure 0 noTys Ty.unit (.frame [.var, .var] (.var dcRefB (.var dcRefB .nil)))) dcClosure
    (.ret (.app (.move ⟨.here, []⟩) {} .none 0 (fun i => i.elim0)))

/-- The stack typing in which the closure body starts:
`c₁ : &ϱ uniq u32, c₂ : &ϱ uniq u32, ‡, y : (&ϱ uniq u32)†, ‡, ϱ`. -/
def dcΓ0 : StackTy dcB :=
  ⟨.var (.init dcRefB) (.var (.init dcRefB) (.frame (.var (.dead dcRefB) (.frame (.abs .nil))))), []⟩

/-- `dcΓ0` is the stack typing that `T-Closure` gives the body: both captured copies
`c₁`, `c₂` get the type `&ϱ uniq u32` of `y`, and `y` itself is killed once. -/
theorem dcΓ0_eq : closureBodyTy (killNC dcSig.bodyTy dcCap)
    (.var (Ty.rename dcCap.inv (dcSig.bodyTy.varTy TVar.here.toIn).ty)
      (.var (Ty.rename dcCap.inv (dcSig.bodyTy.varTy TVar.here.toIn).ty) .nil))
    (Inst.nil.tys noTys) = dcΓ0 := by
  rfl

/-! ### Decision helpers for the side conditions of the derivation -/

instance dcDisjointDec {S : Ctx} (p₁ p₂ : APExpr S) : Decidable (p₁.Disjoint p₂) := by
  unfold APExpr.Disjoint APlace.Disjoint APlace.IsPrefix; infer_instance

/-- `τ` is a reference with concrete region `r`. -/
def dcRefTo {S : Ctx} (r : In .rgn S) : Ty S → Bool
  | .ref (.conc r') _ _ => decide (r' = r)
  | _ => false

/-- A checkable sufficient condition for `SafeCond`. -/
def dcSafeB {S : Ctx} (Θ : TempTy S) (Γ : StackTy S) (ω : Own) (excl : List (APlace S))
    (target : APExpr S) : Bool :=
  (regionsOf Γ Θ).all fun p =>
    decide (∀ l ∈ p.2, (ω = .uniq ∨ l.own = .uniq) → l.pe.Disjoint target) ||
    p.1.any fun r => (Γ.explode.any fun q => dcRefTo r q.2) && decide (∀ τ ∈ Θ, r ∉ τ.frgns) &&
      (Γ.explode.all fun q => !dcRefTo r q.2 || decide (q.1 ∈ excl))

theorem dc_safeCond {S : Ctx} {Θ : TempTy S} {Γ : StackTy S} {ω : Own} {excl : List (APlace S)}
    {target : APExpr S} (h : dcSafeB Θ Γ ω excl target = true) : SafeCond Θ Γ ω excl target := by
  intro r' L hm
  have := List.all_eq_true.mp h _ hm
  simp only [Bool.or_eq_true, decide_eq_true_eq] at this
  rcases this with h1 | h2
  · exact .inl h1
  · right
    cases r' with
    | none => simp at h2
    | some r =>
      simp only [Option.any_some, Bool.and_eq_true, List.any_eq_true, decide_eq_true_eq,
        List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h2
      obtain ⟨⟨⟨q, hq, hr⟩, hΘ⟩, hall⟩ := h2
      refine ⟨r, rfl, ?_, hΘ, ?_⟩
      · obtain ⟨π', τ'⟩ := q
        cases τ' with
        | ref ρ ω' τ'' =>
          cases ρ with
          | conc r'' =>
            simp [dcRefTo] at hr
            subst hr
            exact ⟨π', ω', τ'', hq⟩
          | _ => simp [dcRefTo] at hr
        | _ => simp [dcRefTo] at hr
      · intro π' ω' τ' hm'
        rcases hall _ hm' with h | h
        · simp [dcRefTo] at h
        · exact h

/-- A checkable sufficient condition for `NotReborrowed`. -/
def dcNotReborrowedB {S : Ctx} (Γ : StackTy S) (r : In .rgn S) : Bool :=
  Γ.explode.all fun q => !dcRefTo r q.2 ||
    Γ.rgns.all fun p => decide ((⟨.shrd, q.1.derefExpr⟩ : Loan S) ∉ p.2 ∧
      (⟨.uniq, q.1.derefExpr⟩ : Loan S) ∉ p.2)

theorem dc_notReborrowed {S : Ctx} {Γ : StackTy S} {r : In .rgn S}
    (h : dcNotReborrowedB Γ r = true) : NotReborrowed Γ r := by
  intro π ω τ hm ⟨r', L, hrL, hl⟩
  have := List.all_eq_true.mp h _ hm
  simp only [dcRefTo, decide_true, Bool.not_true, Bool.false_or, List.all_eq_true,
    decide_eq_true_eq] at this
  have := this _ hrL
  cases ω
  · exact this.1 hl
  · exact this.2 hl

theorem dc_notInClosure {S : Ctx} {Θ : TempTy S} {Γ : StackTy S} {r : In .rgn S}
    (h : (closureSigRgns Θ Γ).all (fun s => !s.contains r) = true) : NotInClosure Θ Γ r := by
  intro s hs hr
  have := List.all_eq_true.mp h _ hs
  simp_all

/-! ### Typing `*x` -/

theorem dc_placeTy_deref {S : Ctx} {Γ : StackTy S} (x : TVar S) (ρ : Region S) (τ : Ty S)
    (ω ω' : Own) (hle : Own.Le ω ω') (hπ : Γ.placeTyI ⟨x.toIn, []⟩ = some (.ref ρ ω' (.sized τ))) :
    PlaceTy Γ ω (dcDeref x).toAbs (.sized τ) [ρ] :=
  PlaceTy.deref _ [] _ _ _ _ [] (PlaceTy.place _ _ hπ) hle rfl

/-- `*x` through a reference with an abstract region (`O-DerefAbs`). -/
theorem dc_ownSafe_derefAbs {S : Ctx} {Θ : TempTy S} {Γ : StackTy S} (excl : List (APlace S))
    (x : TVar S) (ϱ : In .abs S) (τ : Ty S) (ω : Own)
    (hπ : Γ.placeTyI ⟨x.toIn, []⟩ = some (.ref (.abs ϱ) ω (.sized τ)))
    (hsafe : dcSafeB Θ Γ ω (excl ++ [⟨x.toIn, []⟩]) (dcDeref x).toAbs = true) :
    OwnSafe Θ Γ ω excl (dcDeref x).toAbs [⟨ω, (dcDeref x).toAbs⟩] :=
  OwnSafe.derefAbs excl ⟨x.toIn, []⟩ {} ϱ ω (.sized τ) (.sized τ) [.abs ϱ] hπ
    (dc_placeTy_deref x (.abs ϱ) τ ω ω (.refl _) hπ) (.refl _) (dc_safeCond hsafe)

/-- `O-DerefAbs` for a place expression that is (definitionally) `*x`. -/
theorem dc_ownSafe_derefAbs' {S : Ctx} {Θ : TempTy S} {Γ : StackTy S} (excl : List (APlace S))
    (x : TVar S) (ϱ : In .abs S) (τ : Ty S) (ω : Own) (p : APExpr S) (hp : (dcDeref x).toAbs = p)
    (hπ : Γ.placeTyI ⟨x.toIn, []⟩ = some (.ref (.abs ϱ) ω (.sized τ)))
    (hsafe : dcSafeB Θ Γ ω (excl ++ [⟨x.toIn, []⟩]) (dcDeref x).toAbs = true) :
    OwnSafe Θ Γ ω excl p [⟨ω, p⟩] :=
  hp ▸ dc_ownSafe_derefAbs excl x ϱ τ ω hπ hsafe

/-- `*x` through a reference with a concrete region holding a single loan (`O-Deref`). -/
theorem dc_ownSafe_derefConc {S : Ctx} {Θ : TempTy S} {Γ : StackTy S}
    (x : TVar S) (r : In .rgn S) (τ : Ty S) (ω : Own) (l : Loan S) (L₁ : List (Loan S))
    (hπ : Γ.placeTyI ⟨x.toIn, []⟩ = some (.ref (.conc r) ω (.sized τ)))
    (hl : Γ.loans r = [l])
    (hrec : OwnSafe Θ Γ ω (exclOf [l] ++ [⟨x.toIn, []⟩]) l.pe L₁)
    (hsafe : dcSafeB Θ Γ ω (exclOf [l] ++ [⟨x.toIn, []⟩]) (dcDeref x).toAbs = true) :
    OwnSafe Θ Γ ω [] (dcDeref x).toAbs (L₁ ++ [⟨ω, (dcDeref x).toAbs⟩]) := by
  have h := OwnSafe.deref (Θ := Θ) (Γ := Γ) (ω := ω) [] ⟨x.toIn, []⟩ {} r ω (.sized τ) [L₁] hπ
    (.refl _) (by simp [hl]) (by
      rw [hl]
      intro lo hlo
      simp at hlo
      subst hlo
      cases l with
      | mk o pe =>
        cases pe <;> simpa [APExpr.plug, APExpr.append, APlace.append] using hrec)
    (by rw [hl]; exact dc_safeCond (by simpa using hsafe))
  simpa using h

/-- **The aliasing body type checks.**  In the stack typing `dcΓ0` (two copies of the
unique reference `y`), the body that takes the unique borrows `a = &r₁ uniq *c₁` and
`b = &r₂ uniq *c₂` of the same location, writes through `b` and then through `a`,
is well typed. -/
theorem dcBody_typed : HasType sig [] dcΓ0 dcBodyOpen Ty.unit dcΓ0 := by
  refine' Typing.ret (h := ?r1)
  case r1 =>
  refine' Typing.letrgn (τ₁ := Ty.unit) (τ := Ty.unit) (h := ?h1) (hpop := ?hpop1) (hτ := ?hτ1)
  case h1 =>
    refine' Typing.ret (h := ?r2)
    case r2 =>
    refine' Typing.letrgn (τ₁ := Ty.unit) (τ := Ty.unit) (h := ?h2) (hpop := ?hpop2) (hτ := ?hτ2)
    case h2 =>
      refine' Typing.letE (τa := _) (τ₁ := _)
        (τ₂ := Ty.unit) (τ := Ty.unit) (h₁ := ?ha) (hr := ?hra) (hnrb := ?hnrba)
        (h₂ := ?hbodya) (hdead := ?hdeada) (hpop := ?hpopa) (hτ := ?hτa)
      case ha =>
        refine' Typing.borrow (hr := ?hr) (hnic := ?hnic) (hsafe := ?hsafe) (htc := ?htc)
        case hr => rfl
        case htc => exact dc_placeTy_deref _ (.abs dcϱ.there.there) Ty.u32 .uniq .uniq (.refl _) rfl
        case hnic => exact dc_notInClosure rfl
        case hsafe =>
          exact dc_ownSafe_derefAbs [] _ dcϱ.there.there Ty.u32 .uniq rfl rfl
      case hra => exact .refl _ _ _
      case hnrba => intro r _; exact dc_notReborrowed rfl
      case hbodya =>
        refine' Typing.letE (τa := _) (τ₁ := _)
          (τ₂ := Ty.unit) (τ := Ty.unit) (h₁ := ?hb) (hr := ?hrb) (hnrb := ?hnrbb)
          (h₂ := ?hbodyb) (hdead := ?hdeadb) (hpop := ?hpopb) (hτ := ?hτb)
        case hb =>
          refine' Typing.borrow (hr := ?hr) (hnic := ?hnic) (hsafe := ?hsafe) (htc := ?htc)
          case hr => rfl
          case htc => exact dc_placeTy_deref _ (.abs dcϱ.there.there.there) Ty.u32 .uniq .uniq (.refl _) rfl
          case hnic => exact dc_notInClosure rfl
          case hsafe =>
            exact dc_ownSafe_derefAbs [] _ dcϱ.there.there.there Ty.u32 .uniq rfl rfl
        case hrb => exact .refl _ _ _
        case hnrbb =>
          intro r hr
          simp [Ty.frgns, Region.frgns, XTy.frgns, Ty.u32] at hr
          subst hr
          exact dc_notReborrowed rfl
        case hbodyb =>
          refine' Typing.seq (h₁ := ?s1) (h₂ := ?s2)
          case s1 =>
            refine' Typing.assignDeref (ha := ?he) (htc := ?htc) (hr := ?hr) (hsafe := ?hsafe)
            case he => exact Typing.val _ _ _ _ (Typing.vPrim _ _ _)
            case htc => exact dc_placeTy_deref _ (.conc (.there (.there .here))) Ty.u32 .uniq .uniq (.refl _) rfl
            case hr => exact .refl _ _ _
            case hsafe =>
              exact dc_ownSafe_derefConc _ _ Ty.u32 .uniq _ _ rfl rfl
                (dc_ownSafe_derefAbs' _ (.skipVar (.skipVar (.skipRgn (.skipRgn (.skipVar .here)))))
                  dcϱ.there.there.there.there Ty.u32 .uniq _ rfl rfl rfl) rfl
          case s2 =>
            refine' Typing.seq (h₁ := ?s3) (h₂ := ?s4)
            case s3 =>
              refine' Typing.assignDeref (ha := ?he) (htc := ?htc) (hr := ?hr) (hsafe := ?hsafe)
              case he => exact Typing.val _ _ _ _ (Typing.vPrim _ _ _)
              case htc =>
                exact dc_placeTy_deref _ (.conc (.there (.there (.there .here)))) Ty.u32 .uniq .uniq
                  (.refl _) rfl
              case hr => exact .refl _ _ _
              case hsafe =>
                exact dc_ownSafe_derefConc _ _ Ty.u32 .uniq _ _ rfl rfl
                  (dc_ownSafe_derefAbs' _ (.skipVar (.skipVar (.skipRgn (.skipRgn .here))))
                    dcϱ.there.there.there.there Ty.u32 .uniq _ rfl rfl rfl) rfl
            case s4 =>
              refine' Typing.ret (h := ?r3)
              case r3 =>
              refine' Typing.drop (π := ⟨.here, []⟩) (hπ := ?d1) (hd := ?d2) (h := ?d3)
              case d1 => rfl
              case d2 => rfl
              case d3 =>
                refine' Typing.drop (π := ⟨.there .here, []⟩) (hπ := ?d1) (hd := ?d2) (h := ?d3)
                case d1 => rfl
                case d2 => rfl
                case d3 => exact Typing.atom _ _ _ _ _ (Typing.val _ _ _ _ (Typing.vPrim _ _ _))
        all_goals try rfl
      all_goals try rfl
    all_goals try rfl
  all_goals try rfl

/-- The capture list `[y, y]` is not duplicate-free. -/
theorem dcCap_not_nodup : ¬ dcCap.Nodup := by
  simp [dcCap, Cap.Nodup, Cap.vars]

/-- The (empty) outer binders of the closure. -/
abbrev dcθ : Inst [] dcSig.bodyCtx := .nil

/-- Every premise of `T-Closure` other than the new `Cap.Nodup` holds for the
closure that captures `y` twice (with the stack typing of the body of `dup`): before
the fix, the closure was well typed, with the aliasing body `dcBody`. -/
theorem dc_closure_other_premises :
    ∃ (Φc : FrameTy ([.var, .var] ++ .frame :: dcSig.bodyCtx) [.var, .var])
      (Γ' : StackTy dcSig.bodyCtx),
      capturedFrame dcSig.bodyTy dcCap = some Φc ∧
      (∀ r ∈ dcCap.rgns,
        r ∉ (List.ofFn (dcθ.tys noTys)).flatMap Ty.frgns ++ (dcθ.ty Ty.unit).frgns) ∧
      (∀ r ∈ (List.ofFn (dcθ.tys noTys)).flatMap Ty.frgns ++ (dcθ.ty Ty.unit).frgns,
        dcSig.bodyTy.loans r = []) ∧
      dcθ.Covered (dcθ.closureTy noTys Ty.unit (.frame [.var, .var] Φc)) ∧
      HasType sig (TempTy.rename (TRen.frameRen 0 [.var, .var] dcSig.bodyCtx) [])
        (closureBodyTy (killNC dcSig.bodyTy dcCap) Φc (dcθ.tys noTys))
        (dcBody.openBody dcθ.toTSub) ((dcθ.ty Ty.unit).rename (TRen.frameRen 0 [.var, .var] dcSig.bodyCtx))
        dcΓ0 ∧
      (gcLoans (TempTy.rename (TRen.frameRen 0 [.var, .var] dcSig.bodyCtx)
        ([] ++ dcθ.ty Ty.unit :: List.ofFn (dcθ.tys noTys))) dcΓ0).popFrame 0 [.var, .var] = some Γ' := by
  refine ⟨_, _, rfl, ?_, ?_, ?_, ?_, rfl⟩
  · intro r hr; simp [dcCap, Cap.rgns] at hr
  · intro r hr; simp [Inst.ty, Ty.unit, Ty.subst, Ty.frgns] at hr
  · intro Δ ρ _; rfl
  · rw [dcBody_open]; exact dcBody_typed

/-- The closure capturing `y` twice is not well typed, in any stack typing. -/
theorem dc_closure_untyped {Θ : TempTy dcSig.bodyCtx} {Γ Γ' : StackTy dcSig.bodyCtx}
    {τ : Ty dcSig.bodyCtx} : ¬ HasTypeC sig Θ Γ dcClosure τ Γ' := by
  intro h
  change Typing sig (TyJ.comp Θ Γ dcClosure τ Γ') at h
  generalize hJ : TyJ.comp Θ Γ dcClosure τ Γ' = J at h
  induction h generalizing Γ with
  | drop _ _ _ _ _ _ _ _ _ _ _ ih => cases hJ; exact ih rfl
  | closure _ _ _ _ _ _ _ _ _ _ _ _ _ _ hnodup =>
      cases hJ
      exact dcCap_not_nodup hnodup
  | _ => cases hJ

/-- The body of `dup` is not well typed, in any stack typing. -/
theorem dc_fnBody_untyped {Θ : TempTy dcSig.bodyCtx} {Γ Γ' : StackTy dcSig.bodyCtx}
    {τ : Ty dcSig.bodyCtx} : ¬ HasType sig Θ Γ dcFnBody τ Γ' := by
  intro h
  cases h with
  | letE _ _ _ _ _ _ _ _ _ _ _ _ h₁ => exact dc_closure_untyped h₁

/-- The global function `dup` is not well formed. -/
theorem dc_fn_not_wf : ¬ FnDefWF (sig := sig) dcSig dcFnBody := by
  rintro ⟨_, _, _, h, -, -⟩
  exact dc_fnBody_untyped h

/-- A global environment holding `dup`. -/
def dcG : GlobalEnv [dcSig] := .cons dcFnBody .nil

/-- The global environment holding `dup` is not well formed. -/
theorem dcG_not_wf : ¬ GlobalWF dcG := fun h => dc_fn_not_wf (h .here)

/-- What `E-Closure` would do with this capture list: both captured slots receive
the value of `y`, so with `y` a pointer the closure frame would hold two copies of
the same `&uniq` pointer. -/
theorem dc_env_aliases {sig : Sig} (σ : Stack sig dcSig.bodyCtx) :
    Env.ofCap σ dcCap = .var (σ.get .here) (.var (σ.get .here) .nil) := rfl

end Oxide
