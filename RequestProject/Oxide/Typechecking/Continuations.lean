module

public import RequestProject.Oxide.Typechecking.Validity

/-!
# Typechecking, part 4: continuations and configurations

The paper types runtime terms `framed e`, `shift e` and evaluation contexts as
ordinary expressions.  With the abstract machine, the work left to do is a
continuation instead, and it gets its own judgment:
`ContOK sig Θ Γ τ κ` says that plugging a value of type `τ`, produced with output
stack typing `Γ` by an expression typed under the temporaries `Θ`, into `κ`
gives a well-typed program.  Each rule is the corresponding typing rule of the
paper with its first premise (the subexpression now in focus) removed.  The
frames `popVar`, `popRgn` and `popFrame` check, like `T-Let`, `T-LetRegion` and
`T-Closure`, that the result type and the stack typing can be strengthened past
the popped binders.

A configuration is well typed (`ConfigTyped`) if its stack is valid for some
stack typing, its focus is well typed in it, and its continuation accepts the
result.
-/

@[expose] public section

namespace Oxide

/-- A vector of length `i + 1 + j` seen as a zipper: the first `i` entries, the
entry at the hole, and the last `j` entries. -/
def Fin.zipper {α : Type} {i j : Nat} (xs : Fin (i + 1 + j) → α) : List α × α × List α :=
  (List.ofFn fun t : Fin i => xs (Fin.castAdd j t.castSucc), xs (Fin.castAdd j (Fin.last i)),
    List.ofFn fun t : Fin j => xs (Fin.natAdd (i + 1) t))

/-- The judgment for continuations. -/
inductive ContOK (sig : Sig) : {S : Ctx} → TempTy S → StackTy S → Ty S → Cont sig S → Prop
  /-- the end of the program accepts any value -/
  | halt {S : Ctx} (Θ : TempTy S) (Γ : StackTy S) (τ : Ty S) : ContOK sig Θ Γ τ .halt
  /-- `T-BorrowIndex` -/
  | borrowIdx {S : Ctx} (Θ : TempTy S) (Γ : StackTy S) (r : In .rgn S) (ω : Own) (p : PExpr S)
      (κ : Cont sig S) (L : List (Loan S)) (τ : XTy S) (τ' : Ty S) (ρs : List (Region S))
      (hr : Γ.loans r = []) (hnic : NotInClosure Θ Γ r)
      (hsafe : OwnSafe Θ Γ ω [] p.toAbs L) (htc : PlaceTy Γ ω p.toAbs τ ρs)
      (hτ : (∃ n, τ = .sized (.array τ' n)) ∨ τ = .slice τ')
      (hκ : ContOK sig Θ (Γ.setLoans r L) (.ref (.conc r) ω (.sized τ')) κ) :
      ContOK sig Θ Γ Ty.u32 (.borrowIdx r ω p κ)
  /-- `T-BorrowSlice`, first bound -/
  | borrowSlice₁ {S : Ctx} (Θ : TempTy S) (Γ Γ₂ : StackTy S) (r : In .rgn S) (ω : Own)
      (p : PExpr S) (e₂ : Term sig S) (κ : Cont sig S) (L : List (Loan S)) (τ : XTy S) (τ' : Ty S)
      (ρs : List (Region S))
      (he₂ : HasType sig Θ Γ e₂ Ty.u32 Γ₂)
      (hr : Γ₂.loans r = []) (hnic : NotInClosure Θ Γ₂ r)
      (hsafe : OwnSafe Θ Γ₂ ω [] p.toAbs L) (htc : PlaceTy Γ₂ ω p.toAbs τ ρs)
      (hτ : (∃ n, τ = .sized (.array τ' n)) ∨ τ = .slice τ')
      (hκ : ContOK sig Θ (Γ₂.setLoans r L) (.ref (.conc r) ω (.slice τ')) κ) :
      ContOK sig Θ Γ Ty.u32 (.borrowSlice₁ r ω p e₂ κ)
  /-- `T-BorrowSlice`, second bound -/
  | borrowSlice₂ {S : Ctx} (Θ : TempTy S) (Γ : StackTy S) (r : In .rgn S) (ω : Own)
      (p : PExpr S) (v : Value sig S) (κ : Cont sig S) (L : List (Loan S)) (τ : XTy S) (τ' : Ty S)
      (ρs : List (Region S))
      (hv : HasTypeV sig Θ Γ v Ty.u32)
      (hr : Γ.loans r = []) (hnic : NotInClosure Θ Γ r)
      (hsafe : OwnSafe Θ Γ ω [] p.toAbs L) (htc : PlaceTy Γ ω p.toAbs τ ρs)
      (hτ : (∃ n, τ = .sized (.array τ' n)) ∨ τ = .slice τ')
      (hκ : ContOK sig Θ (Γ.setLoans r L) (.ref (.conc r) ω (.slice τ')) κ) :
      ContOK sig Θ Γ Ty.u32 (.borrowSlice₂ r ω p v κ)
  /-- `T-IndexCopy` -/
  | index {S : Ctx} (Θ : TempTy S) (Γ : StackTy S) (p : PExpr S) (κ : Cont sig S)
      (L : List (Loan S)) (τ : XTy S) (τ' : Ty S) (ρs : List (Region S))
      (hsafe : OwnSafe Θ Γ .shrd [] p.toAbs L) (htc : PlaceTy Γ .shrd p.toAbs τ ρs)
      (hτ : (∃ n, τ = .sized (.array τ' n)) ∨ τ = .slice τ') (hc : τ'.copyable = true)
      (hκ : ContOK sig Θ Γ τ' κ) :
      ContOK sig Θ Γ Ty.u32 (.index p κ)
  /-- `T-AssignDeref` -/
  | assignDeref {S : Ctx} (Θ : TempTy S) (Γ Γ' : StackTy S) (p : PExpr S) (κ : Cont sig S)
      (L : List (Loan S)) (τn τo : Ty S) (ρs : List (Region S))
      (htc : PlaceTy Γ .uniq p.toAbs (.sized τo) ρs)
      (hr : Rewrite Θ .combine Γ τn τo Γ')
      (hsafe : OwnSafe Θ Γ' .uniq [] p.toAbs L)
      (hκ : ContOK sig Θ Γ' Ty.unit κ) :
      ContOK sig Θ Γ τn (.assign p κ)
  /-- `T-Assign` -/
  | assign {S : Ctx} (Θ : TempTy S) (Γ Γ' Γ'' : StackTy S) (p : PExpr S) (κ : Cont sig S)
      (π : APlace S) (τ : Ty S) (τx : MTy S)
      (hp : p.toAbs = π.toExpr)
      (hx : Γ.placeTy π = some τx)
      (huniq : ∀ r ω τ', τx = .init (.ref (.conc r) ω τ') → RgnUniqueTo r π Γ)
      (hr : RewriteM Θ .noop (Γ.rsub π.derefExpr) τ τx Γ')
      (hsafe : τx.IsDead ∨ OwnSafe Θ Γ' .uniq [] π.toExpr [⟨.uniq, π.toExpr⟩])
      (hΓ'' : Γ'.setPlaceTy π (.init τ) = some Γ'')
      (hκ : ContOK sig Θ Γ'' Ty.unit κ) :
      ContOK sig Θ Γ τ (.assign p κ)
  /-- `T-Let` -/
  | letE {S : Ctx} (Θ : TempTy S) (Γ Γ₁' Γ' : StackTy S) (Γ₂ : StackTy (.var :: S))
      (τ τa τr : Ty S) (τ₂ : Ty (.var :: S)) (e₂ : Term sig (.var :: S)) (κ : Cont sig S)
      (hr : Rewrite Θ .combine Γ τ τa Γ₁')
      (hnrb : ∀ r ∈ τa.frgns, NotReborrowed Γ₁' r)
      (h₂ : HasType sig (Θ.rename (TRen.wk S .var))
        (gcLoans (Θ.rename (TRen.wk S .var)) (Γ₁'.pushVar (.init (τa.wk .var)))) e₂ τ₂ Γ₂)
      (hdead : (Γ₂.varTy .here).IsDead)
      (hpop : (gcLoans (τ₂ :: Θ.rename (TRen.wk S .var)) Γ₂).popL [.var] = some Γ')
      (hτ : τ₂.prename (PRen.drop S .var) = some τr)
      (hκ : ContOK sig Θ Γ' τr κ) :
      ContOK sig Θ Γ τ (.letE τa e₂ κ)
  /-- `T-Seq` -/
  | seq {S : Ctx} (Θ : TempTy S) (Γ Γ₂ : StackTy S) (τ τ₂ : Ty S) (e₂ : Term sig S) (κ : Cont sig S)
      (h₂ : HasType sig Θ (gcLoans Θ Γ) e₂ τ₂ Γ₂) (hκ : ContOK sig Θ Γ₂ τ₂ κ) :
      ContOK sig Θ Γ τ (.seq e₂ κ)
  /-- `T-AppFunction`, function position -/
  | appFn {S : Ctx} (Θ : TempTy S) (Γ Γₙ Γb : StackTy S) (b : Binders) (θ : TArgs b S) (k : Nat)
      (args : Fin k → Term sig S) (κ : Cont sig S) (ps : Fin k → Ty (b.ctx ++ S)) (τf : Ty (b.ctx ++ S))
      (bs : List (Fin b.nϱ × Fin b.nϱ))
      (hΦs : ∀ i, EnvWF Γ (θ.frames i)) (hτs : ∀ i, TyWF Γ (θ.tys i))
      (hargs : HasTypeArgs sig Θ Γ (List.ofFn args) (List.ofFn fun i => (ps i).inst θ) Γₙ)
      (hnrb : ∀ i, ∀ r ∈ ((ps i).inst θ).frgns, NotReborrowed Γₙ r)
      (hbounds : OutlivesMany Θ .combine Γₙ
        (bs.map fun p => ((b.absAt p.1).inst θ, (b.absAt p.2).inst θ)) Γb)
      (hκ : ContOK sig Θ Γb (τf.inst θ) κ) :
      ContOK sig Θ Γ (.fn b k ps τf .empty bs) (.appFn b θ k args κ)
  /-- `T-AppClosure`, function position -/
  | appFnClosure {S : Ctx} (Θ : TempTy S) (Γ Γₙ : StackTy S) (θ : TArgs {} S) (k : Nat)
      (args : Fin k → Term sig S) (κ : Cont sig S) (ps : Fin k → Ty S) (τf : Ty S) (Φc : FrameExpr S)
      (hargs : Typing sig (.argsRw Θ Γ (List.ofFn args) (List.ofFn ps) Γₙ))
      (hnrb : ∀ i, ∀ r ∈ (ps i).frgns, NotReborrowed Γₙ r)
      (hκ : ContOK sig Θ Γₙ τf κ) :
      ContOK sig Θ Γ (Ty.closure k ps τf Φc) (.appFn {} θ k args κ)
  /-- `T-AppFunction`, argument position: `i` arguments done, `j` left -/
  | appArg {S : Ctx} (Θ : TempTy S) (Γ Γₙ Γb : StackTy S) (f : Value sig S) (b : Binders)
      (θ : TArgs b S) (i j : Nat) (done : Fin i → Value sig S) (rest : Fin j → Term sig S)
      (κ : Cont sig S) (ps : Fin (i + 1 + j) → Ty (b.ctx ++ S)) (τf : Ty (b.ctx ++ S))
      (bs : List (Fin b.nϱ × Fin b.nϱ))
      (hf : HasTypeV sig Θ Γ f (.fn b (i + 1 + j) ps τf .empty bs))
      (hdone : HasTypeVs sig Θ Γ (List.ofFn done) (Fin.zipper fun t => (ps t).inst θ).1)
      (hrest : HasTypeArgs sig (Θ ++ (Fin.zipper fun t => (ps t).inst θ).1 ++
          [(Fin.zipper fun t => (ps t).inst θ).2.1])
        Γ (List.ofFn rest) (Fin.zipper fun t => (ps t).inst θ).2.2 Γₙ)
      (hnrb : ∀ t, ∀ r ∈ ((ps t).inst θ).frgns, NotReborrowed Γₙ r)
      (hbounds : OutlivesMany Θ .combine Γₙ
        (bs.map fun p => ((b.absAt p.1).inst θ, (b.absAt p.2).inst θ)) Γb)
      (hκ : ContOK sig Θ Γb (τf.inst θ) κ) :
      ContOK sig (Θ ++ (Fin.zipper fun t => (ps t).inst θ).1) Γ
        (Fin.zipper fun t => (ps t).inst θ).2.1 (.appArg f b θ i j done rest κ)
  /-- `T-AppClosure`, argument position: `i` arguments done, `j` left -/
  | appArgClosure {S : Ctx} (Θ : TempTy S) (Γ Γ₁' Γₙ : StackTy S) (f : Value sig S) (θ : TArgs {} S)
      (i j : Nat) (done : Fin i → Value sig S) (rest : Fin j → Term sig S) (κ : Cont sig S)
      (ps : Fin (i + 1 + j) → Ty S) (τf : Ty S) (Φc : FrameExpr S) (τ : Ty S)
      (hf : HasTypeV sig Θ Γ f (Ty.closure (i + 1 + j) ps τf Φc))
      (hdone : HasTypeVs sig Θ Γ (List.ofFn done) (Fin.zipper ps).1)
      (hr : Rewrite (Θ ++ (Fin.zipper ps).1) .combineUnrest Γ τ (Fin.zipper ps).2.1 Γ₁')
      (hrest : Typing sig (.argsRw (Θ ++ (Fin.zipper ps).1 ++ [(Fin.zipper ps).2.1]) Γ₁' (List.ofFn rest)
        (Fin.zipper ps).2.2 Γₙ))
      (hnrb : ∀ t, ∀ r ∈ (ps t).frgns, NotReborrowed Γₙ r)
      (hκ : ContOK sig Θ Γₙ τf κ) :
      ContOK sig (Θ ++ (Fin.zipper ps).1) Γ τ (.appArg f {} θ i j done rest κ)
  /-- `T-Branch` -/
  | ite {S : Ctx} (Θ : TempTy S) (Γ Γ₂ Γ₃ Γ₂' Γ₃' Γ' : StackTy S) (e₂ e₃ : Term sig S) (κ : Cont sig S)
      (τ τ₂ τ₃ : Ty S)
      (h₂ : HasType sig Θ Γ e₂ τ₂ Γ₂) (h₃ : HasType sig Θ Γ e₃ τ₃ Γ₃)
      (hτ : τ = τ₂ ∨ τ = τ₃)
      (hr₂ : Rewrite Θ .combine Γ₂ τ₂ τ Γ₂') (hr₃ : Rewrite Θ .combine Γ₃ τ₃ τ Γ₃')
      (hu : StackTy.union Γ₂' Γ₃' = some Γ')
      (hκ : ContOK sig Θ Γ' τ κ) :
      ContOK sig Θ Γ Ty.bool (.ite e₂ e₃ κ)
  /-- `T-ForArray` -/
  | forArray {S : Ctx} (Θ : TempTy S) (Γ : StackTy S) (Γ₂ : StackTy (.var :: S))
      (e₂ : Term sig (.var :: S)) (κ : Cont sig S) (τ : Ty S) (n : Nat)
      (hnrb : ∀ r ∈ τ.frgns, NotReborrowed Γ r)
      (h₂ : HasType sig (Θ.rename (TRen.wk S .var)) (Γ.pushVar (.init (τ.wk .var))) e₂ Ty.unit Γ₂)
      (hdead : (Γ₂.varTy .here).IsDead)
      (hpop : (gcLoans (Θ.rename (TRen.wk S .var)) Γ₂).popL [.var] = some Γ)
      (hκ : ContOK sig Θ Γ Ty.unit κ) :
      ContOK sig Θ Γ (.array τ n) (.forE e₂ κ)
  /-- `T-ForSlice` -/
  | forSlice {S : Ctx} (Θ : TempTy S) (Γ : StackTy S) (Γ₂ : StackTy (.var :: S))
      (e₂ : Term sig (.var :: S)) (κ : Cont sig S) (ρ : Region S) (ω : Own) (τ : Ty S)
      (hnrb : ∀ r ∈ (Ty.ref ρ ω (.sized τ)).frgns, NotReborrowed Γ r)
      (h₂ : HasType sig (Θ.rename (TRen.wk S .var))
        (Γ.pushVar (.init ((Ty.ref ρ ω (.sized τ)).wk .var))) e₂ Ty.unit Γ₂)
      (hpop : (gcLoans (Θ.rename (TRen.wk S .var)) Γ₂).popL [.var] = some Γ)
      (hκ : ContOK sig Θ Γ Ty.unit κ) :
      ContOK sig Θ Γ (.ref ρ ω (.slice τ)) (.forE e₂ κ)
  /-- `T-Tuple`, after the components `done` -/
  | tuple {S : Ctx} (Θ : TempTy S) (Γ Γ' : StackTy S) (i j : Nat) (done : Fin i → Value sig S)
      (rest : Fin j → Term sig S) (κ : Cont sig S) (τs : Fin (i + 1 + j) → Ty S)
      (hdone : HasTypeVs sig Θ Γ (List.ofFn done) (Fin.zipper τs).1)
      (hrest : HasTypeArgs sig (Θ ++ (Fin.zipper τs).1 ++ [(Fin.zipper τs).2.1]) Γ (List.ofFn rest)
        (Fin.zipper τs).2.2 Γ')
      (hκ : ContOK sig Θ Γ' (.tuple (i + 1 + j) τs) κ) :
      ContOK sig (Θ ++ (Fin.zipper τs).1) Γ (Fin.zipper τs).2.1 (.tuple i j done rest κ)
  /-- `T-Array`, after the elements `done` -/
  | array {S : Ctx} (Θ : TempTy S) (Γ Γ' : StackTy S) (i j : Nat) (done : Fin i → Value sig S)
      (rest : Fin j → Term sig S) (κ : Cont sig S) (τ : Ty S)
      (hdone : HasTypeVs sig Θ Γ (List.ofFn done) (List.replicate i τ))
      (hrest : HasTypeArgs sig (Θ ++ List.replicate i τ ++ [τ]) Γ (List.ofFn rest) (List.replicate j τ) Γ')
      (hκ : ContOK sig Θ Γ' (.array τ (i + 1 + j)) κ) :
      ContOK sig (Θ ++ List.replicate i τ) Γ τ (.array i j done rest κ)
  /-- `T-Left` -/
  | inl {S : Ctx} (Θ : TempTy S) (Γ : StackTy S) (τ₁ τ₂ : Ty S) (κ : Cont sig S)
      (hκ : ContOK sig Θ Γ (.sum τ₁ τ₂) κ) : ContOK sig Θ Γ τ₁ (.inl τ₁ τ₂ κ)
  /-- `T-Right` -/
  | inr {S : Ctx} (Θ : TempTy S) (Γ : StackTy S) (τ₁ τ₂ : Ty S) (κ : Cont sig S)
      (hκ : ContOK sig Θ Γ (.sum τ₁ τ₂) κ) : ContOK sig Θ Γ τ₂ (.inr τ₁ τ₂ κ)
  /-- `T-Match` -/
  | matchE {S : Ctx} (Θ : TempTy S) (Γ Γ₁p Γ₂p Γ₁' Γ₂' Γ'' : StackTy S)
      (Γ₁ Γ₂ : StackTy (.var :: S)) (e₁ e₂ : Term sig (.var :: S)) (κ : Cont sig S)
      (τl τr τ τ₁' τ₂' : Ty S) (τ₁ τ₂ : Ty (.var :: S))
      (hnrb : ∀ r ∈ (Ty.sum τl τr).frgns, NotReborrowed Γ r)
      (h₁ : HasType sig (Θ.rename (TRen.wk S .var)) (Γ.pushVar (.init (τl.wk .var))) e₁ τ₁ Γ₁)
      (h₂ : HasType sig (Θ.rename (TRen.wk S .var)) (Γ.pushVar (.init (τr.wk .var))) e₂ τ₂ Γ₂)
      (hd₁ : (Γ₁.varTy .here).IsDead) (hd₂ : (Γ₂.varTy .here).IsDead)
      (hpop₁ : (gcLoans (τ₁ :: Θ.rename (TRen.wk S .var)) Γ₁).popL [.var] = some Γ₁p)
      (hpop₂ : (gcLoans (τ₂ :: Θ.rename (TRen.wk S .var)) Γ₂).popL [.var] = some Γ₂p)
      (hτ₁ : τ₁.prename (PRen.drop S .var) = some τ₁')
      (hτ₂ : τ₂.prename (PRen.drop S .var) = some τ₂')
      (hτ : τ = τ₁' ∨ τ = τ₂')
      (hr₁ : Rewrite Θ .combine Γ₁p τ₁' τ Γ₁') (hr₂ : Rewrite Θ .combine Γ₂p τ₂' τ Γ₂')
      (hu : StackTy.union Γ₁' Γ₂' = some Γ'')
      (hκ : ContOK sig Θ Γ'' τ κ) :
      ContOK sig Θ Γ (.sum τl τr) (.matchE e₁ e₂ κ)
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
