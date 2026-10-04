module

public import RequestProject.Oxide.Typechecking.RegionRewriting

/-!
# Typechecking, part 2: the typing judgment

Paper §3.5 ("Typechecking Oxide Programs"), Figures "Selected Oxide Typing Rules"
and "Oxide Typing Rule for Application"; appendix B.4 ("Typing"), together with
the well-formedness judgments of appendix B.1 for types and stack typings, and
referent typing from appendix B.5.

The judgment `Σ; Δ; Γ; Θ ⊢ e : τ ⇒ Γ'` is `HasType G Θ Γ e τ Γ'`, where `Γ`
contains `Δ` and all of `Θ`, `Γ`, `e`, `τ`, `Γ'` live in the same scope `S`.  All
judgments are packed into one inductive family `Typing` so that Lean's induction
principle covers them simultaneously.

Since the sorts of types are separate families, the paper's sort premises
(`τ^SI`, `τ^XI`, `τ^SD`, `τ^SX`) and its length premises are gone.

**Popping binders.**  Where a rule ends the scope of a binder (`T-Let`,
`T-LetRegion`, `T-ForArray`, `T-ForSlice`, `T-Match`, and the frame of a closure
body in `T-Closure`), the output stack typing must be *strengthened* past the
binder: the scoped stack typing forces the question of what happens to entries
that still mention it, which the paper leaves implicit.  We first garbage-collect
the loans (`gc-loans`, keeping the regions of the result type alive) and then
require every remaining type and loan to be independent of the popped binder;
the result type must be independent of it too.  This is the no-escape condition
for popped frames that the paper's `T-Framed` lacks.
-/

@[expose] public section

namespace Oxide

/-- Rename a temporary typing. -/
def TempTy.rename {S S' : Ctx} (ρ : TRen S S') (Θ : TempTy S) : TempTy S' := Θ.map (Ty.rename ρ)

/-! ## Referent well-formedness (`WF-Ref*`) -/

/-- `Σ; Γ ⊢ 𝓡 : τ^XI`.  In `WF-RefIndexSlice` and `WF-RefSliceSlice` we add the
bound check against the slice the referent designates. -/
inductive RefTy {S : Ctx} (Γ : StackTy S) : Referent S → XTy S → Prop
  | id (x : In .var S) (τ : Ty S) (h : (Γ.varTy x).toTy? = some τ) : RefTy Γ ⟨x, []⟩ (.sized τ)
  | proj (R : Referent S) (k : Nat) (τs : Fin k → Ty S) (i : Nat) (hi : i < k)
      (h : RefTy Γ R (.sized (.tuple k τs))) :
      RefTy Γ (R.snoc (.proj i)) (.sized (τs ⟨i, hi⟩))
  | idxArray (R : Referent S) (τ : Ty S) (n i : Nat) (h : RefTy Γ R (.sized (.array τ n))) (hi : i < n) :
      RefTy Γ (R.snoc (.idx i)) (.sized τ)
  | idxSlice (root : In .var S) (steps : List RStep) (a b i : Nat) (τ : Ty S)
      (h : RefTy Γ ⟨root, steps ++ [.slice a b]⟩ (.slice τ)) (hi : i < b - a) :
      RefTy Γ ⟨root, steps ++ [.slice a b, .idx i]⟩ (.sized τ)
  | sliceArray (R : Referent S) (τ : Ty S) (n i j : Nat) (h : RefTy Γ R (.sized (.array τ n)))
      (hij : i ≤ j) (hj : j ≤ n) :
      RefTy Γ (R.snoc (.slice i j)) (.slice τ)
  | sliceSlice (root : In .var S) (steps : List RStep) (a b i j : Nat) (τ : Ty S)
      (h : RefTy Γ ⟨root, steps ++ [.slice a b]⟩ (.slice τ)) (hij : i ≤ j) (hj : j ≤ b - a) :
      RefTy Γ ⟨root, steps ++ [.slice a b, .slice i j]⟩ (.slice τ)

/-! ## Well-formedness of types and stack typings (`WF-*`)

Scoping is guaranteed by construction; what remains of the paper's
well-formedness judgments are the conditions on return types and on the loans of
the frames captured by closure types. -/

mutual
/-- Type well-formedness `Σ; Δ; Γ ⊢ τ`. -/
inductive TyWF (G : GlobalEnv) : {S : Ctx} → StackTy S → Ty S → Prop
  | base {S : Ctx} (Γ : StackTy S) (b : BaseTy) : TyWF G Γ (.base b)
  | tvar {S : Ctx} (Γ : StackTy S) (α : In .tvar S) : TyWF G Γ (.tvar α)
  | ref {S : Ctx} (Γ : StackTy S) (ρ : Region S) (ω : Own) (τ : Ty S) (h : TyWF G Γ τ) :
      TyWF G Γ (.ref ρ ω (.sized τ))
  | refSlice {S : Ctx} (Γ : StackTy S) (ρ : Region S) (ω : Own) (τ : Ty S) (h : TyWF G Γ τ) :
      TyWF G Γ (.ref ρ ω (.slice τ))
  | array {S : Ctx} (Γ : StackTy S) (τ : Ty S) (n : Nat) (h : TyWF G Γ τ) : TyWF G Γ (.array τ n)
  | tuple {S : Ctx} (Γ : StackTy S) (k : Nat) (τs : Fin k → Ty S) (h : ∀ i, TyWF G Γ (τs i)) :
      TyWF G Γ (.tuple k τs)
  | sum {S : Ctx} (Γ : StackTy S) (τ₁ τ₂ : Ty S) (h₁ : TyWF G Γ τ₁) (h₂ : TyWF G Γ τ₂) :
      TyWF G Γ (.sum τ₁ τ₂)
  | fn {S : Ctx} (Γ : StackTy S) (b : Binders) (k : Nat) (ps : Fin k → Ty (b.ctx ++ S))
      (ret : Ty (b.ctx ++ S)) (env : FrameExpr (b.ctx ++ S)) (bs : List (Fin b.nϱ × Fin b.nϱ))
      (hret : ∀ r ∈ strengthenL b.ctx ret.frgns, ∀ τ' ∈ Γ.cod, r ∉ τ'.frgnsOut)
      (henv : EnvWF G (Γ.pushBinders b bs) env)
      (hr : TyWF G (Γ.pushBinders b bs) ret)
      (hps : ∀ i, TyWF G (Γ.pushBinders b bs) (ps i)) :
      TyWF G Γ (.fn b k ps ret env bs)
/-- Frame expression well-formedness `Σ; Δ; Γ ⊢ Φ` (`WF-EnvVar`, `WF-Env`). -/
inductive EnvWF (G : GlobalEnv) : {S : Ctx} → StackTy S → FrameExpr S → Prop
  | var {S : Ctx} (Γ : StackTy S) (φ : In .fvar S) : EnvWF G Γ (.var φ)
  | frame {S : Ctx} (Γ : StackTy S) (f : Ctx) (Φ : FrameTy (f ++ .frame :: S) f)
      (h : StackWF G (Γ.pushFrame Φ)) : EnvWF G Γ (.frame f Φ)
/-- Stack typing well-formedness `Σ; Δ ⊢ Γ`: initialized variable types are well
formed, and loans name places that have a type. -/
inductive StackWF (G : GlobalEnv) : {S : Ctx} → StackTy S → Prop
  | mk {S : Ctx} (Γ : StackTy S)
      (hty : ∀ x τ, (Γ.varTy x).toTy? = some τ → TyWF G Γ τ)
      (hloans : ∀ r, ∀ l ∈ Γ.loans r, ∃ τ ρs, PlaceTy Γ l.own l.pe τ ρs) :
      StackWF G Γ
end

/-! ## The typing judgments -/

/-- The forms of the typing judgments of Oxide: expressions
`Σ; Δ; Γ; Θ ⊢ e : τ ⇒ Γ'`, argument lists (plain and with rewriting), values,
maybe-unsized values, maybe-dead values (stack slots), lists of values and
captured frames. -/
inductive TyJ where
  | expr {S : Ctx} (Θ : TempTy S) (Γ : StackTy S) (e : Term S) (τ : Ty S) (Γ' : StackTy S)
  | args {S : Ctx} (Θ : TempTy S) (Γ : StackTy S) (es : List (Term S)) (τs : List (Ty S))
      (Γ' : StackTy S)
  | argsRw {S : Ctx} (Θ : TempTy S) (Γ : StackTy S) (es : List (Term S)) (τs : List (Ty S))
      (Γ' : StackTy S)
  | val {S : Ctx} (Θ : TempTy S) (Γ : StackTy S) (v : Value S) (τ : Ty S)
  | xval {S : Ctx} (Θ : TempTy S) (Γ : StackTy S) (v : Value S) (τ : XTy S)
  | mval {S : Ctx} (Γ : StackTy S) (v : Value S) (τ : MTy S)
  | vals {S : Ctx} (Θ : TempTy S) (Γ : StackTy S) (vs : List (Value S)) (τs : List (Ty S))
  | env {S T f : Ctx} (Γ : StackTy T) (ρ : TRen S T) (ε : Env S f) (Φ : FrameTy T f)

/-- The stack typing in which a closure body runs: the parameters on top of the
captured frame. -/
def closureBodyTy {S f : Ctx} (Γ : StackTy S) (Φc : FrameTy (f ++ .frame :: S) f) {k : Nat}
    (ps : Fin k → Ty S) : StackTy (vars k ++ (f ++ .frame :: S)) :=
  (Γ.pushFrame Φc).pushVars fun i => (ps i).rename (TRen.wkFrame f S)

/-- The typing judgments of Oxide (appendix "Statics"), as a single inductive
family indexed by the form of the judgment. -/
inductive Typing (G : GlobalEnv) : TyJ → Prop
  -- ## Expressions `Σ; Δ; Γ; Θ ⊢ e : τ ⇒ Γ'`
  /-- values -/
  | val {S : Ctx} (Θ : TempTy S) (Γ : StackTy S) (v : Value S) (τ : Ty S)
      (h : Typing G (.val Θ Γ v τ)) : Typing G (.expr Θ Γ (.val v) τ Γ)
  /-- `T-Move` -/
  | move {S : Ctx} (Θ : TempTy S) (Γ Γ' : StackTy S) (p : PlaceExpr S) (π : APlace S) (τ : Ty S)
      (hp : p.toAbs = π.toExpr)
      (hsafe : OwnSafe Θ Γ .uniq [] π.toExpr [⟨.uniq, π.toExpr⟩])
      (hty : Γ.placeTyI π = some τ) (hnc : τ.noncopyable = true)
      (hΓ' : Γ.setPlaceTy π (.dead τ) = some Γ') :
      Typing G (.expr Θ Γ (.place p) τ Γ')
  /-- `T-Copy` -/
  | copy {S : Ctx} (Θ : TempTy S) (Γ : StackTy S) (p : PlaceExpr S) (L : List (Loan S)) (τ : Ty S)
      (ρs : List (Region S))
      (hsafe : OwnSafe Θ Γ .shrd [] p.toAbs L)
      (htc : PlaceTy Γ .shrd p.toAbs (.sized τ) ρs) (hc : τ.copyable = true) :
      Typing G (.expr Θ Γ (.place p) τ Γ)
  /-- `T-Borrow` -/
  | borrow {S : Ctx} (Θ : TempTy S) (Γ : StackTy S) (r : In .rgn S) (ω : Own) (p : PlaceExpr S)
      (L : List (Loan S)) (τ : XTy S) (ρs : List (Region S))
      (hr : Γ.loans r = []) (hnic : NotInClosure Θ Γ r)
      (hsafe : OwnSafe Θ Γ ω [] p.toAbs L) (htc : PlaceTy Γ ω p.toAbs τ ρs) :
      Typing G (.expr Θ Γ (.borrow r ω p) (.ref (.conc r) ω τ) (Γ.setLoans r L))
  /-- `T-BorrowIndex` -/
  | borrowIdx {S : Ctx} (Θ : TempTy S) (Γ Γ₁ : StackTy S) (r : In .rgn S) (ω : Own)
      (p : PlaceExpr S) (e : Term S) (L : List (Loan S)) (τ : XTy S) (τ' : Ty S)
      (ρs : List (Region S))
      (he : Typing G (.expr Θ Γ e Ty.u32 Γ₁))
      (hr : Γ₁.loans r = []) (hnic : NotInClosure Θ Γ₁ r)
      (hsafe : OwnSafe Θ Γ₁ ω [] p.toAbs L) (htc : PlaceTy Γ₁ ω p.toAbs τ ρs)
      (hτ : (∃ n, τ = .sized (.array τ' n)) ∨ τ = .slice τ') :
      Typing G (.expr Θ Γ (.borrowIdx r ω p e) (.ref (.conc r) ω (.sized τ')) (Γ₁.setLoans r L))
  /-- `T-BorrowSlice` (we allow borrowing a slice of an array as well as of a slice) -/
  | borrowSlice {S : Ctx} (Θ : TempTy S) (Γ Γ₁ Γ₂ : StackTy S) (r : In .rgn S) (ω : Own)
      (p : PlaceExpr S) (e₁ e₂ : Term S) (L : List (Loan S)) (τ : XTy S) (τ' : Ty S)
      (ρs : List (Region S))
      (he₁ : Typing G (.expr Θ Γ e₁ Ty.u32 Γ₁)) (he₂ : Typing G (.expr Θ Γ₁ e₂ Ty.u32 Γ₂))
      (hr : Γ₂.loans r = []) (hnic : NotInClosure Θ Γ₂ r)
      (hsafe : OwnSafe Θ Γ₂ ω [] p.toAbs L) (htc : PlaceTy Γ₂ ω p.toAbs τ ρs)
      (hτ : (∃ n, τ = .sized (.array τ' n)) ∨ τ = .slice τ') :
      Typing G (.expr Θ Γ (.borrowSlice r ω p e₁ e₂) (.ref (.conc r) ω (.slice τ')) (Γ₂.setLoans r L))
  /-- `T-IndexCopy` -/
  | index {S : Ctx} (Θ : TempTy S) (Γ Γ' : StackTy S) (p : PlaceExpr S) (e : Term S)
      (L : List (Loan S)) (τ : XTy S) (τ' : Ty S) (ρs : List (Region S))
      (he : Typing G (.expr Θ Γ e Ty.u32 Γ'))
      (hsafe : OwnSafe Θ Γ' .shrd [] p.toAbs L) (htc : PlaceTy Γ' .shrd p.toAbs τ ρs)
      (hτ : (∃ n, τ = .sized (.array τ' n)) ∨ τ = .slice τ') (hc : τ'.copyable = true) :
      Typing G (.expr Θ Γ (.index p e) τ' Γ')
  /-- `T-Seq` -/
  | seq {S : Ctx} (Θ : TempTy S) (Γ Γ₁ Γ₂ : StackTy S) (e₁ e₂ : Term S) (τ₁ τ₂ : Ty S)
      (h₁ : Typing G (.expr Θ Γ e₁ τ₁ Γ₁)) (h₂ : Typing G (.expr Θ (gcLoans Θ Γ₁) e₂ τ₂ Γ₂)) :
      Typing G (.expr Θ Γ (.seq e₁ e₂) τ₂ Γ₂)
  /-- `T-Branch` -/
  | ite {S : Ctx} (Θ : TempTy S) (Γ Γ₁ Γ₂ Γ₃ Γ₂' Γ₃' Γ' : StackTy S) (e₁ e₂ e₃ : Term S)
      (τ τ₂ τ₃ : Ty S)
      (h₁ : Typing G (.expr Θ Γ e₁ Ty.bool Γ₁))
      (h₂ : Typing G (.expr Θ Γ₁ e₂ τ₂ Γ₂)) (h₃ : Typing G (.expr Θ Γ₁ e₃ τ₃ Γ₃))
      (hτ : τ = τ₂ ∨ τ = τ₃)
      (hr₂ : Rewrite Θ .combine Γ₂ τ₂ τ Γ₂') (hr₃ : Rewrite Θ .combine Γ₃ τ₃ τ Γ₃')
      (hu : StackTy.union Γ₂' Γ₃' = some Γ') :
      Typing G (.expr Θ Γ (.ite e₁ e₂ e₃) τ Γ')
  /-- `T-Let`: the variable must be dead at the end of the body, and is then
  popped. -/
  | letE {S : Ctx} (Θ : TempTy S) (Γ Γ₁ Γ₁' Γ' : StackTy S) (Γ₂ : StackTy (.var :: S))
      (τa τ₁ τ : Ty S) (τ₂ : Ty (.var :: S)) (e₁ : Term S) (e₂ : Term (.var :: S))
      (h₁ : Typing G (.expr Θ Γ e₁ τ₁ Γ₁))
      (hr : Rewrite Θ .combine Γ₁ τ₁ τa Γ₁')
      (hnrb : ∀ r ∈ τa.frgns, NotReborrowed Γ₁' r)
      (h₂ : Typing G (.expr (Θ.rename (TRen.wk S .var))
        (gcLoans (Θ.rename (TRen.wk S .var)) (Γ₁'.pushVar (.init (τa.wk .var)))) e₂ τ₂ Γ₂))
      (hdead : (Γ₂.varTy .here).IsDead)
      (hpop : (gcLoans (τ₂ :: Θ.rename (TRen.wk S .var)) Γ₂).popL [.var] = some Γ')
      (hτ : τ₂.prename (PRen.drop S .var) = some τ) :
      Typing G (.expr Θ Γ (.letE τa e₁ e₂) τ Γ')
  /-- `T-LetRegion`: the body is typed with a fresh region `r ↦ {}`, which is then
  popped. -/
  | letrgn {S : Ctx} (Θ : TempTy S) (Γ Γ' : StackTy S) (Γ₁ : StackTy (.rgn :: S))
      (e : Term (.rgn :: S)) (τ₁ : Ty (.rgn :: S)) (τ : Ty S)
      (h : Typing G (.expr (Θ.rename (TRen.wk S .rgn)) (Γ.pushRgn []) e τ₁ Γ₁))
      (hpop : (gcLoans (τ₁ :: Θ.rename (TRen.wk S .rgn)) Γ₁).popL [.rgn] = some Γ')
      (hτ : τ₁.prename (PRen.drop S .rgn) = some τ) :
      Typing G (.expr Θ Γ (.letrgn e) τ Γ')
  /-- `T-AssignDeref` -/
  | assignDeref {S : Ctx} (Θ : TempTy S) (Γ Γ₁ Γ' : StackTy S) (p : PlaceExpr S) (e : Term S)
      (L : List (Loan S)) (τn τo : Ty S) (ρs : List (Region S))
      (he : Typing G (.expr Θ Γ e τn Γ₁))
      (htc : PlaceTy Γ₁ .uniq p.toAbs (.sized τo) ρs)
      (hr : Rewrite Θ .combine Γ₁ τn τo Γ')
      (hsafe : OwnSafe Θ Γ' .uniq [] p.toAbs L) :
      Typing G (.expr Θ Γ (.assign p e) Ty.unit Γ')
  /-- `T-Assign` -/
  | assign {S : Ctx} (Θ : TempTy S) (Γ Γ₁ Γ' Γ'' : StackTy S) (p : PlaceExpr S) (e : Term S)
      (π : APlace S) (τ : Ty S) (τx : MTy S)
      (he : Typing G (.expr Θ Γ e τ Γ₁))
      (hp : p.toAbs = π.toExpr)
      (hx : Γ₁.placeTy π = some τx)
      (huniq : ∀ r ω τ', τx = .init (.ref (.conc r) ω τ') → RgnUniqueTo r π Γ₁)
      (hr : RewriteM Θ .noop (Γ₁.rsub π.derefExpr) τ τx Γ')
      (hsafe : τx.IsDead ∨ OwnSafe Θ Γ' .uniq [] π.toExpr [⟨.uniq, π.toExpr⟩])
      (hΓ'' : Γ'.setPlaceTy π (.init τ) = some Γ'') :
      Typing G (.expr Θ Γ (.assign p e) Ty.unit Γ'')
  /-- `T-While` -/
  | whileE {S : Ctx} (Θ : TempTy S) (Γ Γ₁ Γ₂ : StackTy S) (e₁ e₂ : Term S)
      (h₁ : Typing G (.expr Θ Γ e₁ Ty.bool Γ₁)) (h₂ : Typing G (.expr Θ Γ₁ e₂ Ty.unit Γ₂))
      (h₁' : Typing G (.expr Θ Γ₂ e₁ Ty.bool Γ₂)) (h₂' : Typing G (.expr Θ Γ₂ e₂ Ty.unit Γ₂)) :
      Typing G (.expr Θ Γ (.whileE e₁ e₂) Ty.unit Γ₂)
  /-- `T-ForArray` -/
  | forArray {S : Ctx} (Θ : TempTy S) (Γ Γ₁ : StackTy S) (Γ₂ : StackTy (.var :: S)) (e₁ : Term S)
      (e₂ : Term (.var :: S)) (τ : Ty S) (n : Nat)
      (h₁ : Typing G (.expr Θ Γ e₁ (.array τ n) Γ₁))
      (hnrb : ∀ r ∈ τ.frgns, NotReborrowed Γ₁ r)
      (h₂ : Typing G (.expr (Θ.rename (TRen.wk S .var)) (Γ₁.pushVar (.init (τ.wk .var))) e₂ Ty.unit Γ₂))
      (hdead : (Γ₂.varTy .here).IsDead)
      (hpop : (gcLoans (Θ.rename (TRen.wk S .var)) Γ₂).popL [.var] = some Γ₁) :
      Typing G (.expr Θ Γ (.forE e₁ e₂) Ty.unit Γ₁)
  /-- `T-ForSlice` -/
  | forSlice {S : Ctx} (Θ : TempTy S) (Γ Γ₁ : StackTy S) (Γ₂ : StackTy (.var :: S)) (e₁ : Term S)
      (e₂ : Term (.var :: S)) (ρ : Region S) (ω : Own) (τ : Ty S)
      (h₁ : Typing G (.expr Θ Γ e₁ (.ref ρ ω (.slice τ)) Γ₁))
      (hnrb : ∀ r ∈ (Ty.ref ρ ω (.sized τ)).frgns, NotReborrowed Γ₁ r)
      (h₂ : Typing G (.expr (Θ.rename (TRen.wk S .var))
        (Γ₁.pushVar (.init ((Ty.ref ρ ω (.sized τ)).wk .var))) e₂ Ty.unit Γ₂))
      (hpop : (gcLoans (Θ.rename (TRen.wk S .var)) Γ₂).popL [.var] = some Γ₁) :
      Typing G (.expr Θ Γ (.forE e₁ e₂) Ty.unit Γ₁)
  /-- `T-Closure`.  The closure captures the variables and regions of the current
  frame selected by `s`; `body` is the body `body'` (whose scope is the captured
  frame with the parameters on top) read back in the current scope.  Captured
  regions must not occur in the signature.  The captured non-copyable variables
  become dead, and the body is checked in a new frame holding the parameters on
  top of the captured frame `Φc`; that frame must then be poppable. -/
  | closure {S : Ctx} (Θ : TempTy S) (Γ Γ' : StackTy S) (k : Nat) (ps : Fin k → Ty S) (ret : Ty S)
      (body : Term (vars k ++ S)) (f : Ctx) (s : Sel f S)
      (body' : Term (vars k ++ (f ++ .frame :: S))) (Φc : FrameTy (f ++ .frame :: S) f)
      (Γb : StackTy (vars k ++ (f ++ .frame :: S)))
      (hbody : body = body'.rename (s.ren.liftN (vars k)))
      (hΦc : capturedFrame Γ s = some Φc)
      (hsig : ∀ r ∈ s.selRgns, r ∉ (List.ofFn ps).flatMap Ty.frgns ++ ret.frgns)
      (hparams : ∀ r ∈ (List.ofFn ps).flatMap Ty.frgns ++ ret.frgns, Γ.loans r = [])
      (hb : Typing G (.expr (Θ.rename (TRen.frameRen k f S)) (closureBodyTy (killNC Γ s) Φc ps) body'
        (ret.rename (TRen.frameRen k f S)) Γb))
      (hpop : (gcLoans ((Θ ++ ret :: List.ofFn ps).rename (TRen.frameRen k f S)) Γb).popFrame k f =
        some Γ') :
      Typing G (.expr Θ Γ (.closure k ps ret body) (Ty.closure k ps ret (.frame f Φc)) Γ')
  /-- `T-AppFunction`: `δ = [Φ̄/φ̄][ρ̄/ϱ̄][τ̄/ᾱ]` (the bounds `ϱ₁ : ϱ₂` are checked as
  `δ(ϱ₁) :> δ(ϱ₂)`) -/
  | appFn {S : Ctx} (Θ : TempTy S) (Γ Γ₀ Γₙ Γb : StackTy S) (e : Term S) (b : Binders)
      (Φs : Fin b.nφ → FrameExpr S) (ρs : Fin b.nϱ → Region S) (τs : Fin b.nα → Ty S) (k : Nat)
      (args : Fin k → Term S) (ps : Fin k → Ty (b.ctx ++ S)) (τf : Ty (b.ctx ++ S))
      (bs : List (Fin b.nϱ × Fin b.nϱ))
      (hΦs : ∀ i, EnvWF G Γ (Φs i)) (hτs : ∀ i, TyWF G Γ (τs i))
      (hf : Typing G (.expr Θ Γ e (.fn b k ps τf .empty bs) Γ₀))
      (hargs : Typing G (.args Θ Γ₀ (List.ofFn args) (List.ofFn fun i => (ps i).inst b Φs ρs τs) Γₙ))
      (hnrb : ∀ i, ∀ r ∈ ((ps i).inst b Φs ρs τs).frgns, NotReborrowed Γₙ r)
      (hbounds : OutlivesMany Θ .combine Γₙ
        (bs.map fun p => ((b.absAt p.1).inst b Φs ρs τs, (b.absAt p.2).inst b Φs ρs τs)) Γb) :
      Typing G (.expr Θ Γ (.app e b Φs ρs τs k args) (τf.inst b Φs ρs τs) Γb)
  /-- `T-AppClosure` -/
  | appClosure {S : Ctx} (Θ : TempTy S) (Γ Γ₀ Γₙ : StackTy S) (e : Term S) (k : Nat)
      (args : Fin k → Term S) (ps : Fin k → Ty S) (τf : Ty S) (Φc : FrameExpr S)
      (Φs : Fin 0 → FrameExpr S) (ρs : Fin 0 → Region S) (τs : Fin 0 → Ty S)
      (hf : Typing G (.expr Θ Γ e (Ty.closure k ps τf Φc) Γ₀))
      (hargs : Typing G (.argsRw Θ Γ₀ (List.ofFn args) (List.ofFn ps) Γₙ))
      (hnrb : ∀ i, ∀ r ∈ (ps i).frgns, NotReborrowed Γₙ r) :
      Typing G (.expr Θ Γ (.app e {} Φs ρs τs k args) τf Γₙ)
  /-- `T-Tuple` -/
  | tuple {S : Ctx} (Θ : TempTy S) (Γ Γ' : StackTy S) (k : Nat) (es : Fin k → Term S)
      (τs : Fin k → Ty S) (h : Typing G (.args Θ Γ (List.ofFn es) (List.ofFn τs) Γ')) :
      Typing G (.expr Θ Γ (.tuple k es) (.tuple k τs) Γ')
  /-- `T-Array` -/
  | array {S : Ctx} (Θ : TempTy S) (Γ Γ' : StackTy S) (k : Nat) (es : Fin k → Term S) (τ : Ty S)
      (h : Typing G (.args Θ Γ (List.ofFn es) (List.replicate k τ) Γ')) :
      Typing G (.expr Θ Γ (.array k es) (.array τ k) Γ')
  /-- `T-Abort` -/
  | abort {S : Ctx} (Θ : TempTy S) (Γ : StackTy S) (s : String) (τ : Ty S) :
      Typing G (.expr Θ Γ (.abort s) τ Γ)
  /-- `T-Drop` -/
  | drop {S : Ctx} (Θ : TempTy S) (Γ Γd Γf : StackTy S) (π : APlace S) (τπ τ : Ty S) (e : Term S)
      (hπ : Γ.placeTyI π = some τπ) (hd : Γ.setPlaceTy π (.dead τπ) = some Γd)
      (h : Typing G (.expr Θ Γd e τ Γf)) :
      Typing G (.expr Θ Γ e τ Γf)
  /-- `T-Left` -/
  | inl {S : Ctx} (Θ : TempTy S) (Γ Γ' : StackTy S) (τ₁ τ₂ : Ty S) (e : Term S)
      (h : Typing G (.expr Θ Γ e τ₁ Γ')) :
      Typing G (.expr Θ Γ (.inl τ₁ τ₂ e) (.sum τ₁ τ₂) Γ')
  /-- `T-Right` -/
  | inr {S : Ctx} (Θ : TempTy S) (Γ Γ' : StackTy S) (τ₁ τ₂ : Ty S) (e : Term S)
      (h : Typing G (.expr Θ Γ e τ₂ Γ')) :
      Typing G (.expr Θ Γ (.inr τ₁ τ₂ e) (.sum τ₁ τ₂) Γ')
  /-- `T-Match` -/
  | matchE {S : Ctx} (Θ : TempTy S) (Γ Γ' Γ₁p Γ₂p Γ₁' Γ₂' Γ'' : StackTy S)
      (Γ₁ Γ₂ : StackTy (.var :: S)) (e : Term S) (e₁ e₂ : Term (.var :: S))
      (τl τr τ τ₁' τ₂' : Ty S) (τ₁ τ₂ : Ty (.var :: S))
      (h : Typing G (.expr Θ Γ e (.sum τl τr) Γ'))
      (hnrb : ∀ r ∈ (Ty.sum τl τr).frgns, NotReborrowed Γ' r)
      (h₁ : Typing G (.expr (Θ.rename (TRen.wk S .var)) (Γ'.pushVar (.init (τl.wk .var))) e₁ τ₁ Γ₁))
      (h₂ : Typing G (.expr (Θ.rename (TRen.wk S .var)) (Γ'.pushVar (.init (τr.wk .var))) e₂ τ₂ Γ₂))
      (hd₁ : (Γ₁.varTy .here).IsDead) (hd₂ : (Γ₂.varTy .here).IsDead)
      (hpop₁ : (gcLoans (τ₁ :: Θ.rename (TRen.wk S .var)) Γ₁).popL [.var] = some Γ₁p)
      (hpop₂ : (gcLoans (τ₂ :: Θ.rename (TRen.wk S .var)) Γ₂).popL [.var] = some Γ₂p)
      (hτ₁ : τ₁.prename (PRen.drop S .var) = some τ₁')
      (hτ₂ : τ₂.prename (PRen.drop S .var) = some τ₂')
      (hτ : τ = τ₁' ∨ τ = τ₂')
      (hr₁ : Rewrite Θ .combine Γ₁p τ₁' τ Γ₁') (hr₂ : Rewrite Θ .combine Γ₂p τ₂' τ Γ₂')
      (hu : StackTy.union Γ₁' Γ₂' = some Γ'') :
      Typing G (.expr Θ Γ (.matchE e e₁ e₂) τ Γ'')
  -- ## Argument lists: the `i`-th expression is typed with the types of the
  -- previous ones added to `Θ`.
  | argsNil {S : Ctx} (Θ : TempTy S) (Γ : StackTy S) : Typing G (.args Θ Γ [] [] Γ)
  | argsCons {S : Ctx} (Θ : TempTy S) (Γ Γ₁ Γ₂ : StackTy S) (e : Term S) (es : List (Term S))
      (τ : Ty S) (τs : List (Ty S)) (h : Typing G (.expr Θ Γ e τ Γ₁))
      (t : Typing G (.args (Θ ++ [τ]) Γ₁ es τs Γ₂)) :
      Typing G (.args Θ Γ (e :: es) (τ :: τs) Γ₂)
  -- ## Closure arguments (`T-AppClosure`): each argument is rewritten with mode `⊞`.
  | argsRwNil {S : Ctx} (Θ : TempTy S) (Γ : StackTy S) : Typing G (.argsRw Θ Γ [] [] Γ)
  | argsRwCons {S : Ctx} (Θ : TempTy S) (Γ Γ₁ Γ₁' Γ₂ : StackTy S) (e : Term S) (es : List (Term S))
      (τ' τ : Ty S) (τs : List (Ty S)) (h : Typing G (.expr Θ Γ e τ' Γ₁))
      (hr : Rewrite Θ .combineUnrest Γ₁ τ' τ Γ₁')
      (t : Typing G (.argsRw (Θ ++ [τ]) Γ₁' es τs Γ₂)) :
      Typing G (.argsRw Θ Γ (e :: es) (τ :: τs) Γ₂)
  -- ## Values `Σ; Δ; Γ; Θ ⊢ v : τ ⇒ Γ` (values never change the stack typing).
  /-- `T-Unit` -/
  | vUnit {S : Ctx} (Θ : TempTy S) (Γ : StackTy S) : Typing G (.val Θ Γ Value.unit Ty.unit)
  /-- `T-u32` -/
  | vNum {S : Ctx} (Θ : TempTy S) (Γ : StackTy S) (n : Nat) : Typing G (.val Θ Γ (Value.num n) Ty.u32)
  /-- `T-True`, `T-False` -/
  | vBool {S : Ctx} (Θ : TempTy S) (Γ : StackTy S) (b : Bool) :
      Typing G (.val Θ Γ (.prim (.bool b)) Ty.bool)
  /-- `T-Function` -/
  | vFn {S : Ctx} (Θ : TempTy S) (Γ : StackTy S) (f : String) (d : FnDef)
      (hd : G.lookup f = some d) :
      Typing G (.val Θ Γ (.fn f) d.ty)
  /-- tuple values (`T-Tuple`) -/
  | vTuple {S : Ctx} (Θ : TempTy S) (Γ : StackTy S) (k : Nat) (vs : Fin k → Value S)
      (τs : Fin k → Ty S) (h : Typing G (.vals Θ Γ (List.ofFn vs) (List.ofFn τs))) :
      Typing G (.val Θ Γ (.tuple k vs) (.tuple k τs))
  /-- array values (`T-Array`) -/
  | vArray {S : Ctx} (Θ : TempTy S) (Γ : StackTy S) (k : Nat) (vs : Fin k → Value S) (τ : Ty S)
      (h : Typing G (.vals Θ Γ (List.ofFn vs) (List.replicate k τ))) :
      Typing G (.val Θ Γ (.array k vs) (.array τ k))
  /-- `T-Pointer` -/
  | vPtr {S : Ctx} (Θ : TempTy S) (Γ : StackTy S) (R : Referent S) (r : In .rgn S) (ω : Own)
      (τ : XTy S) (hR : RefTy Γ R τ) (hl : (⟨ω, R.base.toExpr⟩ : Loan S) ∈ Γ.loans r) :
      Typing G (.val Θ Γ (.ptr R) (.ref (.conc r) ω τ))
  /-- `T-ClosureValue` (together with `WF-Frame` for the captured frame): the
  captured values have the types of the captured frame `Φc`, and the body is
  checked in a new frame holding the parameters on top of it. -/
  | vClosure {S : Ctx} (Θ : TempTy S) (Γ : StackTy S) (f : Ctx) (env : Env S f) (k : Nat)
      (ps : Fin k → Ty S) (ret : Ty S) (body : Term (vars k ++ (f ++ .frame :: S)))
      (Φc : FrameTy (f ++ .frame :: S) f) (Γb : StackTy (vars k ++ (f ++ .frame :: S)))
      (henv : Typing G (.env (Γ.pushFrame Φc) (TRen.wkFrame f S) env Φc))
      (hb : Typing G (.expr (Θ.rename (TRen.frameRen k f S)) (closureBodyTy Γ Φc ps) body
        (ret.rename (TRen.frameRen k f S)) Γb))
      (hpop : ((gcLoans ((Θ ++ ret :: List.ofFn ps).rename (TRen.frameRen k f S)) Γb).popFrame k f).isSome) :
      Typing G (.val Θ Γ (.closure f env k ps ret body) (Ty.closure k ps ret (.frame f Φc)))
  /-- `T-Left` on values -/
  | vInl {S : Ctx} (Θ : TempTy S) (Γ : StackTy S) (τ₁ τ₂ : Ty S) (v : Value S)
      (h : Typing G (.val Θ Γ v τ₁)) : Typing G (.val Θ Γ (.inl τ₁ τ₂ v) (.sum τ₁ τ₂))
  /-- `T-Right` on values -/
  | vInr {S : Ctx} (Θ : TempTy S) (Γ : StackTy S) (τ₁ τ₂ : Ty S) (v : Value S)
      (h : Typing G (.val Θ Γ v τ₂)) : Typing G (.val Θ Γ (.inr τ₁ τ₂ v) (.sum τ₁ τ₂))
  -- ## Maybe-unsized values (what a pointer may point to)
  | xSized {S : Ctx} (Θ : TempTy S) (Γ : StackTy S) (v : Value S) (τ : Ty S)
      (h : Typing G (.val Θ Γ v τ)) : Typing G (.xval Θ Γ v (.sized τ))
  /-- slice values (`T-Slice`) -/
  | xSlice {S : Ctx} (Θ : TempTy S) (Γ : StackTy S) (k : Nat) (vs : Fin k → Value S) (τ : Ty S)
      (h : Typing G (.vals Θ Γ (List.ofFn vs) (List.replicate k τ))) :
      Typing G (.xval Θ Γ (.slice k vs) (.slice τ))
  -- ## Maybe-dead values (the contents of stack slots)
  | mInit {S : Ctx} (Γ : StackTy S) (v : Value S) (τ : Ty S) (h : Typing G (.val [] Γ v τ)) :
      Typing G (.mval Γ v (.init τ))
  /-- `T-Dead`: any value has any dead type -/
  | mDead {S : Ctx} (Γ : StackTy S) (v : Value S) (τ : Ty S) : Typing G (.mval Γ v (.dead τ))
  /-- partially moved tuples -/
  | mTuple {S : Ctx} (Γ : StackTy S) (k : Nat) (vs : Fin k → Value S) (ms : Fin k → MTy S)
      (h : ∀ i, Typing G (.mval Γ (vs i) (ms i))) : Typing G (.mval Γ (.tuple k vs) (.tuple k ms))
  -- ## Lists of values
  | vsNil {S : Ctx} (Θ : TempTy S) (Γ : StackTy S) : Typing G (.vals Θ Γ [] [])
  | vsCons {S : Ctx} (Θ : TempTy S) (Γ : StackTy S) (v : Value S) (vs : List (Value S)) (τ : Ty S)
      (τs : List (Ty S)) (h : Typing G (.val Θ Γ v τ)) (t : Typing G (.vals (Θ ++ [τ]) Γ vs τs)) :
      Typing G (.vals Θ Γ (v :: vs) (τ :: τs))
  -- ## Captured frames: each captured value has the type of its entry
  | envNil {S T : Ctx} (Γ : StackTy T) (ρ : TRen S T) : Typing G (.env Γ ρ (.nil : Env S []) .nil)
  | envVar {S T f : Ctx} (Γ : StackTy T) (ρ : TRen S T) (v : Value S) (ε : Env S f) (τ : Ty T)
      (Φ : FrameTy T f) (h : Typing G (.val [] Γ (v.rename ρ) τ)) (t : Typing G (.env Γ ρ ε Φ)) :
      Typing G (.env Γ ρ (.var v ε) (.var τ Φ))
  | envRgn {S T f : Ctx} (Γ : StackTy T) (ρ : TRen S T) (ε : Env S f) (L : List (Loan T))
      (Φ : FrameTy T f) (t : Typing G (.env Γ ρ ε Φ)) :
      Typing G (.env Γ ρ (.rgn ε) (.rgn L Φ))

/-- `Σ; Δ; Γ; Θ ⊢ e : τ ⇒ Γ'`. -/
abbrev HasType (G : GlobalEnv) {S : Ctx} (Θ : TempTy S) (Γ : StackTy S) (e : Term S) (τ : Ty S)
    (Γ' : StackTy S) : Prop := Typing G (.expr Θ Γ e τ Γ')

/-- Typing of argument lists. -/
abbrev HasTypeArgs (G : GlobalEnv) {S : Ctx} (Θ : TempTy S) (Γ : StackTy S) (es : List (Term S))
    (τs : List (Ty S)) (Γ' : StackTy S) : Prop := Typing G (.args Θ Γ es τs Γ')

/-- Value typing `Σ; Δ; Γ; Θ ⊢ v : τ ⇒ Γ`. -/
abbrev HasTypeV (G : GlobalEnv) {S : Ctx} (Θ : TempTy S) (Γ : StackTy S) (v : Value S) (τ : Ty S) :
    Prop := Typing G (.val Θ Γ v τ)

/-- Typing of the content of a stack slot (maybe dead). -/
abbrev HasTypeM (G : GlobalEnv) {S : Ctx} (Γ : StackTy S) (v : Value S) (τ : MTy S) : Prop :=
  Typing G (.mval Γ v τ)

/-- Typing of lists of values. -/
abbrev HasTypeVs (G : GlobalEnv) {S : Ctx} (Θ : TempTy S) (Γ : StackTy S) (vs : List (Value S))
    (τs : List (Ty S)) : Prop := Typing G (.vals Θ Γ vs τs)

end Oxide
