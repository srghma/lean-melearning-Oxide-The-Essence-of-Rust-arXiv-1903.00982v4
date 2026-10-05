module

public import RequestProject.Oxide.Typechecking.RegionRewriting

/-!
# Typechecking, part 2: the typing judgment

Paper §3.5 ("Typechecking Oxide Programs"), Figures "Selected Oxide Typing Rules"
and "Oxide Typing Rule for Application"; appendix B.4 ("Typing"), together with
the well-formedness judgments of appendix B.1 for types and stack typings, and
referent typing from appendix B.5.

The judgment `Σ; Δ; Γ; Θ ⊢ e : τ ⇒ Γ'` is `HasType sig Θ Γ e τ Γ'`, where `Γ`
contains `Δ` and all of `Θ`, `Γ`, `e`, `τ`, `Γ'` live in the same scope `S`.
Following the A-normal form of terms it comes in three layers: atoms
(`HasTypeA`: `T-Move`, `T-Copy` and values), computations (`HasTypeC`: one rule
per operation, whose operand premises are atom judgments, plus `T-Drop`) and
terms (`HasType`: `T-Let`, `T-Seq` and a computation in tail position).  The
rules are the paper's, with each operand premise now about an atom.  All
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
  /-- `WF-RefId` and `WF-RefProj` -/
  | place (π : APlace S) (τ : Ty S) (h : Γ.placeTyI π = some τ) : RefTy Γ (.place π) (.sized τ)
  /-- `WF-RefIndexArray`, followed by projections -/
  | idxArray (R : Referent S) (τ : Ty S) (n i : Nat) (q : List Nat) (p : TyPath τ)
      (h : RefTy Γ R (.sized (.array τ n))) (hi : i < n) (hq : TyPath.ofList τ q = some p) :
      RefTy Γ (.index R i q) (.sized p.target)
  /-- `WF-RefIndexSlice`, followed by projections -/
  | idxSlice (R : Referent S) (a l i : Nat) (q : List Nat) (τ : Ty S) (p : TyPath τ)
      (h : RefTy Γ (.slice R a l) (.slice τ)) (hi : i < l) (hq : TyPath.ofList τ q = some p) :
      RefTy Γ (.index (.slice R a l) i q) (.sized p.target)
  /-- `WF-RefSliceArray` -/
  | sliceArray (R : Referent S) (τ : Ty S) (n a l : Nat) (h : RefTy Γ R (.sized (.array τ n)))
      (hl : a + l ≤ n) :
      RefTy Γ (.slice R a l) (.slice τ)
  /-- `WF-RefSliceSlice` -/
  | sliceSlice (R : Referent S) (a l a' l' : Nat) (τ : Ty S) (h : RefTy Γ (.slice R a l) (.slice τ))
      (hl : a' + l' ≤ l) :
      RefTy Γ (.slice (.slice R a l) a' l') (.slice τ)

/-! ## Well-formedness of types and stack typings (`WF-*`)

Scoping is guaranteed by construction; what remains of the paper's
well-formedness judgments are the conditions on return types and on the loans of
the frames captured by closure types. -/

mutual
/-- Type well-formedness `Σ; Δ; Γ ⊢ τ`. -/
inductive TyWF : {S : Ctx} → StackTy S → Ty S → Prop
  | base {S : Ctx} (Γ : StackTy S) (b : BaseTy) : TyWF Γ (.base b)
  | tvar {S : Ctx} (Γ : StackTy S) (α : In .tvar S) : TyWF Γ (.tvar α)
  | ref {S : Ctx} (Γ : StackTy S) (ρ : Region S) (ω : Own) (τ : Ty S) (h : TyWF Γ τ) :
      TyWF Γ (.ref ρ ω (.sized τ))
  | refSlice {S : Ctx} (Γ : StackTy S) (ρ : Region S) (ω : Own) (τ : Ty S) (h : TyWF Γ τ) :
      TyWF Γ (.ref ρ ω (.slice τ))
  | array {S : Ctx} (Γ : StackTy S) (τ : Ty S) (n : Nat) (h : TyWF Γ τ) : TyWF Γ (.array τ n)
  | tuple {S : Ctx} (Γ : StackTy S) (k : Nat) (τs : Fin k → Ty S) (h : ∀ i, TyWF Γ (τs i)) :
      TyWF Γ (.tuple k τs)
  | sum {S : Ctx} (Γ : StackTy S) (τ₁ τ₂ : Ty S) (h₁ : TyWF Γ τ₁) (h₂ : TyWF Γ τ₂) :
      TyWF Γ (.sum τ₁ τ₂)
  | fn {S : Ctx} (Γ : StackTy S) (b : Binders) (k : Nat) (ps : Fin k → Ty (b.ctx ++ S))
      (ret : Ty (b.ctx ++ S)) (env : FrameExpr (b.ctx ++ S)) (bs : List (Fin b.nϱ × Fin b.nϱ))
      (hret : ∀ r ∈ strengthenL b.ctx ret.frgns, ∀ τ' ∈ Γ.cod, r ∉ τ'.frgnsOut)
      (henv : EnvWF (Γ.pushBinders b bs) env)
      (hr : TyWF (Γ.pushBinders b bs) ret)
      (hps : ∀ i, TyWF (Γ.pushBinders b bs) (ps i)) :
      TyWF Γ (.fn b k ps ret env bs)
/-- Frame expression well-formedness `Σ; Δ; Γ ⊢ Φ` (`WF-EnvVar`, `WF-Env`). -/
inductive EnvWF : {S : Ctx} → StackTy S → FrameExpr S → Prop
  | var {S : Ctx} (Γ : StackTy S) (φ : In .fvar S) : EnvWF Γ (.var φ)
  | frame {S : Ctx} (Γ : StackTy S) (f : Ctx) (Φ : FrameTy (f ++ .frame :: S) f)
      (h : StackWF (Γ.pushFrame Φ)) : EnvWF Γ (.frame f Φ)
/-- Stack typing well-formedness `Σ; Δ ⊢ Γ`: initialized variable types are well
formed, and loans name places that have a type. -/
inductive StackWF : {S : Ctx} → StackTy S → Prop
  | mk {S : Ctx} (Γ : StackTy S)
      (hty : ∀ x τ, (Γ.varTy x).toTy? = some τ → TyWF Γ τ)
      (hloans : ∀ r, ∀ l ∈ Γ.loans r, ∃ τ ρs, PlaceTy Γ l.own l.pe τ ρs) :
      StackWF Γ
end

/-! ## The typing judgments -/

/-- The forms of the typing judgments of Oxide.  Following the A-normal form of
terms, the paper's expression judgment `Σ; Δ; Γ; Θ ⊢ e : τ ⇒ Γ'` is split into
three judgments: atoms, computations and terms.  The other forms are argument
lists (lists of atoms, plain and with rewriting), values, maybe-unsized values,
maybe-dead values (stack slots), lists of values and captured frames. -/
inductive TyJ (sig : Sig) where
  | atom {S : Ctx} (Θ : TempTy S) (Γ : StackTy S) (a : Atom sig S) (τ : Ty S) (Γ' : StackTy S)
  | comp {S : Ctx} (Θ : TempTy S) (Γ : StackTy S) (c : Comp sig S) (τ : Ty S) (Γ' : StackTy S)
  | expr {S : Ctx} (Θ : TempTy S) (Γ : StackTy S) (e : Term sig S) (τ : Ty S) (Γ' : StackTy S)
  | args {S : Ctx} (Θ : TempTy S) (Γ : StackTy S) (as : List (Atom sig S)) (τs : List (Ty S))
      (Γ' : StackTy S)
  | argsRw {S : Ctx} (Θ : TempTy S) (Γ : StackTy S) (as : List (Atom sig S)) (τs : List (Ty S))
      (Γ' : StackTy S)
  | val {S : Ctx} (Θ : TempTy S) (Γ : StackTy S) (v : Value sig S) (τ : Ty S)
  | xval {S : Ctx} (Θ : TempTy S) (Γ : StackTy S) (v : Value sig S) (τ : XTy S)
  | mval {S : Ctx} (Γ : StackTy S) (v : Value sig S) (τ : MTy S)
  | vals {S : Ctx} (Θ : TempTy S) (Γ : StackTy S) (vs : List (Value sig S)) (τs : List (Ty S))
  | env {S T f : Ctx} (Γ : StackTy T) (ρ : TRen S T) (ε : Env sig S f) (Φ : FrameTy T f)

/-- The stack typing in which a closure body runs: the parameters on top of the
captured frame. -/
def closureBodyTy {S f : Ctx} (Γ : StackTy S) (Φc : FrameTy (f ++ .frame :: S) f) {k : Nat}
    (ps : Fin k → Ty S) : StackTy (vars k ++ (f ++ .frame :: S)) :=
  (Γ.pushFrame Φc).pushVars fun i => (ps i).rename (TRen.wkFrame f S)

/-- A type written in a closure scope, read in the enclosing scope. -/
abbrev Inst.ty {o S : Ctx} (θ : Inst o S) (τ : Ty o) : Ty S := τ.subst θ.toTSub

/-- Parameter types written in a closure scope, read in the enclosing scope. -/
abbrev Inst.tys {o S : Ctx} (θ : Inst o S) {k : Nat} (ps : Fin k → Ty o) : Fin k → Ty S :=
  fun i => θ.ty (ps i)

/-- Every binder that a closure body can mention through its entries `θ` occurs in
the closure's type `τ`: whenever `τ` can be strengthened past some binders (they
do not occur in it), so can `θ`.  This is the condition that rules out a closure
outliving a region (or variable) that its body still mentions. -/
def Inst.Covered {o S : Ctx} (θ : Inst o S) (τ : Ty S) : Prop :=
  ∀ (Δ : Ctx) (ρ : PRen S Δ), (τ.prename ρ).isSome → (θ.prename ρ).isSome

/-- The typing judgments of Oxide (appendix "Statics"), as a single inductive
family indexed by the form of the judgment. -/
inductive Typing (sig : Sig) : TyJ sig → Prop
  -- ## Atoms `Σ; Δ; Γ; Θ ⊢ a : τ ⇒ Γ'`
  /-- values -/
  | val {S : Ctx} (Θ : TempTy S) (Γ : StackTy S) (v : Value sig S) (τ : Ty S)
      (h : Typing sig (.val Θ Γ v τ)) : Typing sig (.atom Θ Γ (.val v) τ Γ)
  /-- `T-Move`: moving out of a place (of any type; the paper restricts `T-Move` to
  non-copyable types, but a move of a copyable value is harmless and is how a
  value is moved out in Rust's MIR) -/
  | move {S : Ctx} (Θ : TempTy S) (Γ Γ' : StackTy S) (π : TPlace S) (τ : Ty S)
      (hsafe : OwnSafe Θ Γ .uniq [] π.toAbs.toExpr [⟨.uniq, π.toAbs.toExpr⟩])
      (hty : Γ.placeTyI π.toAbs = some τ)
      (hΓ' : Γ.setPlaceTy π.toAbs (.dead τ) = some Γ') :
      Typing sig (.atom Θ Γ (.move π) τ Γ')
  /-- `T-Copy`: copying requires a copyable type -/
  | copy {S : Ctx} (Θ : TempTy S) (Γ : StackTy S) (p : PExpr S) (L : List (Loan S)) (τ : Ty S)
      (ρs : List (Region S))
      (hsafe : OwnSafe Θ Γ .shrd [] p.toAbs L)
      (htc : PlaceTy Γ .shrd p.toAbs (.sized τ) ρs) (hc : τ.copyable = true) :
      Typing sig (.atom Θ Γ (.copy p) τ Γ)
  -- ## Computations `Σ; Δ; Γ; Θ ⊢ c : τ ⇒ Γ'`
  /-- an atom as a computation -/
  | atom {S : Ctx} (Θ : TempTy S) (Γ Γ' : StackTy S) (a : Atom sig S) (τ : Ty S)
      (h : Typing sig (.atom Θ Γ a τ Γ')) : Typing sig (.comp Θ Γ (.atom a) τ Γ')
  /-- `T-Borrow` -/
  | borrow {S : Ctx} (Θ : TempTy S) (Γ : StackTy S) (r : In .rgn S) (ω : Own) (p : PExpr S)
      (L : List (Loan S)) (τ : XTy S) (ρs : List (Region S))
      (hr : Γ.loans r = []) (hnic : NotInClosure Θ Γ r)
      (hsafe : OwnSafe Θ Γ ω [] p.toAbs L) (htc : PlaceTy Γ ω p.toAbs τ ρs) :
      Typing sig (.comp Θ Γ (.borrow r ω p) (.ref (.conc r) ω τ) (Γ.setLoans r L))
  /-- `T-BorrowIndex` -/
  | borrowIdx {S : Ctx} (Θ : TempTy S) (Γ Γ₁ : StackTy S) (r : In .rgn S) (ω : Own)
      (p : PExpr S) (a : Atom sig S) (L : List (Loan S)) (τ : XTy S) (τ' : Ty S)
      (ρs : List (Region S))
      (ha : Typing sig (.atom Θ Γ a Ty.u32 Γ₁))
      (hr : Γ₁.loans r = []) (hnic : NotInClosure Θ Γ₁ r)
      (hsafe : OwnSafe Θ Γ₁ ω [] p.toAbs L) (htc : PlaceTy Γ₁ ω p.toAbs τ ρs)
      (hτ : (∃ n, τ = .sized (.array τ' n)) ∨ τ = .slice τ') :
      Typing sig (.comp Θ Γ (.borrowIdx r ω p a) (.ref (.conc r) ω (.sized τ')) (Γ₁.setLoans r L))
  /-- `T-BorrowSlice` (we allow borrowing a slice of an array as well as of a slice) -/
  | borrowSlice {S : Ctx} (Θ : TempTy S) (Γ Γ₁ Γ₂ : StackTy S) (r : In .rgn S) (ω : Own)
      (p : PExpr S) (a₁ a₂ : Atom sig S) (L : List (Loan S)) (τ : XTy S) (τ' : Ty S)
      (ρs : List (Region S))
      (ha₁ : Typing sig (.atom Θ Γ a₁ Ty.u32 Γ₁)) (ha₂ : Typing sig (.atom Θ Γ₁ a₂ Ty.u32 Γ₂))
      (hr : Γ₂.loans r = []) (hnic : NotInClosure Θ Γ₂ r)
      (hsafe : OwnSafe Θ Γ₂ ω [] p.toAbs L) (htc : PlaceTy Γ₂ ω p.toAbs τ ρs)
      (hτ : (∃ n, τ = .sized (.array τ' n)) ∨ τ = .slice τ') :
      Typing sig (.comp Θ Γ (.borrowSlice r ω p a₁ a₂) (.ref (.conc r) ω (.slice τ'))
        (Γ₂.setLoans r L))
  /-- `T-IndexCopy` -/
  | index {S : Ctx} (Θ : TempTy S) (Γ Γ' : StackTy S) (p : PExpr S) (a : Atom sig S)
      (L : List (Loan S)) (τ : XTy S) (τ' : Ty S) (ρs : List (Region S))
      (ha : Typing sig (.atom Θ Γ a Ty.u32 Γ'))
      (hsafe : OwnSafe Θ Γ' .shrd [] p.toAbs L) (htc : PlaceTy Γ' .shrd p.toAbs τ ρs)
      (hτ : (∃ n, τ = .sized (.array τ' n)) ∨ τ = .slice τ') (hc : τ'.copyable = true) :
      Typing sig (.comp Θ Γ (.index p a) τ' Γ')
  /-- `T-AssignDeref` -/
  | assignDeref {S : Ctx} (Θ : TempTy S) (Γ Γ₁ Γ' : StackTy S) (p : PExpr S) (a : Atom sig S)
      (L : List (Loan S)) (τn τo : Ty S) (ρs : List (Region S))
      (ha : Typing sig (.atom Θ Γ a τn Γ₁))
      (htc : PlaceTy Γ₁ .uniq p.toAbs (.sized τo) ρs)
      (hr : Rewrite Θ .combine Γ₁ τn τo Γ')
      (hsafe : OwnSafe Θ Γ' .uniq [] p.toAbs L) :
      Typing sig (.comp Θ Γ (.assign p a) Ty.unit Γ')
  /-- `T-Assign` -/
  | assign {S : Ctx} (Θ : TempTy S) (Γ Γ₁ Γ' Γ'' : StackTy S) (p : PExpr S) (a : Atom sig S)
      (π : APlace S) (τ : Ty S) (τx : MTy S)
      (ha : Typing sig (.atom Θ Γ a τ Γ₁))
      (hp : p.toAbs = π.toExpr)
      (hx : Γ₁.placeTy π = some τx)
      (huniq : ∀ r ω τ', τx = .init (.ref (.conc r) ω τ') → RgnUniqueTo r π Γ₁)
      (hr : RewriteM Θ .noop (Γ₁.rsub π.derefExpr) τ τx Γ')
      (hsafe : τx.IsDead ∨ OwnSafe Θ Γ' .uniq [] π.toExpr [⟨.uniq, π.toExpr⟩])
      (hΓ'' : Γ'.setPlaceTy π (.init τ) = some Γ'') :
      Typing sig (.comp Θ Γ (.assign p a) Ty.unit Γ'')
  /-- `T-Closure`.  The closure captures the frame `f` given by `c` (variables and
  regions of the current scope); its body, parameter types and return type are
  written in the closure's own scope, whose outer binders stand for `θ`.  Every
  binder the body can mention through `θ` must occur in the closure's type
  (`Inst.Covered`), so that the closure value can be strengthened past any binder
  its type does not mention.  The capture list names every variable and region
  at most once (`Cap.Nodup`).  Captured regions must not occur in the signature.
  The captured non-copyable variables become dead, and the opened body is checked
  in a new frame holding the parameters on top of the captured frame `Φc`; that
  frame must then be poppable. -/
  | closure {S : Ctx} (Θ : TempTy S) (Γ Γ' : StackTy S) (f : Ctx) (c : Cap S f) (o : Ctx)
      (θ : Inst o S) (k : Nat) (ps : Fin k → Ty o) (ret : Ty o)
      (body : Term sig (vars k ++ (f ++ .frame :: o))) (Φc : FrameTy (f ++ .frame :: S) f)
      (Γb : StackTy (vars k ++ (f ++ .frame :: S)))
      (hΦc : capturedFrame Γ c = some Φc) (hnodup : c.Nodup)
      (hsig : ∀ r ∈ c.rgns, r ∉ (List.ofFn (θ.tys ps)).flatMap Ty.frgns ++ (θ.ty ret).frgns)
      (hparams : ∀ r ∈ (List.ofFn (θ.tys ps)).flatMap Ty.frgns ++ (θ.ty ret).frgns, Γ.loans r = [])
      (hcov : θ.Covered (θ.closureTy ps ret (.frame f Φc)))
      (hb : Typing sig (.expr (Θ.rename (TRen.frameRen k f S)) (closureBodyTy (killNC Γ c) Φc (θ.tys ps))
        (body.openBody θ.toTSub) ((θ.ty ret).rename (TRen.frameRen k f S)) Γb))
      (hpop : (gcLoans ((Θ ++ θ.ty ret :: List.ofFn (θ.tys ps)).rename (TRen.frameRen k f S)) Γb).popFrame
        k f = some Γ') :
      Typing sig (.comp Θ Γ (.closure f c o θ k ps ret body) (θ.closureTy ps ret (.frame f Φc)) Γ')
  /-- `T-AppFunction`: `δ = [Φ̄/φ̄][ρ̄/ϱ̄][τ̄/ᾱ]` (the bounds `ϱ₁ : ϱ₂` are checked as
  `δ(ϱ₁) :> δ(ϱ₂)`) -/
  | appFn {S : Ctx} (Θ : TempTy S) (Γ Γ₀ Γₙ Γb : StackTy S) (a : Atom sig S) (b : Binders)
      (θ : TArgs b S) (k : Nat) (args : Fin k → Atom sig S) (ps : Fin k → Ty (b.ctx ++ S))
      (τf : Ty (b.ctx ++ S)) (bs : List (Fin b.nϱ × Fin b.nϱ))
      (hΦs : ∀ i, EnvWF Γ (θ.frames i)) (hτs : ∀ i, TyWF Γ (θ.tys i))
      (hf : Typing sig (.atom Θ Γ a (.fn b k ps τf .empty bs) Γ₀))
      (hargs : Typing sig (.args Θ Γ₀ (List.ofFn args) (List.ofFn fun i => (ps i).inst θ) Γₙ))
      (hnrb : ∀ i, ∀ r ∈ ((ps i).inst θ).frgns, NotReborrowed Γₙ r)
      (hbounds : OutlivesMany Θ .combine Γₙ
        (bs.map fun p => ((b.absAt p.1).inst θ, (b.absAt p.2).inst θ)) Γb) :
      Typing sig (.comp Θ Γ (.app a b θ k args) (τf.inst θ) Γb)
  /-- `T-AppClosure` -/
  | appClosure {S : Ctx} (Θ : TempTy S) (Γ Γ₀ Γₙ : StackTy S) (a : Atom sig S) (k : Nat)
      (args : Fin k → Atom sig S) (ps : Fin k → Ty S) (τf : Ty S) (Φc : FrameExpr S)
      (θ : TArgs {} S)
      (hf : Typing sig (.atom Θ Γ a (Ty.closure k ps τf Φc) Γ₀))
      (hargs : Typing sig (.argsRw Θ Γ₀ (List.ofFn args) (List.ofFn ps) Γₙ))
      (hnrb : ∀ i, ∀ r ∈ (ps i).frgns, NotReborrowed Γₙ r) :
      Typing sig (.comp Θ Γ (.app a {} θ k args) τf Γₙ)
  /-- `T-Tuple` -/
  | tuple {S : Ctx} (Θ : TempTy S) (Γ Γ' : StackTy S) (k : Nat) (as : Fin k → Atom sig S)
      (τs : Fin k → Ty S) (h : Typing sig (.args Θ Γ (List.ofFn as) (List.ofFn τs) Γ')) :
      Typing sig (.comp Θ Γ (.tuple k as) (.tuple k τs) Γ')
  /-- `T-Array` -/
  | array {S : Ctx} (Θ : TempTy S) (Γ Γ' : StackTy S) (k : Nat) (as : Fin k → Atom sig S) (τ : Ty S)
      (h : Typing sig (.args Θ Γ (List.ofFn as) (List.replicate k τ) Γ')) :
      Typing sig (.comp Θ Γ (.array k as) (.array τ k) Γ')
  /-- `T-Left` -/
  | inl {S : Ctx} (Θ : TempTy S) (Γ Γ' : StackTy S) (τ₁ τ₂ : Ty S) (a : Atom sig S)
      (h : Typing sig (.atom Θ Γ a τ₁ Γ')) :
      Typing sig (.comp Θ Γ (.inl τ₁ τ₂ a) (.sum τ₁ τ₂) Γ')
  /-- `T-Right` -/
  | inr {S : Ctx} (Θ : TempTy S) (Γ Γ' : StackTy S) (τ₁ τ₂ : Ty S) (a : Atom sig S)
      (h : Typing sig (.atom Θ Γ a τ₂ Γ')) :
      Typing sig (.comp Θ Γ (.inr τ₁ τ₂ a) (.sum τ₁ τ₂) Γ')
  /-- `T-Abort` -/
  | abort {S : Ctx} (Θ : TempTy S) (Γ : StackTy S) (s : String) (τ : Ty S) :
      Typing sig (.comp Θ Γ (.abort s) τ Γ)
  /-- `T-LetRegion`: the body is typed with a fresh region `r ↦ {}`, which is then
  popped. -/
  | letrgn {S : Ctx} (Θ : TempTy S) (Γ Γ' : StackTy S) (Γ₁ : StackTy (.rgn :: S))
      (e : Term sig (.rgn :: S)) (τ₁ : Ty (.rgn :: S)) (τ : Ty S)
      (h : Typing sig (.expr (Θ.rename (TRen.wk S .rgn)) (Γ.pushRgn []) e τ₁ Γ₁))
      (hpop : (gcLoans (τ₁ :: Θ.rename (TRen.wk S .rgn)) Γ₁).popL [.rgn] = some Γ')
      (hτ : τ₁.prename (PRen.drop S .rgn) = some τ) :
      Typing sig (.comp Θ Γ (.letrgn e) τ Γ')
  /-- `T-Branch` -/
  | ite {S : Ctx} (Θ : TempTy S) (Γ Γ₁ Γ₂ Γ₃ Γ₂' Γ₃' Γ' : StackTy S) (a : Atom sig S)
      (e₁ e₂ : Term sig S) (τ τ₂ τ₃ : Ty S)
      (ha : Typing sig (.atom Θ Γ a Ty.bool Γ₁))
      (h₂ : Typing sig (.expr Θ Γ₁ e₁ τ₂ Γ₂)) (h₃ : Typing sig (.expr Θ Γ₁ e₂ τ₃ Γ₃))
      (hτ : τ = τ₂ ∨ τ = τ₃)
      (hr₂ : Rewrite Θ .combine Γ₂ τ₂ τ Γ₂') (hr₃ : Rewrite Θ .combine Γ₃ τ₃ τ Γ₃')
      (hu : StackTy.union Γ₂' Γ₃' = some Γ') :
      Typing sig (.comp Θ Γ (.ite a e₁ e₂) τ Γ')
  /-- `T-While` -/
  | whileE {S : Ctx} (Θ : TempTy S) (Γ Γ₁ Γ₂ : StackTy S) (e₁ e₂ : Term sig S)
      (h₁ : Typing sig (.expr Θ Γ e₁ Ty.bool Γ₁)) (h₂ : Typing sig (.expr Θ Γ₁ e₂ Ty.unit Γ₂))
      (h₁' : Typing sig (.expr Θ Γ₂ e₁ Ty.bool Γ₂)) (h₂' : Typing sig (.expr Θ Γ₂ e₂ Ty.unit Γ₂)) :
      Typing sig (.comp Θ Γ (.whileE e₁ e₂) Ty.unit Γ₂)
  /-- `T-ForArray` -/
  | forArray {S : Ctx} (Θ : TempTy S) (Γ Γ₁ : StackTy S) (Γ₂ : StackTy (.var :: S)) (a : Atom sig S)
      (e : Term sig (.var :: S)) (τ : Ty S) (n : Nat)
      (ha : Typing sig (.atom Θ Γ a (.array τ n) Γ₁))
      (hnrb : ∀ r ∈ τ.frgns, NotReborrowed Γ₁ r)
      (h₂ : Typing sig (.expr (Θ.rename (TRen.wk S .var)) (Γ₁.pushVar (.init (τ.wk .var))) e Ty.unit Γ₂))
      (hdead : (Γ₂.varTy .here).IsDead)
      (hpop : (gcLoans (Θ.rename (TRen.wk S .var)) Γ₂).popL [.var] = some Γ₁) :
      Typing sig (.comp Θ Γ (.forE a e) Ty.unit Γ₁)
  /-- `T-ForSlice` -/
  | forSlice {S : Ctx} (Θ : TempTy S) (Γ Γ₁ : StackTy S) (Γ₂ : StackTy (.var :: S)) (a : Atom sig S)
      (e : Term sig (.var :: S)) (ρ : Region S) (ω : Own) (τ : Ty S)
      (ha : Typing sig (.atom Θ Γ a (.ref ρ ω (.slice τ)) Γ₁))
      (hnrb : ∀ r ∈ (Ty.ref ρ ω (.sized τ)).frgns, NotReborrowed Γ₁ r)
      (h₂ : Typing sig (.expr (Θ.rename (TRen.wk S .var))
        (Γ₁.pushVar (.init ((Ty.ref ρ ω (.sized τ)).wk .var))) e Ty.unit Γ₂))
      (hpop : (gcLoans (Θ.rename (TRen.wk S .var)) Γ₂).popL [.var] = some Γ₁) :
      Typing sig (.comp Θ Γ (.forE a e) Ty.unit Γ₁)
  /-- `T-Match` -/
  | matchE {S : Ctx} (Θ : TempTy S) (Γ Γ' Γ₁p Γ₂p Γ₁' Γ₂' Γ'' : StackTy S)
      (Γ₁ Γ₂ : StackTy (.var :: S)) (a : Atom sig S) (e₁ e₂ : Term sig (.var :: S))
      (τl τr τ τ₁' τ₂' : Ty S) (τ₁ τ₂ : Ty (.var :: S))
      (ha : Typing sig (.atom Θ Γ a (.sum τl τr) Γ'))
      (hnrb : ∀ r ∈ (Ty.sum τl τr).frgns, NotReborrowed Γ' r)
      (h₁ : Typing sig (.expr (Θ.rename (TRen.wk S .var)) (Γ'.pushVar (.init (τl.wk .var))) e₁ τ₁ Γ₁))
      (h₂ : Typing sig (.expr (Θ.rename (TRen.wk S .var)) (Γ'.pushVar (.init (τr.wk .var))) e₂ τ₂ Γ₂))
      (hd₁ : (Γ₁.varTy .here).IsDead) (hd₂ : (Γ₂.varTy .here).IsDead)
      (hpop₁ : (gcLoans (τ₁ :: Θ.rename (TRen.wk S .var)) Γ₁).popL [.var] = some Γ₁p)
      (hpop₂ : (gcLoans (τ₂ :: Θ.rename (TRen.wk S .var)) Γ₂).popL [.var] = some Γ₂p)
      (hτ₁ : τ₁.prename (PRen.drop S .var) = some τ₁')
      (hτ₂ : τ₂.prename (PRen.drop S .var) = some τ₂')
      (hτ : τ = τ₁' ∨ τ = τ₂')
      (hr₁ : Rewrite Θ .combine Γ₁p τ₁' τ Γ₁') (hr₂ : Rewrite Θ .combine Γ₂p τ₂' τ Γ₂')
      (hu : StackTy.union Γ₁' Γ₂' = some Γ'') :
      Typing sig (.comp Θ Γ (.matchE a e₁ e₂) τ Γ'')
  /-- `T-Drop`: an initialized place may be dropped before any computation -/
  | drop {S : Ctx} (Θ : TempTy S) (Γ Γd Γf : StackTy S) (π : APlace S) (τπ τ : Ty S) (c : Comp sig S)
      (hπ : Γ.placeTyI π = some τπ) (hd : Γ.setPlaceTy π (.dead τπ) = some Γd)
      (h : Typing sig (.comp Θ Γd c τ Γf)) :
      Typing sig (.comp Θ Γ c τ Γf)
  -- ## Terms `Σ; Δ; Γ; Θ ⊢ e : τ ⇒ Γ'`
  /-- a computation in tail position -/
  | ret {S : Ctx} (Θ : TempTy S) (Γ Γ' : StackTy S) (c : Comp sig S) (τ : Ty S)
      (h : Typing sig (.comp Θ Γ c τ Γ')) : Typing sig (.expr Θ Γ (.ret c) τ Γ')
  /-- `T-Let`: the variable must be dead at the end of the body, and is then
  popped. -/
  | letE {S : Ctx} (Θ : TempTy S) (Γ Γ₁ Γ₁' Γ' : StackTy S) (Γ₂ : StackTy (.var :: S))
      (τa τ₁ τ : Ty S) (τ₂ : Ty (.var :: S)) (c : Comp sig S) (e : Term sig (.var :: S))
      (h₁ : Typing sig (.comp Θ Γ c τ₁ Γ₁))
      (hr : Rewrite Θ .combine Γ₁ τ₁ τa Γ₁')
      (hnrb : ∀ r ∈ τa.frgns, NotReborrowed Γ₁' r)
      (h₂ : Typing sig (.expr (Θ.rename (TRen.wk S .var))
        (gcLoans (Θ.rename (TRen.wk S .var)) (Γ₁'.pushVar (.init (τa.wk .var)))) e τ₂ Γ₂))
      (hdead : (Γ₂.varTy .here).IsDead)
      (hpop : (gcLoans (τ₂ :: Θ.rename (TRen.wk S .var)) Γ₂).popL [.var] = some Γ')
      (hτ : τ₂.prename (PRen.drop S .var) = some τ) :
      Typing sig (.expr Θ Γ (.letE τa c e) τ Γ')
  /-- `T-Seq` -/
  | seq {S : Ctx} (Θ : TempTy S) (Γ Γ₁ Γ₂ : StackTy S) (c : Comp sig S) (e : Term sig S) (τ₁ τ₂ : Ty S)
      (h₁ : Typing sig (.comp Θ Γ c τ₁ Γ₁)) (h₂ : Typing sig (.expr Θ (gcLoans Θ Γ₁) e τ₂ Γ₂)) :
      Typing sig (.expr Θ Γ (.seq c e) τ₂ Γ₂)
  -- ## Argument lists (atoms): the `i`-th atom is typed with the types of the
  -- previous ones added to `Θ`.
  | argsNil {S : Ctx} (Θ : TempTy S) (Γ : StackTy S) : Typing sig (.args Θ Γ [] [] Γ)
  | argsCons {S : Ctx} (Θ : TempTy S) (Γ Γ₁ Γ₂ : StackTy S) (a : Atom sig S) (as : List (Atom sig S))
      (τ : Ty S) (τs : List (Ty S)) (h : Typing sig (.atom Θ Γ a τ Γ₁))
      (t : Typing sig (.args (Θ ++ [τ]) Γ₁ as τs Γ₂)) :
      Typing sig (.args Θ Γ (a :: as) (τ :: τs) Γ₂)
  -- ## Closure arguments (`T-AppClosure`): each argument is rewritten with mode `⊞`.
  | argsRwNil {S : Ctx} (Θ : TempTy S) (Γ : StackTy S) : Typing sig (.argsRw Θ Γ [] [] Γ)
  | argsRwCons {S : Ctx} (Θ : TempTy S) (Γ Γ₁ Γ₁' Γ₂ : StackTy S) (a : Atom sig S)
      (as : List (Atom sig S)) (τ' τ : Ty S) (τs : List (Ty S)) (h : Typing sig (.atom Θ Γ a τ' Γ₁))
      (hr : Rewrite Θ .combineUnrest Γ₁ τ' τ Γ₁')
      (t : Typing sig (.argsRw (Θ ++ [τ]) Γ₁' as τs Γ₂)) :
      Typing sig (.argsRw Θ Γ (a :: as) (τ :: τs) Γ₂)
  -- ## Values `Σ; Δ; Γ; Θ ⊢ v : τ ⇒ Γ` (values never change the stack typing).
  /-- `T-Unit`, `T-u32`, `T-True`, `T-False`: a constant has its base type -/
  | vPrim {S : Ctx} (Θ : TempTy S) (Γ : StackTy S) {b : BaseTy} (c : Prim b) :
      Typing sig (.val Θ Γ (.prim c) (.base b))
  /-- `T-Function` -/
  | vFn {S : Ctx} (Θ : TempTy S) (Γ : StackTy S) (f : FnIdx sig) :
      Typing sig (.val Θ Γ (.fn f) f.get.ty)
  /-- tuple values (`T-Tuple`) -/
  | vTuple {S : Ctx} (Θ : TempTy S) (Γ : StackTy S) (k : Nat) (vs : Fin k → Value sig S)
      (τs : Fin k → Ty S) (h : Typing sig (.vals Θ Γ (List.ofFn vs) (List.ofFn τs))) :
      Typing sig (.val Θ Γ (.tuple k vs) (.tuple k τs))
  /-- array values (`T-Array`) -/
  | vArray {S : Ctx} (Θ : TempTy S) (Γ : StackTy S) (k : Nat) (vs : Fin k → Value sig S) (τ : Ty S)
      (h : Typing sig (.vals Θ Γ (List.ofFn vs) (List.replicate k τ))) :
      Typing sig (.val Θ Γ (.array k vs) (.array τ k))
  /-- `T-Pointer` -/
  | vPtr {S : Ctx} (Θ : TempTy S) (Γ : StackTy S) (R : Referent S) (r : In .rgn S) (ω : Own)
      (τ : XTy S) (hR : RefTy Γ R τ) (hl : (⟨ω, R.base.toExpr⟩ : Loan S) ∈ Γ.loans r) :
      Typing sig (.val Θ Γ (.ptr R) (.ref (.conc r) ω τ))
  /-- `T-ClosureValue` (together with `WF-Frame` for the captured frame): the
  captured values have the types of the captured frame `Φc`, the binders the body
  can mention occur in the type, and the opened body is checked in a new frame
  holding the parameters on top of the captured frame. -/
  | vClosure {S : Ctx} (Θ : TempTy S) (Γ : StackTy S) (f : Ctx) (env : Env sig S f) (o : Ctx)
      (θ : Inst o S) (k : Nat) (ps : Fin k → Ty o) (ret : Ty o)
      (body : Term sig (vars k ++ (f ++ .frame :: o))) (Φc : FrameTy (f ++ .frame :: S) f)
      (Γb : StackTy (vars k ++ (f ++ .frame :: S)))
      (henv : Typing sig (.env (Γ.pushFrame Φc) (TRen.wkFrame f S) env Φc))
      (hcov : θ.Covered (θ.closureTy ps ret (.frame f Φc)))
      (hb : Typing sig (.expr (Θ.rename (TRen.frameRen k f S)) (closureBodyTy Γ Φc (θ.tys ps))
        (body.openBody θ.toTSub) ((θ.ty ret).rename (TRen.frameRen k f S)) Γb))
      (hpop : ((gcLoans ((Θ ++ θ.ty ret :: List.ofFn (θ.tys ps)).rename (TRen.frameRen k f S)) Γb).popFrame
        k f).isSome) :
      Typing sig (.val Θ Γ (.closure f env o θ k ps ret body) (θ.closureTy ps ret (.frame f Φc)))
  /-- `T-Left` on values -/
  | vInl {S : Ctx} (Θ : TempTy S) (Γ : StackTy S) (τ₁ τ₂ : Ty S) (v : Value sig S)
      (h : Typing sig (.val Θ Γ v τ₁)) : Typing sig (.val Θ Γ (.inl τ₁ τ₂ v) (.sum τ₁ τ₂))
  /-- `T-Right` on values -/
  | vInr {S : Ctx} (Θ : TempTy S) (Γ : StackTy S) (τ₁ τ₂ : Ty S) (v : Value sig S)
      (h : Typing sig (.val Θ Γ v τ₂)) : Typing sig (.val Θ Γ (.inr τ₁ τ₂ v) (.sum τ₁ τ₂))
  -- ## Maybe-unsized values (what a pointer may point to)
  | xSized {S : Ctx} (Θ : TempTy S) (Γ : StackTy S) (v : Value sig S) (τ : Ty S)
      (h : Typing sig (.val Θ Γ v τ)) : Typing sig (.xval Θ Γ v (.sized τ))
  /-- slice values (`T-Slice`) -/
  | xSlice {S : Ctx} (Θ : TempTy S) (Γ : StackTy S) (k : Nat) (vs : Fin k → Value sig S) (τ : Ty S)
      (h : Typing sig (.vals Θ Γ (List.ofFn vs) (List.replicate k τ))) :
      Typing sig (.xval Θ Γ (.slice k vs) (.slice τ))
  -- ## Maybe-dead values (the contents of stack slots)
  | mInit {S : Ctx} (Γ : StackTy S) (v : Value sig S) (τ : Ty S) (h : Typing sig (.val [] Γ v τ)) :
      Typing sig (.mval Γ v (.init τ))
  /-- `T-Dead`: any value has any dead type -/
  | mDead {S : Ctx} (Γ : StackTy S) (v : Value sig S) (τ : Ty S) : Typing sig (.mval Γ v (.dead τ))
  /-- partially moved tuples -/
  | mTuple {S : Ctx} (Γ : StackTy S) (k : Nat) (vs : Fin k → Value sig S) (ms : Fin k → MTy S)
      (h : ∀ i, Typing sig (.mval Γ (vs i) (ms i))) : Typing sig (.mval Γ (.tuple k vs) (.tuple k ms))
  -- ## Lists of values
  | vsNil {S : Ctx} (Θ : TempTy S) (Γ : StackTy S) : Typing sig (.vals Θ Γ [] [])
  | vsCons {S : Ctx} (Θ : TempTy S) (Γ : StackTy S) (v : Value sig S) (vs : List (Value sig S)) (τ : Ty S)
      (τs : List (Ty S)) (h : Typing sig (.val Θ Γ v τ)) (t : Typing sig (.vals (Θ ++ [τ]) Γ vs τs)) :
      Typing sig (.vals Θ Γ (v :: vs) (τ :: τs))
  -- ## Captured frames: each captured value has the type of its entry
  | envNil {S T : Ctx} (Γ : StackTy T) (ρ : TRen S T) : Typing sig (.env Γ ρ (.nil : Env sig S []) .nil)
  | envVar {S T f : Ctx} (Γ : StackTy T) (ρ : TRen S T) (v : Value sig S) (ε : Env sig S f) (τ : Ty T)
      (Φ : FrameTy T f) (h : Typing sig (.val [] Γ (v.rename ρ) τ)) (t : Typing sig (.env Γ ρ ε Φ)) :
      Typing sig (.env Γ ρ (.var v ε) (.var τ Φ))
  | envRgn {S T f : Ctx} (Γ : StackTy T) (ρ : TRen S T) (ε : Env sig S f) (L : List (Loan T))
      (Φ : FrameTy T f) (t : Typing sig (.env Γ ρ ε Φ)) :
      Typing sig (.env Γ ρ (.rgn ε) (.rgn L Φ))

/-- Atom typing `Σ; Δ; Γ; Θ ⊢ a : τ ⇒ Γ'`. -/
abbrev HasTypeA (sig : Sig) {S : Ctx} (Θ : TempTy S) (Γ : StackTy S) (a : Atom sig S) (τ : Ty S)
    (Γ' : StackTy S) : Prop := Typing sig (.atom Θ Γ a τ Γ')

/-- Computation typing `Σ; Δ; Γ; Θ ⊢ c : τ ⇒ Γ'`. -/
abbrev HasTypeC (sig : Sig) {S : Ctx} (Θ : TempTy S) (Γ : StackTy S) (c : Comp sig S) (τ : Ty S)
    (Γ' : StackTy S) : Prop := Typing sig (.comp Θ Γ c τ Γ')

/-- Term typing `Σ; Δ; Γ; Θ ⊢ e : τ ⇒ Γ'`. -/
abbrev HasType (sig : Sig) {S : Ctx} (Θ : TempTy S) (Γ : StackTy S) (e : Term sig S) (τ : Ty S)
    (Γ' : StackTy S) : Prop := Typing sig (.expr Θ Γ e τ Γ')

/-- Typing of argument lists (lists of atoms). -/
abbrev HasTypeArgs (sig : Sig) {S : Ctx} (Θ : TempTy S) (Γ : StackTy S) (as : List (Atom sig S))
    (τs : List (Ty S)) (Γ' : StackTy S) : Prop := Typing sig (.args Θ Γ as τs Γ')

/-- Value typing `Σ; Δ; Γ; Θ ⊢ v : τ ⇒ Γ`. -/
abbrev HasTypeV (sig : Sig) {S : Ctx} (Θ : TempTy S) (Γ : StackTy S) (v : Value sig S) (τ : Ty S) :
    Prop := Typing sig (.val Θ Γ v τ)

/-- Typing of the content of a stack slot (maybe dead). -/
abbrev HasTypeM (sig : Sig) {S : Ctx} (Γ : StackTy S) (v : Value sig S) (τ : MTy S) : Prop :=
  Typing sig (.mval Γ v τ)

/-- Typing of lists of values. -/
abbrev HasTypeVs (sig : Sig) {S : Ctx} (Θ : TempTy S) (Γ : StackTy S) (vs : List (Value sig S))
    (τs : List (Ty S)) : Prop := Typing sig (.vals Θ Γ vs τs)

end Oxide
