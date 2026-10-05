module

public import RequestProject.Oxide.Metafunctions.Stacks

/-!
# Oxide: operational semantics as an abstract machine

The small-step semantics `Σ ⊢ (σ; e) → (σ'; e')` of the paper (appendix
"Dynamics") as a continuation-based (CK-style) machine for terms in A-normal
form.  A configuration `⟨S, σ, e, κ⟩` (`Config`) consists of a stack, a term in
focus and a continuation, all in scope `S`.  A finished computation is the term
`Term.val v`.

* The operands of a computation are atoms, which are evaluated in one go, left to
  right (`EvalAtom`, `EvalAtoms`): a value evaluates to itself, `move π` reads `π`
  and overwrites it with `dead` (`E-Move`), `copy p` reads `p` (`E-Copy`).  So a
  computation whose operands are atoms reduces in a single step (the paper's
  reduction rules); no evaluation context is needed for operands.
* `let x : τ = c; e` and `c; e` put `c` in focus and push the rest of the term on
  the continuation; the value of `c` is then consumed by that continuation frame.
* `let`, `for`, `match`, `letrgn` and calls push a binding or a frame on the stack
  together with a continuation frame `popVar`, `popRgn` or `popFrame`, which
  replaces the paper's runtime forms `shift e`, `shiftprov e` and `framed e`.
  When the result value reaches such a frame, it is strengthened past the popped
  binders; this fails if the value still mentions them (a pointer into the
  popped frame), and then the machine is stuck.  This is the situation of the
  paper's counterexample to preservation, which here cannot even produce a
  dangling pointer.
* `while e₁ { e₂ }` evaluates its condition (a term) under the continuation frame
  `Cont.whileE`.
* `abort!` stops the machine (`E-EvalCtxAbort`).

* Every use of a place says whether it moves or copies (`Atom.move`,
  `Atom.copy`), so `E-Move` and `E-Copy` never compete; `E-Move` takes a place
  (no dereference) by construction.
* `E-Closure` is deterministic: the closure term says what it captures.

Deviations from the paper (all forced by the representation, see the README):
* `E-Closure` copies the captured values into the closure's frame (the paper
  additionally overwrites captured non-copyable variables with `dead`, which
  requires type information not available at runtime);
* slices are given by their start and their length.
-/

@[expose] public section

namespace Oxide

variable {sig : Sig}

/-! ## Evaluation of atoms -/

/-- `σ ⊢ a ⇓ v ⊣ σ'`: the atom `a` evaluates to `v`, turning the stack `σ` into
`σ'`. -/
inductive EvalAtom {S : Ctx} : Stack sig S → Atom sig S → Value sig S → Stack sig S → Prop
  /-- a value evaluates to itself -/
  | val (σ : Stack sig S) (v : Value sig S) : EvalAtom σ (.val v) v σ
  /-- `E-Move`: the place is read and overwritten with `dead` -/
  | move (σ σ' : Stack sig S) (π : TPlace S) (v : Value sig S)
      (hv : σ.read (.place π.toAbs) = some v) (hw : σ.write (.place π.toAbs) .dead = some σ') :
      EvalAtom σ (.move π) v σ'
  /-- `E-Copy` -/
  | copy (σ : Stack sig S) (p : PExpr S) (R : Referent S) (v : Value sig S)
      (hR : σ.evalPlace p = some R) (hv : σ.read R = some v) :
      EvalAtom σ (.copy p) v σ

/-- Left-to-right evaluation of a vector of atoms. -/
inductive EvalAtoms {S : Ctx} : {k : Nat} → Stack sig S → (Fin k → Atom sig S) →
    (Fin k → Value sig S) → Stack sig S → Prop
  | nil (σ : Stack sig S) (as : Fin 0 → Atom sig S) : EvalAtoms σ as Fin.elim0 σ
  | cons {k : Nat} (σ σ₁ σ₂ : Stack sig S) (as : Fin (k + 1) → Atom sig S) (v : Value sig S)
      (vs : Fin k → Value sig S) (h : EvalAtom σ (as 0) v σ₁)
      (t : EvalAtoms σ₁ (fun i => as i.succ) vs σ₂) :
      EvalAtoms σ as (Fin.cases v vs) σ₂

/-! ## Calls -/

/-- Calling a function value with argument values, continuing with `κ`.  The
number of arguments is the arity of the function by construction. -/
inductive Call (G : GlobalEnv sig) {S : Ctx} (σ : Stack sig S) (κ : Cont sig S) :
    Value sig S → (b : Binders) → TArgs b S → (k : Nat) → (Fin k → Value sig S) → Config sig → Prop
  /-- `E-AppClosure`: a new frame holding the arguments on top of the captured
  frame is pushed, and the body is opened in it. -/
  | closure (f : Ctx) (env : Env sig S f) (o : Ctx) (θ : Inst o S) (k : Nat) (ps : Fin k → Ty o)
      (ret : Ty o) (body : Term sig (vars k ++ (f ++ .frame :: o))) (b : Binders) (θa : TArgs b S)
      (vs : Fin k → Value sig S) :
      Call G σ κ (.closure f env o θ k ps ret body) b θa k vs
        ⟨vars k ++ (f ++ .frame :: S), σ.pushFrame vs env, body.openBody θ.toTSub, .popFrame k f κ⟩
  /-- `E-AppFunction`: the instantiated body runs in a new frame holding the
  arguments. -/
  | fn (fn : FnIdx sig) (θa : TArgs fn.get.binders S) (vs : Fin fn.get.k → Value sig S) :
      Call G σ κ (.fn fn) fn.get.binders θa fn.get.k vs
        ⟨vars fn.get.k ++ ([] ++ .frame :: S), σ.pushFrame vs .nil, G.instBody fn θa,
          .popFrame fn.get.k [] κ⟩

/-! ## Steps -/

/-- `Σ ⊢ (σ; e) → (σ'; e')`: one step of the machine. -/
inductive Step (G : GlobalEnv sig) : Config sig → Config sig → Prop
  -- ## Atoms in tail position
  /-- `E-Move` -/
  | move {S : Ctx} (σ σ' : Stack sig S) (π : TPlace S) (κ : Cont sig S) (v : Value sig S)
      (hv : σ.read (.place π.toAbs) = some v) (hw : σ.write (.place π.toAbs) .dead = some σ') :
      Step G ⟨S, σ, .ret (.atom (.move π)), κ⟩ ⟨S, σ', .val v, κ⟩
  /-- `E-Copy` -/
  | copy {S : Ctx} (σ : Stack sig S) (p : PExpr S) (κ : Cont sig S) (R : Referent S) (v : Value sig S)
      (hR : σ.evalPlace p = some R) (hv : σ.read R = some v) :
      Step G ⟨S, σ, .ret (.atom (.copy p)), κ⟩ ⟨S, σ, .val v, κ⟩
  -- ## Places and borrows
  /-- `E-Borrow` -/
  | borrow {S : Ctx} (σ : Stack sig S) (r : In .rgn S) (ω : Own) (p : PExpr S) (κ : Cont sig S)
      (R : Referent S) (v : Value sig S) (hR : σ.evalPlace p = some R) (hv : σ.read R = some v) :
      Step G ⟨S, σ, .ret (.borrow r ω p), κ⟩ ⟨S, σ, .val (.ptr R), κ⟩
  /-- `E-BorrowIndex` -/
  | borrowIdx {S : Ctx} (σ σ₁ : Stack sig S) r ω p (a : Atom sig S) (κ : Cont sig S) (R : Referent S)
      (k : Nat) (vs : Fin k → Value sig S) (i : UInt32) (ha : EvalAtom σ a (Value.num i) σ₁)
      (hR : σ₁.evalPlace p = some R)
      (hv : σ₁.read R = some (.array k vs) ∨ σ₁.read R = some (.slice k vs))
      (hi : i.toNat < k) :
      Step G ⟨S, σ, .ret (.borrowIdx r ω p a), κ⟩ ⟨S, σ₁, .val (.ptr (.index R i.toNat [])), κ⟩
  /-- `E-BorrowIndexOOB` -/
  | borrowIdxOOB {S : Ctx} (σ σ₁ : Stack sig S) r ω p (a : Atom sig S) (κ : Cont sig S)
      (R : Referent S) (k : Nat) (vs : Fin k → Value sig S) (i : UInt32)
      (ha : EvalAtom σ a (Value.num i) σ₁) (hR : σ₁.evalPlace p = some R)
      (hv : σ₁.read R = some (.array k vs) ∨ σ₁.read R = some (.slice k vs))
      (hi : k ≤ i.toNat) :
      Step G ⟨S, σ, .ret (.borrowIdx r ω p a), κ⟩
        ⟨S, σ₁, .abort "attempted to index out of bounds", κ⟩
  /-- `E-BorrowSlice`: `p[i..j]` is the slice of length `j - i` starting at `i` -/
  | borrowSlice {S : Ctx} (σ σ₁ σ₂ : Stack sig S) r ω p (a₁ a₂ : Atom sig S) (κ : Cont sig S)
      (R : Referent S) (k : Nat) (vs : Fin k → Value sig S) (i j : UInt32)
      (ha₁ : EvalAtom σ a₁ (Value.num i) σ₁) (ha₂ : EvalAtom σ₁ a₂ (Value.num j) σ₂)
      (hR : σ₂.evalPlace p = some R)
      (hv : σ₂.read R = some (.array k vs) ∨ σ₂.read R = some (.slice k vs))
      (hij : i.toNat ≤ j.toNat) (hj : j.toNat ≤ k) :
      Step G ⟨S, σ, .ret (.borrowSlice r ω p a₁ a₂), κ⟩
        ⟨S, σ₂, .val (.ptr (.slice R i.toNat (j.toNat - i.toNat))), κ⟩
  /-- `E-BorrowSliceOOB` -/
  | borrowSliceOOB {S : Ctx} (σ σ₁ σ₂ : Stack sig S) r ω p (a₁ a₂ : Atom sig S) (κ : Cont sig S)
      (R : Referent S) (k : Nat) (vs : Fin k → Value sig S) (i j : UInt32)
      (ha₁ : EvalAtom σ a₁ (Value.num i) σ₁) (ha₂ : EvalAtom σ₁ a₂ (Value.num j) σ₂)
      (hR : σ₂.evalPlace p = some R)
      (hv : σ₂.read R = some (.array k vs) ∨ σ₂.read R = some (.slice k vs))
      (hoob : ¬ (i.toNat ≤ j.toNat ∧ j.toNat ≤ k)) :
      Step G ⟨S, σ, .ret (.borrowSlice r ω p a₁ a₂), κ⟩
        ⟨S, σ₂, .abort "attempted to slice out of bounds", κ⟩
  /-- `E-IndexCopy` -/
  | index {S : Ctx} (σ σ₁ : Stack sig S) p (a : Atom sig S) (κ : Cont sig S) (R : Referent S)
      (k : Nat) (vs : Fin k → Value sig S) (i : UInt32) (ha : EvalAtom σ a (Value.num i) σ₁)
      (hR : σ₁.evalPlace p = some R)
      (hv : σ₁.read R = some (.array k vs) ∨ σ₁.read R = some (.slice k vs)) (hi : i.toNat < k) :
      Step G ⟨S, σ, .ret (.index p a), κ⟩ ⟨S, σ₁, .val (vs ⟨i.toNat, hi⟩), κ⟩
  /-- `E-IndexCopyOOB` -/
  | indexOOB {S : Ctx} (σ σ₁ : Stack sig S) p (a : Atom sig S) (κ : Cont sig S) (R : Referent S)
      (k : Nat) (vs : Fin k → Value sig S) (i : UInt32) (ha : EvalAtom σ a (Value.num i) σ₁)
      (hR : σ₁.evalPlace p = some R)
      (hv : σ₁.read R = some (.array k vs) ∨ σ₁.read R = some (.slice k vs)) (hi : k ≤ i.toNat) :
      Step G ⟨S, σ, .ret (.index p a), κ⟩ ⟨S, σ₁, .abort "attempted to index out of bounds", κ⟩
  /-- `E-Assign` -/
  | assign {S : Ctx} (σ σ₁ σ' : Stack sig S) p (a : Atom sig S) (κ : Cont sig S) (R : Referent S)
      (v : Value sig S) (ha : EvalAtom σ a v σ₁) (hR : σ₁.evalPlace p = some R)
      (hw : σ₁.write R v = some σ') :
      Step G ⟨S, σ, .ret (.assign p a), κ⟩ ⟨S, σ', .val Value.unit, κ⟩
  -- ## Bindings
  /-- `let x : τ = c; e`: evaluate `c` first -/
  | letPush {S : Ctx} (σ : Stack sig S) τ (c : Comp sig S) e (κ : Cont sig S) :
      Step G ⟨S, σ, .letE τ c e, κ⟩ ⟨S, σ, .ret c, .letE τ e κ⟩
  /-- `E-Let` -/
  | letE {S : Ctx} (σ : Stack sig S) τ (v : Value sig S) e (κ : Cont sig S) :
      Step G ⟨S, σ, .val v, .letE τ e κ⟩ ⟨.var :: S, σ.pushVar v, e, .popVar κ⟩
  /-- `c; e`: evaluate `c` first -/
  | seqPush {S : Ctx} (σ : Stack sig S) (c : Comp sig S) (e : Term sig S) (κ : Cont sig S) :
      Step G ⟨S, σ, .seq c e, κ⟩ ⟨S, σ, .ret c, .seq e κ⟩
  /-- `E-Seq` -/
  | seq {S : Ctx} (σ : Stack sig S) (v : Value sig S) (e : Term sig S) (κ : Cont sig S) :
      Step G ⟨S, σ, .val v, .seq e κ⟩ ⟨S, σ, e, κ⟩
  /-- `E-LetRegion`: a region marker is pushed; it is popped once the body is a
  value. -/
  | letrgn {S : Ctx} (σ : Stack sig S) (e : Term sig (.rgn :: S)) (κ : Cont sig S) :
      Step G ⟨S, σ, .ret (.letrgn e), κ⟩ ⟨.rgn :: S, σ.pushRgn, e, .popRgn κ⟩
  /-- `E-Shift`: pop the most recent variable -/
  | popVar {S : Ctx} (σ : Stack sig (.var :: S)) (v : Value sig (.var :: S)) (v' : Value sig S)
      (κ : Cont sig S) (hv : v.prename (PRen.drop S .var) = some v') :
      Step G ⟨.var :: S, σ, .val v, .popVar κ⟩ ⟨S, σ.popL [.var], .val v', κ⟩
  /-- popping a region marker (`shiftprov`) -/
  | popRgn {S : Ctx} (σ : Stack sig (.rgn :: S)) (v : Value sig (.rgn :: S)) (v' : Value sig S)
      (κ : Cont sig S) (hv : v.prename (PRen.drop S .rgn) = some v') :
      Step G ⟨.rgn :: S, σ, .val v, .popRgn κ⟩ ⟨S, σ.popL [.rgn], .val v', κ⟩
  /-- `E-Framed`: pop the frame of a call -/
  | popFrame {S : Ctx} (k : Nat) (f : Ctx) (σ : Stack sig (vars k ++ (f ++ .frame :: S)))
      (v : Value sig (vars k ++ (f ++ .frame :: S))) (v' : Value sig S) (κ : Cont sig S)
      (hv : v.popFrame k f = some v') :
      Step G ⟨vars k ++ (f ++ .frame :: S), σ, .val v, .popFrame k f κ⟩ ⟨S, σ.popFrame k f, .val v', κ⟩
  -- ## Control
  /-- `E-IfTrue` -/
  | iteTrue {S : Ctx} (σ σ₁ : Stack sig S) (a : Atom sig S) (e₁ e₂ : Term sig S) (κ : Cont sig S)
      (ha : EvalAtom σ a Value.tt σ₁) :
      Step G ⟨S, σ, .ret (.ite a e₁ e₂), κ⟩ ⟨S, σ₁, e₁, κ⟩
  /-- `E-IfFalse` -/
  | iteFalse {S : Ctx} (σ σ₁ : Stack sig S) (a : Atom sig S) (e₁ e₂ : Term sig S) (κ : Cont sig S)
      (ha : EvalAtom σ a Value.ff σ₁) :
      Step G ⟨S, σ, .ret (.ite a e₁ e₂), κ⟩ ⟨S, σ₁, e₂, κ⟩
  /-- `E-While`: evaluate the condition -/
  | whileE {S : Ctx} (σ : Stack sig S) (e₁ e₂ : Term sig S) (κ : Cont sig S) :
      Step G ⟨S, σ, .ret (.whileE e₁ e₂), κ⟩ ⟨S, σ, e₁, .whileE e₁ e₂ κ⟩
  /-- the condition holds: run the body, then the loop again -/
  | whileTrue {S : Ctx} (σ : Stack sig S) (e₁ e₂ : Term sig S) (κ : Cont sig S) :
      Step G ⟨S, σ, .val Value.tt, .whileE e₁ e₂ κ⟩ ⟨S, σ, e₂, .seq (.ret (.whileE e₁ e₂)) κ⟩
  /-- the condition fails: the loop is done -/
  | whileFalse {S : Ctx} (σ : Stack sig S) (e₁ e₂ : Term sig S) (κ : Cont sig S) :
      Step G ⟨S, σ, .val Value.ff, .whileE e₁ e₂ κ⟩ ⟨S, σ, .val Value.unit, κ⟩
  /-- `E-ForArray` -/
  | forArray {S : Ctx} (σ σ₁ : Stack sig S) (a : Atom sig S) (k : Nat) (vs : Fin (k + 1) → Value sig S)
      e (κ : Cont sig S) (ha : EvalAtom σ a (.array (k + 1) vs) σ₁) :
      Step G ⟨S, σ, .ret (.forE a e), κ⟩
        ⟨.var :: S, σ₁.pushVar (vs 0), e,
          .popVar (.seq (.ret (.forE (.val (.array k fun i => vs i.succ)) e)) κ)⟩
  /-- `E-ForEmptyArray` -/
  | forEmptyArray {S : Ctx} (σ σ₁ : Stack sig S) (a : Atom sig S) (vs : Fin 0 → Value sig S) e
      (κ : Cont sig S) (ha : EvalAtom σ a (.array 0 vs) σ₁) :
      Step G ⟨S, σ, .ret (.forE a e), κ⟩ ⟨S, σ₁, .val Value.unit, κ⟩
  /-- `E-ForSlice`: the first element of the slice `𝓡[a .. a + l + 1]` is `𝓡[a]` -/
  | forSlice {S : Ctx} (σ σ₁ : Stack sig S) (a : Atom sig S) (R : Referent S) (s l : Nat) (k : Nat)
      (vs : Fin k → Value sig S) e (κ : Cont sig S) (ha : EvalAtom σ a (.ptr (.slice R s (l + 1))) σ₁)
      (hv : σ₁.read R = some (.array k vs) ∨ σ₁.read R = some (.slice k vs)) :
      Step G ⟨S, σ, .ret (.forE a e), κ⟩
        ⟨.var :: S, σ₁.pushVar (.ptr (.index R s [])), e,
          .popVar (.seq (.ret (.forE (.val (.ptr (.slice R (s + 1) l))) e)) κ)⟩
  /-- `E-ForEmptySlice` -/
  | forEmptySlice {S : Ctx} (σ σ₁ : Stack sig S) (a : Atom sig S) (R : Referent S) (s : Nat) e
      (κ : Cont sig S) (ha : EvalAtom σ a (.ptr (.slice R s 0)) σ₁) :
      Step G ⟨S, σ, .ret (.forE a e), κ⟩ ⟨S, σ₁, .val Value.unit, κ⟩
  /-- `E-MatchLeft` -/
  | matchLeft {S : Ctx} (σ σ₁ : Stack sig S) (a : Atom sig S) τ₁ τ₂ (v : Value sig S) e₁ e₂
      (κ : Cont sig S) (ha : EvalAtom σ a (.inl τ₁ τ₂ v) σ₁) :
      Step G ⟨S, σ, .ret (.matchE a e₁ e₂), κ⟩ ⟨.var :: S, σ₁.pushVar v, e₁, .popVar κ⟩
  /-- `E-MatchRight` -/
  | matchRight {S : Ctx} (σ σ₁ : Stack sig S) (a : Atom sig S) τ₁ τ₂ (v : Value sig S) e₁ e₂
      (κ : Cont sig S) (ha : EvalAtom σ a (.inr τ₁ τ₂ v) σ₁) :
      Step G ⟨S, σ, .ret (.matchE a e₁ e₂), κ⟩ ⟨.var :: S, σ₁.pushVar v, e₂, .popVar κ⟩
  -- ## Closures and calls
  /-- `E-Closure`: the captured frame is read off the stack. -/
  | closure {S : Ctx} (σ : Stack sig S) (f : Ctx) (c : Cap S f) (o : Ctx) (θ : Inst o S) (k : Nat)
      (ps : Fin k → Ty o) (ret : Ty o) (body : Term sig (vars k ++ (f ++ .frame :: o)))
      (κ : Cont sig S) :
      Step G ⟨S, σ, .ret (.closure f c o θ k ps ret body), κ⟩
        ⟨S, σ, .val (.closure f (Env.ofCap σ c) o θ k ps ret body), κ⟩
  /-- `E-App`: the function and the arguments are evaluated, then the call is made -/
  | app {S : Ctx} (σ σ₁ σ₂ : Stack sig S) (a : Atom sig S) b θ (k : Nat) (args : Fin k → Atom sig S)
      (fv : Value sig S) (vs : Fin k → Value sig S) (κ : Cont sig S) (c : Config sig)
      (hf : EvalAtom σ a fv σ₁) (hargs : EvalAtoms σ₁ args vs σ₂) (h : Call G σ₂ κ fv b θ k vs c) :
      Step G ⟨S, σ, .ret (.app a b θ k args), κ⟩ c
  -- ## Tuples, arrays and sums
  /-- tuples -/
  | tuple {S : Ctx} (σ σ' : Stack sig S) (k : Nat) (as : Fin k → Atom sig S) (vs : Fin k → Value sig S)
      (κ : Cont sig S) (h : EvalAtoms σ as vs σ') :
      Step G ⟨S, σ, .ret (.tuple k as), κ⟩ ⟨S, σ', .val (.tuple k vs), κ⟩
  /-- arrays -/
  | array {S : Ctx} (σ σ' : Stack sig S) (k : Nat) (as : Fin k → Atom sig S) (vs : Fin k → Value sig S)
      (κ : Cont sig S) (h : EvalAtoms σ as vs σ') :
      Step G ⟨S, σ, .ret (.array k as), κ⟩ ⟨S, σ', .val (.array k vs), κ⟩
  /-- left injections -/
  | inl {S : Ctx} (σ σ' : Stack sig S) τ₁ τ₂ (a : Atom sig S) (v : Value sig S) (κ : Cont sig S)
      (h : EvalAtom σ a v σ') :
      Step G ⟨S, σ, .ret (.inl τ₁ τ₂ a), κ⟩ ⟨S, σ', .val (.inl τ₁ τ₂ v), κ⟩
  /-- right injections -/
  | inr {S : Ctx} (σ σ' : Stack sig S) τ₁ τ₂ (a : Atom sig S) (v : Value sig S) (κ : Cont sig S)
      (h : EvalAtom σ a v σ') :
      Step G ⟨S, σ, .ret (.inr τ₁ τ₂ a), κ⟩ ⟨S, σ', .val (.inr τ₁ τ₂ v), κ⟩

/-- Reflexive-transitive closure `Σ ⊢ (σ; e) →* (σ'; e')`. -/
inductive Steps (G : GlobalEnv sig) : Config sig → Config sig → Prop
  | refl (c : Config sig) : Steps G c c
  | step (c c' c'' : Config sig) (h : Step G c c') (t : Steps G c' c'') : Steps G c c''

/-- A configuration is final if it has produced its value (a value in focus and
nothing left to do) or has aborted. -/
def Config.IsFinal (c : Config sig) : Prop :=
  (∃ v, c.focus = .val v ∧ c.cont = .halt) ∨ (∃ s, c.focus = .abort s)

end Oxide
