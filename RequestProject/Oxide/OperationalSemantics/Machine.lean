module

public import RequestProject.Oxide.Metafunctions.Stacks

/-!
# Oxide: operational semantics as an abstract machine

The small-step semantics `Σ ⊢ (σ; e) → (σ'; e')` of the paper (appendix
"Dynamics") as a continuation-based (CK-style) machine.  A configuration
`⟨S, σ, e, κ⟩` (`Config`) consists of a stack, an expression in focus and a
continuation, all in scope `S`.

* A compound expression moves its first subexpression into focus and pushes the
  rest on the continuation (the paper's evaluation contexts `𝒞`).
* A value in focus is consumed by the topmost continuation frame (the paper's
  reduction rules).
* `let`, `for`, `match`, `letrgn` and calls push a binding or a frame on the stack
  together with a continuation frame `popVar`, `popRgn` or `popFrame`, which
  replaces the paper's runtime forms `shift e`, `shiftprov e` and `framed e`.
  When the result value reaches such a frame, it is strengthened past the popped
  binders; this fails if the value still mentions them (a pointer into the
  popped frame), and then the machine is stuck.  This is the situation of the
  paper's counterexample to preservation, which here cannot even produce a
  dangling pointer.
* `abort!` stops the machine (`E-EvalCtxAbort`).

* Every use of a place says whether it moves or copies (`Term.move`,
  `Term.copy`), so `E-Move` and `E-Copy` never compete; `E-Move` takes a place
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

/-- Append an element to a vector. -/
def vsnoc {α : Type} {n : Nat} (xs : Fin n → α) (x : α) : Fin (n + 1) → α :=
  fun t => if h : t.val < n then xs ⟨t.val, h⟩ else x

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

/-- `Σ ⊢ (σ; e) → (σ'; e')`: one step of the machine. -/
inductive Step (G : GlobalEnv sig) : Config sig → Config sig → Prop
  -- ## Places and borrows
  /-- `E-Move`: the place is read and overwritten with `dead` -/
  | move {S : Ctx} (σ σ' : Stack sig S) (π : TPlace S) (κ : Cont sig S) (v : Value sig S)
      (hv : σ.read (.place π.toAbs) = some v) (hw : σ.write (.place π.toAbs) .dead = some σ') :
      Step G ⟨S, σ, .move π, κ⟩ ⟨S, σ', .val v, κ⟩
  /-- `E-Copy` -/
  | copy {S : Ctx} (σ : Stack sig S) (p : PExpr S) (κ : Cont sig S) (R : Referent S) (v : Value sig S)
      (hR : σ.evalPlace p = some R) (hv : σ.read R = some v) :
      Step G ⟨S, σ, .copy p, κ⟩ ⟨S, σ, .val v, κ⟩
  /-- `E-Borrow` -/
  | borrow {S : Ctx} (σ : Stack sig S) (r : In .rgn S) (ω : Own) (p : PExpr S) (κ : Cont sig S)
      (R : Referent S) (v : Value sig S) (hR : σ.evalPlace p = some R) (hv : σ.read R = some v) :
      Step G ⟨S, σ, .borrow r ω p, κ⟩ ⟨S, σ, .val (.ptr R), κ⟩
  | borrowIdxPush {S : Ctx} (σ : Stack sig S) r ω p (e : Term sig S) (κ : Cont sig S) :
      Step G ⟨S, σ, .borrowIdx r ω p e, κ⟩ ⟨S, σ, e, .borrowIdx r ω p κ⟩
  /-- `E-BorrowIndex` -/
  | borrowIdx {S : Ctx} (σ : Stack sig S) r ω p (κ : Cont sig S) (R : Referent S) (k : Nat)
      (vs : Fin k → Value sig S) (i : UInt32)
      (hR : σ.evalPlace p = some R) (hv : σ.read R = some (.array k vs) ∨ σ.read R = some (.slice k vs))
      (hi : i.toNat < k) :
      Step G ⟨S, σ, .val (Value.num i), .borrowIdx r ω p κ⟩
        ⟨S, σ, .val (.ptr (.index R i.toNat [])), κ⟩
  /-- `E-BorrowIndexOOB` -/
  | borrowIdxOOB {S : Ctx} (σ : Stack sig S) r ω p (κ : Cont sig S) (R : Referent S) (k : Nat)
      (vs : Fin k → Value sig S) (i : UInt32)
      (hR : σ.evalPlace p = some R) (hv : σ.read R = some (.array k vs) ∨ σ.read R = some (.slice k vs))
      (hi : k ≤ i.toNat) :
      Step G ⟨S, σ, .val (Value.num i), .borrowIdx r ω p κ⟩
        ⟨S, σ, .abort "attempted to index out of bounds", κ⟩
  | borrowSlicePush {S : Ctx} (σ : Stack sig S) r ω p (e₁ e₂ : Term sig S) (κ : Cont sig S) :
      Step G ⟨S, σ, .borrowSlice r ω p e₁ e₂, κ⟩ ⟨S, σ, e₁, .borrowSlice₁ r ω p e₂ κ⟩
  | borrowSliceNext {S : Ctx} (σ : Stack sig S) r ω p (e₂ : Term sig S) (v : Value sig S)
      (κ : Cont sig S) :
      Step G ⟨S, σ, .val v, .borrowSlice₁ r ω p e₂ κ⟩ ⟨S, σ, e₂, .borrowSlice₂ r ω p v κ⟩
  /-- `E-BorrowSlice`: `p[i..j]` is the slice of length `j - i` starting at `i` -/
  | borrowSlice {S : Ctx} (σ : Stack sig S) r ω p (κ : Cont sig S) (R : Referent S) (k : Nat)
      (vs : Fin k → Value sig S) (i j : UInt32)
      (hR : σ.evalPlace p = some R) (hv : σ.read R = some (.array k vs) ∨ σ.read R = some (.slice k vs))
      (hij : i.toNat ≤ j.toNat) (hj : j.toNat ≤ k) :
      Step G ⟨S, σ, .val (Value.num j), .borrowSlice₂ r ω p (Value.num i) κ⟩
        ⟨S, σ, .val (.ptr (.slice R i.toNat (j.toNat - i.toNat))), κ⟩
  /-- `E-BorrowSliceOOB` -/
  | borrowSliceOOB {S : Ctx} (σ : Stack sig S) r ω p (κ : Cont sig S) (R : Referent S) (k : Nat)
      (vs : Fin k → Value sig S) (i j : UInt32)
      (hR : σ.evalPlace p = some R) (hv : σ.read R = some (.array k vs) ∨ σ.read R = some (.slice k vs))
      (hoob : ¬ (i.toNat ≤ j.toNat ∧ j.toNat ≤ k)) :
      Step G ⟨S, σ, .val (Value.num j), .borrowSlice₂ r ω p (Value.num i) κ⟩
        ⟨S, σ, .abort "attempted to slice out of bounds", κ⟩
  | indexPush {S : Ctx} (σ : Stack sig S) p (e : Term sig S) (κ : Cont sig S) :
      Step G ⟨S, σ, .index p e, κ⟩ ⟨S, σ, e, .index p κ⟩
  /-- `E-IndexCopy` -/
  | index {S : Ctx} (σ : Stack sig S) p (κ : Cont sig S) (R : Referent S) (k : Nat)
      (vs : Fin k → Value sig S) (i : UInt32) (hR : σ.evalPlace p = some R)
      (hv : σ.read R = some (.array k vs) ∨ σ.read R = some (.slice k vs)) (hi : i.toNat < k) :
      Step G ⟨S, σ, .val (Value.num i), .index p κ⟩ ⟨S, σ, .val (vs ⟨i.toNat, hi⟩), κ⟩
  /-- `E-IndexCopyOOB` -/
  | indexOOB {S : Ctx} (σ : Stack sig S) p (κ : Cont sig S) (R : Referent S) (k : Nat)
      (vs : Fin k → Value sig S) (i : UInt32) (hR : σ.evalPlace p = some R)
      (hv : σ.read R = some (.array k vs) ∨ σ.read R = some (.slice k vs)) (hi : k ≤ i.toNat) :
      Step G ⟨S, σ, .val (Value.num i), .index p κ⟩ ⟨S, σ, .abort "attempted to index out of bounds", κ⟩
  | assignPush {S : Ctx} (σ : Stack sig S) p (e : Term sig S) (κ : Cont sig S) :
      Step G ⟨S, σ, .assign p e, κ⟩ ⟨S, σ, e, .assign p κ⟩
  /-- `E-Assign` -/
  | assign {S : Ctx} (σ σ' : Stack sig S) p (κ : Cont sig S) (R : Referent S) (v : Value sig S)
      (hR : σ.evalPlace p = some R) (hw : σ.write R v = some σ') :
      Step G ⟨S, σ, .val v, .assign p κ⟩ ⟨S, σ', .val Value.unit, κ⟩
  -- ## Bindings
  /-- `E-LetRegion`: a region marker is pushed; it is popped once the body is a
  value. -/
  | letrgn {S : Ctx} (σ : Stack sig S) (e : Term sig (.rgn :: S)) (κ : Cont sig S) :
      Step G ⟨S, σ, .letrgn e, κ⟩ ⟨.rgn :: S, σ.pushRgn, e, .popRgn κ⟩
  | letPush {S : Ctx} (σ : Stack sig S) τ (e₁ : Term sig S) e₂ (κ : Cont sig S) :
      Step G ⟨S, σ, .letE τ e₁ e₂, κ⟩ ⟨S, σ, e₁, .letE τ e₂ κ⟩
  /-- `E-Let` -/
  | letE {S : Ctx} (σ : Stack sig S) τ (v : Value sig S) e₂ (κ : Cont sig S) :
      Step G ⟨S, σ, .val v, .letE τ e₂ κ⟩ ⟨.var :: S, σ.pushVar v, e₂, .popVar κ⟩
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
  | seqPush {S : Ctx} (σ : Stack sig S) (e₁ e₂ : Term sig S) (κ : Cont sig S) :
      Step G ⟨S, σ, .seq e₁ e₂, κ⟩ ⟨S, σ, e₁, .seq e₂ κ⟩
  /-- `E-Seq` -/
  | seq {S : Ctx} (σ : Stack sig S) (v : Value sig S) (e₂ : Term sig S) (κ : Cont sig S) :
      Step G ⟨S, σ, .val v, .seq e₂ κ⟩ ⟨S, σ, e₂, κ⟩
  | itePush {S : Ctx} (σ : Stack sig S) (e₁ e₂ e₃ : Term sig S) (κ : Cont sig S) :
      Step G ⟨S, σ, .ite e₁ e₂ e₃, κ⟩ ⟨S, σ, e₁, .ite e₂ e₃ κ⟩
  /-- `E-IfTrue` -/
  | iteTrue {S : Ctx} (σ : Stack sig S) (e₂ e₃ : Term sig S) (κ : Cont sig S) :
      Step G ⟨S, σ, .val Value.tt, .ite e₂ e₃ κ⟩ ⟨S, σ, e₂, κ⟩
  /-- `E-IfFalse` -/
  | iteFalse {S : Ctx} (σ : Stack sig S) (e₂ e₃ : Term sig S) (κ : Cont sig S) :
      Step G ⟨S, σ, .val Value.ff, .ite e₂ e₃ κ⟩ ⟨S, σ, e₃, κ⟩
  /-- `E-While` -/
  | whileE {S : Ctx} (σ : Stack sig S) (e₁ e₂ : Term sig S) (κ : Cont sig S) :
      Step G ⟨S, σ, .whileE e₁ e₂, κ⟩ ⟨S, σ, .ite e₁ (.seq e₂ (.whileE e₁ e₂)) (.val Value.unit), κ⟩
  | forPush {S : Ctx} (σ : Stack sig S) (e₁ : Term sig S) e₂ (κ : Cont sig S) :
      Step G ⟨S, σ, .forE e₁ e₂, κ⟩ ⟨S, σ, e₁, .forE e₂ κ⟩
  /-- `E-ForArray` -/
  | forArray {S : Ctx} (σ : Stack sig S) (k : Nat) (vs : Fin (k + 1) → Value sig S) e₂ (κ : Cont sig S) :
      Step G ⟨S, σ, .val (.array (k + 1) vs), .forE e₂ κ⟩
        ⟨.var :: S, σ.pushVar (vs 0), e₂,
          .popVar (.seq (.forE (.val (.array k fun i => vs i.succ)) e₂) κ)⟩
  /-- `E-ForEmptyArray` -/
  | forEmptyArray {S : Ctx} (σ : Stack sig S) (vs : Fin 0 → Value sig S) e₂ (κ : Cont sig S) :
      Step G ⟨S, σ, .val (.array 0 vs), .forE e₂ κ⟩ ⟨S, σ, .val Value.unit, κ⟩
  /-- `E-ForSlice`: the first element of the slice `𝓡[a .. a + l + 1]` is `𝓡[a]` -/
  | forSlice {S : Ctx} (σ : Stack sig S) (R : Referent S) (a l : Nat) (k : Nat)
      (vs : Fin k → Value sig S) e₂ (κ : Cont sig S)
      (hv : σ.read R = some (.array k vs) ∨ σ.read R = some (.slice k vs)) :
      Step G ⟨S, σ, .val (.ptr (.slice R a (l + 1))), .forE e₂ κ⟩
        ⟨.var :: S, σ.pushVar (.ptr (.index R a [])), e₂,
          .popVar (.seq (.forE (.val (.ptr (.slice R (a + 1) l))) e₂) κ)⟩
  /-- `E-ForEmptySlice` -/
  | forEmptySlice {S : Ctx} (σ : Stack sig S) (R : Referent S) (a : Nat) e₂ (κ : Cont sig S) :
      Step G ⟨S, σ, .val (.ptr (.slice R a 0)), .forE e₂ κ⟩ ⟨S, σ, .val Value.unit, κ⟩
  -- ## Closures and calls
  /-- `E-Closure`: the captured frame is read off the stack. -/
  | closure {S : Ctx} (σ : Stack sig S) (f : Ctx) (c : Cap S f) (o : Ctx) (θ : Inst o S) (k : Nat)
      (ps : Fin k → Ty o) (ret : Ty o) (body : Term sig (vars k ++ (f ++ .frame :: o)))
      (κ : Cont sig S) :
      Step G ⟨S, σ, .closure f c o θ k ps ret body, κ⟩
        ⟨S, σ, .val (.closure f (Env.ofCap σ c) o θ k ps ret body), κ⟩
  | appPush {S : Ctx} (σ : Stack sig S) (e : Term sig S) b θ (k : Nat) (args : Fin k → Term sig S)
      (κ : Cont sig S) :
      Step G ⟨S, σ, .app e b θ k args, κ⟩ ⟨S, σ, e, .appFn b θ k args κ⟩
  /-- a call without arguments -/
  | appNil {S : Ctx} (σ : Stack sig S) (v : Value sig S) b θ (args : Fin 0 → Term sig S)
      (κ : Cont sig S) (c : Config sig) (h : Call G σ κ v b θ 0 Fin.elim0 c) :
      Step G ⟨S, σ, .val v, .appFn b θ 0 args κ⟩ c
  | appFirstArg {S : Ctx} (σ : Stack sig S) (v : Value sig S) b θ (k : Nat)
      (args : Fin (k + 1) → Term sig S) (κ : Cont sig S) :
      Step G ⟨S, σ, .val v, .appFn b θ (k + 1) args κ⟩
        ⟨S, σ, args 0, .appArg v b θ 0 k Fin.elim0 (fun i => args i.succ) κ⟩
  | appNextArg {S : Ctx} (σ : Stack sig S) (v f : Value sig S) b θ (i j : Nat)
      (done : Fin i → Value sig S) (rest : Fin (j + 1) → Term sig S) (κ : Cont sig S) :
      Step G ⟨S, σ, .val v, .appArg f b θ i (j + 1) done rest κ⟩
        ⟨S, σ, rest 0, .appArg f b θ (i + 1) j (vsnoc done v) (fun t => rest t.succ) κ⟩
  | appLastArg {S : Ctx} (σ : Stack sig S) (v f : Value sig S) b θ (i : Nat)
      (done : Fin i → Value sig S) (rest : Fin 0 → Term sig S) (κ : Cont sig S) (c : Config sig)
      (h : Call G σ κ f b θ (i + 1) (vsnoc done v) c) :
      Step G ⟨S, σ, .val v, .appArg f b θ i 0 done rest κ⟩ c
  -- ## Tuples, arrays and sums
  | tupleNil {S : Ctx} (σ : Stack sig S) (es : Fin 0 → Term sig S) (κ : Cont sig S) :
      Step G ⟨S, σ, .tuple 0 es, κ⟩ ⟨S, σ, .val (.tuple 0 Fin.elim0), κ⟩
  | tuplePush {S : Ctx} (σ : Stack sig S) (k : Nat) (es : Fin (k + 1) → Term sig S) (κ : Cont sig S) :
      Step G ⟨S, σ, .tuple (k + 1) es, κ⟩ ⟨S, σ, es 0, .tuple 0 k Fin.elim0 (fun i => es i.succ) κ⟩
  | tupleNext {S : Ctx} (σ : Stack sig S) (v : Value sig S) (i j : Nat) (done : Fin i → Value sig S)
      (rest : Fin (j + 1) → Term sig S) (κ : Cont sig S) :
      Step G ⟨S, σ, .val v, .tuple i (j + 1) done rest κ⟩
        ⟨S, σ, rest 0, .tuple (i + 1) j (vsnoc done v) (fun t => rest t.succ) κ⟩
  | tupleVal {S : Ctx} (σ : Stack sig S) (v : Value sig S) (i : Nat) (done : Fin i → Value sig S)
      (rest : Fin 0 → Term sig S) (κ : Cont sig S) :
      Step G ⟨S, σ, .val v, .tuple i 0 done rest κ⟩ ⟨S, σ, .val (.tuple (i + 1) (vsnoc done v)), κ⟩
  | arrayNil {S : Ctx} (σ : Stack sig S) (es : Fin 0 → Term sig S) (κ : Cont sig S) :
      Step G ⟨S, σ, .array 0 es, κ⟩ ⟨S, σ, .val (.array 0 Fin.elim0), κ⟩
  | arrayPush {S : Ctx} (σ : Stack sig S) (k : Nat) (es : Fin (k + 1) → Term sig S) (κ : Cont sig S) :
      Step G ⟨S, σ, .array (k + 1) es, κ⟩ ⟨S, σ, es 0, .array 0 k Fin.elim0 (fun i => es i.succ) κ⟩
  | arrayNext {S : Ctx} (σ : Stack sig S) (v : Value sig S) (i j : Nat) (done : Fin i → Value sig S)
      (rest : Fin (j + 1) → Term sig S) (κ : Cont sig S) :
      Step G ⟨S, σ, .val v, .array i (j + 1) done rest κ⟩
        ⟨S, σ, rest 0, .array (i + 1) j (vsnoc done v) (fun t => rest t.succ) κ⟩
  | arrayVal {S : Ctx} (σ : Stack sig S) (v : Value sig S) (i : Nat) (done : Fin i → Value sig S)
      (rest : Fin 0 → Term sig S) (κ : Cont sig S) :
      Step G ⟨S, σ, .val v, .array i 0 done rest κ⟩ ⟨S, σ, .val (.array (i + 1) (vsnoc done v)), κ⟩
  | inlPush {S : Ctx} (σ : Stack sig S) τ₁ τ₂ (e : Term sig S) (κ : Cont sig S) :
      Step G ⟨S, σ, .inl τ₁ τ₂ e, κ⟩ ⟨S, σ, e, .inl τ₁ τ₂ κ⟩
  | inlVal {S : Ctx} (σ : Stack sig S) τ₁ τ₂ (v : Value sig S) (κ : Cont sig S) :
      Step G ⟨S, σ, .val v, .inl τ₁ τ₂ κ⟩ ⟨S, σ, .val (.inl τ₁ τ₂ v), κ⟩
  | inrPush {S : Ctx} (σ : Stack sig S) τ₁ τ₂ (e : Term sig S) (κ : Cont sig S) :
      Step G ⟨S, σ, .inr τ₁ τ₂ e, κ⟩ ⟨S, σ, e, .inr τ₁ τ₂ κ⟩
  | inrVal {S : Ctx} (σ : Stack sig S) τ₁ τ₂ (v : Value sig S) (κ : Cont sig S) :
      Step G ⟨S, σ, .val v, .inr τ₁ τ₂ κ⟩ ⟨S, σ, .val (.inr τ₁ τ₂ v), κ⟩
  | matchPush {S : Ctx} (σ : Stack sig S) (e : Term sig S) e₁ e₂ (κ : Cont sig S) :
      Step G ⟨S, σ, .matchE e e₁ e₂, κ⟩ ⟨S, σ, e, .matchE e₁ e₂ κ⟩
  /-- `E-MatchLeft` -/
  | matchLeft {S : Ctx} (σ : Stack sig S) τ₁ τ₂ (v : Value sig S) e₁ e₂ (κ : Cont sig S) :
      Step G ⟨S, σ, .val (.inl τ₁ τ₂ v), .matchE e₁ e₂ κ⟩ ⟨.var :: S, σ.pushVar v, e₁, .popVar κ⟩
  /-- `E-MatchRight` -/
  | matchRight {S : Ctx} (σ : Stack sig S) τ₁ τ₂ (v : Value sig S) e₁ e₂ (κ : Cont sig S) :
      Step G ⟨S, σ, .val (.inr τ₁ τ₂ v), .matchE e₁ e₂ κ⟩ ⟨.var :: S, σ.pushVar v, e₂, .popVar κ⟩

/-- Reflexive-transitive closure `Σ ⊢ (σ; e) →* (σ'; e')`. -/
inductive Steps (G : GlobalEnv sig) : Config sig → Config sig → Prop
  | refl (c : Config sig) : Steps G c c
  | step (c c' c'' : Config sig) (h : Step G c c') (t : Steps G c' c'') : Steps G c c''

/-- A configuration is final if it has produced its value (a value in focus and
nothing left to do) or has aborted. -/
def Config.IsFinal (c : Config sig) : Prop :=
  (∃ v, c.focus = .val v ∧ c.cont = .halt) ∨ (∃ s, c.focus = .abort s)

end Oxide
