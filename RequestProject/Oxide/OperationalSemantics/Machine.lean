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

Deviations from the paper (all forced by the representation, see the README):
* `E-Closure` copies the selected captured values into the closure's frame (the
  paper additionally overwrites captured non-copyable variables with `dead`,
  which requires type information not available at runtime);
* slices use half-open bounds `[n₁, n₂)`.
-/

@[expose] public section

namespace Oxide

/-- Calling a function value with argument values, continuing with `κ`. -/
inductive Call (G : GlobalEnv) {S : Ctx} (σ : Stack S) (κ : Cont S) :
    Value S → (b : Binders) → (Fin b.nφ → FrameExpr S) → (Fin b.nϱ → Region S) →
      (Fin b.nα → Ty S) → List (Value S) → Config → Prop
  /-- `E-AppClosure`: a new frame holding the arguments on top of the captured
  frame is pushed. -/
  | closure (f : Ctx) (env : Env S f) (ps : Fin k → Ty S) (ret : Ty S)
      (body : Term (vars k ++ (f ++ .frame :: S))) (b : Binders) Φs ρs τs (vs : List (Value S))
      (hlen : vs.length = k) :
      Call G σ κ (.closure f env k ps ret body) b Φs ρs τs vs
        ⟨vars k ++ (f ++ .frame :: S), σ.pushFrame (fun i => vs.get (i.cast hlen.symm)) env, body,
          .popFrame k f κ⟩
  /-- `E-AppFunction`: the instantiated body runs in a new frame holding the
  arguments. -/
  | fn (fname : String) (d : FnDef) (hd : G.lookup fname = some d) Φs ρs τs (vs : List (Value S))
      (hlen : vs.length = d.k) :
      Call G σ κ (.fn fname) d.binders Φs ρs τs vs
        ⟨vars d.k ++ ([] ++ .frame :: S), σ.pushFrame (fun i => vs.get (i.cast hlen.symm)) .nil,
          d.instBody Φs ρs τs, .popFrame d.k [] κ⟩

/-- `Σ ⊢ (σ; e) → (σ'; e')`: one step of the machine. -/
inductive Step (G : GlobalEnv) : Config → Config → Prop
  -- ## Places and borrows
  /-- `E-Move` -/
  | move {S : Ctx} (σ σ' : Stack S) (p : PlaceExpr S) (κ : Cont S) (R : Referent S) (v : Value S)
      (hplace : POp.deref ∉ p.ops)
      (hR : σ.evalPlace p = some R) (hv : σ.read R = some v) (hw : σ.write R .dead = some σ') :
      Step G ⟨S, σ, .place p, κ⟩ ⟨S, σ', .val v, κ⟩
  /-- `E-Copy` -/
  | copy {S : Ctx} (σ : Stack S) (p : PlaceExpr S) (κ : Cont S) (R : Referent S) (v : Value S)
      (hR : σ.evalPlace p = some R) (hv : σ.read R = some v) :
      Step G ⟨S, σ, .place p, κ⟩ ⟨S, σ, .val v, κ⟩
  /-- `E-Borrow` -/
  | borrow {S : Ctx} (σ : Stack S) (r : In .rgn S) (ω : Own) (p : PlaceExpr S) (κ : Cont S)
      (R : Referent S) (v : Value S) (hR : σ.evalPlace p = some R) (hv : σ.read R = some v) :
      Step G ⟨S, σ, .borrow r ω p, κ⟩ ⟨S, σ, .val (.ptr R), κ⟩
  | borrowIdxPush {S : Ctx} (σ : Stack S) r ω p (e : Term S) (κ : Cont S) :
      Step G ⟨S, σ, .borrowIdx r ω p e, κ⟩ ⟨S, σ, e, .borrowIdx r ω p κ⟩
  /-- `E-BorrowIndex` -/
  | borrowIdx {S : Ctx} (σ : Stack S) r ω p (κ : Cont S) (R : Referent S) (k : Nat)
      (vs : Fin k → Value S) (i : Nat)
      (hR : σ.evalPlace p = some R) (hv : σ.read R = some (.array k vs) ∨ σ.read R = some (.slice k vs))
      (hi : i < k) :
      Step G ⟨S, σ, .val (Value.num i), .borrowIdx r ω p κ⟩ ⟨S, σ, .val (.ptr (R.snoc (.idx i))), κ⟩
  /-- `E-BorrowIndexOOB` -/
  | borrowIdxOOB {S : Ctx} (σ : Stack S) r ω p (κ : Cont S) (R : Referent S) (k : Nat)
      (vs : Fin k → Value S) (i : Nat)
      (hR : σ.evalPlace p = some R) (hv : σ.read R = some (.array k vs) ∨ σ.read R = some (.slice k vs))
      (hi : k ≤ i) :
      Step G ⟨S, σ, .val (Value.num i), .borrowIdx r ω p κ⟩
        ⟨S, σ, .abort "attempted to index out of bounds", κ⟩
  | borrowSlicePush {S : Ctx} (σ : Stack S) r ω p (e₁ e₂ : Term S) (κ : Cont S) :
      Step G ⟨S, σ, .borrowSlice r ω p e₁ e₂, κ⟩ ⟨S, σ, e₁, .borrowSlice₁ r ω p e₂ κ⟩
  | borrowSliceNext {S : Ctx} (σ : Stack S) r ω p (e₂ : Term S) (v : Value S) (κ : Cont S) :
      Step G ⟨S, σ, .val v, .borrowSlice₁ r ω p e₂ κ⟩ ⟨S, σ, e₂, .borrowSlice₂ r ω p v κ⟩
  /-- `E-BorrowSlice` -/
  | borrowSlice {S : Ctx} (σ : Stack S) r ω p (κ : Cont S) (R : Referent S) (k : Nat)
      (vs : Fin k → Value S) (i j : Nat)
      (hR : σ.evalPlace p = some R) (hv : σ.read R = some (.array k vs) ∨ σ.read R = some (.slice k vs))
      (hij : i ≤ j) (hj : j ≤ k) :
      Step G ⟨S, σ, .val (Value.num j), .borrowSlice₂ r ω p (Value.num i) κ⟩
        ⟨S, σ, .val (.ptr (R.snoc (.slice i j))), κ⟩
  /-- `E-BorrowSliceOOB` -/
  | borrowSliceOOB {S : Ctx} (σ : Stack S) r ω p (κ : Cont S) (R : Referent S) (k : Nat)
      (vs : Fin k → Value S) (i j : Nat)
      (hR : σ.evalPlace p = some R) (hv : σ.read R = some (.array k vs) ∨ σ.read R = some (.slice k vs))
      (hoob : ¬ (i ≤ j ∧ j ≤ k)) :
      Step G ⟨S, σ, .val (Value.num j), .borrowSlice₂ r ω p (Value.num i) κ⟩
        ⟨S, σ, .abort "attempted to slice out of bounds", κ⟩
  | indexPush {S : Ctx} (σ : Stack S) p (e : Term S) (κ : Cont S) :
      Step G ⟨S, σ, .index p e, κ⟩ ⟨S, σ, e, .index p κ⟩
  /-- `E-IndexCopy` -/
  | index {S : Ctx} (σ : Stack S) p (κ : Cont S) (R : Referent S) (k : Nat) (vs : Fin k → Value S)
      (i : Nat) (hR : σ.evalPlace p = some R)
      (hv : σ.read R = some (.array k vs) ∨ σ.read R = some (.slice k vs)) (hi : i < k) :
      Step G ⟨S, σ, .val (Value.num i), .index p κ⟩ ⟨S, σ, .val (vs ⟨i, hi⟩), κ⟩
  /-- `E-IndexCopyOOB` -/
  | indexOOB {S : Ctx} (σ : Stack S) p (κ : Cont S) (R : Referent S) (k : Nat)
      (vs : Fin k → Value S) (i : Nat) (hR : σ.evalPlace p = some R)
      (hv : σ.read R = some (.array k vs) ∨ σ.read R = some (.slice k vs)) (hi : k ≤ i) :
      Step G ⟨S, σ, .val (Value.num i), .index p κ⟩ ⟨S, σ, .abort "attempted to index out of bounds", κ⟩
  | assignPush {S : Ctx} (σ : Stack S) p (e : Term S) (κ : Cont S) :
      Step G ⟨S, σ, .assign p e, κ⟩ ⟨S, σ, e, .assign p κ⟩
  /-- `E-Assign` -/
  | assign {S : Ctx} (σ σ' : Stack S) p (κ : Cont S) (R : Referent S) (v : Value S)
      (hR : σ.evalPlace p = some R) (hw : σ.write R v = some σ') :
      Step G ⟨S, σ, .val v, .assign p κ⟩ ⟨S, σ', .val Value.unit, κ⟩
  -- ## Bindings
  /-- `E-LetRegion`: a region marker is pushed; it is popped once the body is a
  value. -/
  | letrgn {S : Ctx} (σ : Stack S) (e : Term (.rgn :: S)) (κ : Cont S) :
      Step G ⟨S, σ, .letrgn e, κ⟩ ⟨.rgn :: S, σ.pushRgn, e, .popRgn κ⟩
  | letPush {S : Ctx} (σ : Stack S) τ (e₁ : Term S) e₂ (κ : Cont S) :
      Step G ⟨S, σ, .letE τ e₁ e₂, κ⟩ ⟨S, σ, e₁, .letE τ e₂ κ⟩
  /-- `E-Let` -/
  | letE {S : Ctx} (σ : Stack S) τ (v : Value S) e₂ (κ : Cont S) :
      Step G ⟨S, σ, .val v, .letE τ e₂ κ⟩ ⟨.var :: S, σ.pushVar v, e₂, .popVar κ⟩
  /-- `E-Shift`: pop the most recent variable -/
  | popVar {S : Ctx} (σ : Stack (.var :: S)) (v : Value (.var :: S)) (v' : Value S) (κ : Cont S)
      (hv : v.prename (PRen.drop S .var) = some v') :
      Step G ⟨.var :: S, σ, .val v, .popVar κ⟩ ⟨S, σ.popL [.var], .val v', κ⟩
  /-- popping a region marker (`shiftprov`) -/
  | popRgn {S : Ctx} (σ : Stack (.rgn :: S)) (v : Value (.rgn :: S)) (v' : Value S) (κ : Cont S)
      (hv : v.prename (PRen.drop S .rgn) = some v') :
      Step G ⟨.rgn :: S, σ, .val v, .popRgn κ⟩ ⟨S, σ.popL [.rgn], .val v', κ⟩
  /-- `E-Framed`: pop the frame of a call -/
  | popFrame {S : Ctx} (k : Nat) (f : Ctx) (σ : Stack (vars k ++ (f ++ .frame :: S)))
      (v : Value (vars k ++ (f ++ .frame :: S))) (v' : Value S) (κ : Cont S)
      (hv : v.popFrame k f = some v') :
      Step G ⟨vars k ++ (f ++ .frame :: S), σ, .val v, .popFrame k f κ⟩ ⟨S, σ.popFrame k f, .val v', κ⟩
  -- ## Control
  | seqPush {S : Ctx} (σ : Stack S) (e₁ e₂ : Term S) (κ : Cont S) :
      Step G ⟨S, σ, .seq e₁ e₂, κ⟩ ⟨S, σ, e₁, .seq e₂ κ⟩
  /-- `E-Seq` -/
  | seq {S : Ctx} (σ : Stack S) (v : Value S) (e₂ : Term S) (κ : Cont S) :
      Step G ⟨S, σ, .val v, .seq e₂ κ⟩ ⟨S, σ, e₂, κ⟩
  | itePush {S : Ctx} (σ : Stack S) (e₁ e₂ e₃ : Term S) (κ : Cont S) :
      Step G ⟨S, σ, .ite e₁ e₂ e₃, κ⟩ ⟨S, σ, e₁, .ite e₂ e₃ κ⟩
  /-- `E-IfTrue` -/
  | iteTrue {S : Ctx} (σ : Stack S) (e₂ e₃ : Term S) (κ : Cont S) :
      Step G ⟨S, σ, .val Value.tt, .ite e₂ e₃ κ⟩ ⟨S, σ, e₂, κ⟩
  /-- `E-IfFalse` -/
  | iteFalse {S : Ctx} (σ : Stack S) (e₂ e₃ : Term S) (κ : Cont S) :
      Step G ⟨S, σ, .val Value.ff, .ite e₂ e₃ κ⟩ ⟨S, σ, e₃, κ⟩
  /-- `E-While` -/
  | whileE {S : Ctx} (σ : Stack S) (e₁ e₂ : Term S) (κ : Cont S) :
      Step G ⟨S, σ, .whileE e₁ e₂, κ⟩ ⟨S, σ, .ite e₁ (.seq e₂ (.whileE e₁ e₂)) (.val Value.unit), κ⟩
  | forPush {S : Ctx} (σ : Stack S) (e₁ : Term S) e₂ (κ : Cont S) :
      Step G ⟨S, σ, .forE e₁ e₂, κ⟩ ⟨S, σ, e₁, .forE e₂ κ⟩
  /-- `E-ForArray` -/
  | forArray {S : Ctx} (σ : Stack S) (k : Nat) (vs : Fin (k + 1) → Value S) e₂ (κ : Cont S) :
      Step G ⟨S, σ, .val (.array (k + 1) vs), .forE e₂ κ⟩
        ⟨.var :: S, σ.pushVar (vs 0), e₂,
          .popVar (.seq (.forE (.val (.array k fun i => vs i.succ)) e₂) κ)⟩
  /-- `E-ForEmptyArray` -/
  | forEmptyArray {S : Ctx} (σ : Stack S) (vs : Fin 0 → Value S) e₂ (κ : Cont S) :
      Step G ⟨S, σ, .val (.array 0 vs), .forE e₂ κ⟩ ⟨S, σ, .val Value.unit, κ⟩
  /-- `E-ForSlice` -/
  | forSlice {S : Ctx} (σ : Stack S) (R : Referent S) (i j : Nat) (k : Nat) (vs : Fin k → Value S)
      e₂ (κ : Cont S)
      (hv : σ.read R = some (.array k vs) ∨ σ.read R = some (.slice k vs)) (hij : i < j) :
      Step G ⟨S, σ, .val (.ptr (R.snoc (.slice i j))), .forE e₂ κ⟩
        ⟨.var :: S, σ.pushVar (.ptr (R.snoc (.idx i))), e₂,
          .popVar (.seq (.forE (.val (.ptr (R.snoc (.slice (i + 1) j)))) e₂) κ)⟩
  /-- `E-ForEmptySlice` -/
  | forEmptySlice {S : Ctx} (σ : Stack S) (R : Referent S) (i : Nat) e₂ (κ : Cont S) :
      Step G ⟨S, σ, .val (.ptr (R.snoc (.slice i i))), .forE e₂ κ⟩ ⟨S, σ, .val Value.unit, κ⟩
  -- ## Closures and calls
  /-- `E-Closure`: the variables and regions of the current frame selected by `s`
  are captured; the body `body` of the closure is the body `body'` of the closure
  value read back in the scope where the closure is written. -/
  | closure {S : Ctx} (σ : Stack S) (k : Nat) (ps : Fin k → Ty S) (ret : Ty S)
      (body : Term (vars k ++ S)) (κ : Cont S) (f : Ctx) (s : Sel f S)
      (body' : Term (vars k ++ (f ++ .frame :: S))) (env : Env S f)
      (hbody : body = body'.rename (s.ren.liftN (vars k)))
      (henv : Env.build f (fun j => σ.get (s.renF j)) = some env) :
      Step G ⟨S, σ, .closure k ps ret body, κ⟩ ⟨S, σ, .val (.closure f env k ps ret body'), κ⟩
  | appPush {S : Ctx} (σ : Stack S) (e : Term S) b Φs ρs τs (k : Nat) (args : Fin k → Term S)
      (κ : Cont S) :
      Step G ⟨S, σ, .app e b Φs ρs τs k args, κ⟩ ⟨S, σ, e, .appFn b Φs ρs τs k args κ⟩
  /-- a call without arguments -/
  | appNil {S : Ctx} (σ : Stack S) (v : Value S) b Φs ρs τs (args : Fin 0 → Term S) (κ : Cont S)
      (c : Config) (h : Call G σ κ v b Φs ρs τs [] c) :
      Step G ⟨S, σ, .val v, .appFn b Φs ρs τs 0 args κ⟩ c
  | appFirstArg {S : Ctx} (σ : Stack S) (v : Value S) b Φs ρs τs (k : Nat)
      (args : Fin (k + 1) → Term S) (κ : Cont S) :
      Step G ⟨S, σ, .val v, .appFn b Φs ρs τs (k + 1) args κ⟩
        ⟨S, σ, args 0, .appArg v b Φs ρs τs [] (List.ofFn fun i => args i.succ) κ⟩
  | appNextArg {S : Ctx} (σ : Stack S) (v f : Value S) b Φs ρs τs (done : List (Value S)) (e : Term S)
      (rest : List (Term S)) (κ : Cont S) :
      Step G ⟨S, σ, .val v, .appArg f b Φs ρs τs done (e :: rest) κ⟩
        ⟨S, σ, e, .appArg f b Φs ρs τs (done ++ [v]) rest κ⟩
  | appLastArg {S : Ctx} (σ : Stack S) (v f : Value S) b Φs ρs τs (done : List (Value S))
      (κ : Cont S) (c : Config) (h : Call G σ κ f b Φs ρs τs (done ++ [v]) c) :
      Step G ⟨S, σ, .val v, .appArg f b Φs ρs τs done [] κ⟩ c
  -- ## Tuples, arrays and sums
  | tupleNil {S : Ctx} (σ : Stack S) (es : Fin 0 → Term S) (κ : Cont S) :
      Step G ⟨S, σ, .tuple 0 es, κ⟩ ⟨S, σ, .val (.tuple 0 Fin.elim0), κ⟩
  | tuplePush {S : Ctx} (σ : Stack S) (k : Nat) (es : Fin (k + 1) → Term S) (κ : Cont S) :
      Step G ⟨S, σ, .tuple (k + 1) es, κ⟩ ⟨S, σ, es 0, .tuple [] (List.ofFn fun i => es i.succ) κ⟩
  | tupleNext {S : Ctx} (σ : Stack S) (v : Value S) (done : List (Value S)) (e : Term S)
      (rest : List (Term S)) (κ : Cont S) :
      Step G ⟨S, σ, .val v, .tuple done (e :: rest) κ⟩ ⟨S, σ, e, .tuple (done ++ [v]) rest κ⟩
  | tupleVal {S : Ctx} (σ : Stack S) (v : Value S) (done : List (Value S)) (κ : Cont S) :
      Step G ⟨S, σ, .val v, .tuple done [] κ⟩ ⟨S, σ, .val (.tuple _ (listFin (done ++ [v]))), κ⟩
  | arrayNil {S : Ctx} (σ : Stack S) (es : Fin 0 → Term S) (κ : Cont S) :
      Step G ⟨S, σ, .array 0 es, κ⟩ ⟨S, σ, .val (.array 0 Fin.elim0), κ⟩
  | arrayPush {S : Ctx} (σ : Stack S) (k : Nat) (es : Fin (k + 1) → Term S) (κ : Cont S) :
      Step G ⟨S, σ, .array (k + 1) es, κ⟩ ⟨S, σ, es 0, .array [] (List.ofFn fun i => es i.succ) κ⟩
  | arrayNext {S : Ctx} (σ : Stack S) (v : Value S) (done : List (Value S)) (e : Term S)
      (rest : List (Term S)) (κ : Cont S) :
      Step G ⟨S, σ, .val v, .array done (e :: rest) κ⟩ ⟨S, σ, e, .array (done ++ [v]) rest κ⟩
  | arrayVal {S : Ctx} (σ : Stack S) (v : Value S) (done : List (Value S)) (κ : Cont S) :
      Step G ⟨S, σ, .val v, .array done [] κ⟩ ⟨S, σ, .val (.array _ (listFin (done ++ [v]))), κ⟩
  | inlPush {S : Ctx} (σ : Stack S) τ₁ τ₂ (e : Term S) (κ : Cont S) :
      Step G ⟨S, σ, .inl τ₁ τ₂ e, κ⟩ ⟨S, σ, e, .inl τ₁ τ₂ κ⟩
  | inlVal {S : Ctx} (σ : Stack S) τ₁ τ₂ (v : Value S) (κ : Cont S) :
      Step G ⟨S, σ, .val v, .inl τ₁ τ₂ κ⟩ ⟨S, σ, .val (.inl τ₁ τ₂ v), κ⟩
  | inrPush {S : Ctx} (σ : Stack S) τ₁ τ₂ (e : Term S) (κ : Cont S) :
      Step G ⟨S, σ, .inr τ₁ τ₂ e, κ⟩ ⟨S, σ, e, .inr τ₁ τ₂ κ⟩
  | inrVal {S : Ctx} (σ : Stack S) τ₁ τ₂ (v : Value S) (κ : Cont S) :
      Step G ⟨S, σ, .val v, .inr τ₁ τ₂ κ⟩ ⟨S, σ, .val (.inr τ₁ τ₂ v), κ⟩
  | matchPush {S : Ctx} (σ : Stack S) (e : Term S) e₁ e₂ (κ : Cont S) :
      Step G ⟨S, σ, .matchE e e₁ e₂, κ⟩ ⟨S, σ, e, .matchE e₁ e₂ κ⟩
  /-- `E-MatchLeft` -/
  | matchLeft {S : Ctx} (σ : Stack S) τ₁ τ₂ (v : Value S) e₁ e₂ (κ : Cont S) :
      Step G ⟨S, σ, .val (.inl τ₁ τ₂ v), .matchE e₁ e₂ κ⟩ ⟨.var :: S, σ.pushVar v, e₁, .popVar κ⟩
  /-- `E-MatchRight` -/
  | matchRight {S : Ctx} (σ : Stack S) τ₁ τ₂ (v : Value S) e₁ e₂ (κ : Cont S) :
      Step G ⟨S, σ, .val (.inr τ₁ τ₂ v), .matchE e₁ e₂ κ⟩ ⟨.var :: S, σ.pushVar v, e₂, .popVar κ⟩

/-- Reflexive-transitive closure `Σ ⊢ (σ; e) →* (σ'; e')`. -/
inductive Steps (G : GlobalEnv) : Config → Config → Prop
  | refl (c : Config) : Steps G c c
  | step (c c' c'' : Config) (h : Step G c c') (t : Steps G c' c'') : Steps G c c''

/-- A configuration is final if it has produced its value (a value in focus and
nothing left to do) or has aborted. -/
def Config.IsFinal (c : Config) : Prop :=
  (∃ v, c.focus = .val v ∧ c.cont = .halt) ∨ (∃ s, c.focus = .abort s)

end Oxide
