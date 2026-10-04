module
public import RequestProject.Oxide.Metafunctions.Terms

/-!
# Oxide: dynamics

Small-step operational semantics `Σ ⊢ (σ; e) → (σ'; e')` of Oxide (appendix
"Dynamics"), using single-layer evaluation contexts.  Nested evaluation contexts
are obtained by iterating the congruence rule `E-EvalCtx`.

Deviations from the paper (all forced by the representation, see the README):
* tuples, arrays and injections whose components are values take one
  administrative step to become values (`E-TupleVal`, …);
* `E-Closure` copies the captured values into the closure's frame (the paper
  additionally overwrites captured non-copyable variables with `dead`, which
  requires type information that is not available at runtime; the typing rule
  `T-Closure` still marks them dead statically);
* slices use half-open bounds `[n₁, n₂)`.
-/

@[expose] public section

namespace Oxide

/-- A list of terms consisting of the values `vs` followed by `rest`. -/
def Terms.ofVals {n : Nat} (vs : List Value) (rest : Terms n) : Terms n :=
  vs.foldr (fun v acc => .cons (.val v) acc) rest

/-- Single-layer evaluation contexts `𝒞`.  `ECtx m n` has a hole of scope `m` and
builds a term of scope `n`. -/
inductive ECtx : Nat → Nat → Type where
  | borrowIdx {n} (r : Region) (ω : Own) (p : PlaceExpr n) : ECtx n n
  | borrowSlice₁ {n} (r : Region) (ω : Own) (p : PlaceExpr n) (e₂ : Term n) : ECtx n n
  | borrowSlice₂ {n} (r : Region) (ω : Own) (p : PlaceExpr n) (v : Value) : ECtx n n
  | index {n} (p : PlaceExpr n) : ECtx n n
  | letE {n} (τ : Ty) (e₂ : Term (n + 1)) : ECtx n n
  | shiftRgn {n} : ECtx n n
  | assign {n} (p : PlaceExpr n) : ECtx n n
  | seq {n} (e₂ : Term n) : ECtx n n
  | framed {n} (m : Nat) : ECtx m n
  | shift {n} : ECtx (n + 1) n
  | appFn {n} (envs : List FrameExpr) (rgns : List Region) (tys : List Ty) (args : Terms n) :
      ECtx n n
  | appArg {n} (f : Value) (envs : List FrameExpr) (rgns : List Region) (tys : List Ty)
      (vs : List Value) (rest : Terms n) : ECtx n n
  | ite {n} (e₂ e₃ : Term n) : ECtx n n
  | forE {n} (e₂ : Term (n + 1)) : ECtx n n
  | tuple {n} (vs : List Value) (rest : Terms n) : ECtx n n
  | array {n} (vs : List Value) (rest : Terms n) : ECtx n n
  | inl {n} (τ₁ τ₂ : Ty) : ECtx n n
  | inr {n} (τ₁ τ₂ : Ty) : ECtx n n
  | matchE {n} (e₁ e₂ : Term (n + 1)) : ECtx n n

/-- Plugging a term into an evaluation context `𝒞[e]`. -/
def ECtx.plug {m n : Nat} : ECtx m n → Term m → Term n
  | .borrowIdx r ω p, e => .borrowIdx r ω p e
  | .borrowSlice₁ r ω p e₂, e => .borrowSlice r ω p e e₂
  | .borrowSlice₂ r ω p v, e => .borrowSlice r ω p (.val v) e
  | .index p, e => .index p e
  | .letE τ e₂, e => .letE τ e e₂
  | .shiftRgn, e => .shiftRgn e
  | .assign p, e => .assign p e
  | .seq e₂, e => .seq e e₂
  | .framed m, e => .framed m e
  | .shift, e => .shift e
  | .appFn envs rgns tys args, e => .app e envs rgns tys args
  | .appArg f envs rgns tys vs rest, e => .app (.val f) envs rgns tys (Terms.ofVals vs (.cons e rest))
  | .ite e₂ e₃, e => .ite e e₂ e₃
  | .forE e₂, e => .forE e e₂
  | .tuple vs rest, e => .tuple (Terms.ofVals vs (.cons e rest))
  | .array vs rest, e => .array (Terms.ofVals vs (.cons e rest))
  | .inl τ₁ τ₂, e => .inl τ₁ τ₂ e
  | .inr τ₁ τ₂, e => .inr τ₁ τ₂ e
  | .matchE e₁ e₂, e => .matchE e e₁ e₂

/-- The referent `𝓡` extended by one step. -/
def Referent.snoc (R : Referent) (s : RStep) : Referent := ⟨R.root, R.steps ++ [s]⟩

/-- `Σ ⊢ (σ; e) → (σ'; e')`. -/
inductive Step (G : GlobalEnv) : Stack → {n : Nat} → Term n → Stack → Term n → Prop
  /-- `E-Move` -/
  | move {n} (σ σ' : Stack) (p : PlaceExpr n) (R : Referent) (v : Value)
      (hplace : POp.deref ∉ p.ops)
      (hR : σ.evalPlace p = some R) (hv : σ.read R = some v) (hw : σ.write R .dead = some σ') :
      Step G σ (.place p) σ' (.val v)
  /-- `E-Copy` -/
  | copy {n} (σ : Stack) (p : PlaceExpr n) (R : Referent) (v : Value)
      (hR : σ.evalPlace p = some R) (hv : σ.read R = some v) :
      Step G σ (.place p) σ (.val v)
  /-- `E-Borrow` -/
  | borrow {n} (σ : Stack) (r : Region) (ω : Own) (p : PlaceExpr n) (R : Referent) (v : Value)
      (hR : σ.evalPlace p = some R) (hv : σ.read R = some v) :
      Step G σ (.borrow r ω p) σ (.val (.ptr R))
  /-- `E-BorrowIndex` -/
  | borrowIdx {n} (σ : Stack) (r : Region) (ω : Own) (p : PlaceExpr n) (R : Referent)
      (vs : List Value) (i : Nat)
      (hR : σ.evalPlace p = some R) (hv : σ.read R = some (.array vs) ∨ σ.read R = some (.slice vs))
      (hi : i < vs.length) :
      Step G σ (.borrowIdx r ω p (.val (Value.num i))) σ (.val (.ptr (R.snoc (.idx i))))
  /-- `E-BorrowIndexOOB` -/
  | borrowIdxOOB {n} (σ : Stack) (r : Region) (ω : Own) (p : PlaceExpr n) (R : Referent)
      (vs : List Value) (i : Nat)
      (hR : σ.evalPlace p = some R) (hv : σ.read R = some (.array vs) ∨ σ.read R = some (.slice vs))
      (hi : vs.length ≤ i) :
      Step G σ (.borrowIdx r ω p (.val (Value.num i))) σ (.abort "attempted to index out of bounds")
  /-- `E-BorrowSlice` -/
  | borrowSlice {n} (σ : Stack) (r : Region) (ω : Own) (p : PlaceExpr n) (R : Referent)
      (vs : List Value) (i j : Nat)
      (hR : σ.evalPlace p = some R) (hv : σ.read R = some (.array vs) ∨ σ.read R = some (.slice vs))
      (hij : i ≤ j) (hj : j ≤ vs.length) :
      Step G σ (.borrowSlice r ω p (.val (Value.num i)) (.val (Value.num j))) σ
        (.val (.ptr (R.snoc (.slice i j))))
  /-- `E-BorrowSliceOOB` -/
  | borrowSliceOOB {n} (σ : Stack) (r : Region) (ω : Own) (p : PlaceExpr n) (R : Referent)
      (vs : List Value) (i j : Nat)
      (hR : σ.evalPlace p = some R) (hv : σ.read R = some (.array vs) ∨ σ.read R = some (.slice vs))
      (hoob : ¬ (i ≤ j ∧ j ≤ vs.length)) :
      Step G σ (.borrowSlice r ω p (.val (Value.num i)) (.val (Value.num j))) σ
        (.abort "attempted to slice out of bounds")
  /-- `E-IndexCopy` -/
  | index {n} (σ : Stack) (p : PlaceExpr n) (R : Referent) (vs : List Value) (i : Nat) (v : Value)
      (hR : σ.evalPlace p = some R) (hv : σ.read R = some (.array vs) ∨ σ.read R = some (.slice vs))
      (hi : vs[i]? = some v) :
      Step G σ (.index p (.val (Value.num i))) σ (.val v)
  /-- `E-IndexCopyOOB` -/
  | indexOOB {n} (σ : Stack) (p : PlaceExpr n) (R : Referent) (vs : List Value) (i : Nat)
      (hR : σ.evalPlace p = some R) (hv : σ.read R = some (.array vs) ∨ σ.read R = some (.slice vs))
      (hi : vs.length ≤ i) :
      Step G σ (.index p (.val (Value.num i))) σ (.abort "attempted to index out of bounds")
  /-- `E-Framed` -/
  | framed {n} (ς : StackFrame) (σ : Stack) (m : Nat) (v : Value) :
      Step G (ς :: σ) (n := n) (.framed m (.val v)) σ (.val v)
  /-- `E-Shift` -/
  | shift {n} (v' : Value) (ς : StackFrame) (σ : Stack) (v : Value) :
      Step G ((.val v' :: ς) :: σ) (n := n) (.shift (.val v)) (ς :: σ) (.val v)
  /-- popping a region marker (`shiftprov`) -/
  | shiftRgn {n} (ς : StackFrame) (σ : Stack) (v : Value) :
      Step G ((.rgn :: ς) :: σ) (n := n) (.shiftRgn (.val v)) (ς :: σ) (.val v)
  /-- `E-IfTrue` -/
  | iteTrue {n} (σ : Stack) (e₁ e₂ : Term n) : Step G σ (.ite (.val Value.tt) e₁ e₂) σ e₁
  /-- `E-IfFalse` -/
  | iteFalse {n} (σ : Stack) (e₁ e₂ : Term n) : Step G σ (.ite (.val Value.ff) e₁ e₂) σ e₂
  /-- `E-MatchLeft` -/
  | matchLeft {n} (σ : Stack) (τ₁ τ₂ : Ty) (v : Value) (e₁ e₂ : Term (n + 1)) :
      Step G σ (.matchE (.val (.inl τ₁ τ₂ v)) e₁ e₂) (σ.push v) (.shift e₁)
  /-- `E-MatchRight` -/
  | matchRight {n} (σ : Stack) (τ₁ τ₂ : Ty) (v : Value) (e₁ e₂ : Term (n + 1)) :
      Step G σ (.matchE (.val (.inr τ₁ τ₂ v)) e₁ e₂) (σ.push v) (.shift e₂)
  /-- `E-LetRegion`: a region marker is pushed on the top frame and the bound
  region is opened with its level; the marker is popped by `shiftprov` once the body
  has been evaluated -/
  | letrgn {n} (σ : Stack) (e : Term n) :
      Step G σ (.letrgn e) (σ.pushEntry .rgn) (.shiftRgn (e.openRgns [σ.numRgns]))
  /-- `E-Let` -/
  | letE {n} (σ : Stack) (τ : Ty) (v : Value) (e : Term (n + 1)) :
      Step G σ (.letE τ (.val v) e) (σ.push v) (.shift e)
  /-- `E-Seq` -/
  | seq {n} (σ : Stack) (v : Value) (e : Term n) : Step G σ (.seq (.val v) e) σ e
  /-- `E-Assign` -/
  | assign {n} (σ σ' : Stack) (p : PlaceExpr n) (R : Referent) (v : Value)
      (hR : σ.evalPlace p = some R) (hw : σ.write R v = some σ') :
      Step G σ (.assign p (.val v)) σ' (.val Value.unit)
  /-- `E-While` -/
  | whileE {n} (σ : Stack) (e₁ e₂ : Term n) :
      Step G σ (.whileE e₁ e₂) σ (.ite e₁ (.seq e₂ (.whileE e₁ e₂)) (.val Value.unit))
  /-- `E-ForArray` -/
  | forArray {n} (σ : Stack) (v : Value) (vs : List Value) (e : Term (n + 1)) :
      Step G σ (.forE (.val (.array (v :: vs))) e) (σ.push v)
        (.seq (.shift e) (.forE (.val (.array vs)) e))
  /-- `E-ForEmptyArray` -/
  | forEmptyArray {n} (σ : Stack) (e : Term (n + 1)) :
      Step G σ (.forE (.val (.array [])) e) σ (.val Value.unit)
  /-- `E-ForSlice` -/
  | forSlice {n} (σ : Stack) (R : Referent) (i j : Nat) (vs : List Value) (e : Term (n + 1))
      (hv : σ.read R = some (.array vs) ∨ σ.read R = some (.slice vs)) (hij : i < j) :
      Step G σ (.forE (.val (.ptr (R.snoc (.slice i j)))) e) (σ.push (.ptr (R.snoc (.idx i))))
        (.seq (.shift e) (.forE (.val (.ptr (R.snoc (.slice (i + 1) j)))) e))
  /-- `E-ForEmptySlice` -/
  | forEmptySlice {n} (σ : Stack) (R : Referent) (i : Nat) (e : Term (n + 1)) :
      Step G σ (.forE (.val (.ptr (R.snoc (.slice i i)))) e) σ (.val Value.unit)
  /-- `E-Closure`: the body's free variables `ρ 0, …, ρ (m-1)` are captured into
  the closure's frame, and the concrete regions `rs` of the body that do not occur in
  the signature are abstracted (they become bound regions of the closure value). -/
  | closure {n} (σ : Stack) (k : Nat) (ps : List Ty) (ret : Ty) (body : Term (n + k)) (m : Nat)
      (ρ : Fin m → Fin n) (body' : Term (m + k)) (frame : List Value) (rs : List Nat)
      (hbody : body = (body'.rename (liftRen k ρ)).openRgns rs)
      (hmono : ∀ i j : Fin m, i.val < j.val → (ρ i).val < (ρ j).val)
      (hocc : ∀ j : Fin m, body'.occurs (k + j.val) = true)
      (hrsNodup : rs.Nodup)
      (hrs : ∀ r, r ∈ rs ↔ (r ∈ body.frgns ∧ r ∉ Ty.frgnsL ps ∧ r ∉ ret.frgns))
      (hlen : frame.length = m)
      (hframe : ∀ j : Fin m, σ.topVal (ρ j).val = frame[j.val]?) :
      Step G σ (.closure k ps ret body) σ (.val (.closure m k rs.length frame ps ret body'))
  /-- `E-AppClosure`: a new frame holding the arguments, the captured values and
  `q` fresh region markers is pushed; the closure's bound regions are opened with
  the levels of these markers. -/
  | appClosure {n} (σ : Stack) (m k q : Nat) (frame : List Value) (ps : List Ty) (ret : Ty)
      (body : Term (m + k)) (envs : List FrameExpr) (rgns : List Region) (tys : List Ty)
      (vs : List Value) (hlen : vs.length = k) :
      Step G σ (.app (.val (.closure m k q frame ps ret body)) envs rgns tys (Terms.ofVals vs .nil))
        ((vs.reverse.map .val ++ frame.map .val ++ List.replicate q .rgn) :: σ) (n := n)
        (.framed (m + k) (body.openRgns (newLevels σ.numRgns q)))
  /-- `E-AppFunction` -/
  | appFn {n} (σ : Stack) (f : String) (d : FnDef) (envs : List FrameExpr) (rgns : List Region)
      (tys : List Ty) (vs : List Value) (hd : G.lookup f = some d) (hlen : vs.length = d.params.length) :
      Step G σ (.app (.val (.fn f)) envs rgns tys (Terms.ofVals vs .nil))
        ((vs.reverse.map .val) :: σ) (n := n)
        (.framed d.params.length (d.body.inst ⟨envs, rgns, tys⟩))
  /-- tuples of values are values -/
  | tupleVal {n} (σ : Stack) (vs : List Value) :
      Step G σ (n := n) (.tuple (Terms.ofVals vs .nil)) σ (.val (.tuple vs))
  /-- arrays of values are values -/
  | arrayVal {n} (σ : Stack) (vs : List Value) :
      Step G σ (n := n) (.array (Terms.ofVals vs .nil)) σ (.val (.array vs))
  /-- injections of values are values -/
  | inlVal {n} (σ : Stack) (τ₁ τ₂ : Ty) (v : Value) :
      Step G σ (n := n) (.inl τ₁ τ₂ (.val v)) σ (.val (.inl τ₁ τ₂ v))
  /-- injections of values are values -/
  | inrVal {n} (σ : Stack) (τ₁ τ₂ : Ty) (v : Value) :
      Step G σ (n := n) (.inr τ₁ τ₂ (.val v)) σ (.val (.inr τ₁ τ₂ v))
  /-- `E-EvalCtx` -/
  | ctx {m n} (C : ECtx m n) (σ σ' : Stack) (e e' : Term m) (h : Step G σ e σ' e') :
      Step G σ (C.plug e) σ' (C.plug e')
  /-- `E-EvalCtxAbort` -/
  | ctxAbort {m n} (C : ECtx m n) (σ : Stack) (s : String) :
      Step G σ (C.plug (.abort s)) σ (.abort s)

/-- Reflexive-transitive closure `Σ ⊢ (σ; e) →* (σ'; e')`. -/
inductive Steps (G : GlobalEnv) : Stack → {n : Nat} → Term n → Stack → Term n → Prop
  | refl {n} (σ : Stack) (e : Term n) : Steps G σ e σ e
  | step {n} (σ σ' σ'' : Stack) (e e' e'' : Term n) (h : Step G σ e σ' e')
      (t : Steps G σ' e' σ'' e'') : Steps G σ e σ'' e''

/-- A configuration is final if its expression is a value or an `abort!`. -/
def Term.IsFinal {n : Nat} (e : Term n) : Prop := (∃ v, e = .val v) ∨ (∃ s, e = .abort s)

end Oxide
