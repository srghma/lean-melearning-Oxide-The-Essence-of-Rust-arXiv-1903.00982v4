module

public import RequestProject.Oxide.Metafunctions.Places
public import RequestProject.Oxide.Syntax.Runtime

/-!
# Oxide metafunctions, part 5: stacks and referents

Appendix C of the paper (`value-lookup.tex`, `value-update.tex`): lookup and
update of values in runtime stacks, reading and writing at referents, evaluation
of place expressions to referents (§3.6), and pushing and popping stack slots.

Lookups are total, since a variable of the scope always has a slot.

**Paths into values.**  A referent is untyped (the value it points to changes as
the program runs), so it is resolved once against the value stored in its root
slot, into a path `VPath v` indexed by that value (`Referent.resolve`).  Reading
(`VPath.get`) and writing (`VPath.set`) along such a path always succeed; only
the resolution may fail (an index out of bounds, a projection of a non-tuple).
Slicing then indexing resolves to an index into the underlying array.

Popping a binder strengthens the remaining values; the parts of a value that still
mention the popped binder become `dead` (`Value.prenameD`): only slots whose type
is (partially) dead may hold such values.
-/

@[expose] public section

namespace Oxide

variable {sig : Sig}

namespace Slots

variable {Γ : Ctx}

/-- `σ(x)` (total). -/
def get : {S : Ctx} → Slots sig Γ S → In .var S → Value sig Γ
  | _, .var v _, .here => v
  | _, .var _ σ, .there i => σ.get i
  | _, .rgn σ, .there i => σ.get i
  | _, .frame σ, .there i => σ.get i

/-- `σ[x ↦ v]`. -/
def set : {S : Ctx} → Slots sig Γ S → In .var S → Value sig Γ → Slots sig Γ S
  | _, .var _ σ, .here, v => .var v σ
  | _, .var w σ, .there i, v => .var w (σ.set i v)
  | _, .rgn σ, .there i, v => .rgn (σ.set i v)
  | _, .frame σ, .there i, v => .frame (σ.set i v)

/-- Transform all the values. -/
def map {Δ : Ctx} (g : Value sig Γ → Value sig Δ) : {S : Ctx} → Slots sig Γ S → Slots sig Δ S
  | _, .nil => .nil
  | _, .var v σ => .var (g v) (σ.map g)
  | _, .rgn σ => .rgn (σ.map g)
  | _, .frame σ => .frame (σ.map g)

/-- Drop the slots of a prefix `cs` of the shape (without touching the values). -/
def dropL : (cs : Ctx) → {S : Ctx} → Slots sig Γ (cs ++ S) → Slots sig Γ S
  | [], _, σ => σ
  | .var :: cs, _, .var _ σ => σ.dropL cs
  | .rgn :: cs, _, .rgn σ => σ.dropL cs
  | .frame :: cs, _, .frame σ => σ.dropL cs

/-- Concatenate slots. -/
def append : {cs S : Ctx} → Slots sig Γ cs → Slots sig Γ S → Slots sig Γ (cs ++ S)
  | _, _, .nil, b => b
  | _, _, .var v a, b => .var v (a.append b)
  | _, _, .rgn a, b => .rgn (a.append b)
  | _, _, .frame a, b => .frame (a.append b)

/-- The slots holding `k` arguments (argument `i` in the `i`-th most recent slot). -/
def ofFin : {k : Nat} → (Fin k → Value sig Γ) → Slots sig Γ (vars k)
  | 0, _ => .nil
  | _ + 1, vs => .var (vs 0) (ofFin fun i => vs i.succ)

/-- The slots of a captured frame. -/
def ofEnv : {f : Ctx} → Env sig Γ f → Slots sig Γ f
  | _, .nil => .nil
  | _, .var v ε => .var v (ofEnv ε)
  | _, .rgn ε => .rgn (ofEnv ε)

end Slots

/-- The captured frame of a closure, read off the stack (`E-Closure`): each
captured variable holds the value of the variable it copies. -/
def Env.ofCap {S : Ctx} (σ : Stack sig S) : {f : Ctx} → Cap S f → Env sig S f
  | _, .nil => .nil
  | _, .var x c => .var (σ.get x.toIn) (Env.ofCap σ c)
  | _, .rgn _ c => .rgn (Env.ofCap σ c)

/-! ## Paths into values -/

/-- Paths into a value: projections of tuples, indexing of arrays and slices (with
in-bounds indices), and slices of arrays and slices (in bounds) at the end. -/
inductive VPath {Γ : Ctx} : Value sig Γ → Type where
  | here {v : Value sig Γ} : VPath v
  | proj {k : Nat} {vs : Fin k → Value sig Γ} (i : Fin k) (p : VPath (vs i)) : VPath (.tuple k vs)
  | idxA {k : Nat} {vs : Fin k → Value sig Γ} (i : Fin k) (p : VPath (vs i)) : VPath (.array k vs)
  | idxS {k : Nat} {vs : Fin k → Value sig Γ} (i : Fin k) (p : VPath (vs i)) : VPath (.slice k vs)
  | sliceA {k : Nat} {vs : Fin k → Value sig Γ} (start len : Nat) (h : start + len ≤ k) :
      VPath (.array k vs)
  | sliceS {k : Nat} {vs : Fin k → Value sig Γ} (start len : Nat) (h : start + len ≤ k) :
      VPath (.slice k vs)

/-- Replace the elements `[a, a + l)` of a vector by `ws`. -/
def spliceFin {α : Type} {k l : Nat} (vs : Fin k → α) (a : Nat) (ws : Fin l → α) : Fin k → α :=
  fun t => if h : a ≤ t.val ∧ t.val < a + l then ws ⟨t.val - a, by omega⟩ else vs t

/-- Write a slice value `w` of length `l` over the elements `[a, a + l)` (anything
else leaves the vector unchanged: slices are unsized and are never assigned). -/
def Value.spliceInto {Γ : Ctx} {k : Nat} (vs : Fin k → Value sig Γ) (a l : Nat) :
    Value sig Γ → Fin k → Value sig Γ
  | .slice l' ws => if l' = l then spliceFin vs a ws else vs
  | _ => vs

namespace VPath

variable {Γ : Ctx}

/-- The component at the end of a path (total). -/
def get : {v : Value sig Γ} → VPath v → Value sig Γ
  | v, .here => v
  | _, .proj _ p => p.get
  | _, .idxA _ p => p.get
  | _, .idxS _ p => p.get
  | .array _ vs, .sliceA a l h => .slice l fun t => vs ⟨a + t.val, by have := t.isLt; omega⟩
  | .slice _ vs, .sliceS a l h => .slice l fun t => vs ⟨a + t.val, by have := t.isLt; omega⟩

/-- Replace the component at the end of a path (total); this realizes the value
contexts `𝒱[·]` of the paper. -/
def set : {v : Value sig Γ} → VPath v → Value sig Γ → Value sig Γ
  | _, .here, w => w
  | .tuple k vs, .proj i p, w => .tuple k fun t => if t = i then p.set w else vs t
  | .array k vs, .idxA i p, w => .array k fun t => if t = i then p.set w else vs t
  | .slice k vs, .idxS i p, w => .slice k fun t => if t = i then p.set w else vs t
  | .array k vs, .sliceA a l _, w => .array k (Value.spliceInto vs a l w)
  | .slice k vs, .sliceS a l _, w => .slice k (Value.spliceInto vs a l w)

/-- Extend a path by a projection. -/
def snocProj : {v : Value sig Γ} → VPath v → Nat → Option (VPath v)
  | .tuple k _, .here, i => if h : i < k then some (.proj ⟨i, h⟩ .here) else none
  | _, .here, _ => none
  | _, .proj j p, i => (p.snocProj i).map (.proj j)
  | _, .idxA j p, i => (p.snocProj i).map (.idxA j)
  | _, .idxS j p, i => (p.snocProj i).map (.idxS j)
  | _, .sliceA .., _ => none
  | _, .sliceS .., _ => none

/-- Extend a path by projections. -/
def snocProjs {v : Value sig Γ} (p : VPath v) : List Nat → Option (VPath v)
  | [] => some p
  | i :: q => (p.snocProj i).bind fun p' => p'.snocProjs q

/-- Extend a path by indexing (indexing a slice indexes the underlying array). -/
def snocIdx : {v : Value sig Γ} → VPath v → Nat → Option (VPath v)
  | .array k _, .here, i => if h : i < k then some (.idxA ⟨i, h⟩ .here) else none
  | .slice k _, .here, i => if h : i < k then some (.idxS ⟨i, h⟩ .here) else none
  | _, .here, _ => none
  | _, .proj j p, i => (p.snocIdx i).map (.proj j)
  | _, .idxA j p, i => (p.snocIdx i).map (.idxA j)
  | _, .idxS j p, i => (p.snocIdx i).map (.idxS j)
  | _, .sliceA a l h, i => if hi : i < l then some (.idxA ⟨a + i, by omega⟩ .here) else none
  | _, .sliceS a l h, i => if hi : i < l then some (.idxS ⟨a + i, by omega⟩ .here) else none

/-- Extend a path by slicing (a slice of a slice is a slice of the underlying
array). -/
def snocSlice : {v : Value sig Γ} → VPath v → Nat → Nat → Option (VPath v)
  | .array k _, .here, a, l => if h : a + l ≤ k then some (.sliceA a l h) else none
  | .slice k _, .here, a, l => if h : a + l ≤ k then some (.sliceS a l h) else none
  | _, .here, _, _ => none
  | _, .proj j p, a, l => (p.snocSlice a l).map (.proj j)
  | _, .idxA j p, a, l => (p.snocSlice a l).map (.idxA j)
  | _, .idxS j p, a, l => (p.snocSlice a l).map (.idxS j)
  | _, .sliceA a' l' h, a, l =>
      if h' : a + l ≤ l' then some (.sliceA (a' + a) l (by omega)) else none
  | _, .sliceS a' l' h, a, l =>
      if h' : a + l ≤ l' then some (.sliceS (a' + a) l (by omega)) else none

end VPath

/-- Resolve a referent against the value `v` stored in its root slot (the only
point where reading or writing at a referent can fail). -/
def Referent.resolve {Γ : Ctx} : Referent Γ → (v : Value sig Γ) → Option (VPath v)
  | .place π, _ => VPath.here.snocProjs π.path
  | .index R i q, v => (R.resolve v).bind fun p => (p.snocIdx i).bind fun p => p.snocProjs q
  | .slice R a l, v => (R.resolve v).bind fun p => p.snocSlice a l

namespace Stack

variable {S : Ctx}

/-- `σ ⊢ 𝓡 ⇓ 𝒱 × v`: the value stored at a referent. -/
def read (σ : Stack sig S) (R : Referent S) : Option (Value sig S) :=
  (R.resolve (σ.get R.root)).map VPath.get

/-- Write `v` at referent `𝓡`. -/
def write (σ : Stack sig S) (R : Referent S) (v : Value sig S) : Option (Stack sig S) :=
  (R.resolve (σ.get R.root)).map fun p => σ.set R.root (p.set v)

/-- Place-expression evaluation `σ ⊢ p ⇓ 𝓡` (`P-*`): a place denotes itself, and
`(*p).q` follows the pointer stored at `p`. -/
def evalPlace (σ : Stack sig S) : PExpr S → Option (Referent S)
  | .place π => some (.place π.toAbs)
  | .deref p q => (σ.evalPlace p).bind fun R => match σ.read R with
    | some (.ptr R') => R'.projs q
    | _ => none

/-- `σ, x ↦ v` (`E-Let`): push a value; all stored values are weakened. -/
def pushVar (σ : Stack sig S) (v : Value sig S) : Stack sig (.var :: S) :=
  .var (v.wk .var) (σ.map (Value.wk .var))

/-- Push a region marker (`E-LetRegion`). -/
def pushRgn (σ : Stack sig S) : Stack sig (.rgn :: S) := .rgn (σ.map (Value.wk .rgn))

/-- `σ ‡ ς`: push a frame holding the arguments `vs` on top of the captured frame
`env` (`E-AppClosure`, `E-AppFunction`). -/
def pushFrame {k : Nat} {f : Ctx} (σ : Stack sig S) (vs : Fin k → Value sig S) (env : Env sig S f) :
    Stack sig (vars k ++ (f ++ .frame :: S)) :=
  let ρ := TRen.frameRen k f S
  (Slots.ofFin fun i => (vs i).rename ρ).append
    ((Slots.ofEnv (env.rename ρ)).append (.frame (σ.map (Value.rename ρ))))

/-- Pop the slots of a prefix `cs`. -/
def popL (cs : Ctx) (σ : Stack sig (cs ++ S)) : Stack sig S :=
  (σ.dropL cs).map (Value.prenameD (PRen.dropL cs S))

/-- Pop a frame of shape `f` with `k` parameters on top. -/
def popFrame (k : Nat) (f : Ctx) (σ : Stack sig (vars k ++ (f ++ .frame :: S))) : Stack sig S :=
  ((σ.popL (vars k)).popL f).popL [.frame]

end Stack

/-- Strengthen a value past a frame of shape `f` with `k` parameters on top
(fails if it still mentions the frame). -/
def Value.popFrame {S : Ctx} (k : Nat) (f : Ctx) (v : Value sig (vars k ++ (f ++ .frame :: S))) :
    Option (Value sig S) :=
  v.prename (PRen.popFrameK k f S)

end Oxide
