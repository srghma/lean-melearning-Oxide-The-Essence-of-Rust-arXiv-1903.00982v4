module

public import RequestProject.Oxide.Metafunctions.Places
public import RequestProject.Oxide.Syntax.Runtime

/-!
# Oxide metafunctions, part 5: stacks and referents

Appendix C of the paper (`value-lookup.tex`, `value-update.tex`): lookup and
update of values in runtime stacks, reading and writing at referents, evaluation
of place expressions to referents (§3.6), and pushing and popping stack slots.

Lookups are total, since a variable of the scope always has a slot.  Popping a
binder strengthens the remaining values; the parts of a value that still mention
the popped binder become `dead` (`Value.prenameD`): only slots whose type is
(partially) dead may hold such values.
-/

@[expose] public section

namespace Oxide

namespace Slots

variable {Γ : Ctx}

/-- `σ(x)` (total). -/
def get : {S : Ctx} → Slots Γ S → In .var S → Value Γ
  | _, .var v _, .here => v
  | _, .var _ σ, .there i => σ.get i
  | _, .rgn σ, .there i => σ.get i
  | _, .frame σ, .there i => σ.get i

/-- `σ[x ↦ v]`. -/
def set : {S : Ctx} → Slots Γ S → In .var S → Value Γ → Slots Γ S
  | _, .var _ σ, .here, v => .var v σ
  | _, .var w σ, .there i, v => .var w (σ.set i v)
  | _, .rgn σ, .there i, v => .rgn (σ.set i v)
  | _, .frame σ, .there i, v => .frame (σ.set i v)

/-- Transform all the values. -/
def map {Δ : Ctx} (g : Value Γ → Value Δ) : {S : Ctx} → Slots Γ S → Slots Δ S
  | _, .nil => .nil
  | _, .var v σ => .var (g v) (σ.map g)
  | _, .rgn σ => .rgn (σ.map g)
  | _, .frame σ => .frame (σ.map g)

/-- Drop the slots of a prefix `cs` of the shape (without touching the values). -/
def dropL : (cs : Ctx) → {S : Ctx} → Slots Γ (cs ++ S) → Slots Γ S
  | [], _, σ => σ
  | .var :: cs, _, .var _ σ => σ.dropL cs
  | .rgn :: cs, _, .rgn σ => σ.dropL cs
  | .frame :: cs, _, .frame σ => σ.dropL cs

/-- Concatenate slots. -/
def append : {cs S : Ctx} → Slots Γ cs → Slots Γ S → Slots Γ (cs ++ S)
  | _, _, .nil, b => b
  | _, _, .var v a, b => .var v (a.append b)
  | _, _, .rgn a, b => .rgn (a.append b)
  | _, _, .frame a, b => .frame (a.append b)

/-- The slots holding `k` arguments (argument `i` in the `i`-th most recent slot). -/
def ofFin : {k : Nat} → (Fin k → Value Γ) → Slots Γ (vars k)
  | 0, _ => .nil
  | _ + 1, vs => .var (vs 0) (ofFin fun i => vs i.succ)

/-- The slots of a captured frame. -/
def ofEnv : {f : Ctx} → Env Γ f → Slots Γ f
  | _, .nil => .nil
  | _, .var v ε => .var v (ofEnv ε)
  | _, .rgn ε => .rgn (ofEnv ε)

end Slots

/-- Build a captured frame of shape `f` from the values of its variables (fails if
`f` contains entries other than variables and regions). -/
def Env.build {T : Ctx} : (f : Ctx) → (In .var f → Value T) → Option (Env T f)
  | [], _ => some .nil
  | .var :: f, gv => (Env.build f fun j => gv j.there).map (.var (gv .here))
  | .rgn :: f, gv => (Env.build f fun j => gv j.there).map .rgn
  | _ :: _, _ => none

/-! ## Referents -/

/-- Read the component of a value designated by referent steps (`ER-*`). -/
def Value.readSteps {Γ : Ctx} : Value Γ → List RStep → Option (Value Γ)
  | v, [] => some v
  | .tuple k vs, .proj i :: rest => if h : i < k then (vs ⟨i, h⟩).readSteps rest else none
  | .array k vs, .idx i :: rest => if h : i < k then (vs ⟨i, h⟩).readSteps rest else none
  | .slice k vs, .idx i :: rest => if h : i < k then (vs ⟨i, h⟩).readSteps rest else none
  | .array k vs, .slice i j :: rest =>
      if h : i ≤ j ∧ j ≤ k then (Value.slice (j - i) fun t => vs ⟨i + t, by omega⟩).readSteps rest
      else none
  | .slice k vs, .slice i j :: rest =>
      if h : i ≤ j ∧ j ≤ k then (Value.slice (j - i) fun t => vs ⟨i + t, by omega⟩).readSteps rest
      else none
  | _, _ :: _ => none

/-- Replace the elements `[i, j)` of a vector by `ws`. -/
def spliceFin {α : Type} {k m : Nat} (vs : Fin k → α) (i j : Nat) (ws : Fin m → α) (hm : m = j - i) :
    Fin k → α :=
  fun t => if h : i ≤ t.val ∧ t.val < j then ws ⟨t.val - i, by omega⟩ else vs t

/-- Modify the component of a value designated by referent steps; this realizes
the value contexts `𝒱[·]` of the paper. -/
def Value.modifySteps {Γ : Ctx} : Value Γ → List RStep → (Value Γ → Option (Value Γ)) →
    Option (Value Γ)
  | v, [], f => f v
  | .tuple k vs, .proj i :: rest, f =>
      if h : i < k then ((vs ⟨i, h⟩).modifySteps rest f).map fun vi =>
        .tuple k fun t => if t = ⟨i, h⟩ then vi else vs t
      else none
  | .array k vs, .idx i :: rest, f =>
      if h : i < k then ((vs ⟨i, h⟩).modifySteps rest f).map fun vi =>
        .array k fun t => if t = ⟨i, h⟩ then vi else vs t
      else none
  | .slice k vs, .idx i :: rest, f =>
      if h : i < k then ((vs ⟨i, h⟩).modifySteps rest f).map fun vi =>
        .slice k fun t => if t = ⟨i, h⟩ then vi else vs t
      else none
  | .array k vs, .slice i j :: rest, f =>
      if h : i ≤ j ∧ j ≤ k then
        match (Value.slice (j - i) fun t => vs ⟨i + t, by omega⟩).modifySteps rest f with
        | some (.slice m ws) => if hm : m = j - i then some (.array k (spliceFin vs i j ws hm)) else none
        | _ => none
      else none
  | .slice k vs, .slice i j :: rest, f =>
      if h : i ≤ j ∧ j ≤ k then
        match (Value.slice (j - i) fun t => vs ⟨i + t, by omega⟩).modifySteps rest f with
        | some (.slice m ws) => if hm : m = j - i then some (.slice k (spliceFin vs i j ws hm)) else none
        | _ => none
      else none
  | _, _ :: _, _ => none

namespace Stack

variable {S : Ctx}

/-- `σ ⊢ 𝓡 ⇓ 𝒱 × v`: the value stored at a referent. -/
def read (σ : Stack S) (R : Referent S) : Option (Value S) := (σ.get R.root).readSteps R.steps

/-- Write `v` at referent `𝓡`. -/
def write (σ : Stack S) (R : Referent S) (v : Value S) : Option (Stack S) :=
  ((σ.get R.root).modifySteps R.steps (fun _ => some v)).map (σ.set R.root)

/-- One step of place-expression evaluation: a projection extends the referent,
a dereference follows the pointer stored at the referent. -/
def placeStep (σ : Stack S) (R : Referent S) : POp → Option (Referent S)
  | .proj i => some ⟨R.root, R.steps ++ [.proj i]⟩
  | .deref =>
      match σ.read R with
      | some (.ptr R') => some R'
      | _ => none

/-- Place-expression evaluation `σ ⊢ p ⇓ 𝓡` (`P-*`). -/
def evalPlace (σ : Stack S) (p : PlaceExpr S) : Option (Referent S) :=
  p.ops.foldlM σ.placeStep ⟨p.root.toIn, []⟩

/-- `σ, x ↦ v` (`E-Let`): push a value; all stored values are weakened. -/
def pushVar (σ : Stack S) (v : Value S) : Stack (.var :: S) :=
  .var (v.wk .var) (σ.map (Value.wk .var))

/-- Push a region marker (`E-LetRegion`). -/
def pushRgn (σ : Stack S) : Stack (.rgn :: S) := .rgn (σ.map (Value.wk .rgn))

/-- `σ ‡ ς`: push a frame holding the arguments `vs` on top of the captured frame
`env` (`E-AppClosure`, `E-AppFunction`). -/
def pushFrame {k : Nat} {f : Ctx} (σ : Stack S) (vs : Fin k → Value S) (env : Env S f) :
    Stack (vars k ++ (f ++ .frame :: S)) :=
  let ρ := TRen.frameRen k f S
  (Slots.ofFin fun i => (vs i).rename ρ).append
    ((Slots.ofEnv (env.rename ρ)).append (.frame (σ.map (Value.rename ρ))))

/-- Pop the slots of a prefix `cs`. -/
def popL (cs : Ctx) (σ : Stack (cs ++ S)) : Stack S :=
  (σ.dropL cs).map (Value.prenameD (PRen.dropL cs S))

/-- Pop a frame of shape `f` with `k` parameters on top. -/
def popFrame (k : Nat) (f : Ctx) (σ : Stack (vars k ++ (f ++ .frame :: S))) : Stack S :=
  ((σ.popL (vars k)).popL f).popL [.frame]

end Stack

/-- Strengthen a value past a frame of shape `f` with `k` parameters on top
(fails if it still mentions the frame). -/
def Value.popFrame {S : Ctx} (k : Nat) (f : Ctx) (v : Value (vars k ++ (f ++ .frame :: S))) :
    Option (Value S) :=
  v.prename (PRen.popFrameK k f S)

end Oxide
