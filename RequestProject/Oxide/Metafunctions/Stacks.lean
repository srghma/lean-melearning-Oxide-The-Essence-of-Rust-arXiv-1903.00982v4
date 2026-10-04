module

public import RequestProject.Oxide.Metafunctions.StackTypings

/-!
# Oxide metafunctions, part 4: stacks and referents

Appendix C of the paper (`value-lookup.tex`, `value-update.tex`): lookup and
update of values in runtime stacks, reading and writing at referents, and
evaluation of place expressions to referents (§3.6).
-/

@[expose] public section

namespace Oxide

namespace StackFrame
/-- Number of values in a frame. -/
def numVals (ς : StackFrame) : Nat := ς.countP fun | .val _ => true | .rgn => false
/-- Number of region markers in a frame. -/
def numRgns (ς : StackFrame) : Nat := ς.countP fun | .val _ => false | .rgn => true
/-- The `j`-th most recent value of the frame. -/
def valAt : StackFrame → Nat → Option Value
  | [], _ => none
  | .val v :: _, 0 => some v
  | .val _ :: ς, j + 1 => valAt ς j
  | .rgn :: ς, j => valAt ς j
/-- Update the `j`-th most recent value of the frame. -/
def setValAt : StackFrame → Nat → Value → StackFrame
  | [], _, _ => []
  | .val _ :: ς, 0, v => .val v :: ς
  | .val w :: ς, j + 1, v => .val w :: setValAt ς j v
  | .rgn :: ς, j, v => .rgn :: setValAt ς j v
end StackFrame

namespace Stack
/-- Total number of values. -/
def size (σ : Stack) : Nat := (σ.map StackFrame.numVals).sum
/-- Total number of region markers. -/
def numRgns (σ : Stack) : Nat := (σ.map StackFrame.numRgns).sum
/-- Level of the binding with de Bruijn index `i` in the top frame. -/
def idxToLevel (σ : Stack) (i : Nat) : Option Nat :=
  match σ with
  | [] => none
  | ς :: _ => if i < ς.numVals then some (σ.size - 1 - i) else none
/-- `σ(x)` for the variable with de Bruijn index `i` (relative to the top frame). -/
def topVal (σ : Stack) (i : Nat) : Option Value :=
  match σ with
  | [] => none
  | ς :: _ => ς.valAt i
/-- `σ(x)` for the binding at level `ℓ`. -/
def get? : Stack → Nat → Option Value
  | [], _ => none
  | ς :: σ, ℓ =>
      if size σ ≤ ℓ then
        (if ℓ - size σ < ς.numVals then ς.valAt (ς.numVals - 1 - (ℓ - size σ)) else none)
      else get? σ ℓ
/-- `σ[x ↦ v]` for the binding at level `ℓ`. -/
def set : Stack → Nat → Value → Stack
  | [], _, _ => []
  | ς :: σ, ℓ, v =>
      if size σ ≤ ℓ then ς.setValAt (ς.numVals - 1 - (ℓ - size σ)) v :: σ
      else ς :: set σ ℓ v
/-- Extend the top frame. -/
def pushEntry (σ : Stack) (e : StackEntry) : Stack :=
  match σ with
  | [] => [[e]]
  | ς :: σ => (e :: ς) :: σ
/-- `σ, x ↦ v`. -/
def push (σ : Stack) (v : Value) : Stack := σ.pushEntry (.val v)
end Stack

/-! ## Referents -/

/-- Read the component of a value designated by referent steps (`ER-*`). -/
def Value.readSteps : Value → List RStep → Option Value
  | v, [] => some v
  | .tuple vs, .proj i :: rest => (vs[i]?).bind (·.readSteps rest)
  | .array vs, .idx i :: rest => (vs[i]?).bind (·.readSteps rest)
  | .slice vs, .idx i :: rest => (vs[i]?).bind (·.readSteps rest)
  | .array vs, .slice i j :: rest =>
      if i ≤ j ∧ j ≤ vs.length then (Value.slice (vs.extract i j)).readSteps rest else none
  | .slice vs, .slice i j :: rest =>
      if i ≤ j ∧ j ≤ vs.length then (Value.slice (vs.extract i j)).readSteps rest else none
  | _, _ :: _ => none

/-- Modify the component of a value designated by referent steps; this realizes
the value contexts `𝒱[·]` of the paper. -/
def Value.modifySteps : Value → List RStep → (Value → Option Value) → Option Value
  | v, [], f => f v
  | .tuple vs, .proj i :: rest, f =>
      match vs[i]? with
      | some vi => (vi.modifySteps rest f).map fun vi' => .tuple (vs.set i vi')
      | none => none
  | .array vs, .idx i :: rest, f =>
      match vs[i]? with
      | some vi => (vi.modifySteps rest f).map fun vi' => .array (vs.set i vi')
      | none => none
  | .slice vs, .idx i :: rest, f =>
      match vs[i]? with
      | some vi => (vi.modifySteps rest f).map fun vi' => .slice (vs.set i vi')
      | none => none
  | .array vs, .slice i j :: rest, f =>
      if i ≤ j ∧ j ≤ vs.length then
        match (Value.slice (vs.extract i j)).modifySteps rest f with
        | some (.slice ws) =>
            if ws.length = j - i then some (.array (vs.take i ++ ws ++ vs.drop j)) else none
        | _ => none
      else none
  | .slice vs, .slice i j :: rest, f =>
      if i ≤ j ∧ j ≤ vs.length then
        match (Value.slice (vs.extract i j)).modifySteps rest f with
        | some (.slice ws) =>
            if ws.length = j - i then some (.slice (vs.take i ++ ws ++ vs.drop j)) else none
        | _ => none
      else none
  | _, _ :: _, _ => none

namespace Stack
/-- `σ ⊢ 𝓡 ⇓ 𝒱 × v`: the value stored at a referent. -/
def read (σ : Stack) (R : Referent) : Option Value := (σ.get? R.root).bind (·.readSteps R.steps)
/-- `σ[x ↦ 𝒱[v]]` where `𝓡 = 𝓡°[x]` and `σ ⊢ 𝓡 ⇓ 𝒱 × _`: write `v` at referent `𝓡`. -/
def write (σ : Stack) (R : Referent) (v : Value) : Option Stack := do
  let w ← σ.get? R.root
  let w' ← w.modifySteps R.steps (fun _ => some v)
  pure (σ.set R.root w')
/-- One step of place-expression evaluation: a projection extends the referent,
a dereference follows the pointer stored at the referent. -/
def placeStep (σ : Stack) (R : Referent) : POp → Option Referent
  | .proj i => some ⟨R.root, R.steps ++ [.proj i]⟩
  | .deref =>
      match σ.read R with
      | some (.ptr R') => some R'
      | _ => none
/-- Place-expression evaluation `σ ⊢ p ⇓ 𝓡` (`P-*`). -/
def evalPlace {n : Nat} (σ : Stack) (p : PlaceExpr n) : Option Referent := do
  let ℓ ← σ.idxToLevel p.root
  p.ops.foldlM (σ.placeStep) ⟨ℓ, []⟩
end Stack

/-- The innermost place `π` of a referent `𝓡 = 𝓡°[π]`. -/
def Referent.base (R : Referent) : APlace :=
  ⟨R.root, (R.steps.takeWhile fun | .proj _ => true | _ => false).filterMap fun
    | .proj i => some i
    | _ => none⟩

end Oxide
