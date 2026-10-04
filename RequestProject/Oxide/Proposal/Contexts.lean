module

public import RequestProject.Oxide.Proposal.Strengthening

/-!
# Proposal prototype, part 5: contexts indexed by the same scope

The runtime stack `σ` and the stack typing `Γ` (together with the paper's `Δ`)
are indexed by the scope `S` that the terms in focus use.  Lookups are total:
a variable of `S` always has a value and a type.

Pushing is weakening; popping is strengthening and may fail.  The failure is
exactly the situation behind the counterexample to the paper's Preservation
lemma (`not_preservation`): `framed (ptr x)` where `x` lives in the popped
frame.  See `framedPop_dangling` at the end of this file.
-/

@[expose] public section

namespace Oxide.Scoped

/-! ## Runtime stacks -/

/-- `Slots Γ S`: the contents of stack slots of shape `S`, all values living in
scope `Γ`.  Only `.var`, `.rgn` and `.frame` entries exist at runtime (a stack
cannot contain unsubstituted type-level binders). -/
inductive Slots (Γ : Ctx) : Ctx → Type where
  | nil : Slots Γ []
  | var {S : Ctx} (v : Value Γ) (σ : Slots Γ S) : Slots Γ (.var :: S)
  | rgn {S : Ctx} (σ : Slots Γ S) : Slots Γ (.rgn :: S)
  | frame {S : Ctx} (σ : Slots Γ S) : Slots Γ (.frame :: S)

/-- Stacks `σ`: every value may point anywhere in the stack (also to newer
slots), so all values live in the scope of the whole stack. -/
abbrev Stack (S : Ctx) := Slots S S

/-- Total lookup of a variable. -/
def Slots.get {Γ : Ctx} : {S : Ctx} → Slots Γ S → In .var S → Value Γ
  | _, .var v _, .here => v
  | _, .var _ σ, .there i => σ.get i
  | _, .rgn σ, .there i => σ.get i
  | _, .frame σ, .there i => σ.get i

def Slots.map {Γ Δ : Ctx} (g : Value Γ → Value Δ) : {S : Ctx} → Slots Γ S → Slots Δ S
  | _, .nil => .nil
  | _, .var v σ => .var (g v) (σ.map g)
  | _, .rgn σ => .rgn (σ.map g)
  | _, .frame σ => .frame (σ.map g)

def Slots.mapM {Γ Δ : Ctx} (g : Value Γ → Option (Value Δ)) :
    {S : Ctx} → Slots Γ S → Option (Slots Δ S)
  | _, .nil => some .nil
  | _, .var v σ => do pure (.var (← g v) (← σ.mapM g))
  | _, .rgn σ => (σ.mapM g).map .rgn
  | _, .frame σ => (σ.mapM g).map .frame

/-- Drop the slots of a prefix `cs` of the shape (without touching the values). -/
def Slots.dropL {Γ : Ctx} : (cs : Ctx) → {S : Ctx} → Slots Γ (cs ++ S) → Slots Γ S
  | [], _, σ => σ
  | .var :: cs, _, .var _ σ => σ.dropL cs
  | .rgn :: cs, _, .rgn σ => σ.dropL cs
  | .frame :: cs, _, .frame σ => σ.dropL cs

/-- `E-Let`: push a value (all stored values are weakened). -/
def Stack.pushVar {S : Ctx} (σ : Stack S) (v : Value (.var :: S)) : Stack (.var :: S) :=
  .var v (σ.map (Value.rename (TRen.wk S .var)))

/-- `E-LetRegion`: push a region marker. -/
def Stack.pushRgn {S : Ctx} (σ : Stack S) : Stack (.rgn :: S) :=
  .rgn (σ.map (Value.rename (TRen.wk S .rgn)))

/-- `E-Shift`: pop the most recent variable.  Fails if a remaining value still
points to it. -/
def Stack.popVar {S : Ctx} : Stack (.var :: S) → Option (Stack S)
  | .var _ σ => σ.mapM (Value.prename (PRen.drop S .var))

/-- `E-Framed`: pop the frame of shape `f` and return the value `v` computed in
it.  Fails if `v` or a remaining value still mentions the popped frame. -/
def Stack.popFrame {S : Ctx} (f : Ctx) (σ : Stack (f ++ .frame :: S))
    (v : Value (f ++ .frame :: S)) : Option (Stack S × Value S) := do
  let ρ : PRen (f ++ .frame :: S) S :=
    ⟨fun i => ((PRen.dropL f (.frame :: S)).ren i).bind (PRen.drop S .frame).ren⟩
  let σ' ← ((σ.dropL f).dropL [.frame]).mapM (Value.prename ρ)
  let v' ← v.prename ρ
  pure (σ', v')

/-! ## Stack typings (including `Δ`) -/

/-- `SlotTys Γ S`: the stack typing for the binders `S`, all types and loans in
scope `Γ`.  Type-level binders (`Δ`) are entries of the same telescope. -/
inductive SlotTys (Γ : Ctx) : Ctx → Type where
  | nil : SlotTys Γ []
  /-- `x : τ^SX` -/
  | var {S : Ctx} (τ : MTy Γ) (Γs : SlotTys Γ S) : SlotTys Γ (.var :: S)
  /-- `r ↦ {ℓ̄}` -/
  | rgn {S : Ctx} (loans : List (Loan Γ)) (Γs : SlotTys Γ S) : SlotTys Γ (.rgn :: S)
  /-- frame boundary `‡` -/
  | frame {S : Ctx} (Γs : SlotTys Γ S) : SlotTys Γ (.frame :: S)
  /-- `φ : FRM`, `ϱ : RGN`, `α : TYPE` -/
  | fvar {S : Ctx} (Γs : SlotTys Γ S) : SlotTys Γ (.fvar :: S)
  | abs {S : Ctx} (Γs : SlotTys Γ S) : SlotTys Γ (.abs :: S)
  | tvar {S : Ctx} (Γs : SlotTys Γ S) : SlotTys Γ (.tvar :: S)

/-- The typing environment of a judgment: the paper's `Δ` and `Γ` in one,
indexed by the scope of the term being typed. -/
structure StackTy (S : Ctx) where
  slots : SlotTys S S
  /-- the outlives constraints `ϱ₁ :> ϱ₂` of `Δ` -/
  outlives : List (In .abs S × In .abs S)

/-- Total lookup of the type of a variable. -/
def SlotTys.varTy {Γ : Ctx} : {S : Ctx} → SlotTys Γ S → In .var S → MTy Γ
  | _, .var τ _, .here => τ
  | _, .var _ Γs, .there i => Γs.varTy i
  | _, .rgn _ Γs, .there i => Γs.varTy i
  | _, .frame Γs, .there i => Γs.varTy i
  | _, .fvar Γs, .there i => Γs.varTy i
  | _, .abs Γs, .there i => Γs.varTy i
  | _, .tvar Γs, .there i => Γs.varTy i

/-- Total lookup of the loan set of a concrete region. -/
def SlotTys.loans {Γ : Ctx} : {S : Ctx} → SlotTys Γ S → In .rgn S → List (Loan Γ)
  | _, .rgn L _, .here => L
  | _, .var _ Γs, .there i => Γs.loans i
  | _, .rgn _ Γs, .there i => Γs.loans i
  | _, .frame Γs, .there i => Γs.loans i
  | _, .fvar Γs, .there i => Γs.loans i
  | _, .abs Γs, .there i => Γs.loans i
  | _, .tvar Γs, .there i => Γs.loans i

/-! ## Examples -/

/-- `let x : bool = true; x`, a closed program. -/
def exLet : Program :=
  .letE .bool (.val (.prim (.bool true))) (.place ⟨.here, []⟩)

/-- The stack `[‡, x ↦ 5]`: one frame holding one variable. -/
def exStack : Stack ([.var] ++ .frame :: []) := .var (.prim (.num 5)) (.frame .nil)

/-- The configuration of `not_preservation`: `framed (ptr x)` with `x` in the
frame being popped.  In the scoped design `E-Framed` cannot even produce the
dangling pointer: popping the frame fails. -/
theorem framedPop_dangling :
    Stack.popFrame [.var] exStack (.ptr ⟨.here, []⟩) = none := rfl

/-- Popping succeeds when the result does not mention the frame. -/
theorem framedPop_ok :
    (Stack.popFrame [.var] exStack (.prim (.num 7))).isSome = true := rfl

end Oxide.Scoped
