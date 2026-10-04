module

public import RequestProject.Oxide.Syntax.Types

/-!
# Oxide syntax, part 4: environments for typechecking

Paper §3.3 ("Environments for Typechecking"), Figure "Environments in Oxide":
frame typings `Φ`, stack typings `Γ`, temporary typings `Θ` and type
environments `Δ`.

The paper's `Δ` and `Γ` are one telescope here: a `StackTy S` has one entry per
binder of the scope `S` — the type of each variable, the loan set of each
concrete region, frame boundaries, and markers for the type-level binders of `Δ`
— together with the outlives constraints `ϱ₁ :> ϱ₂` of `Δ`.  Lookups are total.

The stack typing is *flat*: every entry lives in the scope of the whole stack,
because older entries may legitimately refer to newer ones (a region of an older
frame may hold a loan to a newer variable).  Pushing an entry therefore weakens
all the others, and popping one *strengthens* them, which may fail.
-/

@[expose] public section

namespace Oxide

/-- `SlotTys Γ S`: the entries of a stack typing for the binders `S`, all types
and loans in scope `Γ`. -/
inductive SlotTys (Γ : Ctx) : Ctx → Type where
  | nil : SlotTys Γ []
  /-- `x : τ^SX` -/
  | var {S : Ctx} (τ : MTy Γ) (Γs : SlotTys Γ S) : SlotTys Γ (.var :: S)
  /-- `r ↦ {ℓ̄}` -/
  | rgn {S : Ctx} (loans : List (Loan Γ)) (Γs : SlotTys Γ S) : SlotTys Γ (.rgn :: S)
  /-- frame boundary `‡` -/
  | frame {S : Ctx} (Γs : SlotTys Γ S) : SlotTys Γ (.frame :: S)
  /-- `φ : FRM` -/
  | fvar {S : Ctx} (Γs : SlotTys Γ S) : SlotTys Γ (.fvar :: S)
  /-- `ϱ : RGN` -/
  | abs {S : Ctx} (Γs : SlotTys Γ S) : SlotTys Γ (.abs :: S)
  /-- `α : TYPE` -/
  | tvar {S : Ctx} (Γs : SlotTys Γ S) : SlotTys Γ (.tvar :: S)

/-- Stack typings `Γ` together with the type environment `Δ`, indexed by the scope
of the term being typed. -/
structure StackTy (S : Ctx) where
  slots : SlotTys S S
  /-- the outlives constraints `ϱ₁ :> ϱ₂` of `Δ` -/
  outlives : List (In .abs S × In .abs S) := []

/-- Temporary (continuation) typings `Θ`. -/
abbrev TempTy (S : Ctx) := List (Ty S)

namespace SlotTys

/-- The empty stack typing entries for a scope without variables and regions. -/
def markers : (S : Ctx) → {Γ : Ctx} → SlotTys Γ S
  | [], _ => .nil
  | .var :: S, _ => .var (.dead .unit) (markers S)
  | .rgn :: S, _ => .rgn [] (markers S)
  | .frame :: S, _ => .frame (markers S)
  | .fvar :: S, _ => .fvar (markers S)
  | .abs :: S, _ => .abs (markers S)
  | .tvar :: S, _ => .tvar (markers S)

/-- Transform all the types and loan sets. -/
def map {Γ Δ : Ctx} (fτ : MTy Γ → MTy Δ) (fL : List (Loan Γ) → List (Loan Δ)) :
    {S : Ctx} → SlotTys Γ S → SlotTys Δ S
  | _, .nil => .nil
  | _, .var τ Γs => .var (fτ τ) (Γs.map fτ fL)
  | _, .rgn L Γs => .rgn (fL L) (Γs.map fτ fL)
  | _, .frame Γs => .frame (Γs.map fτ fL)
  | _, .fvar Γs => .fvar (Γs.map fτ fL)
  | _, .abs Γs => .abs (Γs.map fτ fL)
  | _, .tvar Γs => .tvar (Γs.map fτ fL)

/-- Transform all the types and loan sets, possibly failing. -/
def mapM {Γ Δ : Ctx} (fτ : MTy Γ → Option (MTy Δ)) (fL : List (Loan Γ) → Option (List (Loan Δ))) :
    {S : Ctx} → SlotTys Γ S → Option (SlotTys Δ S)
  | _, .nil => some .nil
  | _, .var τ Γs => do pure (.var (← fτ τ) (← Γs.mapM fτ fL))
  | _, .rgn L Γs => do pure (.rgn (← fL L) (← Γs.mapM fτ fL))
  | _, .frame Γs => (Γs.mapM fτ fL).map .frame
  | _, .fvar Γs => (Γs.mapM fτ fL).map .fvar
  | _, .abs Γs => (Γs.mapM fτ fL).map .abs
  | _, .tvar Γs => (Γs.mapM fτ fL).map .tvar

/-- Rename all the types and loans. -/
def rename {Γ Δ : Ctx} (ρ : TRen Γ Δ) {S : Ctx} (Γs : SlotTys Γ S) : SlotTys Δ S :=
  Γs.map (MTy.rename ρ) (List.map (Loan.rename ρ))

/-- Strengthen all the types and loans (fails if one mentions a removed binder). -/
def prename {Γ Δ : Ctx} (ρ : PRen Γ Δ) {S : Ctx} (Γs : SlotTys Γ S) : Option (SlotTys Δ S) :=
  Γs.mapM (MTy.prename ρ) (List.mapM (Loan.prename ρ))

/-- `Γ(x)`: the type of a variable (total). -/
def varTy {Γ : Ctx} : {S : Ctx} → SlotTys Γ S → In .var S → MTy Γ
  | _, .var τ _, .here => τ
  | _, .var _ Γs, .there i => Γs.varTy i
  | _, .rgn _ Γs, .there i => Γs.varTy i
  | _, .frame Γs, .there i => Γs.varTy i
  | _, .fvar Γs, .there i => Γs.varTy i
  | _, .abs Γs, .there i => Γs.varTy i
  | _, .tvar Γs, .there i => Γs.varTy i

/-- `Γ[x ↦ τ]`. -/
def setVarTy {Γ : Ctx} : {S : Ctx} → SlotTys Γ S → In .var S → MTy Γ → SlotTys Γ S
  | _, .var _ Γs, .here, τ => .var τ Γs
  | _, .var σ Γs, .there i, τ => .var σ (Γs.setVarTy i τ)
  | _, .rgn L Γs, .there i, τ => .rgn L (Γs.setVarTy i τ)
  | _, .frame Γs, .there i, τ => .frame (Γs.setVarTy i τ)
  | _, .fvar Γs, .there i, τ => .fvar (Γs.setVarTy i τ)
  | _, .abs Γs, .there i, τ => .abs (Γs.setVarTy i τ)
  | _, .tvar Γs, .there i, τ => .tvar (Γs.setVarTy i τ)

/-- `Γ(r)`: the loan set of a concrete region (total). -/
def loans {Γ : Ctx} : {S : Ctx} → SlotTys Γ S → In .rgn S → List (Loan Γ)
  | _, .rgn L _, .here => L
  | _, .var _ Γs, .there i => Γs.loans i
  | _, .rgn _ Γs, .there i => Γs.loans i
  | _, .frame Γs, .there i => Γs.loans i
  | _, .fvar Γs, .there i => Γs.loans i
  | _, .abs Γs, .there i => Γs.loans i
  | _, .tvar Γs, .there i => Γs.loans i

/-- `Γ[r ↦ {ℓ̄}]`. -/
def setLoans {Γ : Ctx} : {S : Ctx} → SlotTys Γ S → In .rgn S → List (Loan Γ) → SlotTys Γ S
  | _, .rgn _ Γs, .here, L => .rgn L Γs
  | _, .var τ Γs, .there i, L => .var τ (Γs.setLoans i L)
  | _, .rgn L' Γs, .there i, L => .rgn L' (Γs.setLoans i L)
  | _, .frame Γs, .there i, L => .frame (Γs.setLoans i L)
  | _, .fvar Γs, .there i, L => .fvar (Γs.setLoans i L)
  | _, .abs Γs, .there i, L => .abs (Γs.setLoans i L)
  | _, .tvar Γs, .there i, L => .tvar (Γs.setLoans i L)

/-- Transform every loan set, knowing the region it belongs to. -/
def mapLoans {Γ : Ctx} : {S : Ctx} → (In .rgn S → List (Loan Γ) → List (Loan Γ)) →
    SlotTys Γ S → SlotTys Γ S
  | _, _, .nil => .nil
  | _, f, .var τ Γs => .var τ (Γs.mapLoans fun r => f r.there)
  | _, f, .rgn L Γs => .rgn (f .here L) (Γs.mapLoans fun r => f r.there)
  | _, f, .frame Γs => .frame (Γs.mapLoans fun r => f r.there)
  | _, f, .fvar Γs => .fvar (Γs.mapLoans fun r => f r.there)
  | _, f, .abs Γs => .abs (Γs.mapLoans fun r => f r.there)
  | _, f, .tvar Γs => .tvar (Γs.mapLoans fun r => f r.there)

/-- All variables with their types. -/
def varTys {Γ : Ctx} : {S : Ctx} → SlotTys Γ S → List (In .var S × MTy Γ)
  | _, .nil => []
  | _, .var τ Γs => (.here, τ) :: (Γs.varTys.map fun p => (p.1.there, p.2))
  | _, .rgn _ Γs => Γs.varTys.map fun p => (p.1.there, p.2)
  | _, .frame Γs => Γs.varTys.map fun p => (p.1.there, p.2)
  | _, .fvar Γs => Γs.varTys.map fun p => (p.1.there, p.2)
  | _, .abs Γs => Γs.varTys.map fun p => (p.1.there, p.2)
  | _, .tvar Γs => Γs.varTys.map fun p => (p.1.there, p.2)

/-- All concrete regions with their loan sets. -/
def rgnLoans {Γ : Ctx} : {S : Ctx} → SlotTys Γ S → List (In .rgn S × List (Loan Γ))
  | _, .nil => []
  | _, .var _ Γs => Γs.rgnLoans.map fun p => (p.1.there, p.2)
  | _, .rgn L Γs => (.here, L) :: (Γs.rgnLoans.map fun p => (p.1.there, p.2))
  | _, .frame Γs => Γs.rgnLoans.map fun p => (p.1.there, p.2)
  | _, .fvar Γs => Γs.rgnLoans.map fun p => (p.1.there, p.2)
  | _, .abs Γs => Γs.rgnLoans.map fun p => (p.1.there, p.2)
  | _, .tvar Γs => Γs.rgnLoans.map fun p => (p.1.there, p.2)

/-- Concatenate the entries of a prefix `cs` with those of the rest. -/
def append {Γ : Ctx} : {cs S : Ctx} → SlotTys Γ cs → SlotTys Γ S → SlotTys Γ (cs ++ S)
  | _, _, .nil, b => b
  | _, _, .var τ a, b => .var τ (a.append b)
  | _, _, .rgn L a, b => .rgn L (a.append b)
  | _, _, .frame a, b => .frame (a.append b)
  | _, _, .fvar a, b => .fvar (a.append b)
  | _, _, .abs a, b => .abs (a.append b)
  | _, _, .tvar a, b => .tvar (a.append b)

/-- Drop the entries of a prefix `cs`. -/
def dropL {Γ : Ctx} : (cs : Ctx) → {S : Ctx} → SlotTys Γ (cs ++ S) → SlotTys Γ S
  | [], _, Γs => Γs
  | .var :: cs, _, .var _ Γs => Γs.dropL cs
  | .rgn :: cs, _, .rgn _ Γs => Γs.dropL cs
  | .frame :: cs, _, .frame Γs => Γs.dropL cs
  | .fvar :: cs, _, .fvar Γs => Γs.dropL cs
  | .abs :: cs, _, .abs Γs => Γs.dropL cs
  | .tvar :: cs, _, .tvar Γs => Γs.dropL cs

/-- The entries of a frame typing. -/
def ofFrameTy {Γ : Ctx} : {f : Ctx} → FrameTy Γ f → SlotTys Γ f
  | _, .nil => .nil
  | _, .var τ Φ => .var (.init τ) (ofFrameTy Φ)
  | _, .rgn L Φ => .rgn L (ofFrameTy Φ)

/-- The entries for `k` parameters. -/
def ofVars {Γ : Ctx} : {k : Nat} → (Fin k → MTy Γ) → SlotTys Γ (vars k)
  | 0, _ => .nil
  | _ + 1, τs => .var (τs 0) (ofVars fun i => τs i.succ)

end SlotTys

namespace StackTy

variable {S : Ctx}

/-- `Γ(x)`. -/
def varTy (Γ : StackTy S) (x : In .var S) : MTy S := Γ.slots.varTy x

/-- `Γ[x ↦ τ]`. -/
def setVarTy (Γ : StackTy S) (x : In .var S) (τ : MTy S) : StackTy S :=
  { Γ with slots := Γ.slots.setVarTy x τ }

/-- `Γ(r)`. -/
def loans (Γ : StackTy S) (r : In .rgn S) : List (Loan S) := Γ.slots.loans r

/-- `Γ[r ↦ {ℓ̄}]`. -/
def setLoans (Γ : StackTy S) (r : In .rgn S) (L : List (Loan S)) : StackTy S :=
  { Γ with slots := Γ.slots.setLoans r L }

/-- Transform every loan set. -/
def mapLoans (Γ : StackTy S) (f : In .rgn S → List (Loan S) → List (Loan S)) : StackTy S :=
  { Γ with slots := Γ.slots.mapLoans f }

/-- Rename (in particular, weaken) a stack typing.  The shape stays the same, the
entries are renamed. -/
def renameEntries {S' : Ctx} (ρ : TRen S S') (Γ : StackTy S) : SlotTys S' S := Γ.slots.rename ρ

/-- `Γ, x : τ`: push a variable. -/
def pushVar (Γ : StackTy S) (τ : MTy (.var :: S)) : StackTy (.var :: S) where
  slots := .var τ (Γ.renameEntries (TRen.wk S .var))
  outlives := Γ.outlives.map fun p => (p.1.there, p.2.there)

/-- `Γ, r ↦ {ℓ̄}`: push a region. -/
def pushRgn (Γ : StackTy S) (L : List (Loan (.rgn :: S))) : StackTy (.rgn :: S) where
  slots := .rgn L (Γ.renameEntries (TRen.wk S .rgn))
  outlives := Γ.outlives.map fun p => (p.1.there, p.2.there)

/-- `Γ ‡ Φ`: push a frame of shape `f`. -/
def pushFrame {f : Ctx} (Γ : StackTy S) (Φ : FrameTy (f ++ .frame :: S) f) :
    StackTy (f ++ .frame :: S) where
  slots := (SlotTys.ofFrameTy Φ).append (.frame (Γ.renameEntries (TRen.wkFrame f S)))
  outlives := Γ.outlives.map fun p => ((TRen.wkFrame f S).ren p.1, (TRen.wkFrame f S).ren p.2)

/-- Push `k` parameters (given in the current scope). -/
def pushVars {k : Nat} (Γ : StackTy S) (τs : Fin k → Ty S) : StackTy (vars k ++ S) where
  slots := (SlotTys.ofVars fun i => .init ((τs i).wkL (vars k))).append
    (Γ.renameEntries (TRen.wkL S (vars k)))
  outlives := Γ.outlives.map fun p => ((TRen.wkL S (vars k)).ren p.1, (TRen.wkL S (vars k)).ren p.2)

/-- Pop the entries of a prefix `cs`: the remaining entries are strengthened, which
fails if one of them still mentions a popped binder. -/
def popL (cs : Ctx) (Γ : StackTy (cs ++ S)) : Option (StackTy S) := do
  let ρ := PRen.dropL cs S
  let slots ← (Γ.slots.dropL cs).prename ρ
  let outlives ← Γ.outlives.mapM fun p => do pure ((← ρ.ren p.1), (← ρ.ren p.2))
  pure ⟨slots, outlives⟩

/-- Pop a frame of shape `f` holding `k` parameters on top. -/
def popFrame (k : Nat) (f : Ctx) (Γ : StackTy (vars k ++ (f ++ .frame :: S))) : Option (StackTy S) := do
  let Γ₁ ← Γ.popL (vars k)
  let Γ₂ ← Γ₁.popL f
  Γ₂.popL [.frame]

/-- The type environment of a polymorphic signature: markers for its binders and
its bounds. -/
def ofBinders (b : Binders) (bounds : List (Fin b.nϱ × Fin b.nϱ)) : StackTy b.ctx where
  slots := SlotTys.markers b.ctx
  outlives := bounds.map fun p =>
    (In.weakenL (List.replicate b.nα .tvar) (In.ofFin p.1 (List.replicate b.nφ .fvar)),
     In.weakenL (List.replicate b.nα .tvar) (In.ofFin p.2 (List.replicate b.nφ .fvar)))

/-- `Δ, φ̄ : FRM, ϱ̄ : RGN, ᾱ : TYPE, ϱᵢ :> ϱⱼ`: extend the type environment with the
binders and bounds of a polymorphic signature. -/
def pushBinders (Γ : StackTy S) (b : Binders) (bs : List (Fin b.nϱ × Fin b.nϱ)) :
    StackTy (b.ctx ++ S) where
  slots := (SlotTys.markers b.ctx).append (Γ.renameEntries (TRen.wkL S b.ctx))
  outlives := bs.map (fun p => (b.absIdx p.1, b.absIdx p.2)) ++
    Γ.outlives.map fun p => ((TRen.wkL S b.ctx).ren p.1, (TRen.wkL S b.ctx).ren p.2)

/-- The empty stack typing. -/
def empty : StackTy [] := ⟨.nil, []⟩

end StackTy

end Oxide
