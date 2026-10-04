module

public import RequestProject.Oxide.Syntax.Runtime

/-!
# Oxide metafunctions, part 1: types

Appendix C ("Metafunctions") of the paper; the syntactic categories of types
come from §3.2, paragraphs "Sized and Unsized Types" and "Initialized and Dead
Types".

Syntactic categories of types (`τ^SI`, `τ^XI`, `τ^SD`, `τ^SX`), de Bruijn
operations on types (shifting, instantiation of polymorphic signatures,
opening/closing of concrete-region binders), free regions, (non)copyability and
decomposition of types along paths.
-/

@[expose] public section

namespace Oxide

/-! ## Syntactic categories of types -/

/-- Sized and initialized types `τ^SI`. -/
inductive Ty.SI : Ty → Prop where
  | base (b : BaseTy) : Ty.SI (.base b)
  | tvar (i : Nat) : Ty.SI (.tvar i)
  | ref (ρ : Region) (ω : Own) (τ : Ty) (h : Ty.SI τ) : Ty.SI (.ref ρ ω τ)
  | refSlice (ρ : Region) (ω : Own) (τ : Ty) (h : Ty.SI τ) : Ty.SI (.ref ρ ω (.slice τ))
  | array (τ : Ty) (n : Nat) (h : Ty.SI τ) : Ty.SI (.array τ n)
  | tuple (τs : List Ty) (h : ∀ τ ∈ τs, Ty.SI τ) : Ty.SI (.tuple τs)
  | sum (τ₁ τ₂ : Ty) (h₁ : Ty.SI τ₁) (h₂ : Ty.SI τ₂) : Ty.SI (.sum τ₁ τ₂)
  | fn (nφ nϱ nα : Nat) (ps : List Ty) (r : Ty) (Φ : FrameExpr)
      (bs : List (Nat × Nat)) (hps : ∀ τ ∈ ps, Ty.SI τ) (hr : Ty.SI r) :
      Ty.SI (.fn nφ nϱ nα ps r Φ bs)

/-- Maybe-unsized initialized types `τ^XI ::= τ^SI | [τ^SI]`. -/
def Ty.XI (τ : Ty) : Prop := Ty.SI τ ∨ ∃ τ', τ = .slice τ' ∧ Ty.SI τ'

/-- Dead types `τ^SD ::= τ^SI† | (τ^SD, …)`. -/
inductive Ty.SD : Ty → Prop where
  | dead (τ : Ty) (h : Ty.SI τ) : Ty.SD (.dead τ)
  | tuple (τs : List Ty) (h : ∀ τ ∈ τs, Ty.SD τ) : Ty.SD (.tuple τs)

/-- Maybe-dead types `τ^SX ::= τ^SI | τ^SD | (τ^SX, …)`. -/
inductive Ty.SX : Ty → Prop where
  | si (τ : Ty) (h : Ty.SI τ) : Ty.SX τ
  | sd (τ : Ty) (h : Ty.SD τ) : Ty.SX τ
  | tuple (τs : List Ty) (h : ∀ τ ∈ τs, Ty.SX τ) : Ty.SX (.tuple τs)

/-! ## Frames: counting entries -/

namespace FrameTy
/-- Number of variable bindings in a frame. -/
def numVars (Φ : FrameTy) : Nat := Φ.countP fun | .var _ => true | .rgn _ => false
/-- Number of region bindings in a frame. -/
def numRgns (Φ : FrameTy) : Nat := Φ.countP fun | .var _ => false | .rgn _ => true
end FrameTy

/-! ## De Bruijn operations on types -/

/-- Binder depths when traversing a type: frame variables, abstract regions and
type variables bound by enclosing function types, and concrete regions bound by
enclosing closure frames (or, in terms, by `letrgn` and closure values). -/
structure Depth where
  frm : Nat := 0
  rgn : Nat := 0
  ty : Nat := 0
  bnd : Nat := 0

mutual
/-- Generic traversal of a type, replacing regions, type variables and frame
variables according to the current binder depth. -/
def Ty.map (fR : Depth → Region → Region) (fT : Depth → Nat → Ty)
    (fF : Depth → Nat → FrameExpr) (d : Depth) : Ty → Ty
  | .base b => .base b
  | .tvar i => fT d i
  | .ref ρ ω τ => .ref (fR d ρ) ω (τ.map fR fT fF d)
  | .array τ n => .array (τ.map fR fT fF d) n
  | .slice τ => .slice (τ.map fR fT fF d)
  | .tuple τs => .tuple (Ty.mapL fR fT fF d τs)
  | .sum τ₁ τ₂ => .sum (τ₁.map fR fT fF d) (τ₂.map fR fT fF d)
  | .fn nφ nϱ nα ps r Φ bs =>
      let d' : Depth := { d with frm := d.frm + nφ, rgn := d.rgn + nϱ, ty := d.ty + nα }
      .fn nφ nϱ nα (Ty.mapL fR fT fF d' ps) (r.map fR fT fF d') (FrameExpr.map fR fT fF d' Φ) bs
  | .dead τ => .dead (τ.map fR fT fF d)
/-- `Ty.map` on lists. -/
def Ty.mapL (fR : Depth → Region → Region) (fT : Depth → Nat → Ty)
    (fF : Depth → Nat → FrameExpr) (d : Depth) : List Ty → List Ty
  | [] => []
  | τ :: τs => τ.map fR fT fF d :: Ty.mapL fR fT fF d τs
/-- `Ty.map` on frame expressions (the region entries of a frame bind regions in
its variable entries). -/
def FrameExpr.map (fR : Depth → Region → Region) (fT : Depth → Nat → Ty)
    (fF : Depth → Nat → FrameExpr) (d : Depth) : FrameExpr → FrameExpr
  | .var i => fF d i
  | .frame Φ => .frame (FrameEntry.mapL fR fT fF { d with bnd := d.bnd + FrameTy.numRgns Φ } Φ)
/-- `Ty.map` on the entries of a frame. -/
def FrameEntry.mapL (fR : Depth → Region → Region) (fT : Depth → Nat → Ty)
    (fF : Depth → Nat → FrameExpr) (d : Depth) : List FrameEntry → List FrameEntry
  | [] => []
  | .var τ :: Φ => .var (τ.map fR fT fF d) :: FrameEntry.mapL fR fT fF d Φ
  | .rgn L :: Φ => .rgn L :: FrameEntry.mapL fR fT fF d Φ
end

/-- Amounts by which free de Bruijn indices are shifted. -/
abbrev Shift := Depth

/-- Shift the free indices (those not bound below the cutoff `d`) of a region. -/
def Region.shift (s : Shift) (d : Depth) : Region → Region
  | .abs i => .abs (if d.rgn ≤ i then i + s.rgn else i)
  | .bound i => .bound (if d.bnd ≤ i then i + s.bnd else i)
  | .conc ℓ => .conc ℓ

/-- Shift the free indices of a type by `s` (used when moving a type under binders). -/
def Ty.shift (s : Shift) : Ty → Ty :=
  Ty.map (fun d ρ => ρ.shift s d) (fun d i => .tvar (if d.ty ≤ i then i + s.ty else i))
    (fun d i => .var (if d.frm ≤ i then i + s.frm else i)) {}

/-- Shift the free indices of a frame expression. -/
def FrameExpr.shift (s : Shift) : FrameExpr → FrameExpr :=
  FrameExpr.map (fun d ρ => ρ.shift s d) (fun d i => .tvar (if d.ty ≤ i then i + s.ty else i))
    (fun d i => .var (if d.frm ≤ i then i + s.frm else i)) {}

/-- Instantiation `δ = [Φ̄/φ̄][ρ̄/ϱ̄][τ̄/ᾱ]` of the outermost binders of a polymorphic
signature: index `i` of each sort is replaced by the `i`-th argument; the
remaining free indices are lowered. -/
structure Inst where
  frames : List FrameExpr
  rgns : List Region
  tys : List Ty

namespace Inst
/-- Instantiate a region at depth `d`. -/
def rgn (δ : Inst) (d : Depth) : Region → Region
  | .abs i =>
      if i < d.rgn then .abs i
      else match δ.rgns[i - d.rgn]? with
        | some ρ => ρ.shift d {}
        | none => .abs (i - δ.rgns.length)
  | ρ => ρ
/-- Instantiate a type variable at depth `d`. -/
def tvar (δ : Inst) (d : Depth) (i : Nat) : Ty :=
  if i < d.ty then .tvar i
  else match δ.tys[i - d.ty]? with
    | some τ => τ.shift d
    | none => .tvar (i - δ.tys.length)
/-- Instantiate a frame variable at depth `d`. -/
def frm (δ : Inst) (d : Depth) (i : Nat) : FrameExpr :=
  if i < d.frm then .var i
  else match δ.frames[i - d.frm]? with
    | some Φ => Φ.shift d
    | none => .var (i - δ.frames.length)
end Inst

/-- Apply an instantiation to a type. -/
def Ty.inst (δ : Inst) : Ty → Ty := Ty.map δ.rgn δ.tvar δ.frm {}
/-- Apply an instantiation to a region. -/
def Region.inst (δ : Inst) : Region → Region := δ.rgn {}

/-- Open concrete-region binders: `bound (d + j) ↦ conc ls[j]` (where `d` is the
current binder depth), remaining free bound indices are lowered. -/
def Region.openAt (ls : List Nat) (d : Depth) : Region → Region
  | .bound i =>
      if i < d.bnd then .bound i
      else match ls[i - d.bnd]? with
        | some ℓ => .conc ℓ
        | none => .bound (i - ls.length)
  | ρ => ρ

/-- Close concrete regions: `conc rs[j] ↦ bound (d + j)`; free bound indices are
raised. -/
def Region.closeAt (rs : List Nat) (d : Depth) : Region → Region
  | .conc ℓ =>
      match rs.idxOf? ℓ with
      | some j => .bound (d.bnd + j)
      | none => .conc ℓ
  | .bound i => .bound (if d.bnd ≤ i then i + rs.length else i)
  | ρ => ρ

/-- Open the concrete-region binders of a type with the levels `ls`. -/
def Ty.openRgns (ls : List Nat) : Ty → Ty := Ty.map (Region.openAt ls) (fun _ i => .tvar i)
  (fun _ i => .var i) {}

/-- Close the concrete regions `rs` of a type. -/
def Ty.closeRgns (rs : List Nat) : Ty → Ty := Ty.map (Region.closeAt rs) (fun _ i => .tvar i)
  (fun _ i => .var i) {}

/-- The levels given to the `q` region entries of a frame pushed on a stack typing
with `base` regions: the `j`-th most recent one gets level `base + q - 1 - j`. -/
def newLevels (base q : Nat) : List Nat := (List.range q).map fun j => base + q - 1 - j

/-- A closed frame (as found in a closure type) opened for being pushed on a stack
typing that has `base` regions. -/
def FrameTy.openAt (base : Nat) (Φ : FrameTy) : FrameTy :=
  Φ.map fun
    | .var τ => .var (τ.openRgns (newLevels base Φ.numRgns))
    | .rgn L => .rgn L

/-! ## Regions occurring in types -/

mutual
/-- All concrete regions (levels) occurring in a type (`free-regions`, also used
for "`r` occurs in `τ`"). -/
def Ty.frgns : Ty → List Nat
  | .base _ => []
  | .tvar _ => []
  | .ref (.conc ℓ) _ τ => ℓ :: τ.frgns
  | .ref _ _ τ => τ.frgns
  | .array τ _ => τ.frgns
  | .slice τ => τ.frgns
  | .tuple τs => Ty.frgnsL τs
  | .sum τ₁ τ₂ => τ₁.frgns ++ τ₂.frgns
  | .fn _ _ _ ps r Φ _ => Ty.frgnsL ps ++ r.frgns ++ FrameExpr.frgns Φ
  | .dead τ => τ.frgns
/-- Concrete regions of a list of types. -/
def Ty.frgnsL : List Ty → List Nat
  | [] => []
  | τ :: τs => τ.frgns ++ Ty.frgnsL τs
/-- Concrete regions of a frame expression. -/
def FrameExpr.frgns : FrameExpr → List Nat
  | .var _ => []
  | .frame Φ => FrameEntry.frgnsL Φ
/-- Concrete regions of the entries of a frame. -/
def FrameEntry.frgnsL : List FrameEntry → List Nat
  | [] => []
  | .var τ :: Φ => τ.frgns ++ FrameEntry.frgnsL Φ
  | .rgn _ :: Φ => FrameEntry.frgnsL Φ
end

/-- Concrete regions occurring in a type *outside of* any function type. -/
def Ty.frgnsOut : Ty → List Nat
  | .ref (.conc ℓ) _ τ => ℓ :: τ.frgnsOut
  | .ref _ _ τ => τ.frgnsOut
  | .array τ _ => τ.frgnsOut
  | .slice τ => τ.frgnsOut
  | .tuple τs => (τs.attach.map fun ⟨τ, _⟩ => τ.frgnsOut).flatten
  | .sum τ₁ τ₂ => τ₁.frgnsOut ++ τ₂.frgnsOut
  | .dead τ => τ.frgnsOut
  | _ => []

/-- The function types `(params, ret, env)` occurring (anywhere) in a type. -/
def Ty.fnTypes : Ty → List (List Ty × Ty × FrameExpr)
  | .ref _ _ τ => τ.fnTypes
  | .array τ _ => τ.fnTypes
  | .slice τ => τ.fnTypes
  | .tuple τs => (τs.attach.map fun ⟨τ, _⟩ => τ.fnTypes).flatten
  | .sum τ₁ τ₂ => τ₁.fnTypes ++ τ₂.fnTypes
  | .fn _ _ _ ps r Φ _ =>
      (ps, r, Φ) :: ((ps.attach.map fun ⟨τ, _⟩ => τ.fnTypes).flatten ++ r.fnTypes)
  | .dead τ => τ.fnTypes
  | _ => []

/-- The captured frames `Φ_c` of closure types `(τ̄) →^{Φ_c} τ_r` occurring in a type. -/
def Ty.closureFrames (τ : Ty) : List FrameTy :=
  τ.fnTypes.filterMap fun
    | (_, _, .frame Φ) => some Φ
    | _ => none

/-! ## Copyability -/

/-- `noncopyable` (appendix "Metafunctions"). -/
def Ty.noncopyable : Ty → Bool
  | .base _ => false
  | .tvar _ => true
  | .ref _ .uniq _ => true
  | .ref _ .shrd _ => false
  | .fn .. => false
  | .array τ _ => τ.noncopyable
  | .slice τ => τ.noncopyable
  | .tuple τs => τs.attach.any fun ⟨τ, _⟩ => τ.noncopyable
  | .sum τ₁ τ₂ => τ₁.noncopyable || τ₂.noncopyable
  | .dead _ => true

/-- `copyable τ = ¬ noncopyable τ`. -/
def Ty.copyable (τ : Ty) : Bool := !τ.noncopyable

/-! ## Decomposition of types along paths -/

/-- `τ.q ⇝ τ_□ ⊞ τ'` (`D-End`, `D-Projection`): the component of `τ` at path `q`. -/
def Ty.atPath : Ty → List Nat → Option Ty
  | τ, [] => some τ
  | .tuple τs, i :: q => (τs[i]?).bind (·.atPath q)
  | _, _ :: _ => none

/-- Replace the component of `τ` at path `q` (i.e. `τ_□[τ']`). -/
def Ty.setPath : Ty → List Nat → Ty → Option Ty
  | _, [], τ' => some τ'
  | .tuple τs, i :: q, τ' =>
      match τs[i]? with
      | some τi => (τi.setPath q τ').map fun τi' => .tuple (τs.set i τi')
      | none => none
  | _, _ :: _, _ => none

end Oxide
