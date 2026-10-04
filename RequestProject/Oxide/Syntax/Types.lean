module

public import RequestProject.Oxide.Syntax.Places

/-!
# Oxide syntax, part 2: types

Paper §3.2 ("Types in Oxide"), Figure "Type Syntax of Oxide"; appendix A.  Frame
expressions and frame typings (paper §3.3) are defined here as well, since they
are mutually inductive with types (a closure type records its captured frame).

`Ty Γ` is indexed by the scope `Γ`, so every region, type variable, frame
variable and loan in a type is in scope by construction.  The paper's *sorts* of
types are separate families instead of predicates on one datatype:

* `Ty Γ`  — sized, initialized types `τ^SI`;
* `XTy Γ` — maybe-unsized types `τ^XI` (what a reference may point to);
* `MTy Γ` — maybe-dead types `τ^SX` (what the stack typing records for a
  variable, possibly partially moved): a declared type `τ` together with an
  initialization state `MTy.Of τ` *indexed by* `τ`.

Projection paths into a type are `TyPath τ`, indexed by the type, so a path
never names a missing field; untyped `List Nat` paths are converted once
(`TyPath.ofList`).

So an array of slices `[[τ]; n]`, a dead `let` annotation or a slice as a
closure parameter cannot even be written.
-/

@[expose] public section

namespace Oxide

/-- The binders of a polymorphic signature `<φ̄, ϱ̄, ᾱ>`. -/
structure Binders where
  nφ : Nat := 0
  nϱ : Nat := 0
  nα : Nat := 0
  deriving DecidableEq, Repr

/-- The scope extension made by the binders `<φ̄, ϱ̄, ᾱ>` (most recent first):
the `i`-th type variable is the `i`-th binder, then come the abstract regions and
the frame variables. -/
abbrev Binders.ctx (b : Binders) : Ctx :=
  List.replicate b.nα .tvar ++ (List.replicate b.nϱ .abs ++ List.replicate b.nφ .fvar)

/-- The `i`-th abstract region bound by a signature. -/
def Binders.absIdx {Γ : Ctx} (b : Binders) (i : Fin b.nϱ) : In .abs (b.ctx ++ Γ) :=
  In.inlL (In.weakenL (List.replicate b.nα .tvar) (In.ofFin i (List.replicate b.nφ .fvar)))

/-- Regions `ρ ::= ϱ | r`: an abstract region or a concrete region, both in
scope.  (`letrgn` simply binds a `.rgn`; there is no "opened" form.) -/
inductive Region (Γ : Ctx) where
  | abs (i : In .abs Γ)
  | conc (r : In .rgn Γ)
  deriving DecidableEq, Repr

mutual
/-- Sized, initialized types `τ^SI`. -/
inductive Ty : Ctx → Type where
  | base {Γ : Ctx} (b : BaseTy) : Ty Γ
  | tvar {Γ : Ctx} (α : In .tvar Γ) : Ty Γ
  /-- `&ρ ω τ^XI` -/
  | ref {Γ : Ctx} (ρ : Region Γ) (ω : Own) (τ : XTy Γ) : Ty Γ
  /-- `[τ; n]` -/
  | array {Γ : Ctx} (τ : Ty Γ) (n : Nat) : Ty Γ
  /-- `(τ₁, …, τ_k)` -/
  | tuple {Γ : Ctx} (k : Nat) (τs : Fin k → Ty Γ) : Ty Γ
  /-- `Either<τ₁, τ₂>` -/
  | sum {Γ : Ctx} (τ₁ τ₂ : Ty Γ) : Ty Γ
  /-- `∀<φ̄, ϱ̄, ᾱ>(τ₁, …, τ_k) →^Φ τ_r where ϱᵢ : ϱⱼ`: the parameters, the
  captured environment and the return type live in the extended scope; the bounds
  can only name the bound abstract regions.  Closure types have no binders. -/
  | fn {Γ : Ctx} (b : Binders) (k : Nat) (params : Fin k → Ty (b.ctx ++ Γ))
      (ret : Ty (b.ctx ++ Γ)) (env : FrameExpr (b.ctx ++ Γ))
      (bounds : List (Fin b.nϱ × Fin b.nϱ)) : Ty Γ
/-- Maybe-unsized types `τ^XI`. -/
inductive XTy : Ctx → Type where
  | sized {Γ : Ctx} (τ : Ty Γ) : XTy Γ
  /-- `[τ]` -/
  | slice {Γ : Ctx} (τ : Ty Γ) : XTy Γ
/-- Frame expressions `Φ ::= φ | Φ_frame`.  A literal frame of shape `f` is typed
in the scope where that frame has been pushed (`f ++ ‡ :: Γ`), so its types may
mention the frame's own regions. -/
inductive FrameExpr : Ctx → Type where
  | var {Γ : Ctx} (φ : In .fvar Γ) : FrameExpr Γ
  | frame {Γ : Ctx} (f : Ctx) (Φ : FrameTy (f ++ .frame :: Γ) f) : FrameExpr Γ
/-- `FrameTy Γ f`: a frame typing for a frame of shape `f`, all of whose types
and loans live in scope `Γ`.  Only `.var` and `.rgn` entries exist. -/
inductive FrameTy : Ctx → Ctx → Type where
  | nil {Γ : Ctx} : FrameTy Γ []
  | var {Γ f : Ctx} (τ : Ty Γ) (Φ : FrameTy Γ f) : FrameTy Γ (.var :: f)
  | rgn {Γ f : Ctx} (loans : List (Loan Γ)) (Φ : FrameTy Γ f) : FrameTy Γ (.rgn :: f)
end

instance {Γ : Ctx} : Inhabited (Ty Γ) := ⟨.base .unit⟩

namespace Ty
def bool {Γ : Ctx} : Ty Γ := .base .bool
def u32 {Γ : Ctx} : Ty Γ := .base .u32
def unit {Γ : Ctx} : Ty Γ := .base .unit

/-- A closure type `(τ₁, …, τ_k) →^Φ τ_r` (no binders, no bounds). -/
def closure {Γ : Ctx} (k : Nat) (ps : Fin k → Ty Γ) (ret : Ty Γ) (env : FrameExpr Γ) : Ty Γ :=
  .fn {} k ps ret env []
end Ty

/-- The empty frame expression. -/
def FrameExpr.empty {Γ : Ctx} : FrameExpr Γ := .frame [] .nil

/-! ## Renaming -/

def Region.rename {Γ Δ : Ctx} (ρ : TRen Γ Δ) : Region Γ → Region Δ
  | .abs i => .abs (ρ.ren i)
  | .conc r => .conc (ρ.ren r)

mutual
def Ty.rename {Γ Δ : Ctx} (ρ : TRen Γ Δ) : Ty Γ → Ty Δ
  | .base b => .base b
  | .tvar α => .tvar (ρ.ren α)
  | .ref r ω τ => .ref (r.rename ρ) ω (τ.rename ρ)
  | .array τ n => .array (τ.rename ρ) n
  | .tuple k τs => .tuple k fun i => (τs i).rename ρ
  | .sum τ₁ τ₂ => .sum (τ₁.rename ρ) (τ₂.rename ρ)
  | .fn b k ps ret env bs =>
      .fn b k (fun i => (ps i).rename (ρ.liftN b.ctx)) (ret.rename (ρ.liftN b.ctx))
        (env.rename (ρ.liftN b.ctx)) bs
def XTy.rename {Γ Δ : Ctx} (ρ : TRen Γ Δ) : XTy Γ → XTy Δ
  | .sized τ => .sized (τ.rename ρ)
  | .slice τ => .slice (τ.rename ρ)
def FrameExpr.rename {Γ Δ : Ctx} (ρ : TRen Γ Δ) : FrameExpr Γ → FrameExpr Δ
  | .var φ => .var (ρ.ren φ)
  | .frame f Φ => .frame f (Φ.rename ((ρ.lift .frame).liftN f))
def FrameTy.rename {Γ Δ : Ctx} (ρ : TRen Γ Δ) : {f : Ctx} → FrameTy Γ f → FrameTy Δ f
  | _, .nil => .nil
  | _, .var τ Φ => .var (τ.rename ρ) (Φ.rename ρ)
  | _, .rgn L Φ => .rgn (L.map (Loan.rename ρ)) (Φ.rename ρ)
end

/-- Weakening of a type by one binder. -/
abbrev Ty.wk {Γ : Ctx} (c : Bnd) (τ : Ty Γ) : Ty (c :: Γ) := τ.rename (TRen.wk Γ c)

/-- Weakening of a type by a prefix of binders. -/
abbrev Ty.wkL {Γ : Ctx} (cs : Ctx) (τ : Ty Γ) : Ty (cs ++ Γ) := τ.rename (TRen.wkL Γ cs)

/-! ## Strengthening (partial renaming) -/

def Region.prename {Γ Δ : Ctx} (ρ : PRen Γ Δ) : Region Γ → Option (Region Δ)
  | .abs i => (ρ.ren i).map .abs
  | .conc r => (ρ.ren r).map .conc

mutual
def Ty.prename {Γ Δ : Ctx} (ρ : PRen Γ Δ) : Ty Γ → Option (Ty Δ)
  | .base b => some (.base b)
  | .tvar α => (ρ.ren α).map .tvar
  | .ref r ω τ => do pure (.ref (← r.prename ρ) ω (← τ.prename ρ))
  | .array τ n => do pure (.array (← τ.prename ρ) n)
  | .tuple k τs => do pure (.tuple k (← optFin fun i => (τs i).prename ρ))
  | .sum τ₁ τ₂ => do pure (.sum (← τ₁.prename ρ) (← τ₂.prename ρ))
  | .fn b k ps ret env bs => do
      pure (.fn b k (← optFin fun i => (ps i).prename (ρ.liftN b.ctx))
        (← ret.prename (ρ.liftN b.ctx)) (← env.prename (ρ.liftN b.ctx)) bs)
def XTy.prename {Γ Δ : Ctx} (ρ : PRen Γ Δ) : XTy Γ → Option (XTy Δ)
  | .sized τ => (τ.prename ρ).map .sized
  | .slice τ => (τ.prename ρ).map .slice
def FrameExpr.prename {Γ Δ : Ctx} (ρ : PRen Γ Δ) : FrameExpr Γ → Option (FrameExpr Δ)
  | .var φ => (ρ.ren φ).map .var
  | .frame f Φ => (Φ.prename ((ρ.lift .frame).liftN f)).map (.frame f)
def FrameTy.prename {Γ Δ : Ctx} (ρ : PRen Γ Δ) : {f : Ctx} → FrameTy Γ f → Option (FrameTy Δ f)
  | _, .nil => some .nil
  | _, .var τ Φ => do pure (.var (← τ.prename ρ) (← Φ.prename ρ))
  | _, .rgn L Φ => do pure (.rgn (← L.mapM (Loan.prename ρ)) (← Φ.prename ρ))
end

/-! ## Paths into types -/

/-- Projection paths into a type: `proj i p` can only be applied to a tuple with
a field `i`. -/
inductive TyPath {Γ : Ctx} : Ty Γ → Type where
  | here {τ : Ty Γ} : TyPath τ
  | proj {k : Nat} {τs : Fin k → Ty Γ} (i : Fin k) (p : TyPath (τs i)) : TyPath (.tuple k τs)

namespace TyPath
variable {Γ : Ctx}

/-- The type at the end of a path. -/
def target : {τ : Ty Γ} → TyPath τ → Ty Γ
  | τ, .here => τ
  | _, .proj _ p => p.target

/-- The path as a list of field indices. -/
def toList : {τ : Ty Γ} → TyPath τ → List Nat
  | _, .here => []
  | _, .proj i p => i.val :: p.toList

/-- Convert an untyped path of projections into a typed one (the only place where
an out-of-range projection is detected). -/
def ofList : (τ : Ty Γ) → List Nat → Option (TyPath τ)
  | _, [] => some .here
  | .tuple k τs, i :: q => if h : i < k then (ofList (τs ⟨i, h⟩) q).map (.proj ⟨i, h⟩) else none
  | _, _ :: _ => none

/-- `τ` with the component at the end of the path replaced by `τ'`. -/
def replace : {τ : Ty Γ} → TyPath τ → Ty Γ → Ty Γ
  | _, .here, τ' => τ'
  | .tuple k τs, .proj i p, τ' => .tuple k fun j => if j = i then p.replace τ' else τs j

end TyPath

/-! ## Maybe-dead types -/

/-- The initialization state of a value of declared type `τ`: initialized, dead, or
(for a tuple) one state per field.  Since the state is indexed by the declared
type, a partially moved variable always keeps its declared type. -/
inductive MTy.Of {Γ : Ctx} : Ty Γ → Type where
  | init {τ : Ty Γ} : MTy.Of τ
  /-- `τ†` -/
  | dead {τ : Ty Γ} : MTy.Of τ
  /-- partially moved tuples -/
  | tuple {k : Nat} {τs : Fin k → Ty Γ} (ms : (i : Fin k) → MTy.Of (τs i)) : MTy.Of (.tuple k τs)

/-- Maybe-dead types `τ^SX`: a declared type and its initialization state. -/
structure MTy (Γ : Ctx) where
  ty : Ty Γ
  st : MTy.Of ty

namespace MTy.Of
variable {Γ : Ctx}

/-- The state of field `i` of a tuple. -/
def comp : {k : Nat} → {τs : Fin k → Ty Γ} → MTy.Of (.tuple k τs) → (i : Fin k) → MTy.Of (τs i)
  | _, _, .init, _ => .init
  | _, _, .dead, _ => .dead
  | _, _, .tuple ms, i => ms i

/-- Fully initialized. -/
def full : {τ : Ty Γ} → MTy.Of τ → Bool
  | _, .init => true
  | _, .dead => false
  | _, .tuple (k := k) ms => (List.finRange k).all fun i => (ms i).full

/-- Entirely dead (`τ^SD`). -/
def allDead : {τ : Ty Γ} → MTy.Of τ → Bool
  | _, .init => false
  | _, .dead => true
  | _, .tuple (k := k) ms => (List.finRange k).all fun i => (ms i).allDead

/-- Is literally `init`. -/
def isInit {τ : Ty Γ} : MTy.Of τ → Bool
  | .init => true
  | _ => false

/-- Is literally `dead`. -/
def isDead {τ : Ty Γ} : MTy.Of τ → Bool
  | .dead => true
  | _ => false

/-- The normalizing tuple constructor: a tuple all of whose fields are
initialized (resp. dead) is `init` (resp. `dead`).  Updates only produce
normalized states, so the duplicate encodings of the paper's grammar do not
arise. -/
def mkTuple {k : Nat} {τs : Fin k → Ty Γ} (ms : (i : Fin k) → MTy.Of (τs i)) : MTy.Of (.tuple k τs) :=
  if (List.finRange k).all fun i => (ms i).isInit then .init
  else if (List.finRange k).all fun i => (ms i).isDead then .dead
  else .tuple ms

/-- The (maybe-dead) type at the end of a path (total). -/
def get : {τ : Ty Γ} → MTy.Of τ → (p : TyPath τ) → MTy Γ
  | τ, m, .here => ⟨τ, m⟩
  | _, m, .proj i p => (m.comp i).get p

/-- Replace the component at the end of a path (total); the declared type of
that component becomes the type of the new component. -/
def set : {τ : Ty Γ} → MTy.Of τ → TyPath τ → MTy Γ → MTy Γ
  | _, _, .here, m' => m'
  | .tuple k τs, m, .proj i p, m' =>
      let ms : Fin k → MTy Γ := fun j => if j = i then (m.comp i).set p m' else ⟨τs j, m.comp j⟩
      ⟨.tuple k fun j => (ms j).ty, mkTuple fun j => (ms j).st⟩

end MTy.Of

namespace MTy
variable {Γ : Ctx}

/-- An initialized type. -/
def init (τ : Ty Γ) : MTy Γ := ⟨τ, .init⟩

/-- `τ†` -/
def dead (τ : Ty Γ) : MTy Γ := ⟨τ, .dead⟩

/-- A tuple of maybe-dead types. -/
def tuple (k : Nat) (ms : Fin k → MTy Γ) : MTy Γ :=
  ⟨.tuple k fun i => (ms i).ty, .tuple fun i => (ms i).st⟩

/-- A maybe-dead type that is fully initialized: its declared type. -/
def toTy? (m : MTy Γ) : Option (Ty Γ) := if m.st.full then some m.ty else none

/-- `τ^SD`: a type all of whose parts are dead. -/
def IsDead (m : MTy Γ) : Prop := m.st.allDead = true

end MTy

def MTy.Of.rename {Γ Δ : Ctx} (ρ : TRen Γ Δ) : {τ : Ty Γ} → MTy.Of τ → MTy Δ
  | τ, .init => .init (τ.rename ρ)
  | τ, .dead => .dead (τ.rename ρ)
  | _, .tuple (k := k) ms => .tuple k fun i => (ms i).rename ρ

def MTy.rename {Γ Δ : Ctx} (ρ : TRen Γ Δ) (m : MTy Γ) : MTy Δ := m.st.rename ρ

def MTy.Of.prename {Γ Δ : Ctx} (ρ : PRen Γ Δ) : {τ : Ty Γ} → MTy.Of τ → Option (MTy Δ)
  | τ, .init => (τ.prename ρ).map .init
  | τ, .dead => (τ.prename ρ).map .dead
  | _, .tuple (k := k) ms => (optFin fun i => (ms i).prename ρ).map (.tuple k)

def MTy.prename {Γ Δ : Ctx} (ρ : PRen Γ Δ) (m : MTy Γ) : Option (MTy Δ) := m.st.prename ρ

end Oxide
