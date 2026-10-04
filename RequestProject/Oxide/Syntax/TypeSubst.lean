module

public import RequestProject.Oxide.Syntax.Types

/-!
# Oxide syntax, part 3: type-level substitutions, type arguments and closure scopes

* `TSub Γ Δ`: substitutions mapping the frame variables, abstract regions and type
  variables of `Γ` to frame expressions, regions and types in scope `Δ`, and
  renaming the variables and concrete regions.  They implement the instantiation
  `δ = [Φ̄/φ̄][ρ̄/ϱ̄][τ̄/ᾱ]` of a polymorphic signature (`T-AppFunction`,
  `E-AppFunction`).
* `TArgs b Γ`: the type arguments `::<Φ̄, ρ̄, τ̄>` of a call instantiating the binders
  `b`, bundled in one structure; `TArgs.toTSub` is the induced substitution out of
  `b.ctx`.
* `Inst o Γ`: an explicit, finite substitution of a *closure scope* `o` into `Γ`,
  with one entry per binder of `o`.  A closure body is written in its own scope
  (its parameters, its captured frame and the outer binders `o` it may mention);
  `Inst` says what each outer binder stands for.  Renaming, substituting or
  strengthening a closure only acts on its `Inst`, never on its body.
-/

@[expose] public section

namespace Oxide

/-- Type-level substitutions. -/
structure TSub (Γ Δ : Ctx) where
  fvar : In .fvar Γ → FrameExpr Δ
  abs : In .abs Γ → Region Δ
  tvar : In .tvar Γ → Ty Δ
  var : In .var Γ → In .var Δ
  rgn : In .rgn Γ → In .rgn Δ

namespace TSub

/-- The identity substitution. -/
def id (Γ : Ctx) : TSub Γ Γ := ⟨.var, .abs, .tvar, fun i => i, fun i => i⟩

/-- The substitution induced by a renaming. -/
def ofRen {Γ Δ : Ctx} (ρ : TRen Γ Δ) : TSub Γ Δ :=
  ⟨fun i => .var (ρ.ren i), fun i => .abs (ρ.ren i), fun i => .tvar (ρ.ren i), ρ.ren, ρ.ren⟩

/-- Lift a substitution under one binder. -/
def lift {Γ Δ : Ctx} (σ : TSub Γ Δ) (c : Bnd) : TSub (c :: Γ) (c :: Δ) where
  fvar := fun
    | .here => .var .here
    | .there i => (σ.fvar i).rename (TRen.wk Δ c)
  abs := fun
    | .here => .abs .here
    | .there i => (σ.abs i).rename (TRen.wk Δ c)
  tvar := fun
    | .here => .tvar .here
    | .there i => (σ.tvar i).rename (TRen.wk Δ c)
  var := fun
    | .here => .here
    | .there i => .there (σ.var i)
  rgn := fun
    | .here => .here
    | .there i => .there (σ.rgn i)

/-- Lift a substitution under a list of binders. -/
def liftN {Γ Δ : Ctx} (σ : TSub Γ Δ) : (cs : Ctx) → TSub (cs ++ Γ) (cs ++ Δ)
  | [] => σ
  | c :: cs => (σ.liftN cs).lift c

/-- Combine a substitution for a prefix `cs` with one for the rest of the scope. -/
def append {cs Γ Δ : Ctx} (σ₁ : TSub cs Δ) (σ₂ : TSub Γ Δ) : TSub (cs ++ Γ) Δ where
  fvar i := match In.split cs i with | .inl j => σ₁.fvar j | .inr j => σ₂.fvar j
  abs i := match In.split cs i with | .inl j => σ₁.abs j | .inr j => σ₂.abs j
  tvar i := match In.split cs i with | .inl j => σ₁.tvar j | .inr j => σ₂.tvar j
  var i := match In.split cs i with | .inl j => σ₁.var j | .inr j => σ₂.var j
  rgn i := match In.split cs i with | .inl j => σ₁.rgn j | .inr j => σ₂.rgn j

end TSub

/-! ## Applying substitutions to types -/

def Region.subst {Γ Δ : Ctx} (σ : TSub Γ Δ) : Region Γ → Region Δ
  | .abs i => σ.abs i
  | .conc r => .conc (σ.rgn r)

def APExpr.subst {Γ Δ : Ctx} (σ : TSub Γ Δ) : APExpr Γ → APExpr Δ
  | .place π => .place ⟨σ.var π.root, π.path⟩
  | .deref p q => .deref (p.subst σ) q

def Loan.subst {Γ Δ : Ctx} (σ : TSub Γ Δ) (l : Loan Γ) : Loan Δ := ⟨l.own, l.pe.subst σ⟩

mutual
def Ty.subst {Γ Δ : Ctx} (σ : TSub Γ Δ) : Ty Γ → Ty Δ
  | .base b => .base b
  | .tvar α => σ.tvar α
  | .ref r ω τ => .ref (r.subst σ) ω (τ.subst σ)
  | .array τ n => .array (τ.subst σ) n
  | .tuple k τs => .tuple k fun i => (τs i).subst σ
  | .sum τ₁ τ₂ => .sum (τ₁.subst σ) (τ₂.subst σ)
  | .fn b k ps ret env bs =>
      .fn b k (fun i => (ps i).subst (σ.liftN b.ctx)) (ret.subst (σ.liftN b.ctx))
        (env.subst (σ.liftN b.ctx)) bs
def XTy.subst {Γ Δ : Ctx} (σ : TSub Γ Δ) : XTy Γ → XTy Δ
  | .sized τ => .sized (τ.subst σ)
  | .slice τ => .slice (τ.subst σ)
def FrameExpr.subst {Γ Δ : Ctx} (σ : TSub Γ Δ) : FrameExpr Γ → FrameExpr Δ
  | .var φ => σ.fvar φ
  | .frame f Φ => .frame f (Φ.subst ((σ.lift .frame).liftN f))
def FrameTy.subst {Γ Δ : Ctx} (σ : TSub Γ Δ) : {f : Ctx} → FrameTy Γ f → FrameTy Δ f
  | _, .nil => .nil
  | _, .var τ Φ => .var (τ.subst σ) (Φ.subst σ)
  | _, .rgn L Φ => .rgn (L.map (Loan.subst σ)) (Φ.subst σ)
end

def MTy.Of.subst {Γ Δ : Ctx} (σ : TSub Γ Δ) : {τ : Ty Γ} → MTy.Of τ → MTy Δ
  | τ, .init => .init (τ.subst σ)
  | τ, .dead => .dead (τ.subst σ)
  | _, .tuple (k := k) ms => .tuple k fun i => (ms i).subst σ

def MTy.subst {Γ Δ : Ctx} (σ : TSub Γ Δ) (m : MTy Γ) : MTy Δ := m.st.subst σ

/-! ## Signatures and their instantiation -/

/-- An index of sort `b` into a block of binders of another sort does not exist. -/
def In.skipRep {b c : Bnd} (h : b ≠ c) {k : Nat} {Γ : Ctx} (i : In b (List.replicate k c ++ Γ)) :
    In b Γ :=
  match In.split (List.replicate k c) i with
  | .inl j => absurd (In.sort_of_replicate j) h
  | .inr j => j

/-- The position of an index into a block of binders of its own sort, or an index
into the rest of the scope. -/
def In.splitRep {b : Bnd} {k : Nat} {Γ : Ctx} (i : In b (List.replicate k b ++ Γ)) :
    Fin k ⊕ In b Γ :=
  (In.split (List.replicate k b) i).map In.toFin id

/-- The type arguments `::<Φ̄, ρ̄, τ̄>` instantiating the binders `b` of a
polymorphic signature: exactly `b.nφ` frames, `b.nϱ` regions and `b.nα` types. -/
structure TArgs (b : Binders) (Γ : Ctx) where
  frames : Fin b.nφ → FrameExpr Γ
  rgns : Fin b.nϱ → Region Γ
  tys : Fin b.nα → Ty Γ

namespace TArgs

/-- No type arguments (closure calls). -/
def none {Γ : Ctx} : TArgs {} Γ := ⟨Fin.elim0, Fin.elim0, Fin.elim0⟩

def rename {b : Binders} {Γ Δ : Ctx} (ρ : TRen Γ Δ) (θ : TArgs b Γ) : TArgs b Δ :=
  ⟨fun i => (θ.frames i).rename ρ, fun i => (θ.rgns i).rename ρ, fun i => (θ.tys i).rename ρ⟩

def prename {b : Binders} {Γ Δ : Ctx} (ρ : PRen Γ Δ) (θ : TArgs b Γ) : Option (TArgs b Δ) := do
  pure ⟨← optFin fun i => (θ.frames i).prename ρ, ← optFin fun i => (θ.rgns i).prename ρ,
    ← optFin fun i => (θ.tys i).prename ρ⟩

def subst {b : Binders} {Γ Δ : Ctx} (σ : TSub Γ Δ) (θ : TArgs b Γ) : TArgs b Δ :=
  ⟨fun i => (θ.frames i).subst σ, fun i => (θ.rgns i).subst σ, fun i => (θ.tys i).subst σ⟩

/-- The substitution `[Φ̄/φ̄][ρ̄/ϱ̄][τ̄/ᾱ]` of the binders of a signature (there
are no variables or concrete regions among them). -/
def toTSub {b : Binders} {Δ : Ctx} (θ : TArgs b Δ) : TSub b.ctx Δ where
  fvar i :=
    let j := (In.skipRep (by decide) (In.skipRep (by decide) i) : In .fvar (List.replicate b.nφ .fvar))
    θ.frames (In.toFin j)
  abs i :=
    match In.splitRep (In.skipRep (by decide) i : In .abs (List.replicate b.nϱ .abs ++ _)) with
    | .inl j => θ.rgns j
    | .inr j => absurd (In.sort_of_replicate j) (by decide)
  tvar i :=
    match In.splitRep (i : In .tvar (List.replicate b.nα .tvar ++ _)) with
    | .inl j => θ.tys j
    | .inr j => absurd (In.sort_of_replicate (In.skipRep (c := .abs) (by decide) j)) (by decide)
  var i := absurd (In.sort_of_replicate (In.skipRep (c := .abs) (by decide)
      (In.skipRep (c := .tvar) (by decide) i))) (by decide)
  rgn i := absurd (In.sort_of_replicate (In.skipRep (c := .abs) (by decide)
      (In.skipRep (c := .tvar) (by decide) i))) (by decide)

/-- The instantiation of the binders of a function type at the scope `Γ` of the
function type itself. -/
def inst {b : Binders} {Γ : Ctx} (θ : TArgs b Γ) : TSub (b.ctx ++ Γ) Γ :=
  θ.toTSub.append (TSub.id Γ)

end TArgs

/-- Instantiate a type in the scope of a function type's binders. -/
def Ty.inst {b : Binders} {Γ : Ctx} (θ : TArgs b Γ) (τ : Ty (b.ctx ++ Γ)) : Ty Γ := τ.subst θ.inst

/-- Instantiate a region in the scope of a function type's binders. -/
def Region.inst {b : Binders} {Γ : Ctx} (θ : TArgs b Γ) (ρ : Region (b.ctx ++ Γ)) : Region Γ :=
  ρ.subst θ.inst

/-- The abstract region bound as the `i`-th region binder of a signature. -/
def Binders.absAt {Γ : Ctx} (b : Binders) (i : Fin b.nϱ) : Region (b.ctx ++ Γ) :=
  .abs (b.absIdx i)

/-- Embed a closed signature (in scope `cs`) into any scope. -/
def TRen.inlL (cs Γ : Ctx) : TRen cs (cs ++ Γ) := ⟨In.inlL⟩

/-! ## Closure scopes -/

/-- What a binder of sort `b` stands for in scope `Γ`. -/
@[reducible] def Entry : Bnd → Ctx → Type
  | .fvar, Γ => FrameExpr Γ
  | .abs, Γ => Region Γ
  | .tvar, Γ => Ty Γ
  | .var, Γ => In .var Γ
  | .rgn, Γ => In .rgn Γ
  | .frame, _ => Unit

def Entry.rename {Γ Δ : Ctx} (ρ : TRen Γ Δ) : {b : Bnd} → Entry b Γ → Entry b Δ
  | .fvar, e => FrameExpr.rename ρ e
  | .abs, e => Region.rename ρ e
  | .tvar, e => Ty.rename ρ e
  | .var, e => ρ.ren (b := .var) e
  | .rgn, e => ρ.ren (b := .rgn) e
  | .frame, _ => ()

def Entry.prename {Γ Δ : Ctx} (ρ : PRen Γ Δ) : {b : Bnd} → Entry b Γ → Option (Entry b Δ)
  | .fvar, e => FrameExpr.prename ρ e
  | .abs, e => Region.prename ρ e
  | .tvar, e => Ty.prename ρ e
  | .var, e => ρ.ren (b := .var) e
  | .rgn, e => ρ.ren (b := .rgn) e
  | .frame, _ => some ()

def Entry.subst {Γ Δ : Ctx} (σ : TSub Γ Δ) : {b : Bnd} → Entry b Γ → Entry b Δ
  | .fvar, e => FrameExpr.subst σ e
  | .abs, e => Region.subst σ e
  | .tvar, e => Ty.subst σ e
  | .var, e => σ.var e
  | .rgn, e => σ.rgn e
  | .frame, _ => ()

/-- `Inst o Γ`: an entry in scope `Γ` for each binder of the closure scope `o`. -/
inductive Inst : Ctx → Ctx → Type where
  | nil {Γ : Ctx} : Inst [] Γ
  | cons {Γ o : Ctx} {b : Bnd} (e : Entry b Γ) (θ : Inst o Γ) : Inst (b :: o) Γ

namespace Inst

/-- The entry of a binder (total). -/
def get {Γ : Ctx} : {o : Ctx} → Inst o Γ → {b : Bnd} → In b o → Entry b Γ
  | _, .cons e _, _, .here => e
  | _, .cons _ θ, _, .there i => θ.get i

/-- The substitution described by the entries. -/
def toTSub {o Γ : Ctx} (θ : Inst o Γ) : TSub o Γ :=
  ⟨fun i => θ.get i, fun i => θ.get i, fun i => θ.get i, fun i => θ.get i, fun i => θ.get i⟩

def rename {Γ Δ : Ctx} (ρ : TRen Γ Δ) : {o : Ctx} → Inst o Γ → Inst o Δ
  | _, .nil => .nil
  | _, .cons e θ => .cons (Entry.rename ρ e) (θ.rename ρ)

def prename {Γ Δ : Ctx} (ρ : PRen Γ Δ) : {o : Ctx} → Inst o Γ → Option (Inst o Δ)
  | _, .nil => some .nil
  | _, .cons e θ => do pure (.cons (← Entry.prename ρ e) (← θ.prename ρ))

def subst {Γ Δ : Ctx} (σ : TSub Γ Δ) : {o : Ctx} → Inst o Γ → Inst o Δ
  | _, .nil => .nil
  | _, .cons e θ => .cons (Entry.subst σ e) (θ.subst σ)

end Inst

end Oxide
