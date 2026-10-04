module

public import RequestProject.Oxide.Syntax.Terms

/-!
# Oxide metafunctions, part 1: substitution of type-level binders

The instantiation `δ = [Φ̄/φ̄][ρ̄/ϱ̄][τ̄/ᾱ]` of a polymorphic signature (used by
`T-AppFunction` and `E-AppFunction`).  A substitution `TSub Γ Δ` maps the frame
variables, abstract regions and type variables of `Γ` to frame expressions,
regions and types in scope `Δ`, and renames the variables and concrete regions.
Substitutions on terms (`Sub`) also rename top-frame term variables.
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

/-- Substitutions on terms. -/
structure Sub (Γ Δ : Ctx) extends TSub Γ Δ where
  tv : TVar Γ → TVar Δ

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

/-- Enter a new frame. -/
def enterFrame {Γ Δ : Ctx} (σ : TSub Γ Δ) : Sub (.frame :: Γ) (.frame :: Δ) :=
  { σ.lift .frame with tv := fun i => nomatch i }

/-- Combine a substitution for a prefix `cs` with one for the rest of the scope. -/
def append {cs Γ Δ : Ctx} (σ₁ : TSub cs Δ) (σ₂ : TSub Γ Δ) : TSub (cs ++ Γ) Δ where
  fvar i := match In.split cs i with | .inl j => σ₁.fvar j | .inr j => σ₂.fvar j
  abs i := match In.split cs i with | .inl j => σ₁.abs j | .inr j => σ₂.abs j
  tvar i := match In.split cs i with | .inl j => σ₁.tvar j | .inr j => σ₂.tvar j
  var i := match In.split cs i with | .inl j => σ₁.var j | .inr j => σ₂.var j
  rgn i := match In.split cs i with | .inl j => σ₁.rgn j | .inr j => σ₂.rgn j

end TSub

namespace Sub

/-- Lift a term substitution under one binder. -/
def lift {Γ Δ : Ctx} (σ : Sub Γ Δ) (c : Bnd) : Sub (c :: Γ) (c :: Δ) :=
  { σ.toTSub.lift c with tv := TVar.lift σ.tv }

/-- Lift a term substitution under a list of binders. -/
def liftN {Γ Δ : Ctx} (σ : Sub Γ Δ) : (cs : Ctx) → Sub (cs ++ Γ) (cs ++ Δ)
  | [] => σ
  | c :: cs => (σ.liftN cs).lift c

end Sub

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

/-- The substitution `[Φ̄/φ̄][ρ̄/ϱ̄][τ̄/ᾱ]` of the binders of a signature (there
are no variables or concrete regions among them). -/
def TSub.binders {Δ : Ctx} (b : Binders) (Φs : Fin b.nφ → FrameExpr Δ)
    (ρs : Fin b.nϱ → Region Δ) (τs : Fin b.nα → Ty Δ) : TSub b.ctx Δ where
  fvar i :=
    let j := (In.skipRep (by decide) (In.skipRep (by decide) i) : In .fvar (List.replicate b.nφ .fvar))
    Φs (In.toFin j)
  abs i :=
    match In.splitRep (In.skipRep (by decide) i : In .abs (List.replicate b.nϱ .abs ++ _)) with
    | .inl j => ρs j
    | .inr j => absurd (In.sort_of_replicate j) (by decide)
  tvar i :=
    match In.splitRep (i : In .tvar (List.replicate b.nα .tvar ++ _)) with
    | .inl j => τs j
    | .inr j => absurd (In.sort_of_replicate (In.skipRep (c := .abs) (by decide) j)) (by decide)
  var i := absurd (In.sort_of_replicate (In.skipRep (c := .abs) (by decide)
      (In.skipRep (c := .tvar) (by decide) i))) (by decide)
  rgn i := absurd (In.sort_of_replicate (In.skipRep (c := .abs) (by decide)
      (In.skipRep (c := .tvar) (by decide) i))) (by decide)

/-- The instantiation of the binders of a function type at the scope `Γ` of the
function type itself. -/
def TSub.inst {Γ : Ctx} (b : Binders) (Φs : Fin b.nφ → FrameExpr Γ) (ρs : Fin b.nϱ → Region Γ)
    (τs : Fin b.nα → Ty Γ) : TSub (b.ctx ++ Γ) Γ :=
  (TSub.binders b Φs ρs τs).append (TSub.id Γ)

/-- Embed a closed signature (in scope `b.ctx`) into any scope. -/
def TRen.inlL (cs Γ : Ctx) : TRen cs (cs ++ Γ) := ⟨In.inlL⟩

/-! ## Applying substitutions -/

def Region.subst {Γ Δ : Ctx} (σ : TSub Γ Δ) : Region Γ → Region Δ
  | .abs i => σ.abs i
  | .conc r => .conc (σ.rgn r)

def Loan.subst {Γ Δ : Ctx} (σ : TSub Γ Δ) (l : Loan Γ) : Loan Δ :=
  ⟨l.own, ⟨σ.var l.pe.root, l.pe.ops⟩⟩

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

def MTy.subst {Γ Δ : Ctx} (σ : TSub Γ Δ) : MTy Γ → MTy Δ
  | .init τ => .init (τ.subst σ)
  | .dead τ => .dead (τ.subst σ)
  | .tuple k τs => .tuple k fun i => (τs i).subst σ

mutual
def Term.subst {Γ Δ : Ctx} (σ : Sub Γ Δ) : Term Γ → Term Δ
  | .val v => .val (v.subst σ.toTSub)
  | .place p => .place ⟨σ.tv p.root, p.ops⟩
  | .borrow r ω p => .borrow (σ.rgn r) ω ⟨σ.tv p.root, p.ops⟩
  | .borrowIdx r ω p e => .borrowIdx (σ.rgn r) ω ⟨σ.tv p.root, p.ops⟩ (e.subst σ)
  | .borrowSlice r ω p e₁ e₂ =>
      .borrowSlice (σ.rgn r) ω ⟨σ.tv p.root, p.ops⟩ (e₁.subst σ) (e₂.subst σ)
  | .index p e => .index ⟨σ.tv p.root, p.ops⟩ (e.subst σ)
  | .assign p e => .assign ⟨σ.tv p.root, p.ops⟩ (e.subst σ)
  | .letrgn e => .letrgn (e.subst (σ.lift .rgn))
  | .letE τ e₁ e₂ => .letE (τ.subst σ.toTSub) (e₁.subst σ) (e₂.subst (σ.lift .var))
  | .seq e₁ e₂ => .seq (e₁.subst σ) (e₂.subst σ)
  | .closure k ps r body =>
      .closure k (fun i => (ps i).subst σ.toTSub) (r.subst σ.toTSub) (body.subst (σ.liftN (vars k)))
  | .app f b Φs ρs τs k args =>
      .app (f.subst σ) b (fun i => (Φs i).subst σ.toTSub) (fun i => (ρs i).subst σ.toTSub)
        (fun i => (τs i).subst σ.toTSub) k (fun i => (args i).subst σ)
  | .ite e₁ e₂ e₃ => .ite (e₁.subst σ) (e₂.subst σ) (e₃.subst σ)
  | .tuple k es => .tuple k fun i => (es i).subst σ
  | .array k es => .array k fun i => (es i).subst σ
  | .forE e₁ e₂ => .forE (e₁.subst σ) (e₂.subst (σ.lift .var))
  | .whileE e₁ e₂ => .whileE (e₁.subst σ) (e₂.subst σ)
  | .abort s => .abort s
  | .inl τ₁ τ₂ e => .inl (τ₁.subst σ.toTSub) (τ₂.subst σ.toTSub) (e.subst σ)
  | .inr τ₁ τ₂ e => .inr (τ₁.subst σ.toTSub) (τ₂.subst σ.toTSub) (e.subst σ)
  | .matchE e e₁ e₂ => .matchE (e.subst σ) (e₁.subst (σ.lift .var)) (e₂.subst (σ.lift .var))
def Value.subst {Γ Δ : Ctx} (σ : TSub Γ Δ) : Value Γ → Value Δ
  | .prim c => .prim c
  | .fn f => .fn f
  | .dead => .dead
  | .tuple k vs => .tuple k fun i => (vs i).subst σ
  | .array k vs => .array k fun i => (vs i).subst σ
  | .slice k vs => .slice k fun i => (vs i).subst σ
  | .ptr R => .ptr ⟨σ.var R.root, R.steps⟩
  | .closure f env k ps r body =>
      .closure f (env.subst σ) k (fun i => (ps i).subst σ) (r.subst σ)
        (body.subst ((σ.enterFrame.liftN f).liftN (vars k)))
  | .inl τ₁ τ₂ v => .inl (τ₁.subst σ) (τ₂.subst σ) (v.subst σ)
  | .inr τ₁ τ₂ v => .inr (τ₁.subst σ) (τ₂.subst σ) (v.subst σ)
def Env.subst {Γ Δ : Ctx} (σ : TSub Γ Δ) : {f : Ctx} → Env Γ f → Env Δ f
  | _, .nil => .nil
  | _, .var v ε => .var (v.subst σ) (ε.subst σ)
  | _, .rgn ε => .rgn (ε.subst σ)
end

/-! ## Instantiating signatures -/

/-- Instantiate a type in the scope of a function type's binders. -/
def Ty.inst {Γ : Ctx} (b : Binders) (Φs : Fin b.nφ → FrameExpr Γ) (ρs : Fin b.nϱ → Region Γ)
    (τs : Fin b.nα → Ty Γ) (τ : Ty (b.ctx ++ Γ)) : Ty Γ :=
  τ.subst (TSub.inst b Φs ρs τs)

/-- Instantiate a region in the scope of a function type's binders. -/
def Region.inst {Γ : Ctx} (b : Binders) (Φs : Fin b.nφ → FrameExpr Γ) (ρs : Fin b.nϱ → Region Γ)
    (τs : Fin b.nα → Ty Γ) (ρ : Region (b.ctx ++ Γ)) : Region Γ :=
  ρ.subst (TSub.inst b Φs ρs τs)

/-- The abstract region bound as the `i`-th region binder of a signature. -/
def Binders.absAt {Γ : Ctx} (b : Binders) (i : Fin b.nϱ) : Region (b.ctx ++ Γ) :=
  .abs (b.absIdx i)

/-- The type of a global function (in any scope). -/
def FnDef.ty {Γ : Ctx} (d : FnDef) : Ty Γ :=
  .fn d.binders d.k (fun i => (d.params i).rename (TRen.inlL _ Γ))
    ((d.ret).rename (TRen.inlL _ Γ)) .empty d.bounds

/-- The body of a global function instantiated at a call in scope `Γ`. -/
def FnDef.instBody {Γ : Ctx} (d : FnDef) (Φs : Fin d.binders.nφ → FrameExpr Γ)
    (ρs : Fin d.binders.nϱ → Region Γ) (τs : Fin d.binders.nα → Ty Γ) :
    Term (vars d.k ++ .frame :: Γ) :=
  d.body.subst (((TSub.binders d.binders Φs ρs τs).enterFrame).liftN (vars d.k))

end Oxide
