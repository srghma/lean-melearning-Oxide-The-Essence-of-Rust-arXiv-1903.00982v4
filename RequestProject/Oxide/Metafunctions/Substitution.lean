module

public import RequestProject.Oxide.Syntax.Terms

/-!
# Oxide metafunctions, part 1: substitution in terms and values

The instantiation `δ = [Φ̄/φ̄][ρ̄/ϱ̄][τ̄/ᾱ]` of a polymorphic signature (used by
`T-AppFunction` and `E-AppFunction`) on terms and values.  Substitutions on terms
(`Sub`) also rename top-frame term variables.  The type-level part (`TSub`,
`Ty.subst`, `TArgs`, `Inst`) is in `Syntax/TypeSubst.lean`.

A closure, term or value, is written in its own scope: substituting into it only
substitutes into its captures and into the entries `θ : Inst o Γ` of its outer
binders, never into its body.  The body is *opened* (`Term.openBody`) when the
closure is called, by the substitution `θ.toTSub`, and a global function body by
the substitution of its type arguments.
-/

@[expose] public section

namespace Oxide

/-- Substitutions on terms. -/
structure Sub (Γ Δ : Ctx) extends TSub Γ Δ where
  tv : TVar Γ → TVar Δ

/-- Enter a new frame. -/
def TSub.enterFrame {Γ Δ : Ctx} (σ : TSub Γ Δ) : Sub (.frame :: Γ) (.frame :: Δ) :=
  { σ.lift .frame with tv := fun i => nomatch i }

namespace Sub

/-- Lift a term substitution under one binder. -/
def lift {Γ Δ : Ctx} (σ : Sub Γ Δ) (c : Bnd) : Sub (c :: Γ) (c :: Δ) :=
  { σ.toTSub.lift c with tv := TVar.lift σ.tv }

/-- Lift a term substitution under a list of binders. -/
def liftN {Γ Δ : Ctx} (σ : Sub Γ Δ) : (cs : Ctx) → Sub (cs ++ Γ) (cs ++ Δ)
  | [] => σ
  | c :: cs => (σ.liftN cs).lift c

end Sub

/-- The substitution opening a body written in the scope
`vars k ++ (f ++ ‡ :: o)` (parameters, a frame of shape `f`, outer binders `o`)
for a call in scope `S`, the outer binders standing for `σ`. -/
def TSub.openBody {o S : Ctx} (σ : TSub o S) (k : Nat) (f : Ctx) :
    Sub (vars k ++ (f ++ .frame :: o)) (vars k ++ (f ++ .frame :: S)) :=
  (σ.enterFrame.liftN f).liftN (vars k)

/-! ## Applying substitutions -/

def TPlace.subst {Γ Δ : Ctx} (σ : Sub Γ Δ) (π : TPlace Γ) : TPlace Δ := ⟨σ.tv π.root, π.path⟩

def PExpr.subst {Γ Δ : Ctx} (σ : Sub Γ Δ) : PExpr Γ → PExpr Δ
  | .place π => .place (π.subst σ)
  | .deref p q => .deref (p.subst σ) q

def APlace.subst {Γ Δ : Ctx} (σ : TSub Γ Δ) (π : APlace Γ) : APlace Δ := ⟨σ.var π.root, π.path⟩

def Referent.subst {Γ Δ : Ctx} (σ : TSub Γ Δ) : Referent Γ → Referent Δ
  | .place π => .place (π.subst σ)
  | .index R i q => .index (R.subst σ) i q
  | .slice R a l => .slice (R.subst σ) a l

def Cap.subst {Γ Δ : Ctx} (σ : Sub Γ Δ) : {f : Ctx} → Cap Γ f → Cap Δ f
  | _, .nil => .nil
  | _, .var x c => .var (σ.tv x) (c.subst σ)
  | _, .rgn r c => .rgn (σ.rgn r) (c.subst σ)

variable {sig : Sig}

mutual
def Atom.subst {Γ Δ : Ctx} (σ : Sub Γ Δ) : Atom sig Γ → Atom sig Δ
  | .val v => .val (v.subst σ.toTSub)
  | .move π => .move (π.subst σ)
  | .copy p => .copy (p.subst σ)
def Comp.subst {Γ Δ : Ctx} (σ : Sub Γ Δ) : Comp sig Γ → Comp sig Δ
  | .atom a => .atom (a.subst σ)
  | .borrow r ω p => .borrow (σ.rgn r) ω (p.subst σ)
  | .borrowIdx r ω p a => .borrowIdx (σ.rgn r) ω (p.subst σ) (a.subst σ)
  | .borrowSlice r ω p a₁ a₂ => .borrowSlice (σ.rgn r) ω (p.subst σ) (a₁.subst σ) (a₂.subst σ)
  | .index p a => .index (p.subst σ) (a.subst σ)
  | .assign p a => .assign (p.subst σ) (a.subst σ)
  | .closure f c o θ k ps r body => .closure f (c.subst σ) o (θ.subst σ.toTSub) k ps r body
  | .app f b θ k args => .app (f.subst σ) b (θ.subst σ.toTSub) k (fun i => (args i).subst σ)
  | .tuple k as => .tuple k fun i => (as i).subst σ
  | .array k as => .array k fun i => (as i).subst σ
  | .inl τ₁ τ₂ a => .inl (τ₁.subst σ.toTSub) (τ₂.subst σ.toTSub) (a.subst σ)
  | .inr τ₁ τ₂ a => .inr (τ₁.subst σ.toTSub) (τ₂.subst σ.toTSub) (a.subst σ)
  | .abort s => .abort s
  | .letrgn e => .letrgn (e.subst (σ.lift .rgn))
  | .ite a e₁ e₂ => .ite (a.subst σ) (e₁.subst σ) (e₂.subst σ)
  | .forE a e => .forE (a.subst σ) (e.subst (σ.lift .var))
  | .whileE e₁ e₂ => .whileE (e₁.subst σ) (e₂.subst σ)
  | .matchE a e₁ e₂ => .matchE (a.subst σ) (e₁.subst (σ.lift .var)) (e₂.subst (σ.lift .var))
def Term.subst {Γ Δ : Ctx} (σ : Sub Γ Δ) : Term sig Γ → Term sig Δ
  | .ret c => .ret (c.subst σ)
  | .letE τ c e => .letE (τ.subst σ.toTSub) (c.subst σ) (e.subst (σ.lift .var))
  | .seq c e => .seq (c.subst σ) (e.subst σ)
def Value.subst {Γ Δ : Ctx} (σ : TSub Γ Δ) : Value sig Γ → Value sig Δ
  | .prim c => .prim c
  | .fn f => .fn f
  | .dead => .dead
  | .tuple k vs => .tuple k fun i => (vs i).subst σ
  | .array k vs => .array k fun i => (vs i).subst σ
  | .slice k vs => .slice k fun i => (vs i).subst σ
  | .ptr R => .ptr (R.subst σ)
  | .closure f env o θ k ps r body => .closure f (env.subst σ) o (θ.subst σ) k ps r body
  | .inl τ₁ τ₂ v => .inl (τ₁.subst σ) (τ₂.subst σ) (v.subst σ)
  | .inr τ₁ τ₂ v => .inr (τ₁.subst σ) (τ₂.subst σ) (v.subst σ)
def Env.subst {Γ Δ : Ctx} (σ : TSub Γ Δ) : {f : Ctx} → Env sig Γ f → Env sig Δ f
  | _, .nil => .nil
  | _, .var v ε => .var (v.subst σ) (ε.subst σ)
  | _, .rgn ε => .rgn (ε.subst σ)
end

/-! ## Opening bodies -/

/-- Open a body written in the scope `vars k ++ (f ++ ‡ :: o)` for a call in scope
`S`, the outer binders standing for `σ`. -/
def Term.openBody {o S : Ctx} (σ : TSub o S) {k : Nat} {f : Ctx}
    (body : Term sig (vars k ++ (f ++ .frame :: o))) : Term sig (vars k ++ (f ++ .frame :: S)) :=
  body.subst (σ.openBody k f)

/-- The type of a closure with captured frame `Φ`, whose parameter and return
types `ps`, `ret` are written in its own scope `o`, with entries `θ`. -/
def Inst.closureTy {o Γ : Ctx} (θ : Inst o Γ) {k : Nat} (ps : Fin k → Ty o) (ret : Ty o)
    (Φ : FrameExpr Γ) : Ty Γ :=
  Ty.closure k (fun i => (ps i).subst θ.toTSub) (ret.subst θ.toTSub) Φ

/-- The body of a global function instantiated at a call in scope `Γ`. -/
def GlobalEnv.instBody (G : GlobalEnv sig) {Γ : Ctx} (f : FnIdx sig) (θ : TArgs f.get.binders Γ) :
    Term sig (vars f.get.k ++ ([] ++ .frame :: Γ)) :=
  (G.body f).openBody θ.toTSub

end Oxide
