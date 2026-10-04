module

public import RequestProject.Oxide.Proposal.Terms

/-!
# Proposal prototype, part 4: partial renamings (strengthening)

Removing a binder from a scope (popping a stack slot, a region or a whole frame)
is a *partial* renaming: it fails exactly when the removed binder is still
mentioned.  In the current formalization this situation is silent (a level just
dangles); here it is visible in the types, see `Contexts.lean`.
-/

@[expose] public section

namespace Oxide.Scoped

/-- Partial type-level renamings. -/
structure PRen (Γ Δ : Ctx) where
  ren : {b : Bnd} → In b Γ → Option (In b Δ)

/-- Lift a partial renaming under one binder. -/
def PRen.lift {Γ Δ : Ctx} (ρ : PRen Γ Δ) (c : Bnd) : PRen (c :: Γ) (c :: Δ) where
  ren := fun
    | .here => some .here
    | .there i => (ρ.ren i).map .there

/-- Lift a partial renaming under a list of binders. -/
def PRen.liftN {Γ Δ : Ctx} (ρ : PRen Γ Δ) : (cs : Ctx) → PRen (cs ++ Γ) (cs ++ Δ)
  | [] => ρ
  | c :: cs => (ρ.liftN cs).lift c

/-- Drop the most recent binder. -/
def PRen.drop (Γ : Ctx) (c : Bnd) : PRen (c :: Γ) Γ where
  ren := fun
    | .here => none
    | .there i => some i

/-- Drop a prefix of binders. -/
def PRen.dropL : (cs : Ctx) → (Γ : Ctx) → PRen (cs ++ Γ) Γ
  | [], _ => ⟨some⟩
  | c :: cs, Γ => ⟨fun
    | .here => none
    | .there i => (PRen.dropL cs Γ).ren i⟩

/-- Sequence a vector of optional values. -/
def optFin {α : Type} : {k : Nat} → (Fin k → Option α) → Option (Fin k → α)
  | 0, _ => some Fin.elim0
  | _ + 1, f => do
    let a ← f 0
    let r ← optFin fun i => f i.succ
    pure (Fin.cases a r)

def Region.prename {Γ Δ : Ctx} (ρ : PRen Γ Δ) : Region Γ → Option (Region Δ)
  | .abs i => (ρ.ren i).map .abs
  | .conc r => (ρ.ren r).map .conc

def Loan.prename {Γ Δ : Ctx} (ρ : PRen Γ Δ) (l : Loan Γ) : Option (Loan Δ) :=
  (ρ.ren l.pe.root).map fun r => ⟨l.own, ⟨r, l.pe.ops⟩⟩

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

/-- Partial renamings of terms. -/
structure PRenT (Γ Δ : Ctx) extends PRen Γ Δ where
  tvar : TVar Γ → Option (TVar Δ)

def PRenT.lift {Γ Δ : Ctx} (ρ : PRenT Γ Δ) (c : Bnd) : PRenT (c :: Γ) (c :: Δ) :=
  { ρ.toPRen.lift c with
    tvar := fun
      | .here => some .here
      | .skipVar i => (ρ.tvar i).map .skipVar
      | .skipRgn i => (ρ.tvar i).map .skipRgn }

def PRenT.liftN {Γ Δ : Ctx} (ρ : PRenT Γ Δ) : (cs : Ctx) → PRenT (cs ++ Γ) (cs ++ Δ)
  | [] => ρ
  | c :: cs => (ρ.liftN cs).lift c

def PRen.enterFrame {Γ Δ : Ctx} (ρ : PRen Γ Δ) : PRenT (.frame :: Γ) (.frame :: Δ) :=
  { ρ.lift .frame with tvar := fun i => nomatch i }

mutual
def Term.prename {Γ Δ : Ctx} (ρ : PRenT Γ Δ) : Term Γ → Option (Term Δ)
  | .val v => (v.prename ρ.toPRen).map .val
  | .place p => (ρ.tvar p.root).map fun r => .place ⟨r, p.ops⟩
  | .borrow r ω p => do pure (.borrow (← ρ.ren r) ω ⟨← ρ.tvar p.root, p.ops⟩)
  | .borrowIdx r ω p e => do
      pure (.borrowIdx (← ρ.ren r) ω ⟨← ρ.tvar p.root, p.ops⟩ (← e.prename ρ))
  | .borrowSlice r ω p e₁ e₂ => do
      pure (.borrowSlice (← ρ.ren r) ω ⟨← ρ.tvar p.root, p.ops⟩ (← e₁.prename ρ) (← e₂.prename ρ))
  | .index p e => do pure (.index ⟨← ρ.tvar p.root, p.ops⟩ (← e.prename ρ))
  | .assign p e => do pure (.assign ⟨← ρ.tvar p.root, p.ops⟩ (← e.prename ρ))
  | .letrgn e => (e.prename (ρ.lift .rgn)).map .letrgn
  | .letE τ e₁ e₂ => do
      pure (.letE (← τ.prename ρ.toPRen) (← e₁.prename ρ) (← e₂.prename (ρ.lift .var)))
  | .seq e₁ e₂ => do pure (.seq (← e₁.prename ρ) (← e₂.prename ρ))
  | .closure k ps r body => do
      pure (.closure k (← optFin fun i => (ps i).prename ρ.toPRen) (← r.prename ρ.toPRen)
        (← body.prename (ρ.liftN (vars k))))
  | .app f b Φs ρs τs k args => do
      pure (.app (← f.prename ρ) b (← optFin fun i => (Φs i).prename ρ.toPRen)
        (← optFin fun i => (ρs i).prename ρ.toPRen) (← optFin fun i => (τs i).prename ρ.toPRen) k
        (← optFin fun i => (args i).prename ρ))
  | .ite e₁ e₂ e₃ => do pure (.ite (← e₁.prename ρ) (← e₂.prename ρ) (← e₃.prename ρ))
  | .tuple k es => (optFin fun i => (es i).prename ρ).map (.tuple k)
  | .array k es => (optFin fun i => (es i).prename ρ).map (.array k)
  | .forE e₁ e₂ => do pure (.forE (← e₁.prename ρ) (← e₂.prename (ρ.lift .var)))
  | .whileE e₁ e₂ => do pure (.whileE (← e₁.prename ρ) (← e₂.prename ρ))
  | .abort s => some (.abort s)
  | .inl τ₁ τ₂ e => do pure (.inl (← τ₁.prename ρ.toPRen) (← τ₂.prename ρ.toPRen) (← e.prename ρ))
  | .inr τ₁ τ₂ e => do pure (.inr (← τ₁.prename ρ.toPRen) (← τ₂.prename ρ.toPRen) (← e.prename ρ))
  | .matchE e e₁ e₂ => do
      pure (.matchE (← e.prename ρ) (← e₁.prename (ρ.lift .var)) (← e₂.prename (ρ.lift .var)))
  | .framed f e => (e.prename (ρ.toPRen.enterFrame.liftN f)).map (.framed f)
  | .shift e => (e.prename (ρ.lift .var)).map .shift
  | .shiftRgn e => (e.prename (ρ.lift .rgn)).map .shiftRgn
def Value.prename {Γ Δ : Ctx} (ρ : PRen Γ Δ) : Value Γ → Option (Value Δ)
  | .prim c => some (.prim c)
  | .fn f => some (.fn f)
  | .dead => some .dead
  | .tuple k vs => (optFin fun i => (vs i).prename ρ).map (.tuple k)
  | .array k vs => (optFin fun i => (vs i).prename ρ).map (.array k)
  | .slice k vs => (optFin fun i => (vs i).prename ρ).map (.slice k)
  | .ptr R => (ρ.ren R.root).map fun r => .ptr ⟨r, R.steps⟩
  | .closure f env k ps r body => do
      pure (.closure f (← env.prename ρ) k (← optFin fun i => (ps i).prename ρ) (← r.prename ρ)
        (← body.prename ((ρ.enterFrame.liftN f).liftN (vars k))))
  | .inl τ₁ τ₂ v => do pure (.inl (← τ₁.prename ρ) (← τ₂.prename ρ) (← v.prename ρ))
  | .inr τ₁ τ₂ v => do pure (.inr (← τ₁.prename ρ) (← τ₂.prename ρ) (← v.prename ρ))
def Env.prename {Γ Δ : Ctx} (ρ : PRen Γ Δ) : {f : Ctx} → Env Γ f → Option (Env Δ f)
  | _, .nil => some .nil
  | _, .var v ε => do pure (.var (← v.prename ρ) (← ε.prename ρ))
  | _, .rgn ε => (ε.prename ρ).map .rgn
end

end Oxide.Scoped
