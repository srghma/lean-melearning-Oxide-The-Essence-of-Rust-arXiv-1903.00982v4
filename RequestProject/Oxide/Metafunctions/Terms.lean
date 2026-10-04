module

public import RequestProject.Oxide.Metafunctions.Stacks

/-!
# Oxide metafunctions, part 5: operations on terms

Conversion of place expressions to absolute ones, renaming of term variables,
occurrence checks, free regions of terms and type-level substitutions in
terms.  These are the de Bruijn counterparts of the paper's implicit
substitution and freshness conventions.
-/

@[expose] public section

namespace Oxide

/-- Convert a term-level place expression to an absolute one, using the stack typing. -/
def PlaceExpr.toAbs {n : Nat} (Γ : StackTy) (p : PlaceExpr n) : Option APlaceExpr :=
  (Γ.idxToLevel p.root).map fun ℓ => ⟨ℓ, p.ops⟩

/-- Lift a renaming under `k` binders. -/
def liftRen {a b : Nat} (k : Nat) (ρ : Fin a → Fin b) : Fin (a + k) → Fin (b + k) :=
  fun i => if h : i.val < k then ⟨i.val, by omega⟩
    else ⟨(ρ ⟨i.val - k, by omega⟩).val + k, by have := (ρ ⟨i.val - k, by omega⟩).isLt; omega⟩

/-- Rename the root of a place expression. -/
def PlaceExpr.rename {a b : Nat} (ρ : Fin a → Fin b) (p : PlaceExpr a) : PlaceExpr b :=
  ⟨ρ p.root, p.ops⟩

mutual
/-- Renaming of term variables. -/
def Term.rename {a b : Nat} (ρ : Fin a → Fin b) : Term a → Term b
  | .val v => .val v
  | .place p => .place (p.rename ρ)
  | .borrow r ω p => .borrow r ω (p.rename ρ)
  | .borrowIdx r ω p e => .borrowIdx r ω (p.rename ρ) (e.rename ρ)
  | .borrowSlice r ω p e₁ e₂ => .borrowSlice r ω (p.rename ρ) (e₁.rename ρ) (e₂.rename ρ)
  | .index p e => .index (p.rename ρ) (e.rename ρ)
  | .assign p e => .assign (p.rename ρ) (e.rename ρ)
  | .letrgn e => .letrgn (e.rename ρ)
  | .letE τ e₁ e₂ => .letE τ (e₁.rename ρ) (e₂.rename (liftRen 1 ρ))
  | .seq e₁ e₂ => .seq (e₁.rename ρ) (e₂.rename ρ)
  | .closure k ps r body => .closure k ps r (body.rename (liftRen k ρ))
  | .app f envs rgns tys args => .app (f.rename ρ) envs rgns tys (Terms.rename ρ args)
  | .ite e₁ e₂ e₃ => .ite (e₁.rename ρ) (e₂.rename ρ) (e₃.rename ρ)
  | .tuple es => .tuple (Terms.rename ρ es)
  | .array es => .array (Terms.rename ρ es)
  | .forE e₁ e₂ => .forE (e₁.rename ρ) (e₂.rename (liftRen 1 ρ))
  | .whileE e₁ e₂ => .whileE (e₁.rename ρ) (e₂.rename ρ)
  | .abort s => .abort s
  | .inl τ₁ τ₂ e => .inl τ₁ τ₂ (e.rename ρ)
  | .inr τ₁ τ₂ e => .inr τ₁ τ₂ (e.rename ρ)
  | .matchE e e₁ e₂ => .matchE (e.rename ρ) (e₁.rename (liftRen 1 ρ)) (e₂.rename (liftRen 1 ρ))
  | .framed m e => .framed m e
  | .shift e => .shift (e.rename (liftRen 1 ρ))
  | .shiftRgn e => .shiftRgn (e.rename ρ)
/-- Renaming of lists of terms. -/
def Terms.rename {a b : Nat} (ρ : Fin a → Fin b) : Terms a → Terms b
  | .nil => .nil
  | .cons e es => .cons (e.rename ρ) (Terms.rename ρ es)
end

mutual
/-- Does the variable with (shifted) index `i` occur free in the term? -/
def Term.occurs {n : Nat} : Term n → Nat → Bool
  | .val _, _ => false
  | .place p, i => p.root.val == i
  | .borrow _ _ p, i => p.root.val == i
  | .borrowIdx _ _ p e, i => p.root.val == i || e.occurs i
  | .borrowSlice _ _ p e₁ e₂, i => p.root.val == i || e₁.occurs i || e₂.occurs i
  | .index p e, i => p.root.val == i || e.occurs i
  | .assign p e, i => p.root.val == i || e.occurs i
  | .letrgn e, i => e.occurs i
  | .letE _ e₁ e₂, i => e₁.occurs i || e₂.occurs (i + 1)
  | .seq e₁ e₂, i => e₁.occurs i || e₂.occurs i
  | .closure k _ _ body, i => body.occurs (i + k)
  | .app f _ _ _ args, i => f.occurs i || Terms.occurs args i
  | .ite e₁ e₂ e₃, i => e₁.occurs i || e₂.occurs i || e₃.occurs i
  | .tuple es, i => Terms.occurs es i
  | .array es, i => Terms.occurs es i
  | .forE e₁ e₂, i => e₁.occurs i || e₂.occurs (i + 1)
  | .whileE e₁ e₂, i => e₁.occurs i || e₂.occurs i
  | .abort _, _ => false
  | .inl _ _ e, i => e.occurs i
  | .inr _ _ e, i => e.occurs i
  | .matchE e e₁ e₂, i => e.occurs i || e₁.occurs (i + 1) || e₂.occurs (i + 1)
  | .framed _ _, _ => false
  | .shift e, i => e.occurs (i + 1)
  | .shiftRgn e, i => e.occurs i
/-- Occurrence in lists of terms. -/
def Terms.occurs {n : Nat} : Terms n → Nat → Bool
  | .nil, _ => false
  | .cons e es, i => e.occurs i || Terms.occurs es i
end

/-! ## Terms: type-level operations -/

/-- Concrete regions (levels) of a region. -/
def Region.frgns : Region → List Nat
  | .conc ℓ => [ℓ]
  | _ => []

mutual
/-- Free concrete regions (levels) of a term (`free-regions(e)`). -/
def Term.frgns {n : Nat} : Term n → List Nat
  | .val _ => []
  | .place _ => []
  | .borrow r _ _ => r.frgns
  | .borrowIdx r _ _ e => r.frgns ++ e.frgns
  | .borrowSlice r _ _ e₁ e₂ => r.frgns ++ e₁.frgns ++ e₂.frgns
  | .index _ e => e.frgns
  | .assign _ e => e.frgns
  | .letrgn e => e.frgns
  | .letE τ e₁ e₂ => τ.frgns ++ e₁.frgns ++ e₂.frgns
  | .seq e₁ e₂ => e₁.frgns ++ e₂.frgns
  | .closure _ ps r body => Ty.frgnsL ps ++ r.frgns ++ body.frgns
  | .app f _ rgns tys args =>
      f.frgns ++ rgns.flatMap Region.frgns ++ Ty.frgnsL tys ++ Terms.frgns args
  | .ite e₁ e₂ e₃ => e₁.frgns ++ e₂.frgns ++ e₃.frgns
  | .tuple es => Terms.frgns es
  | .array es => Terms.frgns es
  | .forE e₁ e₂ => e₁.frgns ++ e₂.frgns
  | .whileE e₁ e₂ => e₁.frgns ++ e₂.frgns
  | .abort _ => []
  | .inl τ₁ τ₂ e => τ₁.frgns ++ τ₂.frgns ++ e.frgns
  | .inr τ₁ τ₂ e => τ₁.frgns ++ τ₂.frgns ++ e.frgns
  | .matchE e e₁ e₂ => e.frgns ++ e₁.frgns ++ e₂.frgns
  | .framed _ e => e.frgns
  | .shift e => e.frgns
  | .shiftRgn e => e.frgns
/-- Free concrete regions of lists of terms. -/
def Terms.frgns {n : Nat} : Terms n → List Nat
  | .nil => []
  | .cons e es => e.frgns ++ Terms.frgns es
end

/-- A family of operations on the type-level contents of terms: how to transform
a region annotation and a type at a given binder depth. -/
structure TyOp where
  rgn : Depth → Region → Region
  ty : Depth → Ty → Ty
  frm : Depth → FrameExpr → FrameExpr

mutual
/-- Apply a type-level operation to every annotation of a term (`letrgn` and
closure values bind concrete regions, increasing the depth `bnd`). -/
def Term.mapTy {n : Nat} (f : TyOp) (d : Depth) : Term n → Term n
  | .val v => .val (v.mapTy f d)
  | .place p => .place p
  | .borrow r ω p => .borrow (f.rgn d r) ω p
  | .borrowIdx r ω p e => .borrowIdx (f.rgn d r) ω p (e.mapTy f d)
  | .borrowSlice r ω p e₁ e₂ => .borrowSlice (f.rgn d r) ω p (e₁.mapTy f d) (e₂.mapTy f d)
  | .index p e => .index p (e.mapTy f d)
  | .assign p e => .assign p (e.mapTy f d)
  | .letrgn e => .letrgn (e.mapTy f { d with bnd := d.bnd + 1 })
  | .letE τ e₁ e₂ => .letE (f.ty d τ) (e₁.mapTy f d) (e₂.mapTy f d)
  | .seq e₁ e₂ => .seq (e₁.mapTy f d) (e₂.mapTy f d)
  | .closure k ps r body => .closure k (ps.map (f.ty d)) (f.ty d r) (body.mapTy f d)
  | .app g envs rgns tys args =>
      .app (g.mapTy f d) (envs.map (f.frm d)) (rgns.map (f.rgn d)) (tys.map (f.ty d))
        (Terms.mapTy f d args)
  | .ite e₁ e₂ e₃ => .ite (e₁.mapTy f d) (e₂.mapTy f d) (e₃.mapTy f d)
  | .tuple es => .tuple (Terms.mapTy f d es)
  | .array es => .array (Terms.mapTy f d es)
  | .forE e₁ e₂ => .forE (e₁.mapTy f d) (e₂.mapTy f d)
  | .whileE e₁ e₂ => .whileE (e₁.mapTy f d) (e₂.mapTy f d)
  | .abort s => .abort s
  | .inl τ₁ τ₂ e => .inl (f.ty d τ₁) (f.ty d τ₂) (e.mapTy f d)
  | .inr τ₁ τ₂ e => .inr (f.ty d τ₁) (f.ty d τ₂) (e.mapTy f d)
  | .matchE e e₁ e₂ => .matchE (e.mapTy f d) (e₁.mapTy f d) (e₂.mapTy f d)
  | .framed m e => .framed m (e.mapTy f d)
  | .shift e => .shift (e.mapTy f d)
  | .shiftRgn e => .shiftRgn (e.mapTy f d)
/-- `Term.mapTy` on lists of terms. -/
def Terms.mapTy {n : Nat} (f : TyOp) (d : Depth) : Terms n → Terms n
  | .nil => .nil
  | .cons e es => .cons (e.mapTy f d) (Terms.mapTy f d es)
/-- `Term.mapTy` on values. -/
def Value.mapTy (f : TyOp) (d : Depth) : Value → Value
  | .tuple vs => .tuple (Value.mapTyL f d vs)
  | .array vs => .array (Value.mapTyL f d vs)
  | .slice vs => .slice (Value.mapTyL f d vs)
  | .closure m k q frame ps r body =>
      .closure m k q (Value.mapTyL f d frame) (ps.map (f.ty d)) (f.ty d r)
        (body.mapTy f { d with bnd := d.bnd + q })
  | .inl τ₁ τ₂ v => .inl (f.ty d τ₁) (f.ty d τ₂) (v.mapTy f d)
  | .inr τ₁ τ₂ v => .inr (f.ty d τ₁) (f.ty d τ₂) (v.mapTy f d)
  | v => v
/-- `Term.mapTy` on lists of values. -/
def Value.mapTyL (f : TyOp) (d : Depth) : List Value → List Value
  | [] => []
  | v :: vs => v.mapTy f d :: Value.mapTyL f d vs
end

/-- The type-level operation opening concrete-region binders with levels `ls`. -/
def TyOp.openRgns (ls : List Nat) : TyOp where
  rgn := Region.openAt ls
  ty := fun d => Ty.map (Region.openAt ls) (fun _ i => .tvar i) (fun _ i => .var i)
    { bnd := d.bnd }
  frm := fun d => FrameExpr.map (Region.openAt ls) (fun _ i => .tvar i) (fun _ i => .var i)
    { bnd := d.bnd }

/-- The type-level operation instantiating a polymorphic signature. -/
def TyOp.inst (δ : Inst) : TyOp where
  rgn := fun d => δ.rgn { bnd := d.bnd }
  ty := fun d => Ty.map δ.rgn δ.tvar δ.frm { bnd := d.bnd }
  frm := fun d => FrameExpr.map δ.rgn δ.tvar δ.frm { bnd := d.bnd }

/-- Open the outermost concrete-region binders of a term with the levels `ls`
(`e[r̄/•]`). -/
def Term.openRgns {n : Nat} (ls : List Nat) (e : Term n) : Term n := e.mapTy (TyOp.openRgns ls) {}

/-- Instantiate a function body `e[Φ̄/φ̄][ρ̄/ϱ̄][τ̄/ᾱ]`. -/
def Term.inst {n : Nat} (δ : Inst) (e : Term n) : Term n := e.mapTy (TyOp.inst δ) {}

end Oxide
