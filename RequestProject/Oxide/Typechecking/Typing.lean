module

public import RequestProject.Oxide.Typechecking.RegionRewriting

/-!
# Typechecking, part 2: the typing judgment

Paper §3.5 ("Typechecking Oxide Programs"), Figures "Selected Oxide Typing Rules"
and "Oxide Typing Rule for Application"; appendix B.4 ("Typing"), together with
the well-formedness judgments of appendix B.1 for types, frames and stack
typings (mutually inductive with each other, since a function type contains its
captured frame; the typing rules use them as premises) and referent typing from
appendix B.5 ("Additional Judgments").

The judgment `Σ; Δ; Γ; Θ ⊢ e : τ ⇒ Γ'` is `HasType G Δ Θ Γ e τ Γ'`; value typing
is `HasTypeV`.  All judgments are packed into one inductive family `Typing` so
that Lean's induction principle covers them simultaneously.
-/

@[expose] public section

namespace Oxide

/-! ## Referent well-formedness (`WF-Ref*`) -/

/-- `Σ; Γ ⊢ 𝓡 : τ^XI`.  In `WF-RefIndexSlice` and `WF-RefSliceSlice` we add the
bound check against the slice the referent designates (the paper omits it; it is
needed for "well-formed references evaluate to well-typed values"). -/
inductive RefTy (Γ : StackTy) : Referent → Ty → Prop
  | id (ℓ : Nat) (τ : Ty) (h : Γ.varTy ℓ = some τ) (hsi : τ.SI) : RefTy Γ ⟨ℓ, []⟩ τ
  | proj (R : Referent) (τs : List Ty) (i : Nat) (τ : Ty)
      (h : RefTy Γ R (.tuple τs)) (hi : τs[i]? = some τ) :
      RefTy Γ ⟨R.root, R.steps ++ [.proj i]⟩ τ
  | idxArray (R : Referent) (τ : Ty) (n i : Nat) (h : RefTy Γ R (.array τ n)) (hi : i < n) :
      RefTy Γ ⟨R.root, R.steps ++ [.idx i]⟩ τ
  | idxSlice (root : Nat) (steps : List RStep) (a b i : Nat) (τ : Ty)
      (h : RefTy Γ ⟨root, steps ++ [.slice a b]⟩ (.slice τ)) (hi : i < b - a) :
      RefTy Γ ⟨root, steps ++ [.slice a b, .idx i]⟩ τ
  | sliceArray (R : Referent) (τ : Ty) (n i j : Nat) (h : RefTy Γ R (.array τ n))
      (hij : i ≤ j) (hj : j ≤ n) :
      RefTy Γ ⟨R.root, R.steps ++ [.slice i j]⟩ (.slice τ)
  | sliceSlice (root : Nat) (steps : List RStep) (a b i j : Nat) (τ : Ty)
      (h : RefTy Γ ⟨root, steps ++ [.slice a b]⟩ (.slice τ)) (hij : i ≤ j) (hj : j ≤ b - a) :
      RefTy Γ ⟨root, steps ++ [.slice a b, .slice i j]⟩ (.slice τ)

/-! ## Region well-formedness -/

/-- Region well-formedness `Δ; Γ ⊢ ρ` (`WF-ConcreteRegion`, `WF-AbstractRegion`). -/
inductive RgnWF : TyEnv → StackTy → Region → Prop
  | conc (Δ : TyEnv) (Γ : StackTy) (r : Nat) (h : Γ.HasRgn r) : RgnWF Δ Γ (.conc r)
  | abs (Δ : TyEnv) (Γ : StackTy) (ϱ : Nat) (h : ϱ < Δ.nrgn) : RgnWF Δ Γ (.abs ϱ)

/-! ## Typing -/

/-- The stack typing obtained when a closure captures (and moves) the variables
`caps` (pairs of level and type): non-copyable captured variables become dead. -/
def killNC (Γ : StackTy) (caps : List (Nat × Ty)) : StackTy :=
  caps.foldl (fun Γ c => if c.2.noncopyable then Γ.setVarTy c.1 (.dead c.2) else Γ) Γ

mutual
/-- Type well-formedness `Σ; Δ; Γ ⊢ τ` (`WF-*`). -/
inductive TyWF (G : GlobalEnv) : TyEnv → StackTy → Ty → Prop
  | base (Δ : TyEnv) (Γ : StackTy) (b : BaseTy) : TyWF G Δ Γ (.base b)
  | tvar (Δ : TyEnv) (Γ : StackTy) (α : Nat) (h : α < Δ.nty) : TyWF G Δ Γ (.tvar α)
  | ref (Δ : TyEnv) (Γ : StackTy) (ρ : Region) (ω : Own) (τ : Ty) (hρ : RgnWF Δ Γ ρ)
      (hτ : TyWF G Δ Γ τ) : TyWF G Δ Γ (.ref ρ ω τ)
  | tuple (Δ : TyEnv) (Γ : StackTy) (τs : List Ty) (h : ∀ τ ∈ τs, TyWF G Δ Γ τ) :
      TyWF G Δ Γ (.tuple τs)
  | fn (Δ : TyEnv) (Γ : StackTy) (nφ nϱ nα : Nat) (ps : List Ty) (ret : Ty)
      (Φ : FrameExpr) (bs : List (Nat × Nat))
      (hbs : ∀ b ∈ bs, b.1 < nϱ ∧ b.2 < nϱ)
      (hret : ∀ r ∈ ret.frgns, ∀ τ' ∈ Γ.cod, r ∉ τ'.frgnsOut)
      (henv : EnvWF G (Δ.extend nφ nϱ nα bs) Γ Φ)
      (hr : TyWF G (Δ.extend nφ nϱ nα bs) Γ ret)
      (hps : ∀ τ ∈ ps, TyWF G (Δ.extend nφ nϱ nα bs) Γ τ) :
      TyWF G Δ Γ (.fn nφ nϱ nα ps ret Φ bs)
  | dead (Δ : TyEnv) (Γ : StackTy) (τ : Ty) : TyWF G Δ Γ (.dead τ)
  | array (Δ : TyEnv) (Γ : StackTy) (τ : Ty) (k : Nat) (h : TyWF G Δ Γ τ) :
      TyWF G Δ Γ (.array τ k)
  | slice (Δ : TyEnv) (Γ : StackTy) (τ : Ty) (h : TyWF G Δ Γ τ) : TyWF G Δ Γ (.slice τ)
  | sum (Δ : TyEnv) (Γ : StackTy) (τ₁ τ₂ : Ty) (h₁ : TyWF G Δ Γ τ₁) (h₂ : TyWF G Δ Γ τ₂) :
      TyWF G Δ Γ (.sum τ₁ τ₂)
/-- Frame expression well-formedness `Σ; Δ; Γ ⊢ Φ` (`WF-EnvVar`, `WF-Env`). -/
inductive EnvWF (G : GlobalEnv) : TyEnv → StackTy → FrameExpr → Prop
  | var (Δ : TyEnv) (Γ : StackTy) (φ : Nat) (h : φ < Δ.nfrm) :
      EnvWF G Δ Γ (.var φ)
  | frame (Δ : TyEnv) (Γ : StackTy) (Φ : FrameTy) (h : StackWF G Δ (Φ.openAt Γ.numRgns :: Γ)) :
      EnvWF G Δ Γ (.frame Φ)
/-- Stack typing well-formedness `Σ; Δ ⊢ Γ` (`WF-EmptyStackTyping`, `WF-StackTyping`). -/
inductive StackWF (G : GlobalEnv) : TyEnv → StackTy → Prop
  | empty (Δ : TyEnv) : StackWF G Δ []
  | frame (Δ : TyEnv) (Γ : StackTy) (Φ : FrameTy) (h : StackWF G Δ Γ)
      (hplaces : ∀ π ∈ StackTy.places [Φ], ∃ τ, StackTy.placeTy (Φ :: Γ) π = some τ)
      (hty : ∀ τ ∈ Φ.varTys, TyWF G Δ (Φ :: Γ) τ)
      (hout : ∀ τ ∈ Φ.varTys, ∀ r ∈ τ.frgns, ∀ τ' ∈ Γ.cod, r ∉ τ'.frgnsOut)
      (hloans : ∀ L ∈ Φ.rgnLoans, ∀ l ∈ L, ∃ τ ρs, PlaceTy Δ (Φ :: Γ) l.own l.pe τ ρs) :
      StackWF G Δ (Φ :: Γ)
end

/-- The forms of the typing judgments of Oxide: expressions
`Σ; Δ; Γ; Θ ⊢ e : τ ⇒ Γ'`, argument lists (plain and with rewriting), values and
lists of values. -/
inductive TyJ where
  | expr {n : Nat} (Δ : TyEnv) (Θ : TempTy) (Γ : StackTy) (e : Term n) (τ : Ty) (Γ' : StackTy)
  | args {n : Nat} (Δ : TyEnv) (Θ : TempTy) (Γ : StackTy) (es : Terms n) (τs : List Ty)
      (Γ' : StackTy)
  | argsRw {n : Nat} (Δ : TyEnv) (Θ : TempTy) (Γ : StackTy) (es : Terms n) (τs : List Ty)
      (Γ' : StackTy)
  | val (Δ : TyEnv) (Θ : TempTy) (Γ : StackTy) (v : Value) (τ : Ty)
  | vals (Δ : TyEnv) (Θ : TempTy) (Γ : StackTy) (vs : List Value) (τs : List Ty)

/-- The typing judgments of Oxide (appendix "Statics"), as a single inductive
family indexed by the form of the judgment (see `HasType`, `HasTypeArgs`,
`HasTypeArgsRw`, `HasTypeV`, `HasTypeVs` below). -/
inductive Typing (G : GlobalEnv) : TyJ → Prop
  -- ## Expressions `Σ; Δ; Γ; Θ ⊢ e : τ ⇒ Γ'`
  /-- values -/
  | val {n} (Δ : TyEnv) (Θ : TempTy) (Γ : StackTy) (v : Value) (τ : Ty)
      (h : Typing G (.val Δ Θ Γ v τ)) : Typing G (.expr Δ Θ Γ (n := n) (.val v) τ Γ)
  /-- `T-Move` -/
  | move {n} (Δ : TyEnv) (Θ : TempTy) (Γ Γ' : StackTy) (p : PlaceExpr n) (π : APlace) (τ : Ty)
      (hp : p.toAbs Γ = some π.toExpr)
      (hsafe : OwnSafe Δ Θ Γ .uniq [] π.toExpr [⟨.uniq, π.toExpr⟩])
      (hty : Γ.placeTy π = some τ) (hsi : τ.SI) (hnc : τ.noncopyable = true)
      (hΓ' : Γ.setPlaceTy π (.dead τ) = some Γ') :
      Typing G (.expr Δ Θ Γ (.place p) τ Γ')
  /-- `T-Copy` -/
  | copy {n} (Δ : TyEnv) (Θ : TempTy) (Γ : StackTy) (p : PlaceExpr n) (pa : APlaceExpr)
      (L : List Loan) (τ : Ty) (ρs : List Region)
      (hp : p.toAbs Γ = some pa) (hsafe : OwnSafe Δ Θ Γ .shrd [] pa L)
      (htc : PlaceTy Δ Γ .shrd pa τ ρs) (hsi : τ.SI) (hc : τ.copyable = true) :
      Typing G (.expr Δ Θ Γ (.place p) τ Γ)
  /-- `T-Borrow` -/
  | borrow {n} (Δ : TyEnv) (Θ : TempTy) (Γ : StackTy) (r : Nat) (ω : Own) (p : PlaceExpr n)
      (pa : APlaceExpr) (L : List Loan) (τ : Ty) (ρs : List Region)
      (hp : p.toAbs Γ = some pa) (hr : Γ.loans? r = some []) (hnic : NotInClosure Θ Γ r)
      (hsafe : OwnSafe Δ Θ Γ ω [] pa L) (htc : PlaceTy Δ Γ ω pa τ ρs) (hxi : τ.XI) :
      Typing G (.expr Δ Θ Γ (.borrow (.conc r) ω p) (.ref (.conc r) ω τ) (Γ.setLoans r L))
  /-- `T-BorrowIndex` -/
  | borrowIdx {n} (Δ : TyEnv) (Θ : TempTy) (Γ Γ₁ : StackTy) (r : Nat) (ω : Own)
      (p : PlaceExpr n) (e : Term n) (pa : APlaceExpr) (L : List Loan) (τ τ' : Ty)
      (ρs : List Region)
      (he : Typing G (.expr Δ Θ Γ e Ty.u32 Γ₁))
      (hp : p.toAbs Γ₁ = some pa) (hr : Γ₁.loans? r = some []) (hnic : NotInClosure Θ Γ₁ r)
      (hsafe : OwnSafe Δ Θ Γ₁ ω [] pa L) (htc : PlaceTy Δ Γ₁ ω pa τ ρs)
      (hτ : (∃ k, τ = .array τ' k) ∨ τ = .slice τ') (hsi : τ'.SI) :
      Typing G (.expr Δ Θ Γ (.borrowIdx (.conc r) ω p e) (.ref (.conc r) ω τ') (Γ₁.setLoans r L))
  /-- `T-BorrowSlice` (we allow borrowing a slice of an array as well as of a slice) -/
  | borrowSlice {n} (Δ : TyEnv) (Θ : TempTy) (Γ Γ₁ Γ₂ : StackTy) (r : Nat) (ω : Own)
      (p : PlaceExpr n) (e₁ e₂ : Term n) (pa : APlaceExpr) (L : List Loan) (τ τ' : Ty)
      (ρs : List Region)
      (he₁ : Typing G (.expr Δ Θ Γ e₁ Ty.u32 Γ₁)) (he₂ : Typing G (.expr Δ Θ Γ₁ e₂ Ty.u32 Γ₂))
      (hp : p.toAbs Γ₂ = some pa) (hr : Γ₂.loans? r = some []) (hnic : NotInClosure Θ Γ₂ r)
      (hsafe : OwnSafe Δ Θ Γ₂ ω [] pa L) (htc : PlaceTy Δ Γ₂ ω pa τ ρs)
      (hτ : (∃ k, τ = .array τ' k) ∨ τ = .slice τ') (hsi : τ'.SI) :
      Typing G (.expr Δ Θ Γ (.borrowSlice (.conc r) ω p e₁ e₂) (.ref (.conc r) ω (.slice τ'))
        (Γ₂.setLoans r L))
  /-- `T-IndexCopy` -/
  | index {n} (Δ : TyEnv) (Θ : TempTy) (Γ Γ' : StackTy) (p : PlaceExpr n) (e : Term n)
      (pa : APlaceExpr) (L : List Loan) (τ τ' : Ty) (ρs : List Region)
      (he : Typing G (.expr Δ Θ Γ e Ty.u32 Γ'))
      (hp : p.toAbs Γ' = some pa) (hsafe : OwnSafe Δ Θ Γ' .shrd [] pa L)
      (htc : PlaceTy Δ Γ' .shrd pa τ ρs)
      (hτ : (∃ k, τ = .array τ' k) ∨ τ = .slice τ') (hsi : τ'.SI) (hc : τ'.copyable = true) :
      Typing G (.expr Δ Θ Γ (.index p e) τ' Γ')
  /-- `T-Seq` -/
  | seq {n} (Δ : TyEnv) (Θ : TempTy) (Γ Γ₁ Γ₂ : StackTy) (e₁ e₂ : Term n) (τ₁ τ₂ : Ty)
      (h₁ : Typing G (.expr Δ Θ Γ e₁ τ₁ Γ₁)) (hsi₁ : τ₁.SI)
      (h₂ : Typing G (.expr Δ Θ (gcLoans Θ Γ₁) e₂ τ₂ Γ₂)) (hsi₂ : τ₂.SI) :
      Typing G (.expr Δ Θ Γ (.seq e₁ e₂) τ₂ Γ₂)
  /-- `T-Branch` -/
  | ite {n} (Δ : TyEnv) (Θ : TempTy) (Γ Γ₁ Γ₂ Γ₃ Γ₂' Γ₃' Γ' : StackTy) (e₁ e₂ e₃ : Term n)
      (τ τ₂ τ₃ : Ty)
      (h₁ : Typing G (.expr Δ Θ Γ e₁ Ty.bool Γ₁))
      (h₂ : Typing G (.expr Δ Θ Γ₁ e₂ τ₂ Γ₂)) (h₃ : Typing G (.expr Δ Θ Γ₁ e₃ τ₃ Γ₃))
      (hτ : τ = τ₂ ∨ τ = τ₃) (hsi : τ.SI) (hsi₂ : τ₂.SI) (hsi₃ : τ₃.SI)
      (hr₂ : Rewrite Δ Θ .combine Γ₂ τ₂ τ Γ₂') (hr₃ : Rewrite Δ Θ .combine Γ₃ τ₃ τ Γ₃')
      (hu : StackTy.union Γ₂' Γ₃' = some Γ') :
      Typing G (.expr Δ Θ Γ (.ite e₁ e₂ e₃) τ Γ')
  /-- `T-Let` -/
  | letE {n} (Δ : TyEnv) (Θ : TempTy) (Γ Γ₁ Γ₁' : StackTy) (Φ : FrameTy) (Γ₂ : StackTy)
      (τa τ₁ τ₂ τd : Ty) (e₁ : Term n) (e₂ : Term (n + 1))
      (h₁ : Typing G (.expr Δ Θ Γ e₁ τ₁ Γ₁)) (hsi₁ : τ₁.SI) (hsia : τa.SI)
      (hr : Rewrite Δ Θ .combine Γ₁ τ₁ τa Γ₁')
      (hnrb : ∀ r ∈ τa.frgns, NotReborrowed Γ₁' r)
      (h₂ : Typing G (.expr Δ Θ (gcLoans Θ (Γ₁'.push (.var τa))) e₂ τ₂ ((.var τd :: Φ) :: Γ₂)))
      (hsi₂ : τ₂.SI) (hsd : τd.SD) :
      Typing G (.expr Δ Θ Γ (.letE τa e₁ e₂) τ₂ (Φ :: Γ₂))
  /-- `T-LetRegion`: the bound region is opened with the level `Γ.numRgns` of the
  fresh region entry pushed on the top frame; the result type must not mention it. -/
  | letrgn {n} (Δ : TyEnv) (Θ : TempTy) (Γ : StackTy) (Φ : FrameTy) (Γ' : StackTy)
      (L : List Loan) (e : Term n) (τ : Ty)
      (h : Typing G (.expr Δ Θ (Γ.push (.rgn [])) (e.openRgns [Γ.numRgns]) τ ((.rgn L :: Φ) :: Γ')))
      (hsi : τ.SI) (hfresh : Γ.numRgns ∉ τ.frgns) :
      Typing G (.expr Δ Θ Γ (.letrgn e) τ (Φ :: Γ'))
  /-- `T-AssignDeref` -/
  | assignDeref {n} (Δ : TyEnv) (Θ : TempTy) (Γ Γ₁ Γ' : StackTy) (p : PlaceExpr n) (e : Term n)
      (pa : APlaceExpr) (L : List Loan) (τn τo : Ty) (ρs : List Region)
      (he : Typing G (.expr Δ Θ Γ e τn Γ₁)) (hsin : τn.SI) (hsio : τo.SI)
      (hp : p.toAbs Γ₁ = some pa) (htc : PlaceTy Δ Γ₁ .uniq pa τo ρs)
      (hr : Rewrite Δ Θ .combine Γ₁ τn τo Γ')
      (hsafe : OwnSafe Δ Θ Γ' .uniq [] pa L) :
      Typing G (.expr Δ Θ Γ (.assign p e) Ty.unit Γ')
  /-- `T-Assign` -/
  | assign {n} (Δ : TyEnv) (Θ : TempTy) (Γ Γ₁ Γ' Γ'' : StackTy) (p : PlaceExpr n) (e : Term n)
      (π : APlace) (τ τx : Ty)
      (he : Typing G (.expr Δ Θ Γ e τ Γ₁)) (hsi : τ.SI)
      (hp : p.toAbs Γ₁ = some π.toExpr)
      (hx : Γ₁.placeTy π = some τx) (hsx : τx.SX)
      (huniq : ∀ r ω τ', τx = .ref (.conc r) ω τ' → RgnUniqueTo r π Γ₁)
      (hr : Rewrite Δ Θ .noop (Γ₁.rsub π.derefExpr) τ τx Γ')
      (hsafe : τx.SD ∨ OwnSafe Δ Θ Γ' .uniq [] π.toExpr [⟨.uniq, π.toExpr⟩])
      (hΓ'' : Γ'.setPlaceTy π τ = some Γ'') :
      Typing G (.expr Δ Θ Γ (.assign p e) Ty.unit Γ'')
  /-- `T-While` -/
  | whileE {n} (Δ : TyEnv) (Θ : TempTy) (Γ Γ₁ Γ₂ : StackTy) (e₁ e₂ : Term n)
      (h₁ : Typing G (.expr Δ Θ Γ e₁ Ty.bool Γ₁)) (h₂ : Typing G (.expr Δ Θ Γ₁ e₂ Ty.unit Γ₂))
      (h₁' : Typing G (.expr Δ Θ Γ₂ e₁ Ty.bool Γ₂)) (h₂' : Typing G (.expr Δ Θ Γ₂ e₂ Ty.unit Γ₂)) :
      Typing G (.expr Δ Θ Γ (.whileE e₁ e₂) Ty.unit Γ₂)
  /-- `T-ForArray` -/
  | forArray {n} (Δ : TyEnv) (Θ : TempTy) (Γ Γ₁ : StackTy) (e₁ : Term n) (e₂ : Term (n + 1))
      (τ τd : Ty) (k : Nat)
      (h₁ : Typing G (.expr Δ Θ Γ e₁ (.array τ k) Γ₁)) (hsi : τ.SI)
      (hnrb : ∀ r ∈ τ.frgns, NotReborrowed Γ₁ r)
      (h₂ : Typing G (.expr Δ Θ (Γ₁.push (.var τ)) e₂ Ty.unit (Γ₁.push (.var τd)))) (hsd : τd.SD) :
      Typing G (.expr Δ Θ Γ (.forE e₁ e₂) Ty.unit Γ₁)
  /-- `T-ForSlice` -/
  | forSlice {n} (Δ : TyEnv) (Θ : TempTy) (Γ Γ₁ : StackTy) (e₁ : Term n) (e₂ : Term (n + 1))
      (ρ : Region) (ω : Own) (τ τx : Ty)
      (h₁ : Typing G (.expr Δ Θ Γ e₁ (.ref ρ ω (.slice τ)) Γ₁)) (hsi : τ.SI)
      (hnrb : ∀ r ∈ (Ty.ref ρ ω τ).frgns, NotReborrowed Γ₁ r)
      (h₂ : Typing G (.expr Δ Θ (Γ₁.push (.var (.ref ρ ω τ))) e₂ Ty.unit (Γ₁.push (.var τx))))
      (hsx : τx.SX) :
      Typing G (.expr Δ Θ Γ (.forE e₁ e₂) Ty.unit Γ₁)
  /-- `T-Closure`.  The free variables of the body (other than the parameters) are
  the indices `ρ 0, …, ρ (m-1)` of the enclosing scope, captured (in this order) as
  `caps`; the body is the renaming of `body'`, whose scope is the frame
  `Φ_c, x₁ : τ₁, …, x_k : τ_k`.  The concrete regions `rs` of the body that do not
  occur in the signature are captured too: in `body'` and in the captured frame
  `Φ_c` they are bound (`Region.bound j` for `rs[j]`), and the body is checked with
  these binders opened at the levels of the fresh region entries of the pushed
  frame. -/
  | closure {n} (Δ : TyEnv) (Θ : TempTy) (Γ : StackTy) (k : Nat) (ps : List Ty) (ret : Ty)
      (body : Term (n + k)) (m : Nat) (ρ : Fin m → Fin n) (body' : Term (m + k))
      (caps : List (Nat × Ty)) (rs : List Nat) (Φc Φ' : FrameTy) (Γ' : StackTy)
      (hk : ps.length = k) (hsi : ∀ τ ∈ ps, τ.SI) (hsir : ret.SI)
      (hbody : body = (body'.rename (liftRen k ρ)).openRgns rs)
      (hmono : ∀ i j : Fin m, i.val < j.val → (ρ i).val < (ρ j).val)
      (hocc : ∀ j : Fin m, body'.occurs (k + j.val) = true)
      (hcapLen : caps.length = m)
      (hcaps : ∀ j : Fin m, ∃ ℓ τ, caps[j.val]? = some (ℓ, τ) ∧
        Γ.idxToLevel (ρ j).val = some ℓ ∧ Γ.varTy ℓ = some τ)
      (hrsNodup : rs.Nodup)
      (hrs : ∀ r, r ∈ rs ↔ (r ∈ body.frgns ∧ r ∉ Ty.frgnsL ps ∧ r ∉ ret.frgns))
      (hrsBound : ∀ r ∈ rs, Γ.HasRgn r)
      (hΦc : Φc = caps.map (fun c => FrameEntry.var (c.2.closeRgns rs)) ++
        rs.map (fun r => FrameEntry.rgn ((Γ.loans? r).getD [])))
      (hparams : ∀ r ∈ Ty.frgnsL ps ++ ret.frgns, Γ.loans? r = some [])
      (hb : Typing G (.expr Δ Θ
        (FrameTy.openAt Γ.numRgns (ps.reverse.map FrameEntry.var ++ Φc) :: killNC Γ caps)
        (body'.openRgns (newLevels Γ.numRgns rs.length)) ret (Φ' :: Γ'))) :
      Typing G (.expr Δ Θ Γ (.closure k ps ret body) (Ty.closure ps ret (.frame Φc)) Γ')
  /-- `T-AppFunction`: `δ = [Φ̄/φ̄][ρ̄/ϱ̄][τ̄/ᾱ]` (the outlives bounds `ϱ₁ : ϱ₂` are
  checked as `δ(ϱ₁) :> δ(ϱ₂)`) -/
  | appFn {n} (Δ : TyEnv) (Θ : TempTy) (Γ Γ₀ Γₙ Γb : StackTy) (f : Term n) (Φs : List FrameExpr)
      (ρs : List Region) (τs : List Ty) (args : Terms n) (nφ nϱ nα : Nat)
      (ps : List Ty) (τf : Ty) (bs : List (Nat × Nat))
      (hΦs : ∀ Φ ∈ Φs, EnvWF G Δ Γ Φ) (hρs : ∀ ρ ∈ ρs, RgnWF Δ Γ ρ)
      (hτs : ∀ τ ∈ τs, TyWF G Δ Γ τ) (hτsi : ∀ τ ∈ τs, τ.SI)
      (hlenΦ : Φs.length = nφ) (hlenρ : ρs.length = nϱ) (hlenτ : τs.length = nα)
      (hf : Typing G (.expr Δ Θ Γ f (.fn nφ nϱ nα ps τf (.frame []) bs) Γ₀))
      (hargs : Typing G (.args Δ Θ Γ₀ args (ps.map (Ty.inst ⟨Φs, ρs, τs⟩)) Γₙ))
      (hnrb : ∀ τ ∈ ps, ∀ r ∈ (τ.inst ⟨Φs, ρs, τs⟩).frgns, NotReborrowed Γₙ r)
      (hbounds : OutlivesMany Δ Θ .combine Γₙ
        (bs.map fun b => ((Region.abs b.1).inst ⟨Φs, ρs, τs⟩,
          (Region.abs b.2).inst ⟨Φs, ρs, τs⟩)) Γb) :
      Typing G (.expr Δ Θ Γ (.app f Φs ρs τs args) (τf.inst ⟨Φs, ρs, τs⟩) Γb)
  /-- `T-AppClosure` -/
  | appClosure {n} (Δ : TyEnv) (Θ : TempTy) (Γ Γ₀ Γₙ : StackTy) (f : Term n) (args : Terms n)
      (ps : List Ty) (τf : Ty) (Φc : FrameExpr)
      (hf : Typing G (.expr Δ Θ Γ f (Ty.closure ps τf Φc) Γ₀))
      (hargs : Typing G (.argsRw Δ Θ Γ₀ args ps Γₙ))
      (hnrb : ∀ τ ∈ ps, ∀ r ∈ τ.frgns, NotReborrowed Γₙ r) :
      Typing G (.expr Δ Θ Γ (.app f [] [] [] args) τf Γₙ)
  /-- `T-Tuple` -/
  | tuple {n} (Δ : TyEnv) (Θ : TempTy) (Γ Γ' : StackTy) (es : Terms n) (τs : List Ty)
      (h : Typing G (.args Δ Θ Γ es τs Γ')) (hsi : ∀ τ ∈ τs, τ.SI) :
      Typing G (.expr Δ Θ Γ (.tuple es) (.tuple τs) Γ')
  /-- `T-Array` -/
  | array {n} (Δ : TyEnv) (Θ : TempTy) (Γ Γ' : StackTy) (es : Terms n) (τ : Ty)
      (h : Typing G (.args Δ Θ Γ es (List.replicate es.toList.length τ) Γ')) (hsi : τ.SI) :
      Typing G (.expr Δ Θ Γ (.array es) (.array τ es.toList.length) Γ')
  /-- `T-Abort` -/
  | abort {n} (Δ : TyEnv) (Θ : TempTy) (Γ : StackTy) (s : String) (τ : Ty) (hsx : τ.SX) :
      Typing G (.expr Δ Θ Γ (n := n) (.abort s) τ Γ)
  /-- `T-Drop` -/
  | drop {n} (Δ : TyEnv) (Θ : TempTy) (Γ Γd Γf : StackTy) (π : APlace) (τπ τ : Ty) (e : Term n)
      (hπ : Γ.placeTy π = some τπ) (hsi : τπ.SI) (hd : Γ.setPlaceTy π (.dead τπ) = some Γd)
      (h : Typing G (.expr Δ Θ Γd e τ Γf)) :
      Typing G (.expr Δ Θ Γ e τ Γf)
  /-- `T-Left` -/
  | inl {n} (Δ : TyEnv) (Θ : TempTy) (Γ Γ' : StackTy) (τ₁ τ₂ : Ty) (e : Term n)
      (h : Typing G (.expr Δ Θ Γ e τ₁ Γ')) (hsi₁ : τ₁.SI) (hsi₂ : τ₂.SI) :
      Typing G (.expr Δ Θ Γ (.inl τ₁ τ₂ e) (.sum τ₁ τ₂) Γ')
  /-- `T-Right` -/
  | inr {n} (Δ : TyEnv) (Θ : TempTy) (Γ Γ' : StackTy) (τ₁ τ₂ : Ty) (e : Term n)
      (h : Typing G (.expr Δ Θ Γ e τ₂ Γ')) (hsi₁ : τ₁.SI) (hsi₂ : τ₂.SI) :
      Typing G (.expr Δ Θ Γ (.inr τ₁ τ₂ e) (.sum τ₁ τ₂) Γ')
  /-- `T-Match` -/
  | matchE {n} (Δ : TyEnv) (Θ : TempTy) (Γ Γ' : StackTy) (Φ₁ Φ₂ : FrameTy)
      (Γ₁ Γ₂ Γ₁' Γ₂' Γ'' : StackTy) (e : Term n) (e₁ e₂ : Term (n + 1))
      (τl τr τ₁ τ₂ τ τdl τdr : Ty)
      (h : Typing G (.expr Δ Θ Γ e (.sum τl τr) Γ'))
      (hnrb : ∀ r ∈ (Ty.sum τl τr).frgns, NotReborrowed Γ' r)
      (h₁ : Typing G (.expr Δ Θ (Γ'.push (.var τl)) e₁ τ₁ ((.var τdl :: Φ₁) :: Γ₁)))
      (h₂ : Typing G (.expr Δ Θ (Γ'.push (.var τr)) e₂ τ₂ ((.var τdr :: Φ₂) :: Γ₂)))
      (hsd : τdl.SD ∧ τdr.SD) (hτ : τ = τ₁ ∨ τ = τ₂) (hsi : τ.SI ∧ τ₁.SI ∧ τ₂.SI)
      (hr₁ : Rewrite Δ Θ .combine (Φ₁ :: Γ₁) τ₁ τ Γ₁')
      (hr₂ : Rewrite Δ Θ .combine (Φ₂ :: Γ₂) τ₂ τ Γ₂')
      (hu : StackTy.union Γ₁' Γ₂' = some Γ'') :
      Typing G (.expr Δ Θ Γ (.matchE e e₁ e₂) τ Γ'')
  /-- `T-Shift` -/
  | shift {n} (Δ : TyEnv) (Θ : TempTy) (Γ : StackTy) (Φ : FrameTy) (Γ' : StackTy)
      (e : Term (n + 1)) (τ τd : Ty)
      (h : Typing G (.expr Δ Θ Γ e τ ((.var τd :: Φ) :: Γ'))) (hsi : τ.SI) (hsd : τd.SD) :
      Typing G (.expr Δ Θ Γ (.shift e) τ (Φ :: Γ'))
  /-- typing of the runtime form `shiftprov e` (pops the most recent region
  binding, whose level must not occur in the result type) -/
  | shiftRgn {n} (Δ : TyEnv) (Θ : TempTy) (Γ : StackTy) (Φ : FrameTy) (Γ' : StackTy)
      (L : List Loan) (e : Term n) (τ : Ty)
      (h : Typing G (.expr Δ Θ Γ e τ ((.rgn L :: Φ) :: Γ'))) (hsi : τ.SI)
      (hfresh : StackTy.numRgns (Φ :: Γ') ∉ τ.frgns) :
      Typing G (.expr Δ Θ Γ (.shiftRgn e) τ (Φ :: Γ'))
  /-- `T-Framed` -/
  | framed {n} (Δ : TyEnv) (Θ : TempTy) (Γ : StackTy) (Φ' : FrameTy) (Γ' : StackTy) (m : Nat)
      (e : Term m) (τ : Ty)
      (h : Typing G (.expr Δ Θ Γ e τ (Φ' :: Γ'))) (hsi : τ.SI) :
      Typing G (.expr Δ Θ Γ (n := n) (.framed m e) τ Γ')
  -- ## Argument lists (`T-Tuple`, `T-Array`, `T-AppFunction`): the `i`-th expression
  -- is typed with the types of the previous ones added to `Θ`.
  | argsNil {n} (Δ : TyEnv) (Θ : TempTy) (Γ : StackTy) : Typing G (.args Δ Θ Γ (n := n) .nil [] Γ)
  | argsCons {n} (Δ : TyEnv) (Θ : TempTy) (Γ Γ₁ Γ₂ : StackTy) (e : Term n) (es : Terms n) (τ : Ty)
      (τs : List Ty) (h : Typing G (.expr Δ Θ Γ e τ Γ₁)) (t : Typing G (.args Δ (Θ ++ [τ]) Γ₁ es τs Γ₂)) :
      Typing G (.args Δ Θ Γ (.cons e es) (τ :: τs) Γ₂)
  -- ## Closure arguments (`T-AppClosure`): each argument is rewritten with mode `⊞`
  -- to the parameter type.
  | argsRwNil {n} (Δ : TyEnv) (Θ : TempTy) (Γ : StackTy) : Typing G (.argsRw Δ Θ Γ (n := n) .nil [] Γ)
  | argsRwCons {n} (Δ : TyEnv) (Θ : TempTy) (Γ Γ₁ Γ₁' Γ₂ : StackTy) (e : Term n) (es : Terms n)
      (τ' τ : Ty) (τs : List Ty) (h : Typing G (.expr Δ Θ Γ e τ' Γ₁))
      (hr : Rewrite Δ Θ .combineUnrest Γ₁ τ' τ Γ₁')
      (t : Typing G (.argsRw Δ (Θ ++ [τ]) Γ₁' es τs Γ₂)) :
      Typing G (.argsRw Δ Θ Γ (.cons e es) (τ :: τs) Γ₂)
  -- ## Values `Σ; Δ; Γ; Θ ⊢ v : τ ⇒ Γ` (values never change the stack typing).
  /-- `T-Unit` -/
  | vUnit (Δ : TyEnv) (Θ : TempTy) (Γ : StackTy) : Typing G (.val Δ Θ Γ Value.unit Ty.unit)
  /-- `T-u32` -/
  | vNum (Δ : TyEnv) (Θ : TempTy) (Γ : StackTy) (k : Nat) : Typing G (.val Δ Θ Γ (Value.num k) Ty.u32)
  /-- `T-True`, `T-False` -/
  | vBool (Δ : TyEnv) (Θ : TempTy) (Γ : StackTy) (b : Bool) :
      Typing G (.val Δ Θ Γ (.prim (.bool b)) Ty.bool)
  /-- `T-Function` -/
  | vFn (Δ : TyEnv) (Θ : TempTy) (Γ : StackTy) (f : String) (d : FnDef)
      (hd : G.lookup f = some d) :
      Typing G (.val Δ Θ Γ (.fn f) (.fn d.nφ d.nϱ d.nα d.params d.ret (.frame []) d.bounds))
  /-- `T-Dead`: any value has any dead type -/
  | vDead (Δ : TyEnv) (Θ : TempTy) (Γ : StackTy) (v : Value) (τ : Ty) (hsi : τ.SI) :
      Typing G (.val Δ Θ Γ v (.dead τ))
  /-- tuple values (`T-Tuple`) -/
  | vTuple (Δ : TyEnv) (Θ : TempTy) (Γ : StackTy) (vs : List Value) (τs : List Ty)
      (h : Typing G (.vals Δ Θ Γ vs τs)) :
      Typing G (.val Δ Θ Γ (.tuple vs) (.tuple τs))
  /-- array values (`T-Array`) -/
  | vArray (Δ : TyEnv) (Θ : TempTy) (Γ : StackTy) (vs : List Value) (τ : Ty)
      (h : Typing G (.vals Δ Θ Γ vs (List.replicate vs.length τ))) (hsi : τ.SI) :
      Typing G (.val Δ Θ Γ (.array vs) (.array τ vs.length))
  /-- slice values (`T-Slice`) -/
  | vSlice (Δ : TyEnv) (Θ : TempTy) (Γ : StackTy) (vs : List Value) (τ : Ty)
      (h : Typing G (.vals Δ Θ Γ vs (List.replicate vs.length τ))) (hsi : τ.SI) :
      Typing G (.val Δ Θ Γ (.slice vs) (.slice τ))
  /-- `T-Pointer` -/
  | vPtr (Δ : TyEnv) (Θ : TempTy) (Γ : StackTy) (R : Referent) (r : Nat) (ω : Own) (τ : Ty)
      (L : List Loan) (hR : RefTy Γ R τ) (hxi : τ.XI)
      (hr : Γ.loans? r = some L) (hl : (⟨ω, R.base.toExpr⟩ : Loan) ∈ L) :
      Typing G (.val Δ Θ Γ (.ptr R) (.ref (.conc r) ω τ))
  /-- `T-ClosureValue` (together with `WF-Frame` for the captured frame): the
  captured frame `Φc` binds `q` regions, opened at fresh levels as in `T-Closure` -/
  | vClosure (Δ : TyEnv) (Θ : TempTy) (Γ : StackTy) (m k q : Nat) (frame : List Value)
      (ps : List Ty) (ret : Ty) (body : Term (m + k)) (Φc Φ' : FrameTy) (Γ' : StackTy)
      (hk : ps.length = k) (hm : frame.length = m) (hΦm : Φc.numVars = m)
      (hq : Φc.numRgns = q)
      (hsi : ∀ τ ∈ ps, τ.SI) (hsir : ret.SI)
      (hocc : ∀ j : Fin m, body.occurs (k + j.val) = true)
      (hframe : ∀ (j : Nat) (v : Value) (τ : Ty), frame[j]? = some v →
        (Φc.openAt Γ.numRgns).varAt j = some τ →
        Typing G (.val {} [] (Φc.openAt Γ.numRgns :: Γ) v τ))
      (hb : Typing G (.expr Δ Θ
        (FrameTy.openAt Γ.numRgns (ps.reverse.map FrameEntry.var ++ Φc) :: Γ)
        (body.openRgns (newLevels Γ.numRgns q)) ret (Φ' :: Γ'))) :
      Typing G (.val Δ Θ Γ (.closure m k q frame ps ret body) (Ty.closure ps ret (.frame Φc)))
  /-- `T-Left` on values -/
  | vInl (Δ : TyEnv) (Θ : TempTy) (Γ : StackTy) (τ₁ τ₂ : Ty) (v : Value)
      (h : Typing G (.val Δ Θ Γ v τ₁)) (hsi₁ : τ₁.SI) (hsi₂ : τ₂.SI) :
      Typing G (.val Δ Θ Γ (.inl τ₁ τ₂ v) (.sum τ₁ τ₂))
  /-- `T-Right` on values -/
  | vInr (Δ : TyEnv) (Θ : TempTy) (Γ : StackTy) (τ₁ τ₂ : Ty) (v : Value)
      (h : Typing G (.val Δ Θ Γ v τ₂)) (hsi₁ : τ₁.SI) (hsi₂ : τ₂.SI) :
      Typing G (.val Δ Θ Γ (.inr τ₁ τ₂ v) (.sum τ₁ τ₂))
  -- ## Lists of values (components of tuple, array and slice values).
  | vsNil (Δ : TyEnv) (Θ : TempTy) (Γ : StackTy) : Typing G (.vals Δ Θ Γ [] [])
  | vsCons (Δ : TyEnv) (Θ : TempTy) (Γ : StackTy) (v : Value) (vs : List Value) (τ : Ty)
      (τs : List Ty) (h : Typing G (.val Δ Θ Γ v τ)) (t : Typing G (.vals Δ (Θ ++ [τ]) Γ vs τs)) :
      Typing G (.vals Δ Θ Γ (v :: vs) (τ :: τs))

/-- `Σ; Δ; Γ; Θ ⊢ e : τ ⇒ Γ'`. -/
abbrev HasType (G : GlobalEnv) (Δ : TyEnv) (Θ : TempTy) (Γ : StackTy) {n : Nat} (e : Term n)
    (τ : Ty) (Γ' : StackTy) : Prop := Typing G (.expr Δ Θ Γ e τ Γ')

/-- Typing of argument lists (used by `T-Tuple`, `T-Array`, `T-AppFunction`): the
`i`-th expression is typed with the types of the previous ones added to `Θ`. -/
abbrev HasTypeArgs (G : GlobalEnv) (Δ : TyEnv) (Θ : TempTy) (Γ : StackTy) {n : Nat}
    (es : Terms n) (τs : List Ty) (Γ' : StackTy) : Prop := Typing G (.args Δ Θ Γ es τs Γ')

/-- Typing of closure arguments (`T-AppClosure`): each argument is rewritten with
mode `⊞` to the parameter type. -/
abbrev HasTypeArgsRw (G : GlobalEnv) (Δ : TyEnv) (Θ : TempTy) (Γ : StackTy) {n : Nat}
    (es : Terms n) (τs : List Ty) (Γ' : StackTy) : Prop := Typing G (.argsRw Δ Θ Γ es τs Γ')

/-- Value typing `Σ; Δ; Γ; Θ ⊢ v : τ ⇒ Γ` (values never change the stack typing). -/
abbrev HasTypeV (G : GlobalEnv) (Δ : TyEnv) (Θ : TempTy) (Γ : StackTy) (v : Value) (τ : Ty) :
    Prop := Typing G (.val Δ Θ Γ v τ)

/-- Typing of lists of values (components of tuple, array and slice values). -/
abbrev HasTypeVs (G : GlobalEnv) (Δ : TyEnv) (Θ : TempTy) (Γ : StackTy) (vs : List Value)
    (τs : List Ty) : Prop := Typing G (.vals Δ Θ Γ vs τs)

end Oxide
