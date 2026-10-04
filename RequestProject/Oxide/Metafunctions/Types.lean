module

public import RequestProject.Oxide.Metafunctions.Substitution

/-!
# Oxide metafunctions, part 2: types

Appendix C ("Metafunctions") of the paper: free regions of types,
(non)copyability, the function types and captured frames occurring in a type,
initializedness of maybe-dead types, and decomposition of types along paths
(`explode`, `τ.q ⇝ τ_□ ⊞ τ'`).

The sort predicates of the paper (`τ^SI`, `τ^XI`, `τ^SD`, `τ^SX`) are gone: they
are the types `Ty`, `XTy` and `MTy` themselves.
-/

@[expose] public section

namespace Oxide

/-- Strengthen a list of indices past a prefix of binders (dropping the indices
into the prefix). -/
def strengthenL {b : Bnd} [Bnd.Idx b] {Γ : Ctx} (cs : Ctx) (l : List (In b (cs ++ Γ))) : List (In b Γ) :=
  l.filterMap (PRen.dropL cs Γ).ren

/-- The partial renaming popping a frame of shape `f`. -/
def PRen.popFrameL (f Γ : Ctx) : PRen (f ++ .frame :: Γ) Γ :=
  ⟨fun i => ((PRen.dropL f (.frame :: Γ)).ren i).map In.dropFrame⟩

/-- Strengthen a list of indices past a frame of shape `f`. -/
def strengthenFrame {b : Bnd} [Bnd.Idx b] {Γ : Ctx} (f : Ctx) (l : List (In b (f ++ .frame :: Γ))) :
    List (In b Γ) :=
  l.filterMap (PRen.popFrameL f Γ).ren

/-! ## Concrete regions occurring in types (`free-regions`) -/

/-- Concrete regions of a region. -/
def Region.frgns {Γ : Ctx} : Region Γ → List (In .rgn Γ)
  | .conc r => [r]
  | .abs _ => []

mutual
/-- All concrete regions occurring in a type (also used for "`r` occurs in `τ`").
Regions bound inside the type (the regions of a captured frame) are omitted. -/
def Ty.frgns {Γ : Ctx} : Ty Γ → List (In .rgn Γ)
  | .base _ => []
  | .tvar _ => []
  | .ref ρ _ τ => ρ.frgns ++ τ.frgns
  | .array τ _ => τ.frgns
  | .tuple k τs => (List.finRange k).flatMap fun i => (τs i).frgns
  | .sum τ₁ τ₂ => τ₁.frgns ++ τ₂.frgns
  | .fn b k ps ret env _ =>
      strengthenL b.ctx ((List.finRange k).flatMap (fun i => (ps i).frgns) ++ ret.frgns ++ env.frgns)
def XTy.frgns {Γ : Ctx} : XTy Γ → List (In .rgn Γ)
  | .sized τ => τ.frgns
  | .slice τ => τ.frgns
def FrameExpr.frgns {Γ : Ctx} : FrameExpr Γ → List (In .rgn Γ)
  | .var _ => []
  | .frame f Φ => strengthenFrame f Φ.frgns
def FrameTy.frgns {Γ : Ctx} : {f : Ctx} → FrameTy Γ f → List (In .rgn Γ)
  | _, .nil => []
  | _, .var τ Φ => τ.frgns ++ Φ.frgns
  | _, .rgn _ Φ => Φ.frgns
end

/-- Concrete regions of a maybe-dead type. -/
def MTy.frgns {Γ : Ctx} : MTy Γ → List (In .rgn Γ)
  | .init τ => τ.frgns
  | .dead τ => τ.frgns
  | .tuple k τs => (List.finRange k).flatMap fun i => (τs i).frgns

/-- Concrete regions occurring in a type *outside of* any function type. -/
def Ty.frgnsOut {Γ : Ctx} : Ty Γ → List (In .rgn Γ)
  | .ref ρ _ (.sized τ) => ρ.frgns ++ τ.frgnsOut
  | .ref ρ _ (.slice τ) => ρ.frgns ++ τ.frgnsOut
  | .array τ _ => τ.frgnsOut
  | .tuple k τs => (List.finRange k).flatMap fun i => (τs i).frgnsOut
  | .sum τ₁ τ₂ => τ₁.frgnsOut ++ τ₂.frgnsOut
  | _ => []

/-- `frgnsOut` for maybe-dead types. -/
def MTy.frgnsOut {Γ : Ctx} : MTy Γ → List (In .rgn Γ)
  | .init τ => τ.frgnsOut
  | .dead τ => τ.frgnsOut
  | .tuple k τs => (List.finRange k).flatMap fun i => (τs i).frgnsOut

/-! ## Function types and captured frames occurring in types -/

mutual
/-- The concrete regions mentioned by the signature (parameters and return type)
of each function type occurring in a type. -/
def Ty.sigRgns {Γ : Ctx} : Ty Γ → List (List (In .rgn Γ))
  | .ref _ _ (.sized τ) => τ.sigRgns
  | .ref _ _ (.slice τ) => τ.sigRgns
  | .array τ _ => τ.sigRgns
  | .tuple k τs => (List.finRange k).flatMap fun i => (τs i).sigRgns
  | .sum τ₁ τ₂ => τ₁.sigRgns ++ τ₂.sigRgns
  | .fn b k ps ret _ _ =>
      strengthenL b.ctx ((List.finRange k).flatMap (fun i => (ps i).frgns) ++ ret.frgns) ::
        (((List.finRange k).flatMap fun i => (ps i).sigRgns) ++ ret.sigRgns).map (strengthenL b.ctx)
  | _ => []
end

/-- Strengthen a list of loans past a prefix of binders (dropping the loans to
places in the prefix). -/
def strengthenLoans {Γ : Ctx} (cs : Ctx) (L : List (Loan (cs ++ Γ))) : List (Loan Γ) :=
  L.filterMap (Loan.prename (PRen.dropL cs Γ))

/-- Strengthen a list of loans past a frame of shape `f`. -/
def strengthenLoansFrame {Γ : Ctx} (f : Ctx) (L : List (Loan (f ++ .frame :: Γ))) : List (Loan Γ) :=
  L.filterMap (Loan.prename (PRen.popFrameL f Γ))

mutual
/-- The loan sets of the regions of the frames captured by closure types occurring
in a type (`regions(…)` of a closure frame); loans to places of the captured
frames themselves are omitted. -/
def Ty.closureLoans {Γ : Ctx} : Ty Γ → List (List (Loan Γ))
  | .ref _ _ (.sized τ) => τ.closureLoans
  | .ref _ _ (.slice τ) => τ.closureLoans
  | .array τ _ => τ.closureLoans
  | .tuple k τs => (List.finRange k).flatMap fun i => (τs i).closureLoans
  | .sum τ₁ τ₂ => τ₁.closureLoans ++ τ₂.closureLoans
  | .fn b k ps ret env _ =>
      ((((List.finRange k).flatMap fun i => (ps i).closureLoans) ++ ret.closureLoans ++
        env.closureLoans)).map (strengthenLoans b.ctx)
  | _ => []
def FrameExpr.closureLoans {Γ : Ctx} : FrameExpr Γ → List (List (Loan Γ))
  | .var _ => []
  | .frame f Φ => (Φ.closureLoans).map (strengthenLoansFrame f)
def FrameTy.closureLoans {Γ : Ctx} : {f : Ctx} → FrameTy Γ f → List (List (Loan Γ))
  | _, .nil => []
  | _, .var τ Φ => τ.closureLoans ++ Φ.closureLoans
  | _, .rgn L Φ => L :: Φ.closureLoans
end

/-- `closureLoans` for maybe-dead types. -/
def MTy.closureLoans {Γ : Ctx} : MTy Γ → List (List (Loan Γ))
  | .init τ => τ.closureLoans
  | .dead τ => τ.closureLoans
  | .tuple k τs => (List.finRange k).flatMap fun i => (τs i).closureLoans

/-- `sigRgns` for maybe-dead types. -/
def MTy.sigRgns {Γ : Ctx} : MTy Γ → List (List (In .rgn Γ))
  | .init τ => τ.sigRgns
  | .dead τ => τ.sigRgns
  | .tuple k τs => (List.finRange k).flatMap fun i => (τs i).sigRgns

/-! ## Copyability -/

/-- `noncopyable` (appendix "Metafunctions"). -/
def Ty.noncopyable {Γ : Ctx} : Ty Γ → Bool
  | .base _ => false
  | .tvar _ => true
  | .ref _ .uniq _ => true
  | .ref _ .shrd _ => false
  | .fn .. => false
  | .array τ _ => τ.noncopyable
  | .tuple k τs => (List.finRange k).any fun i => (τs i).noncopyable
  | .sum τ₁ τ₂ => τ₁.noncopyable || τ₂.noncopyable

/-- `copyable τ = ¬ noncopyable τ`. -/
def Ty.copyable {Γ : Ctx} (τ : Ty Γ) : Bool := !τ.noncopyable

/-! ## Maybe-dead types -/

/-- A maybe-dead type that is fully initialized. -/
def MTy.toTy? {Γ : Ctx} : MTy Γ → Option (Ty Γ)
  | .init τ => some τ
  | .dead _ => none
  | .tuple k τs => (optFin fun i => (τs i).toTy?).map (.tuple k)

/-- `τ^SD`: a type all of whose parts are dead. -/
def MTy.IsDead {Γ : Ctx} : MTy Γ → Prop
  | .init _ => False
  | .dead _ => True
  | .tuple k τs => ∀ i : Fin k, (τs i).IsDead

/-- `τ.q ⇝ τ_□ ⊞ τ'` (`D-End`, `D-Projection`): the component of a maybe-dead type
at path `q`. -/
def MTy.atPath {Γ : Ctx} : MTy Γ → List Nat → Option (MTy Γ)
  | m, [] => some m
  | .init (.tuple k τs), i :: q => if h : i < k then (MTy.init (τs ⟨i, h⟩)).atPath q else none
  | .tuple k ms, i :: q => if h : i < k then (ms ⟨i, h⟩).atPath q else none
  | _, _ :: _ => none

/-- Replace the component of a maybe-dead type at path `q` (i.e. `τ_□[τ']`). -/
def MTy.setPath {Γ : Ctx} : MTy Γ → List Nat → MTy Γ → Option (MTy Γ)
  | _, [], m' => some m'
  | .init (.tuple k τs), i :: q, m' =>
      if h : i < k then
        ((MTy.init (τs ⟨i, h⟩)).setPath q m').map fun mi =>
          .tuple k fun j => if j = ⟨i, h⟩ then mi else .init (τs j)
      else none
  | .tuple k ms, i :: q, m' =>
      if h : i < k then
        ((ms ⟨i, h⟩).setPath q m').map fun mi => .tuple k fun j => if j = ⟨i, h⟩ then mi else ms j
      else none
  | _, _ :: _, _ => none

/-- `explode(π : τ)`: tuples are split into their components. -/
def Ty.explode {Γ : Ctx} (π : APlace Γ) : Ty Γ → List (APlace Γ × Ty Γ)
  | .tuple k τs => (List.finRange k).flatMap fun i => (τs i).explode ⟨π.root, π.path ++ [i.val]⟩
  | τ => [(π, τ)]

/-- `explode` for maybe-dead types: the initialized leaves. -/
def MTy.explode {Γ : Ctx} (π : APlace Γ) : MTy Γ → List (APlace Γ × Ty Γ)
  | .init τ => τ.explode π
  | .dead _ => []
  | .tuple k τs => (List.finRange k).flatMap fun i => (τs i).explode ⟨π.root, π.path ++ [i.val]⟩

end Oxide
