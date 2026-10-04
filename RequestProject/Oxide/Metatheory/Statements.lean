module
public import RequestProject.Oxide.Typechecking.Validity
public import RequestProject.Oxide.OperationalSemantics.Dynamics

/-!
# Oxide: metatheory

Statements of the main metatheoretic results of the paper (section
"Metatheory"): canonical forms, progress, preservation and type safety, and the
derivation of type safety from progress and preservation.
-/

@[expose] public section

namespace Oxide

variable {G : GlobalEnv}

/-! ## Canonical forms -/

/-- Values typed by the expression typing judgment are typed by the value typing
judgment (in a stack typing from which the given one is obtained by drops). -/
theorem HasType.val_inv {Δ : TyEnv} {Θ : TempTy} {Γ Γ' : StackTy} {n : Nat} {v : Value} {τ : Ty}
    (h : HasType G Δ Θ Γ (n := n) (.val v) τ Γ') : ∃ Γ₀, HasTypeV G Δ Θ Γ₀ v τ := by
  change Typing G (TyJ.expr Δ Θ Γ (Term.val v : Term n) τ Γ') at h
  generalize hJ : TyJ.expr Δ Θ Γ (Term.val v : Term n) τ Γ' = J at h
  induction h generalizing Γ with
  | val => cases hJ; exact ⟨_, by assumption⟩
  | drop _ _ _ _ _ _ _ _ _ _ _ _ _ ih => cases hJ; exact ih rfl
  | _ => cases hJ

/-- Lists of typed values are as long as their lists of types. -/
theorem HasTypeVs.length_eq {Δ : TyEnv} {Θ : TempTy} {Γ : StackTy} {vs : List Value}
    {τs : List Ty} (h : HasTypeVs G Δ Θ Γ vs τs) : vs.length = τs.length := by
  change Typing G (TyJ.vals Δ Θ Γ vs τs) at h
  generalize hJ : TyJ.vals Δ Θ Γ vs τs = J at h
  induction h generalizing Θ vs τs with
  | vsNil => cases hJ; rfl
  | vsCons _ _ _ _ _ _ _ _ _ _ ih => cases hJ; simp [ih rfl]
  | _ => cases hJ

/-- Canonical forms (Lemma "Canonical Forms" of the paper). -/
theorem canonical_forms {Δ : TyEnv} {Θ : TempTy} {Γ : StackTy} {v : Value} {τ : Ty}
    (h : HasTypeV G Δ Θ Γ v τ) :
    (τ = Ty.bool → ∃ b, v = .prim (.bool b)) ∧
    (τ = Ty.u32 → ∃ k, v = Value.num k) ∧
    (τ = Ty.unit → v = Value.unit) ∧
    (∀ ρ ω τ', τ = .ref ρ ω τ' → ∃ R, v = .ptr R) ∧
    (∀ τ' k, τ = .array τ' k → ∃ vs, v = .array vs ∧ vs.length = k) ∧
    (∀ τ', τ = .slice τ' → ∃ vs, v = .slice vs) ∧
    (∀ τs, τ = .tuple τs → ∃ vs, v = .tuple vs ∧ vs.length = τs.length) ∧
    (∀ τ₁ τ₂, τ = .sum τ₁ τ₂ → (∃ v', v = .inl τ₁ τ₂ v') ∨ (∃ v', v = .inr τ₁ τ₂ v')) ∧
    (∀ nφ nϱ nα ps r Φ bs, τ = .fn nφ nϱ nα ps r Φ bs →
      (∃ f, v = .fn f) ∨ (∃ m q frame body, v = .closure m ps.length q frame ps r body)) := by
  cases h <;> simp_all [Ty.bool, Ty.u32, Ty.unit, Ty.closure, Value.num, Value.unit]
  case vTuple h => exact HasTypeVs.length_eq h
  case vClosure hk _ _ _ _ _ _ _ _ =>
    rintro _ _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl rfl
    subst hk
    exact ⟨rfl, _, HEq.rfl⟩

/-! ## Progress, preservation and type safety -/

/-- **Progress**: a well-typed expression (in the empty type environment) whose
stack typing is satisfied by the stack is a value, an `abort!`, or can take a
step. -/
def Progress (G : GlobalEnv) : Prop :=
  ∀ {n : Nat} (Θ : TempTy) (Γ Γ' : StackTy) (σ : Stack) (e : Term n) (τ : Ty),
    HasType G {} Θ Γ e τ Γ' → StoreValid G Γ σ →
      e.IsFinal ∨ ∃ σ' e', Step G σ e σ' e'

/-- **Preservation**: if a well-typed expression steps, the result is well typed
in a new stack typing that is satisfied by the new stack and keeps the
temporaries valid; its type can be rewritten (mode `+`) into the original type,
and the original output stack typing is the union of the rewritten output
stack typing with some stack typing. -/
def Preservation (G : GlobalEnv) : Prop :=
  ∀ {n : Nat} (Θ : TempTy) (Γ Γf : StackTy) (σ σ' : Stack) (vs : List Value)
    (e e' : Term n) (τ₁ : Ty),
    HasType G {} Θ Γ e τ₁ Γf → StoreValid G Γ σ → TempValid G Γ vs Θ →
    Step G σ e σ' e' →
      ∃ (Γi : StackTy) (τ₂ : Ty) (Γf' Γs Γo : StackTy),
        StoreValid G Γi σ' ∧ TempValid G Γi vs Θ ∧ HasType G {} Θ Γi e' τ₂ Γf' ∧
        Rewrite {} Θ .combine Γf' τ₂ τ₁ Γs ∧ StackTy.union Γs Γo = some Γf

/-- **Type safety**: evaluation of a closed well-typed program (starting from the
empty stack) never gets stuck: every reachable configuration is final (a value or
an `abort!`) or can take a further step.  Hence evaluation produces a value,
aborts, or diverges. -/
def TypeSafety (G : GlobalEnv) : Prop :=
  ∀ (e : Term 0) (τ : Ty) (Γ : StackTy), HasType G {} [] [] e τ Γ →
    ∀ σ' e', Steps G [] e σ' e' → e'.IsFinal ∨ ∃ σ'' e'', Step G σ' e' σ'' e''

/-- Preservation iterated along a sequence of steps (with no temporaries). -/
theorem steps_preserve_typing (hpres : Preservation G) {m : Nat} {σ₀ σ₁ : Stack}
    {e₀ e₁ : Term m} (h : Steps G σ₀ e₀ σ₁ e₁)
    (ht : ∃ Γ₀ τ₀ Γf, HasType G {} [] Γ₀ e₀ τ₀ Γf ∧ StoreValid G Γ₀ σ₀) :
    ∃ Γ₁ τ₁ Γf, HasType G {} [] Γ₁ e₁ τ₁ Γf ∧ StoreValid G Γ₁ σ₁ :=
  match h with
  | .refl _ _ => ht
  | .step σ σ' _ e e' _ hs t =>
    let ⟨Γ₀, τ₀, Γf, ht₀, hσ₀⟩ := ht
    let ⟨Γi, τ₂, Γf', _, _, hσi, _, hti, _⟩ :=
      hpres [] Γ₀ Γf σ σ' [] e e' τ₀ ht₀ hσ₀ ⟨rfl, by simp⟩ hs
    steps_preserve_typing hpres t ⟨Γi, τ₂, Γf', hti, hσi⟩

/-- Type safety follows from progress and preservation (by their interleaved use,
as in the paper).  Note that `Preservation` as stated in the paper is refuted by
`not_preservation`, so this lemma only records the structure of the paper's
argument. -/
theorem type_safety_of_progress_preservation (hprog : Progress G) (hpres : Preservation G) :
    TypeSafety G := by
  intro e τ Γ ht σ' e' hsteps
  obtain ⟨Γ₁, τ₁, Γf, ht₁, hσ₁⟩ := steps_preserve_typing hpres hsteps ⟨[], τ, Γ, ht, .empty⟩
  exact hprog [] Γ₁ Γf σ' e' τ₁ ht₁ hσ₁

end Oxide
