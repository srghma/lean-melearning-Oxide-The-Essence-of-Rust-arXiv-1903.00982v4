module
public import RequestProject.Oxide.Metatheory.Counterexamples.Closure
public import Mathlib.Logic.Relation

/-!
# Preservation restricted to reachable configurations

The paper's Preservation lemma is false for arbitrary configurations
(`not_preservation`).  A natural repair restricts it to configurations that are
reachable from a well-typed closed program run on the empty stack
(`PreservationReach`).  Such a lemma, iterated along the run, yields the invariant
`ReachableTyped` ("every reachable configuration is well typed and its stack is
valid"), and that invariant together with `progress` gives type safety.

Both counterexamples to type safety (`not_type_safety`, `not_type_safety_closure`)
are reachable, so the invariant, and with it the restricted preservation lemma, is
false as well: `not_reachableTyped`, `not_preservationReach`.
-/

@[expose] public section

namespace Oxide

variable {G : GlobalEnv}

/-- The paper's Preservation lemma restricted to configurations reachable from a
well-typed closed program run on the empty stack (without temporaries). -/
def PreservationReach (G : GlobalEnv) : Prop :=
  ∀ (e₀ : Term 0) (τ₀ : Ty) (Γ₀ : StackTy), HasType G {} [] [] e₀ τ₀ Γ₀ →
  ∀ (σ σ' : Stack) (e e' : Term 0), Steps G [] e₀ σ e → Step G σ e σ' e' →
  ∀ (Γ Γf : StackTy) (τ₁ : Ty), HasType G {} [] Γ e τ₁ Γf → StoreValid G Γ σ →
    ∃ (Γi : StackTy) (τ₂ : Ty) (Γf' Γs Γo : StackTy),
      StoreValid G Γi σ' ∧ HasType G {} [] Γi e' τ₂ Γf' ∧
      Rewrite {} [] .combine Γf' τ₂ τ₁ Γs ∧ StackTy.union Γs Γo = some Γf

/-- Every configuration reachable from a well-typed closed program run on the
empty stack is well typed, with a stack satisfying the stack typing. -/
def ReachableTyped (G : GlobalEnv) : Prop :=
  ∀ (e₀ : Term 0) (τ₀ : Ty) (Γ₀ : StackTy), HasType G {} [] [] e₀ τ₀ Γ₀ →
  ∀ (σ : Stack) (e : Term 0), Steps G [] e₀ σ e →
    ∃ (Γ Γf : StackTy) (τ : Ty), HasType G {} [] Γ e τ Γf ∧ StoreValid G Γ σ

/-- Appending a step to a sequence of steps. -/
theorem Steps.snoc {n : Nat} {σ₁ σ₂ σ₃ : Stack} {e₁ e₂ e₃ : Term n}
    (h : Steps G σ₁ e₁ σ₂ e₂) (s : Step G σ₂ e₂ σ₃ e₃) : Steps G σ₁ e₁ σ₃ e₃ := by
  induction h with
  | refl σ e => exact .step _ _ _ _ _ _ s (.refl _ _)
  | step σ σ' σ'' e e' e'' h _ ih => exact .step _ _ _ _ _ _ h (ih s)

/-- `Steps` as the reflexive-transitive closure of the step relation on configurations. -/
theorem Steps.toRTG {n : Nat} {σ σ' : Stack} {e e' : Term n} (h : Steps G σ e σ' e') :
    Relation.ReflTransGen (fun a b : Stack × Term n => Step G a.1 a.2 b.1 b.2) (σ, e) (σ', e') := by
  induction h with
  | refl => exact .refl
  | step _ _ _ _ _ _ s _ ih => exact .head s ih

theorem Steps.ofRTG {n : Nat} {a b : Stack × Term n}
    (h : Relation.ReflTransGen (fun a b : Stack × Term n => Step G a.1 a.2 b.1 b.2) a b) :
    Steps G a.1 a.2 b.1 b.2 := by
  induction h with
  | refl => exact .refl _ _
  | tail _ s ih => exact ih.snoc s

/-- The restricted preservation lemma implies the reachability invariant. -/
theorem reachableTyped_of_preservationReach (hp : PreservationReach G) : ReachableTyped G := by
  intro e₀ τ₀ Γ₀ ht₀ σ e hs
  suffices ∀ c : Stack × Term 0,
      Relation.ReflTransGen (fun a b : Stack × Term 0 => Step G a.1 a.2 b.1 b.2) ([], e₀) c →
      ∃ (Γ Γf : StackTy) (τ : Ty), HasType G {} [] Γ c.2 τ Γf ∧ StoreValid G Γ c.1 from
    this (σ, e) hs.toRTG
  intro c h
  induction h with
  | refl => exact ⟨[], Γ₀, τ₀, ht₀, .empty⟩
  | @tail b c hab s ih =>
    obtain ⟨Γ, Γf, τ, ht, hσ⟩ := ih
    obtain ⟨Γi, τ₂, Γf', -, -, hσi, hti, -, -⟩ :=
      hp e₀ τ₀ Γ₀ ht₀ b.1 c.1 b.2 c.2 (Steps.ofRTG hab) s Γ Γf τ ht hσ
    exact ⟨Γi, Γf', τ₂, hti, hσi⟩

/-- The reachability invariant implies type safety (by `progress`). -/
theorem type_safety_of_reachableTyped (h : ReachableTyped G) : TypeSafety G := by
  intro e τ Γ ht σ' e' hs
  obtain ⟨Γ₁, Γf, τ₁, ht₁, hσ₁⟩ := h e τ Γ ht σ' e' hs
  exact progress_aux ht₁ Γ₁ σ' (Refines.refl Γ₁) hσ₁

/-- The reachability invariant is false (for every global environment). -/
theorem not_reachableTyped : ¬ ReachableTyped G :=
  fun h => not_type_safety (type_safety_of_reachableTyped h)

/-- **Preservation restricted to reachable configurations is false** as well (for
every global environment): restricting the paper's lemma to configurations
reachable from closed programs run on the empty stack does not repair it. -/
theorem not_preservationReach : ¬ PreservationReach G :=
  fun h => not_reachableTyped (reachableTyped_of_preservationReach h)

end Oxide
