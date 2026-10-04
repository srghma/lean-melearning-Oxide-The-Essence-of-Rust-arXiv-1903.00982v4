module

public import RequestProject.Oxide.Typechecking.Continuations
public import RequestProject.Oxide.OperationalSemantics.Machine

/-!
# Oxide: metatheory

Statements of the main metatheoretic results of the paper (section
"Metatheory"): canonical forms, progress, preservation and type safety, and the
derivation of type safety from progress and preservation, for the abstract
machine of `OperationalSemantics/Machine.lean`.
-/

@[expose] public section

namespace Oxide

variable {G : GlobalEnv}

/-! ## Canonical forms -/

/-- Values typed by the expression typing judgment are typed by the value typing
judgment (in a stack typing from which the given one is obtained by drops). -/
theorem HasType.val_inv {S : Ctx} {Θ : TempTy S} {Γ Γ' : StackTy S} {v : Value S} {τ : Ty S}
    (h : HasType G Θ Γ (.val v) τ Γ') : ∃ Γ₀, HasTypeV G Θ Γ₀ v τ := by
  change Typing G (TyJ.expr Θ Γ (Term.val v) τ Γ') at h
  generalize hJ : TyJ.expr Θ Γ (Term.val v) τ Γ' = J at h
  induction h generalizing Γ with
  | val => cases hJ; exact ⟨_, by assumption⟩
  | drop _ _ _ _ _ _ _ _ _ _ _ ih => cases hJ; exact ih rfl
  | _ => cases hJ

/-- The dead value has no (initialized) type. -/
theorem HasTypeV.not_dead {S : Ctx} {Θ : TempTy S} {Γ : StackTy S} {τ : Ty S}
    (h : HasTypeV G Θ Γ .dead τ) : False := by
  cases h

/-- Canonical forms (Lemma "Canonical Forms" of the paper). -/
theorem canonical_forms {S : Ctx} {Θ : TempTy S} {Γ : StackTy S} {v : Value S} {τ : Ty S}
    (h : HasTypeV G Θ Γ v τ) :
    (τ = Ty.bool → ∃ b, v = .prim (.bool b)) ∧
    (τ = Ty.u32 → ∃ n, v = Value.num n) ∧
    (τ = Ty.unit → v = Value.unit) ∧
    (∀ ρ ω τ', τ = .ref ρ ω τ' → ∃ R, v = .ptr R) ∧
    (∀ τ' n, τ = .array τ' n → ∃ vs, v = .array n vs) ∧
    (∀ k τs, τ = .tuple k τs → ∃ vs, v = .tuple k vs) ∧
    (∀ τ₁ τ₂, τ = .sum τ₁ τ₂ → (∃ v', v = .inl τ₁ τ₂ v') ∨ (∃ v', v = .inr τ₁ τ₂ v')) ∧
    (∀ b k ps r Φ bs, τ = .fn b k ps r Φ bs →
      (∃ f, v = .fn f) ∨ (∃ fr env k' ps' r' body, v = .closure fr env k' ps' r' body)) := by
  cases h <;> simp_all [Ty.bool, Ty.u32, Ty.unit, Ty.closure, FnDef.ty, Value.num, Value.unit]
  case vTuple => rintro _ _ rfl _; exact ⟨_, HEq.rfl⟩
  case vClosure => rintro _ _ _ _ _ _ _ rfl _ _ _ _; exact ⟨⟨_, HEq.rfl⟩, _, HEq.rfl⟩

/-! ## Progress, preservation and type safety -/

/-- **Progress**: a well-typed configuration is final (a value with nothing left
to do, or an `abort!`) or can take a step. -/
def Progress (G : GlobalEnv) : Prop :=
  ∀ c : Config, ConfigTyped G c → c.IsFinal ∨ ∃ c', Step G c c'

/-- **Preservation**: a step from a well-typed configuration leads to a well-typed
configuration.  (Since the continuation is typed as well, the paper's
rewriting and union of output stack typings are absorbed by the continuation
judgment.) -/
def Preservation (G : GlobalEnv) : Prop :=
  ∀ c c' : Config, ConfigTyped G c → Step G c c' → ConfigTyped G c'

/-- **Type safety**: evaluation of a closed well-typed program (starting from the
empty stack) never gets stuck: every reachable configuration is final or can take
a further step.  Hence evaluation produces a value, aborts, or diverges. -/
def TypeSafety (G : GlobalEnv) : Prop :=
  ∀ (e : Program) (τ : Ty []) (Γ' : StackTy []), HasType G [] StackTy.empty e τ Γ' →
    ∀ c, Steps G (Config.init e) c → c.IsFinal ∨ ∃ c', Step G c c'

/-- The initial configuration of a well-typed closed program is well typed. -/
theorem ConfigTyped.init {e : Program} {τ : Ty []} {Γ' : StackTy []}
    (h : HasType G [] StackTy.empty e τ Γ') : ConfigTyped G (Config.init e) :=
  ⟨[], StackTy.empty, τ, Γ', fun x => x.elimNil, h, .halt _ _ _⟩

/-- Preservation iterated along a sequence of steps. -/
theorem Steps.preserve (hpres : Preservation G) {c c' : Config} (h : Steps G c c')
    (ht : ConfigTyped G c) : ConfigTyped G c' := by
  induction h with
  | refl => exact ht
  | step c c' c'' hs _ ih => exact ih (hpres c c' ht hs)

/-- Type safety follows from progress and preservation (by their interleaved use,
as in the paper). -/
theorem type_safety_of_progress_preservation (hprog : Progress G) (hpres : Preservation G) :
    TypeSafety G := fun _ _ _ ht c hs => hprog c (hs.preserve hpres (ConfigTyped.init ht))

end Oxide
