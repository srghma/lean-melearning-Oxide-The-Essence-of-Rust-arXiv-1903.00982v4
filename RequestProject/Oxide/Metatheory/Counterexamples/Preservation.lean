module
public import RequestProject.Oxide.Metatheory.Progress.Main

/-!
# Preservation, as stated in the paper, does not hold for arbitrary configurations

The lemma "Preservation" of the paper quantifies over *all* well-typed runtime
configurations.  `T-Framed` types the body of `framed e` in the same stack typing
as the whole expression (whose top frame is the frame that `E-Framed` pops), and
nothing prevents the result value from pointing into that frame.  When `E-Framed`
pops the frame, the pointer dangles and the resulting value cannot be typed at
any type that rewrites into the original one.

Concretely, with the stack typing `Γ = [[r ↦ {shrd x}, x : u32]]` and the stack
`σ = [[r, x ↦ 5]]`, the configuration `(σ; framed (ptr x))` is well typed at
`&r shrd u32` with output stack typing `•`, but it steps to `(•; ptr x)`, and
`ptr x` is only typable at dead types in the (necessarily empty) stack typing of
the empty stack; dead types never rewrite into reference types.

Such configurations are not reachable from closed programs evaluated from the
empty stack (function bodies are checked against signatures whose return types
cannot mention the regions of the callee's frame), so this does not refute type
safety; it shows that a proof of type safety needs an additional invariant on the
configurations that preservation is applied to.
-/

@[expose] public section

namespace Oxide

variable {G : GlobalEnv}

/-- A referent cannot be well formed in the empty stack typing. -/
theorem RefTy.not_nil {R : Referent} {τ : Ty} (h : RefTy [] R τ) : False := by
  induction h with
  | id _ _ hv _ => simp [StackTy.varTy] at hv
  | _ => assumption

/-- Rewriting never turns a dead type into a live one. -/
theorem RewriteJ.dead_left {Δ : TyEnv} {Θ : TempTy} {μ : Mode} {F : RewriteForm}
    (h : RewriteJ Δ Θ μ F) :
    match F with
    | .one _ τ₁ τ₂ _ => (∃ t, τ₁ = .dead t) → ∃ t, τ₂ = .dead t
    | .all .. => True := by
  induction h with
  | refl => exact id
  | trans _ _ _ _ _ _ _ _ ih₁ ih₂ => exact fun h => ih₂ (ih₁ h)
  | ref => rintro ⟨_, h⟩; cases h
  | array => rintro ⟨_, h⟩; cases h
  | slice => rintro ⟨_, h⟩; cases h
  | tuple => rintro ⟨_, h⟩; cases h
  | dead => exact fun _ => ⟨_, rfl⟩
  | allNil => trivial
  | allCons => trivial

/-- The stack typing of the counterexample: one frame with a variable `x : u32`
(level `0`) and, more recently, a region (level `0`) holding the loan `shrd x`. -/
def cexΓ : StackTy := [[.rgn [⟨.shrd, ⟨0, []⟩⟩], .var Ty.u32]]

/-- The stack of the counterexample. -/
def cexσ : Stack := [[.rgn, .val (Value.num 5)]]

/-- The expression of the counterexample: `framed (ptr x)`. -/
def cexE : Term 0 := .framed 1 (.val (.ptr ⟨0, []⟩))

theorem cex_storeValid : StoreValid G cexΓ cexσ :=
  .frame [] [] _ _ .empty (.cons trivial (.cons (Typing.vNum _ _ _ 5) .nil))

theorem cex_typed :
    HasType G {} [] cexΓ cexE (.ref (.conc 0) .shrd Ty.u32) [] := by
  refine Typing.framed {} [] cexΓ _ [] 1 _ _ (Typing.val _ _ _ _ _ ?_) ?_
  · refine Typing.vPtr {} [] cexΓ ⟨0, []⟩ 0 .shrd Ty.u32 [⟨.shrd, ⟨0, []⟩⟩] ?_ ?_ ?_ ?_
    · exact RefTy.id 0 Ty.u32 rfl (.base _)
    · exact .inl (.base _)
    · rfl
    · simp [Referent.base, APlace.toExpr]
  · exact .ref _ _ _ (.base _)

theorem cex_step : Step G cexσ cexE [] (.val (.ptr ⟨0, []⟩)) :=
  Step.framed _ [] 1 _

/-- **Preservation, as stated in the paper (`Preservation`), is false**, for every
global environment (in particular for well-formed ones). -/
theorem not_preservation : ¬ Preservation G := by
  intro hpres
  obtain ⟨Γi, τ₂, Γf', Γs, Γo, hσ, -, ht, hrw, -⟩ :=
    hpres [] cexΓ [] cexσ [] [] cexE _ _ cex_typed cex_storeValid ⟨rfl, by simp⟩ cex_step
  have hΓi : Γi = [] := by cases hσ; rfl
  subst hΓi
  obtain ⟨hR, hv⟩ := HasType.val_inv' ht
  have hΓf' : Γf' = [] := hR.nil_iff.2 rfl
  subst hΓf'
  cases hv with
  | vDead _ _ _ _ t _ =>
    obtain ⟨_, h⟩ := RewriteJ.dead_left hrw ⟨t, rfl⟩
    cases h
  | vPtr _ _ _ _ _ _ _ _ hR' _ _ _ => exact hR'.not_nil

end Oxide
