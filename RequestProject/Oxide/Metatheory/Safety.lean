module
public import RequestProject.Oxide.Metatheory.Counterexamples.Reachability

/-!
# Oxide: progress, preservation and type safety

* `progress` (Lemma "Progress" of the paper) is proved.
* The lemma "Preservation" of the paper, formalized as `Preservation`, is **false**
  as stated: `not_preservation` (in `Metatheory/Counterexamples/Preservation.lean`) gives a
  well-typed runtime configuration `framed (ptr x)` whose step pops the frame that
  `x` lives in.  The former statement `preservation` is therefore commented out
  below.
* The theorem "Type Safety" of the paper, formalized as `TypeSafety`, is also
  **false**: `not_type_safety` (in `Metatheory/Counterexamples/TypeSafety.lean`) runs the
  well-typed closed program `let x : bool = true; x; if x { () } else { () }`; since
  `E-Move` and `E-Copy` both apply to the place `x`, the first use of `x` may move
  it, and the `if` then gets stuck on `dead`.  Independently of moves,
  `not_type_safety_closure` (in `Metatheory/Counterexamples/Closure.lean`) gets stuck after a
  closure returns a pointer into its own (popped) frame.  The former statement
  `type_safety` is therefore commented out below.
* Restricting Preservation to configurations reachable from closed programs does
  not help: `not_preservationReach` (in `Metatheory/Counterexamples/Reachability.lean`).
-/

@[expose] public section

namespace Oxide

variable {G : GlobalEnv}

/-- Progress (Lemma "Progress" of the paper). -/
theorem progress : Progress G :=
  fun _ Γ _ σ _ _ ht hσ => progress_aux ht Γ σ (Refines.refl Γ) hσ

/- The statement of the paper's Preservation lemma is refuted by `not_preservation`
(already for the well-formed global environment `[]`), so it cannot be proved:

theorem preservation (hG : GlobalWF G) : Preservation G := by
  sorry
-/

/- The statement of the paper's Type Safety theorem is refuted by `not_type_safety`
and by `not_type_safety_closure` (for every global environment, in particular the
well-formed `[]`), so it cannot be proved:

theorem type_safety (hG : GlobalWF G) : TypeSafety G := by
  sorry
-/

/-- **Type safety, as stated in the paper, is false**: for every global environment
(in particular for well-formed ones) some well-typed closed program gets stuck. -/
theorem type_safety_false : ¬ TypeSafety G := not_type_safety

end Oxide
