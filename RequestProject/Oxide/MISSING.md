# What is still missing

`lake build` succeeds and the project contains no `sorry`.

The development was rebuilt on the scope-indexed grammar of
`Proposal/PROPOSAL.md`, which replaced the old `Nat`-indexed development. The
proofs that belonged to the old grammar were removed with it and have not been
ported: the progress proof and the supporting lemmas of `proofs.tex`.

## 1. Headline results

| Paper result | Status in Lean |
| --- | --- |
| Canonical forms | proved (`canonical_forms`) |
| Type safety from progress and preservation | proved (`type_safety_of_progress_preservation`) |
| Progress (for the machine) | **stated, open** (`Progress G`). The former counterexample (a closure whose body mentions a region missing from its type) is now ill typed (`tp_closure_untyped`, `tp_stuck_untyped`) |
| Preservation | **stated, open** (`Preservation G`). The former counterexample (`E-Move` on a copyable place) cannot arise: `E-Move` only applies to `Term.move` (`Metatheory/Regressions/MoveCopy.lean`) |
| Type safety | **stated, open** (`TypeSafety G`); both former counterexample programs are handled (`ts_runs`, `tp_prog_untyped`) |

The earlier refutations (`not_progress`, `not_preservation`, `not_type_safety`)
were about the previous rules; with the refinements listed in `README.md`
(§ The type-safety refinements) they no longer apply, and they have been
replaced by the regression files in `Metatheory/Regressions/`. Whether progress
and preservation now hold is not established.

A further problem was found and fixed later: a closure could capture the same
variable twice, and then hold two copies of a unique reference. A closure body
taking two simultaneously live unique borrows of one location type checked
(`dcBody_typed`). This is a violation of the uniqueness discipline, not a
refutation of the stated progress or preservation theorems. `T-Closure` now
requires `Cap.Nodup` (`Metatheory/Regressions/DuplicateCaptures.lean`).

## 2. Supporting lemmas of `proofs.tex`

None are currently formalized for the scoped grammar. Before any progress or
preservation proof, the renaming and strengthening laws are needed:
- `rename_id` and `rename_comp`;
- `prename` after `rename`;
- weakening and strengthening of `Typing`, `PlaceTy`, `OwnSafe` and `StoreValid`;
- type-level substitution lemmas for `GlobalEnv.instBody` and `Term.openBody`.

## 3. Language features not modelled

* `E-Closure` overwriting non-copyable captures with `dead` at runtime. This
  cannot be computed from runtime values; `T-Closure` does it statically.
* `E-Function` and function values `⟨•, fn …⟩`: function names are values.
* Struct, enum and pattern extensions, and the stand-alone
  `T-GarbageCollectLoans` rule. They are only in the macro files, not in the
  paper's figures.
* The "Tested Semantics" part of the paper.

## 4. Infrastructure not in the paper

* There is no executable type checker or interpreter. Typing and stepping are
  relations.
* The coverage premise of `T-Closure`, `Inst.Covered`, is stated semantically
  (via strengthening), not as a decidable syntactic check.
* `DecidableEq` and `Repr` are not derived for `Ty` and `Term`, because of the
  `Fin k → _` fields. Equality of concrete terms is checked by `rfl`.
