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
| Progress (as stated, for the machine) | **refuted** (`not_progress`): a closure value whose body mentions a region that its type does not mention blocks the pop of that region |
| Preservation (as stated) | **refuted** (`not_preservation`) |
| Type safety (as stated) | **refuted**, twice: `not_type_safety` (`E-Move` on a copyable place) and `not_type_safety_scope` (the closure of `not_progress`, reached from a well-typed closed program) |
| A **repaired** Oxide with proved progress, preservation and type safety | **missing** |

The repairs that the counterexamples call for are listed in `README.md`
(§ Results). Whether they are enough is not established.

## 2. Supporting lemmas of `proofs.tex`

None are currently formalized for the scoped grammar. Before any progress or
preservation proof, the renaming and strengthening laws are needed:
- `rename_id` and `rename_comp`;
- `prename` after `rename`;
- weakening and strengthening of `Typing`, `PlaceTy`, `OwnSafe` and `StoreValid`;
- type-level substitution lemmas for `FnDef.instBody`.

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
  relations, and the machine is nondeterministic in what a closure captures.
* `DecidableEq` and `Repr` are not derived for `Ty` and `Term`, because of the
  `Fin k → _` fields. Equality of concrete terms is checked by `rfl`.
