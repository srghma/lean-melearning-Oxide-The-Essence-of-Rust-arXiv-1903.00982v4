# What is still missing (status as of the latest run)

`lake build` succeeds. The only `sorry`s in the project are inside the two
commented-out statements in `Metatheory/Safety.lean` (`preservation` and
`type_safety`), whose statements are refuted.

## 1. Headline results

| Paper result | Status in Lean |
| --- | --- |
| Progress | proved (`progress`) |
| Preservation (as stated) | refuted (`not_preservation`) |
| Type Safety (as stated) | refuted (`not_type_safety`, `not_type_safety_closure`) |
| Preservation restricted to reachable configurations | refuted (`not_preservationReach`) |
| A **repaired** Oxide with a proved preservation / type safety theorem | **missing**: no repaired rules have been written, so there is nothing to prove yet |

The repair needs changes to the rules themselves (see `README.md`):
(i) a type-directed choice between `E-Move` and `E-Copy`; (ii) a no-escape
condition for popped frames (`T-Framed`, closure bodies); and (iii) for the
closure counterexample, which only arises because pointers are de Bruijn
*levels*, either a different representation of referents or the no-escape
condition. Whether these changes are enough is not established.

## 2. Supporting lemmas of `proofs.tex` (67 lemmas)

Legend: **done** = a Lean theorem with the same content exists;
**partial** = only the special cases needed so far; **–** = not formalized.

### Standard and referent lemmas
| Lemma | Status | Lean |
| --- | --- | --- |
| Canonical Forms | done | `canonical_forms` |
| Preservation of Types under Substitution | – | (our dynamics uses frames rather than term substitution; the type-level instantiation `Term.inst` has no typing lemma) |
| Well-Formed References Evaluate to Well-Typed Values | done | `RefTy.read` |
| Place Expressions Reduce | done | `PlaceTy.eval` |
| Reduced Place Expressions Produce Valid Referents | – | |
| Reduced Place Expressions Have Roots in Loan Sets | – | |

### Preservation under region rewriting (8 lemmas)
| Lemma | Status | Lean |
| --- | --- | --- |
| Type Computation is Preserved under Region Rewriting | done | `PlaceTy.rewrite` (also `RefTy.rewrite`) |
| Ownership Safety / Outlives / Region Rewriting preserved under Region Rewriting | – | |
| Region Rewriting is Preserved by Garbage Collecting Loans | – | |
| Closure Body Typing / Value Typing / Stack Well-Formedness preserved under Region Rewriting | – | |

### Drops and garbage collection ("related environments", 13 lemmas)
| Lemma | Status | Lean |
| --- | --- | --- |
| Values Change Environments in Limited Ways | done | `HasType.val_refines` |
| Value Typing Fixed on Output Environments | done | `HasType.val_output` |
| Type Computation is Preserved in Related Environments | partial | `PlaceTy.refine`, `PlaceTy.loanOnly`, `PlaceTy.outlives`, `PlaceTy.gcLoans` |
| Referent Well Formedness Preserved in Related Environments | partial | `RefTy.refine`, `RefTy.loanOnly`, `RefTy.gcLoans` |
| Ownership Safety, Types Well Formed, Related Envs Remain Well-Formed, Related Input/Output, Outlives Preserves Related Envs, Related Envs Preserved by Rewriting, Expression Typing, Value Typing, Stack Validity in Related Environments | – | |

### Popping a frame
| Lemma | Status | Lean |
| --- | --- | --- |
| Stack Validity is Preserved When Popping A Stack Frame | done | `StoreValid.pop` |

### Well-typed extensions (7 lemmas)
| Lemma | Status | Lean |
| --- | --- | --- |
| Type Computation is Preserved under Well-Typed Extensions | done | `PlaceTy.push_var`, `PlaceTy.push_rgn` (also `RefTy.push_*`) |
| Ownership Safety, Outlives, Region Rewriting, Closure Bodies, Values, Stack Validity under Well-Typed Extensions | – | |

### Everything after that – not formalized
* Preservation after Assignment (6 lemmas)
* Values are Well-Typed at Rewritten Types
* Function Definitions are Self-Contained
* Subset-Related Environments (6 lemmas)
* Preservation in More Precise Environments (5 lemmas)
* Preservation under Safe Loan Updates (10 lemmas, incl. "Ownership Safety Produces Non Conflicting Loans")
* Rewriting under Parallel Type Checking and Smaller Continuation Contexts (4 lemmas)

Most of these are steps inside the preservation proof, which fails for the
paper's rules. Several of them do not mention the dynamics at all (ownership
safety under rewriting / extension / loan updates, outlives and rewriting lemmas,
subset-related environments, more precise environments). Those may well be true
for the rules as they stand and could be formalized on their own, and they would
also be needed for any repaired system.

## 3. Language features not modelled

* `E-Closure` overwriting non-copyable captures with `dead` at runtime (not
  computable from runtime values; see `README.md`).
* `E-Function` and function values `⟨•, fn …⟩` (function names are values).
* Struct / enum / pattern extensions and the stand-alone `T-GarbageCollectLoans`
  rule (they are only in the macro files, not in the paper's figures).
* The "Tested Semantics" part of the paper (testing against `rustc`).

## 4. Not in the paper, but missing infrastructure

* No executable type checker or interpreter: typing and stepping are only
  relations, so `[OXIDE| … ]` programs cannot be run or type-checked by `#eval`.
* No metatheory of the de Bruijn operations (`Term.rename`, `Term.openRgns`,
  `Term.inst`): no weakening, renaming or instantiation lemmas for typing.
