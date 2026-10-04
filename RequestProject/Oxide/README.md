# Oxide: The Essence of Rust — Lean 4 formalization

This directory formalizes the language Oxide (Weiss, Gierczak, Patterson, Ahmed,
*Oxide: The Essence of Rust*) following the paper's appendix sources
(`formalization.tex`, `full-lang.tex`, `proofs.tex`, `progress_proof.tex`,
`preservation_proof.tex`, and the `oxide/*.sty` macro files containing the rules).

## Files

The Lean files are grouped into folders following the sections of the paper
(§3 "Oxide, Formally" and appendices A–E).  `READING_GUIDE.md` in this directory
gives the full file-by-file map and a suggested reading order;
`RequestProject/Oxide.lean` imports everything.

| Folder | Paper section |
| --- | --- |
| `Syntax/` | §3.1 Syntax, §3.2 Types, §3.3 Environments (appendix A) |
| `Metafunctions/` | appendix C Metafunctions |
| `AliasManagement/` | §3.4 Region-Based Alias Management (appendix B.3) |
| `Typechecking/` | §3.5 Typechecking Oxide Programs (appendix B) |
| `OperationalSemantics/` | §3.6 Operational Semantics (appendix D) |
| `Metatheory/` | §3.7 Well-typed Oxide programs won't go wrong! (appendix E) |
| `ConcreteSyntax/` | not in the paper: the `[OXIDE| … ]` syntax and examples |

## Results

* `canonical_forms` — proved.
* `progress : Progress G` — proved for every global environment `G`
  (Lemma "Progress").
* `not_preservation : ¬ Preservation G` — proved for every `G`.  The paper's
  Preservation lemma quantifies over all well-typed runtime configurations.
  `T-Framed` types the body of `framed e` in the stack typing whose top frame is
  the one `E-Framed` pops, and nothing stops the resulting value from pointing
  into that frame.  With `Γ = [[r ↦ {shrd x}, x : u32]]` and `σ = [[r, x ↦ 5]]`,
  the configuration `(σ; framed (ptr x))` has type `&r shrd u32` and output
  stack typing `•`. It steps to `(•; ptr x)`, and `ptr x` only has dead types in
  the empty stack typing. Dead types never rewrite into reference types, so no
  stack typing and type satisfy the conclusion of Preservation.
* `not_type_safety : ¬ TypeSafety G` — proved for every `G`.  The program
  `let x : bool = true; x; if x { () } else { () }` is well typed (`ts_typed`).
  `E-Move` and `E-Copy` both apply to the place `x` (as in the paper's rules,
  `E-Move` has no copyability side condition), so the first use of `x` may move
  it.  The second use then copies `dead`, and `if dead { … } else { … }` is stuck
  (`ts_steps`, `ts_stuck`).
* `not_type_safety_closure : ¬ TypeSafety G` — proved for every `G`, without using
  `E-Move`.  In
  `` letrgn<`r> { let x : bool = true; let p : &`r shrd bool = (|| -> &`r shrd bool { &`r shrd x })(); if *p { () } else { () } } ``
  the closure body borrows its own copy of `x` into the outer region `` `r ``
  (allowed by `T-Closure`, `T-Borrow` and `T-AppClosure`).  The pointer designates
  a slot of the closure's frame by its level; after `E-Framed` pops that frame and
  `p` is pushed, the pointer designates `p` itself, so `*p` reads a pointer and the
  `if` is stuck.  With the paper's named variables the pointer `ptr x` would
  instead designate the outer `x` after the pop, so this failure comes from
  representing referents by de Bruijn levels.
* `not_preservationReach` and `not_reachableTyped` — proved.  Restricting
  Preservation to configurations reachable from a well-typed closed program run on
  the empty stack (`PreservationReach`) does not repair it: such a lemma implies
  that every reachable configuration is well typed (`reachableTyped_of_preservationReach`),
  which implies type safety (`type_safety_of_reachableTyped`), which is false.
  The move counterexample contains no `framed`, so no extra condition on
  `T-Framed` alone can repair preservation either.
* `type_safety` — commented out (its statement is refuted) and replaced by
  `type_safety_false`.  `type_safety_of_progress_preservation` formalizes the
  paper's derivation, but its preservation hypothesis is refuted.

Repairing type safety requires dealing with both counterexamples, for example by
(i) making the choice between `E-Move` and `E-Copy` type-directed (say, a
move/copy annotation on place uses, filled in by the type checker), and (ii) adding
a no-escape condition for frames that are popped (`T-Framed`, the closure body in
`T-Closure`/`T-ClosureValue`): neither the result type nor the loans left in the
remaining stack typing may refer to the popped frame.  These changes are not made
here; whether they suffice is not established, and no corrected preservation or
type safety theorem is proved.

## Representation choices and deviations from the paper

* **De Bruijn indices everywhere.** Term variables are de Bruijn indices relative
  to the top stack frame. Referents and loans use absolute de Bruijn *levels*.
  Type-level binders (frame variables, abstract regions, type variables) are
  nameless. Concrete regions are bound by `letrgn` (and by closures). They are
  opened with the level of their stack-typing entry, in locally nameless style.
  Only global function names are strings.
* **Function names are values** (`Value.fn f`).  `E-Function` and the function
  value `⟨•, fn …⟩` it produces are not modelled: `E-AppFunction` looks the name up
  in `Σ` directly.  The paper's main dynamics figure (`full-lang.tex`) does not use
  `E-Function` either.
* **Values are a separate syntactic class** embedded with `Term.val`. Tuples,
  arrays and injections whose components are values take one administrative step
  to become values (`Step.tupleVal`, …).
* **Regions at runtime**: `letrgn` pushes a region marker on the stack (and a
  region entry on the stack typing). The runtime form `shiftRgn` (`shiftprov`)
  pops it once the body is a value.
* **`E-Closure` copies the captured values** into the closure's frame. The paper
  also overwrites the captured variables in `free-nc-vars_σ(e)`, "the variables
  bound to values that are non-copyable", with `dead`.  Non-copyability is a
  property of types, and runtime values do not determine it (a pointer value does
  not record whether it is a shared or unique reference), so this metafunction
  cannot be computed from the stack; as with `E-Move`, marking variables dead
  without type information would make well-typed programs get stuck. `T-Closure` still marks them
  dead statically. The concrete regions captured by a closure are the regions of
  the body that do not occur in the signature (computed syntactically).
* **Slices use half-open bounds** `[n₁, n₂)`. `T-BorrowSlice` allows slicing
  arrays as well as slices.
* **Referent typing** (`WF-RefIndexSlice`, `WF-RefSliceSlice`) adds the bound check
  against the designated slice. The paper omits it, but the lemma "well-formed
  references evaluate to well-typed values" needs it.
* **Outlives bounds** of a polymorphic function `ϱ₁ : ϱ₂` are checked as
  `δ(ϱ₁) :> δ(ϱ₂)` at the call site.
* **Sorts of metavariables** (`τ^SI`, `τ^XI`, …) are explicit premises using the
  predicates `Ty.SI`, `Ty.XI`, `Ty.SD`, `Ty.SX`.
* **Judgments as single inductive families**: the typing judgments (expressions,
  argument lists, values, lists of values), the outlives judgments and the
  rewriting judgments are each one inductive family indexed by the form of the
  judgment. This lets Lean's `induction` work on them. The paper's individual
  judgments are recovered as abbreviations.
* **Progress is generalized** to stack typings that refine the one satisfied by
  the stack (`Refines`). Refinement only replaces components by dead types,
  because `T-Drop`/`T-Move` change the stack typing without changing the stack.
  The type environment plays no role in the proof, so progress holds in any `Δ`.

## Concrete syntax

```lean
example : [OXIDE| let x : u32 = 5; x ] =
    Term.letE Ty.u32 (.val (Value.num 5)) (.place ⟨0, []⟩) := rfl
```

Regions are written as Lean name literals (`` `a `` for `'a`), because Lean lexes
`'a` as a character literal. Frame variables and frame arguments are written
with `@` (`@φ`, `` @{x : u32, `r ↦ {}} ``). See `ConcreteSyntax/Notation.lean` for the full
grammar (including polymorphic function types
`` fn<@φ, `a; T>(τ̄)[Φ] -> τ where `a : `b ``, 1-tuples `(e,)`, dead types `τ†`
and the runtime forms `framed!`, `shift!`, `shiftprov!`, `ptr!`, `dead!`, `val!`,
`closure!`) and `ConcreteSyntax/Examples.lean` for examples.
