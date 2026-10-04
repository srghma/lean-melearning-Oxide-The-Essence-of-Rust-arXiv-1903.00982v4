# Summary of changes for run ca2d47cd-9bd0-4213-ae67-cdfb495a73f6
I wrote the proposal in `RequestProject/Oxide/Proposal/PROPOSAL.md`, together with a small prototype of the design in the same folder. The prototype builds with no `sorry`, and the existing development doesn't use it yet, so nothing else changed. Short answers to your questions:

- **Should `Term` be parametrized by more than `Nat`?** Yes. Today `Term n` only makes the current frame's variables well scoped. Regions, type variables, frame variables, function-type bounds and stack levels are plain `Nat`s, closure arity needs a `params.length = k` side condition, `framed m` is unrelated to the stack, and so on (§1 lists them all, with the typing premises that currently check them). The proposal indexes `Term` by a *scope* `Γ : List Bnd`: the kinds of every binder in scope, most recent first. The kinds are frame variables, abstract regions, type variables, term variables, concrete regions and frame boundaries.
  - Variables are de Bruijn indices that also record what kind of binder they point to (`In b Γ`), so they can't be out of range or point at the wrong kind.
  - Term variables (`TVar Γ`) can't cross a frame boundary, but regions, loans and pointers can.
  - `Term n` is the special case where every binder is a variable, and a closed program is `Term []`.
  - A record of counts would be simpler arithmetic, but it can't say which frame a variable lives in, which `framed`, loans and closures need (alternatives compared in §4).
- **Should `Ty` be parametrized too?** Yes, by the same scope. Types mention regions bound by `letrgn`, type-level binders, and (in closure types) loans that name stack places. With regions as scoped indices, the `bound`/`conc` distinction and "opening" with stack levels go away. I also propose splitting `Ty` by the paper's sorts into separate types: sized (`Ty`), maybe-unsized (`XTy`) and maybe-dead (`MTy`). That replaces about 40 sort premises in the typing rules.
- **Should `Term` have contexts? Which?** Only the scope, i.e. the context with the types erased. I argue against making terms carry the full typing context (intrinsically typed terms):
  - typing is flow-sensitive (`Γ ⇒ Γ'`) and not syntax-directed (`T-Drop`);
  - its side conditions are statements about `Γ`;
  - the evaluation step would have to preserve types by construction, and the project already proves Preservation false for these rules.

  Instead, the stack typing (which absorbs `Δ`) and the runtime stack are indexed by the same scope, so lookups always succeed instead of returning `Option`. Pushing a binder weakens everything stored; popping one *strengthens* and can fail. Function names stay strings (§4.3).
- **A design question I haven't checked:** `T-LetRegion` checks the popped region only against the result type, not against the output stack typing. With a scoped stack typing, popping the region forces that check. Whether today's rules guarantee it is unknown (§3.3).

**One consequence for the counterexamples (§3.3).** With scoped syntax, the configuration behind `not_preservation` (`framed (ptr x)` with `x` in the popped frame) can no longer produce a dangling pointer: popping the frame just fails. `framedPop_dangling` in `Contexts.lean` checks this by `rfl`, and `framedPop_ok` checks that a value not mentioning the frame pops fine. The level reuse behind the closure counterexample can't be represented at all. The underlying problem doesn't disappear, though: it moves from Preservation to Progress, and the `T-Framed` repair is still needed. The move/copy counterexample is unaffected.

**Prototype files:**
- `Scopes.lean`: scopes, variables, renamings, weakening.
- `Types.lean`: the scoped types.
- `Terms.lean`: `Term`, `Value` and closure environments, renaming, function definitions.
- `Strengthening.lean`: renamings that can fail, for all syntax.
- `Contexts.lean`: stacks and stack typings with lookups that always succeed, push/pop, an example closed program and the two theorems above.

**Also in the proposal:**
- costs and risks: weakening on every push, scope-equality casts, no automatic `DecidableEq`, porting about 1,400 lines of progress proof;
- smaller improvements that are worth doing on their own;
- a five-step migration plan.

**Open choices for you (§6):**
- keep `framed`/`shift` inside terms, as the paper does, or move to a continuation-based machine;
- `Fin k → _` fields or length-indexed lists;
- whether to split the type sorts in the first step;
- whether to replace the current development or build alongside it.

I added a pointer to the folder in `RequestProject/Oxide/README.md`. The Properties table now lists the proposed `Term` and `Ty` and `framedPop_dangling` (proved).

# Summary of changes for run eeafb7c4-08f5-4397-85a4-411ef4cf8209
I rebuilt the project and checked it against the paper's appendix lemmas (`proofs.tex`). `lake build` succeeds. The only `sorry`s are inside the two commented-out statements in `Metatheory/Safety.lean`, and both of those statements are proved false. I wrote the full lemma-by-lemma checklist to the new file `RequestProject/Oxide/MISSING.md` and changed no Lean code. Here is what is missing:

**1. A corrected type system with a type safety proof.** Progress is proved. The paper's Preservation and Type Safety, as stated, are both proved false, and so is the "reachable configurations only" version of Preservation. So no theorem is left to prove for the current rules. Getting a true type-safety result means changing the rules first:
- choose between `E-Move` and `E-Copy` based on the type;
- forbid values from escaping a frame when it is popped (`T-Framed`, closure bodies);
- for the closure counterexample, which only happens because pointers use de Bruijn levels, change how pointers are represented or rely on that no-escape rule.

None of these changes are made, and it isn't known whether they would be enough.

**2. Most of the paper's 67 supporting lemmas.**
- **Fully formalized (8):**
  - canonical forms;
  - well-formed references evaluate to well-typed values (`RefTy.read`);
  - place expressions reduce (`PlaceTy.eval`);
  - type computation is preserved under region rewriting and under well-typed extensions;
  - values change environments in limited ways;
  - value typing is fixed on output environments;
  - stack validity is preserved when a frame is popped.
- **Partly formalized (2):** type computation and referent well-formedness in "related environments".
- **Not formalized (about 57):**
  - substitution;
  - the two "reduced place expressions" lemmas;
  - every ownership-safety lemma;
  - the remaining lemmas in the region-rewriting, drop/garbage-collection and well-typed-extension groups;
  - every lemma in the assignment, subset-related, more-precise-environment, safe-loan-update and parallel-type-checking groups.

  Most of these are steps of the preservation proof, which fails. Several of them never mention evaluation, so they may still hold for the current rules and could be proved on their own. Any corrected system would need them too.

**3. Language features not modelled:**
- `E-Closure` marking moved captures dead at runtime;
- `E-Function` and function values;
- the struct/enum/pattern extensions and the stand-alone `T-GarbageCollectLoans` rule, which appear only in the macro files, not in the paper's figures;
- the paper's tests against `rustc`.

**4. Infrastructure the paper doesn't need, but you might want:**
- **No type checker or interpreter you can run.** Typing and evaluation are only defined as relations, so a `[OXIDE| … ]` program can't be type-checked or executed with `#eval`.
- **No lemmas about the de Bruijn operations.** There are no weakening, renaming or instantiation lemmas for `Term.rename`, `Term.openRgns` or `Term.inst`.

The type-safety repair in point 1 is the main open item. The evaluation-free lemmas in point 2, or a type checker and interpreter you can run, could be worked on independently of it.

# Summary of changes for run 4b7eecde-0e36-46c1-ae8c-309db88208b5
I regrouped the Lean files into folders under `RequestProject/Oxide/` that follow the paper's sections, and wrote a reading guide, `RequestProject/Oxide/READING_GUIDE.md`. The move changed no definitions or proofs, only where the code lives, the module docstrings and the import lines. `lake build` succeeds, and the only `sorry`s are the two old statements that were already commented out in `Metatheory/Safety.lean`.

**New layout** (§ numbers refer to section 3, "Oxide, Formally", and the letters to the appendices):
- **`Syntax/`** (§3.1–3.3, appendix A): the old `Syntax.lean`, split into:
  - `Places.lean`: places and annotations;
  - `Types.lean`: §3.2;
  - `Environments.lean`: §3.3;
  - `Terms.lean`: terms, values and global functions; `Term n` with `Term 0` closed;
  - `Runtime.lean`: stacks.
- **`Metafunctions/`** (appendix C): the old `Meta.lean`, split into `Types`, `Places`, `StackTypings`, `Stacks` and `Terms`.
- **`AliasManagement/OwnershipSafety.lean`** (§3.4): place typing and ownership safety.
- **`Typechecking/`** (§3.5, appendix B): the old `Statics.lean`, split into `RegionRewriting`, `Typing` and `Validity`.
- **`OperationalSemantics/Dynamics.lean`** (§3.6, appendix D).
- **`Metatheory/`** (§3.7, appendix E):
  - `Statements.lean`: the old `Metatheory.lean`;
  - `Progress/*`;
  - `SupportingLemmas.lean`: the old `Support.lean`;
  - `Counterexamples/{Preservation, TypeSafety, Closure, Reachability}.lean`;
  - `Safety.lean`.
- **`ConcreteSyntax/`** (not part of the paper): `Notation.lean` (the `[OXIDE| … ]` syntax) and `Examples.lean`.
- **`RequestProject/Oxide.lean`**: a new file that imports everything, in reading order.

The new folders follow §3, but definitions still have to come in dependency order, which sometimes differs from the paper's. Types (§3.2) are defined before terms (§3.1), and the metafunctions (appendix C) before the type system. The guide explains each of these places.

**`READING_GUIDE.md` contains:**
- the three naming conventions to know first (de Bruijn indices for variables, de Bruijn levels for pointers and loans, nameless type-level binders);
- a table mapping each paper section, subsection and figure to its Lean file and main declarations;
- notes on where Lean's order differs from the paper's, and how to find a rule by its name (e.g. `T-Borrow`);
- a suggested order in three passes: the language, then the type system, then the metatheory;
- an import diagram between the folders;
- a status table:

| Result | Status |
| --- | --- |
| Canonical forms, progress | proved |
| Preservation as stated in the paper | refuted |
| Type safety as stated in the paper | refuted |
| Preservation restricted to reachable configurations | refuted |

I also updated the file references in `RequestProject/Oxide/README.md` (its file table now points to the guide), in `GAPS_AND_GRAMMAR_DIFFERENCES.md`, in the docstrings, and in the Properties table.

# Summary of changes for run 1e49d504-aa9c-411e-84a1-d92b8a4f8525
The paper's Type Safety theorem, as formalized here, is false, and I proved that in Lean. The repair you suggested (Preservation restricted to configurations reachable from a closed program on the empty stack) is false too. So there is no correct type-safety or corrected-preservation theorem to finish for these rules. I proved neither; a repaired system would need changes to the rules themselves. `lake build` succeeds, the project has no `sorry` left outside comments, and the new results use only the standard axioms.

**Type safety**
- **`not_type_safety`** (`TypeSafetyCounterexample.lean`): the program `let x : bool = true; x; if x { () } else { () }` is well typed. The paper's `E-Move` rule has no condition that the place's type be non-copyable, so the first use of `x` may move it. The second use then reads `dead`, and the `if` is stuck. This holds for every global environment, including the well-formed `[]`.
- **`not_type_safety_closure`** (`ClosureCounterexample.lean`): a second, independent failure that uses no moves. In ``letrgn<`r> { let x : bool = true; let p : &`r shrd bool = (|| -> &`r shrd bool { &`r shrd x })(); if *p { () } else { () } }``, the closure borrows its own copy of `x` into `` `r `` and returns the pointer. Because pointers name their target by de Bruijn level, after the closure's frame is popped and `p` is pushed, the pointer points at `p` itself, and the `if` is stuck. With the paper's named variables the pointer would point at the outer `x` instead, so this failure comes from our level-based representation, not from the paper.
- The old `type_safety` statement is commented out with an explanation in `Safety.lean` and replaced by `type_safety_false`.

**Corrected preservation**
- **`not_preservationReach`** (`Reachability.lean`) refutes the reachability-restricted lemma. Applied step by step, it would make every reachable configuration well typed (`reachableTyped_of_preservationReach`), which with `progress` gives type safety (`type_safety_of_reachableTyped`).
- Your other option, an extra condition on `T-Framed`, can't be enough alone: the move counterexample involves no `framed` at all.
- `README.md` sketches what a repair would have to address: a type-directed choice between move and copy, and a rule that nothing escapes a popped frame. I haven't made these changes, and it's not established that they would be enough.

**Supporting lemmas** (`Support.lean`), all proved:
- stack validity is preserved when a frame is popped;
- value typing is fixed on the output environment, and values change environments only in limited ways;
- place typing and referent well-formedness are preserved under region rewriting, outlives and garbage collection of loans, since all three only change loan sets;
- the same holds when a variable or region is pushed on the top frame (well-typed extension).

The lemmas about ownership safety, value typing and stack validity under rewriting, extension and assignment are not formalized. They are steps inside the preservation proof, which fails here.

**`[OXIDE| … ]` syntax**: all the listed gaps are filled, and each example in `Examples.lean` is checked by `rfl`.
- Calls take frame arguments: `` f::<@φ, @{x : u32, `r ↦ {}}, `a; τ>(…) ``.
- Function types have quantifiers, a captured environment and `where` bounds: `` fn<@φ, `a, `b; T>(τ̄)[@φ] -> τ where `a : `b ``.
- `[OXIDE_FN| … ]` binds frame variables.
- There are 1-tuples `(e,)` / `(τ,)` and dead types `τ†`.
- Runtime forms: `framed!`, `shift!`, `shiftprov!`, `ptr!`, `dead!`, `val!` and closure values `closure!`.
- Regions inside a written frame always get empty loan sets, because loans refer to absolute stack positions.

**Left unmodelled, with reasons in `README.md` and `GAPS_AND_GRAMMAR_DIFFERENCES.md`**
- **`E-Closure` marking moved captures dead:** the paper decides which captures to kill by whether their runtime values are "non-copyable". That is a property of types, and a runtime pointer doesn't record whether it is shared or unique. Killing captures without type information would also make well-typed programs get stuck, just like `E-Move`.
- **`E-Function`:** function names stay values. The paper's main dynamics figure doesn't use `E-Function` either.
- **Struct/enum extensions:** they aren't part of the language the paper presents.

The Properties table now marks type safety and the reachability-restricted preservation as refuted. It adds the closure counterexample and three of the supporting lemmas (proved), and its descriptions of the notation and step relation are updated.

# Summary of changes for run 14aa446f-ee36-4df3-b77e-aef801863d7b
The formalization is unfinished in two ways. Type safety is still unproved: `type_safety` in `RequestProject/Oxide/Safety.lean` is the one remaining `sorry`, and `lake build` succeeds otherwise. Most of the paper's supporting lemmas are also missing. On grammar: ours does differ from the paper's, and most of the differences come from de Bruijn indexing or from keeping values separate. Two of them change meaning: slice bounds, and injections being values. I compared the Lean code with the paper's own grammars (`essence-full.tex`, `full-lang.tex`, `oxide/*.sty`) and wrote the full side-by-side comparison to `RequestProject/Oxide/GAPS_AND_GRAMMAR_DIFFERENCES.md`. I didn't change any Lean code.

**What's missing**
- **Type safety.** The paper derives it from Preservation, but Preservation as stated is false, and the project proves that.
- **A corrected preservation lemma.** I haven't stated one. It would need an extra assumption so that a value computed inside `framed e` can't point into the frame being popped. Either "reachable from a closed program run on the empty stack" or an extra condition on `T-Framed` would do.
- **Supporting lemmas from `proofs.tex`.** These cover referents, region rewriting, drops and garbage collection, frame popping, well-typed extension and assignment. They are mostly not formalized; only what progress needs exists.
- **`E-Closure` marking moved captures dead at runtime.** Not modelled; our semantics copies the captured values instead.
- **Function values.** `E-Function` and the function value it produces aren't modelled: a function name `f` is already a value. The paper's main dynamics figure doesn't use `E-Function` either.
- **Gaps in `[OXIDE| … ]`:**
  - calls can't pass frame arguments `Φ̄`;
  - function types have no quantifiers, captured environment or `where` bounds;
  - `[OXIDE_FN| … ]` can't bind frame variables;
  - there's no syntax for 1-tuples, dead types or runtime forms.
- **Not part of the presented language, and not formalized:** the struct/enum/pattern extensions and the stand-alone `T-GarbageCollectLoans` rule. Both appear only in the macro files, not in the paper's figures.

**Grammar differences**
- **Naming:**
  - Variables are de Bruijn indices: `Term n`, with `Term 0` closed.
  - `letrgn` binds its region namelessly. Regions have a third form, `bound i`, besides abstract regions and opened concrete regions `conc ℓ`.
  - Type, region and frame variables are indices. The type environment `Δ` is just three counts plus a list of outlives pairs.
  - Loans, places and referents are rooted at absolute levels rather than names.
- **Values:**
  - `Value` is a separate type embedded with `Term.val`; constants and function names are written as values.
  - Unlike the paper's value grammar, ours includes `inl`/`inr` values. The paper leaves them out, but its `match` reduction rules need them.
  - Tuples, arrays and injections whose parts are values take one extra step to become values.
- **Types:** there is one `Ty` type, and the paper's separate sorts (sized, maybe-unsized, dead, maybe-dead) are predicates on it. So the syntax allows ill-sorted types, which the typing rules reject. The same applies to `let`, closure parameters and `Left`/`Right` annotations.
- **Borrows:** `&r ω p` accepts any region syntactically; typing only accepts concrete ones.
- **Extra counts in terms:** closures store their parameter count `k`, and `framed` stores the size of its frame.
- **Runtime stack:** frames contain region markers that the paper doesn't have. `letrgn e` steps immediately to `shiftRgn e'`, whereas the paper reduces inside `letrgn` and then applies `letrgn<r>{v} → v`.
- **Slices:** the paper's `[n₁..n₂]` is inclusive; ours is half-open `[n₁, n₂)`, including in the `[OXIDE|…]` syntax. So `p[1..3]` denotes two elements in ours and three in the paper. Referent typing also adds a bound check, and slice borrows also accept arrays.
- **Evaluation contexts:**
  - `essence-full.tex` lists `while e₁ { e₂ }` as a context, but it has no hole, which looks like a typo in the paper. We have no `while` context; the loop just unfolds.
  - `essence-full.tex` leaves out the `for` and array contexts. The appendix grammar (`full-lang.tex`) includes both, and so do we.

# Summary of changes for run de5688d6-85ba-4697-8bd9-7de554dc8b55
I formalized Oxide in Lean 4 and Mathlib, under `RequestProject/Oxide/`. Progress and canonical forms are proved. The paper's Preservation lemma, as stated, turned out to be false, and I proved that it is false. Type safety is still open: it is the one remaining `sorry`, in `Safety.lean`.

**Language definitions** (you asked for de Bruijn everywhere and `Term : Nat → Type`):
- **Syntax:** `Term n` is the type of expressions with at most `n` free variables, so `Term 0` is the type of closed programs. Variables, `letrgn` regions and type-level binders are all nameless; only global function names are strings.
- **Typing, ownership safety, outlives and rewriting, well-formedness:** all formalized, with stack validity in `StoreValid`.
- **Small-step semantics:** formalized with evaluation contexts.
- **`[OXIDE| … ]` syntax:** produces a `Term 0`. There are also `[OXIDE_TY| … ]` for types and `[OXIDE_FN| fn f<…>(…) -> τ where … { … } ]` for functions. Regions are written `` `a `` because Lean reads `'a` as a character literal. The examples in `Examples.lean` are each checked by `rfl` against the term they denote.

**Results** (all build; the proofs use only the standard axioms):
- **`canonical_forms`:** proved.
- **`progress`:** proved for every global environment, with no well-formedness assumption. The proof is in `Progress/*.lean`.
- **`not_preservation`:** a proof that the paper's Preservation statement is false, for every global environment including the well-formed `[]`. Take the stack typing `[[r ↦ {shrd x}, x : u32]]` and the stack `[[r, x ↦ 5]]`. By `T-Framed`, `framed (ptr x)` has type `&r shrd u32`. `E-Framed` then pops the frame holding `x`, leaving `ptr x` pointing at nothing in the empty stack. That value can only be given dead types, and dead types never rewrite into reference types. A closed program run from the empty stack can't reach this configuration, so it doesn't refute type safety itself. I commented out the old `preservation` statement and left a note explaining why.
- **`type_safety`:** still `sorry`. The paper proves it from progress and preservation, so a proof would need a preservation lemma restricted to reachable configurations. I did not attempt that.

**Deviations from the paper** are listed in `RequestProject/Oxide/README.md`. The main ones:
- values are a separate class, and tuples, arrays and injections of values take one extra step to become values;
- `E-Closure` copies the captured values instead of also marking them dead at runtime;
- slices use half-open bounds;
- referent typing adds a slice bound check;
- the judgments are written as single inductive families so Lean's induction works on them.

The Properties table lists the main definitions plus canonical forms and progress (proved), preservation (refuted) and type safety (in progress).