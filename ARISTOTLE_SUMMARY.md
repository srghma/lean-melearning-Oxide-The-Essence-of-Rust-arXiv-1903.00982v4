# Summary of changes for run a86fc9a5-f7b8-4dcc-a8e2-6e5d770abad2
The Oxide grammar is now in A-normal form. `lake build` succeeds with no `sorry` and no new axioms. The theorems listed below use only `propext`, `Classical.choice` and `Quot.sound`.

**The grammar** (`Syntax/Terms.lean`) has three mutually inductive levels, all indexed by the signature and the scope. A closed program is still a `Term sig []`.
```
a ::= v | move π | copy p                                        (Atom)
c ::= a | &r ω p | &r ω p[a] | &r ω p[a₁..a₂] | p[a] | p := a
    | closure | a::<…>(ā) | (ā) | [ā] | Left(a) | Right(a) | abort!
    | letrgn<r> { e } | if a { e } else { e } | for x in a { e }
    | while e { e } | match a { … }                               (Comp)
e ::= let x : τ = c; e | c; e | c                                (Term)
```
- Every operand is an atom, and every intermediate result is named by a `let`.
- The right-hand side of a `let` is a computation, never another `let` or a sequence.
- **Design choice:** `if`, `match`, `for`, `while` and `letrgn` count as computations, so they can be bound by a `let`. This is the usual relaxed A-normal form for a language with blocks. Strict A-normal form would need join points.
- The condition of `while` is a term, because it is re-evaluated on every iteration.
- `Term.val v` is shorthand for a finished value.

**What changed with it:**
- **Renaming, strengthening, substitution:** written for all three levels.
- **Typing** (`Typechecking/Typing.lean`): the judgment is split into atoms (`HasTypeA`), computations (`HasTypeC`) and terms (`HasType`). The rules are the paper's, with each operand premise now about an atom. The drop rule applies before any computation.
- **Machine** (`OperationalSemantics/Machine.lean`): the atoms of a computation are evaluated left to right in one step (`EvalAtom`, `EvalAtoms`), so each computation reduces in one step. The only continuation frames left are `let`, `seq`, `while` and the three pops. The frames for half-evaluated arguments, tuples and arrays are gone. `Continuations.lean` follows suit.
- **Concrete syntax** (`ConcreteSyntax/Notation.lean`): `[OXIDE| … ]` accepts only programs in A-normal form. A non-atomic operand, or a `let` in operand position, is rejected with a message asking you to bind it with `let` first. It can't convert programs automatically, because every `let` needs a type annotation.

**Updated and re-checked:**
- All examples in `ConcreteSyntax/Examples.lean`, rewritten in A-normal form. There is a new machine run where `(x, 1)` is built in a single step, and a check that a nested tuple operand is rejected.
- The three regression files:
  - move/copy: the program was already in A-normal form; `ts_typed` and `ts_runs` are proved, plus a new `EvalAtom.copy_inv`.
  - closure scopes: `tp_prog_untyped` and `tp_stuck_untyped` are proved.
  - duplicate captures: the closure is now bound by a `let` before the call (`let f = || …; f()`); `dcBody_typed`, `dc_closure_untyped`, `dc_fn_not_wf` and `dcG_not_wf` are proved.
- `canonical_forms` and `type_safety_of_progress_preservation` still hold. The value inversion lemma `HasType.val_inv` is proved.
- `README.md`, `READING_GUIDE.md`, `GAPS_AND_GRAMMAR_DIFFERENCES.md`, `MISSING.md` and the file headers describe the new grammar. I updated the Properties table to match.

As before, progress, preservation and type safety are stated but not proved.

# Summary of changes for run 24e9f7c8-78b8-4882-a1ee-fa87b9fb325c
You were right: duplicate captures let two unique references alias. I built a concrete counterexample in Lean, then fixed the typing rule. `lake build` succeeds with no `sorry` and no new axioms; the key theorems use only `propext`, `Classical.choice` and `Quot.sound`.

**The counterexample** (`Metatheory/Regressions/DuplicateCaptures.lean`)

The function is `fn dup<ϱ>(y : &ϱ uniq u32) -> () { (|| -> () { body })() }`. Its closure captures `y` twice, as `c₁` and `c₂`, and the body is:
```
letrgn<r₁> { letrgn<r₂> {
  let a : &r₁ uniq u32 = &r₁ uniq *c₁;
  let b : &r₂ uniq u32 = &r₂ uniq *c₂;
  *b := 2; *a := 1; () } }
```
This takes two unique borrows of the same location `*y` that are live at the same time, and writes through `b` while `a` is still used afterwards. Rust's borrow checker rejects this; the old rules accepted it.
- **The body type checks** (`dcBody_typed`), in exactly the stack typing the old `T-Closure` produced (`dcΓ0_eq`).
- **Why it passes:** `y`'s region is abstract, so each dereference is checked through the abstract-region rule. That rule only compares `*c₂` against existing loans. The loan `uniq *c₁` has a different root variable, so it counts as disjoint from `*c₂`.
- **Every other premise of the old rule holds** (`dc_closure_other_premises`). In an earlier commit, before the fix, the whole function was shown to be well formed.
- **At runtime both copies hold `y`'s pointer** (`dc_env_aliases`).

This breaks uniqueness. It does not refute the stated progress, preservation or type-safety theorems, which remain unproved.

**The fix**
- `Cap.Nodup` (in `Syntax/Terms.lean`) says a capture list names each variable and each region at most once. It is decidable.
- `T-Closure` now has the premise `hnodup : c.Nodup`.
- **Regression results, all proved:** the capture list is not duplicate-free (`dcCap_not_nodup`). The closure is ill typed in every stack typing (`dc_closure_untyped`), and so is the function body (`dc_fnBody_untyped`). The function is not well formed (`dc_fn_not_wf`), and neither is a global environment containing it (`dcG_not_wf`).
- The other regression files and examples still build. The `[OXIDE| … ]` syntax already produced duplicate-free captures.

**Why a typing premise and not the selection from item 3:** captures are renamed through arbitrary functions on term variables. These need not be injective or order-preserving, so a duplicate-free selection would not survive renaming. Under the rule from the earlier note, the condition therefore belongs in the typing rules.

**Not checked in Lean:** that the same body with `y` captured once is rejected. Informally, the second borrow then conflicts with the loan `uniq *c`.

I updated `README.md`, `READING_GUIDE.md`, `MISSING.md`, `Proposal/CORRECT_BY_CONSTRUCTION.md` and the comment on `dupCap`, and added the new file to `RequestProject/Oxide.lean`. The Properties table has a new proved entry for this regression, and the typing entry's comment mentions the new premise. The counterexample and the fix are in separate commits.

# Summary of changes for run 81518266-fc34-49a8-9e44-3d4f68bf5700
Much of the grammar is already correct by construction. That covers scopes, top-frame variables, the sorts of types, move vs. copy, places vs. place expressions, closure scopes, typed paths, `MTy` indexed by its declared type, functions by signature, and `Fin k` arities. The rule I'd use for the rest: **put an invariant in the type if it depends only on the syntax and survives renaming and substitution. Leave anything that depends on the stack typing to the typing rules.**

I wrote this up in `RequestProject/Oxide/Proposal/CORRECT_BY_CONSTRUCTION.md`. Lean witnesses and prototypes are in `RequestProject/Oxide/Proposal/CorrectByConstruction.lean`. That file builds with no `sorry` or warnings, `lake build` succeeds, and the grammar the rest of the project uses is unchanged. The changes, most valuable first:

1. **Keep runtime values out of source programs.** `Term.val` accepts any value, so a program can contain `dead`, a raw `ptr` to a local, a slice or a closure value. The witnesses `srcWithPtr` and `srcWithDead` type check today. The machine never substitutes values into terms, so the fix is small:
   - `Term.val` becomes `Term.const`, holding only constants and function names (`SrcVal`).
   - The machine's focus becomes `eval e | ret v`, the usual CEK split.
   - The `for` loop step that puts a pointer back into a term (`.forE (.val (.ptr …)) e₂`) becomes a continuation frame.
2. **Split values by sort, as types already are.** Prototypes `SVal`/`XVal`/`MVal` match `Ty`/`XTy`/`MTy`:
   - slices exist only behind a pointer;
   - `dead` exists only in stack slots;
   - stack slots hold `MVal`, and reading through a pointer returns `XVal`.

   The witness `tupleOfSlice` shows a slice inside a tuple value is writable today.
3. **Captures as an ordered selection of the current frame.** `Cap` can name the same variable twice (`dupCap`, `dupCap_not_nodup`). The typing then gives both copies the variable's type, and `killNC` kills the original once. I suspect this lets two `&uniq` copies alias inside a closure body, but I have not confirmed it with a typing derivation. The prototype `TopSel` only selects current-frame entries, in order. The proved theorem `TopSel.toCap_vars_nodup` shows its captures never name a variable twice.
4. **One encoding per initialization state.** `.init` and "a tuple of `.init`" are different states today (`initPair_ne`). The prototype `MSt` indexes each state by a kind (`init | dead | mixed`), and its tuple constructor must be genuinely mixed. Each type then has exactly one fully initialized state and one dead state (proved as `Subsingleton` instances), and `mkTuple` becomes total.
5. **Make closure coverage decidable.** Replace the semantic `Inst.Covered` with a check that the free binders of each entry are among those of the closure type. A fully syntactic version would break type substitution. I have not proved the check equivalent to `Covered`.
6. **Choose move or copy by type in the concrete syntax.** Add a type-directed elaboration pass, as rustc does when it builds MIR. Then `let x : bool = true; x; if x {…}` no longer needs `copy!(x)`.
7. **Smaller items:**
   - store a single type annotation on injection values;
   - give place-expression contexts a structured type;
   - leave index expressions as they are.

What should stay out of the grammar: array lengths against literal arity, projection indices in terms, ownership and loans. All of them depend on the stack typing, so encoding them would make terms intrinsically typed. I'd start with items 1, 3 and 5, which give the most for the least work. None of the proposals has been carried into the main grammar yet, and the Properties table is unchanged.

## Suggested follow-up

The abstract syntax lets a closure list the same variable twice in its captures (`Cap`). The closure typing then gives both copies that variable's type, even when it is not copyable (for example a `&uniq` reference). I suspect this lets two unique references alias inside the closure body, but I haven't confirmed it in Lean. I can switch captures to the duplicate-free selection described in item 3, or try to build a concrete counterexample first.

# Summary of changes for run 894bf31f-4f74-4547-8380-572560837dc7
I didn't change any files. These answers come from reading the current sources (`Typing.lean`, `Machine.lean`, `Scopes.lean`, `Types.lean`, `TypeSubst.lean`, `Notation.lean`). None of the reasoning below has been checked in Lean, and progress, preservation and type safety are still stated but not proved.

## 1. Should `T-Move` accept copyable types?

**It isn't a soundness bug.** The paper's restriction stopped being a safety condition once move and copy became separate syntax:
- In the paper, one place-use form is typed either way, and the type decides between `T-Move` and `T-Copy`. The runtime rule `E-Move` can't see types, so it may kill a `bool` that the typing treated as copied. That mismatch was the old `not_type_safety` counterexample.
- Now the syntax decides. `Term.move π` sets the place to `.dead τ` in the typing and writes `dead` in `E-Move`, whatever its type. The typing and the stack always agree on what is dead.
- A later use of a moved copyable place is ill typed, because `T-Copy` needs a `PlaceTy`. `T-Move` still requires unique ownership safety, so you can't move a place with outstanding shared loans. This is how `Operand::Move` works in Rust's MIR.

**It does make the system differ from the paper.**
- With the restriction (`τ.copyable = false` added to `T-Move`), the move/copy marking is fully determined by types. A well-typed paper program then has exactly one well-typed marked version, which is the clean "faithful refinement" story.
- With the relaxation, a program can have several marked versions, and some of them reject later uses.

**The real issue is the concrete syntax, and neither choice fixes it.** `[OXIDE| … ]` turns a bare place without a dereference into a `move`, without looking at types:
- As things stand, `let x : bool = true; x; if x {…} else {…}` written with bare `x` is a move, then a use of a dead place. It is ill typed, although the paper accepts it. You have to write `copy!(x)`, as the regression program in `MoveCopy.lean` does.
- With the restriction, even `let x : u32 = 5; x` (the first example in `Examples.lean`) becomes ill typed, because a bare `x` would be a move of a copyable value.

**My recommendation:**
- If the aim is the paper's type system exactly, add the one-line premise to `T-Move`. In that case also make the elaboration choose by type, as rustc does when it builds MIR. A place without a dereference has a declared root type (every `let` and parameter is annotated), so a bare place can become `copy` when its field type is copyable and `move` otherwise.
- If the aim is a MIR-style calculus, keep the current rule and describe it as an intended, harmless extension.

The current rule can't, on its own, make a well-typed program get stuck.

## 2. Is `Inst.Covered` a bug?

**No, I believe it's correct.** It says: for every partial renaming `ρ`, if the closure type `τ` survives strengthening by `ρ`, so do the entries `θ`. I expect this to be equivalent to the syntactic check "every binder that occurs free in `θ` also occurs free in `τ`":
- **Syntactic check implies `Covered`:** strengthening a type succeeds exactly when `ρ` is defined on all of its free binders.
- **`Covered` implies the syntactic check:** if some binder `x` were free in `θ` but not in `τ`, take the renaming that is the identity except that it drops `x`. Then `τ` survives and `θ` doesn't.

The condition itself isn't in the paper. It was added to close the closure-scope hole (a closure body mentioning a region or variable that its type doesn't record).

**Should it change?** That's a choice about presentation and executability, not correctness.
- Since the typing judgment is a relation and there is no type checker, the semantic form causes no inconsistency. It is the form preservation will actually use (strengthening a closure value).
- It is harder to read, and you can't decide it by computation.
- The better form is a free-binder function or relation on `Region`, `Ty`, `XTy`, `FrameExpr`, `FrameTy`, `Loan`, `Entry` and `Inst`, with the coverage premise stated as inclusion. Keep the current definition as a proved equivalent lemma for the metatheory.
- That proof needs lemmas about lifting partial renamings under the binders of `fn` types and frames. I haven't done it. I can add it, and/or the `T-Move` change with type-directed elaboration, if you want either.

# Summary of changes for run 856f2a90-5ca8-45f1-9d94-2418b8a76242
I implemented the main type-safety proposals in the Oxide formalization. `lake build` succeeds (8051 jobs, no warnings). The project has no `sorry`, `axiom` or `@[implemented_by]`, and the key theorems use only `propext`, `Classical.choice` and `Quot.sound`. Progress, preservation and type safety are still stated but not proved for the new rules.

**What changed** (the full table is under "The type-safety refinements" in `RequestProject/Oxide/README.md`):
- **Place expressions grouped by dereferences** (`Syntax/Places.lean`): a place is a root plus a projection path (`APlace`/`TPlace`), and a place expression is `PExpr.place π | PExpr.deref p q`. `base`, `splitDeref`, `IsPlace` and plugging into a context are now plain pattern matches. `Referent` has the same shape (`place | index R i q | slice R start len`).
- **Move vs. copy:** `Term.move (π : TPlace)` and `Term.copy (p : PExpr)`. Because `move` takes a place with no dereference, the old `hplace` premise of `E-Move` is gone. `T-Copy` requires a copyable type, and `E-Move` only applies to `move`.
- **Closures in their own scope:** a closure lists what it captures (`Cap Γ f`) and its outer binders (`θ : Inst o Γ`), and its body is typed in that smaller scope. `T-Closure` and `T-ClosureValue` require the premise `Inst.Covered`. `E-Closure` is now deterministic.
- **Typed paths:** `TyPath τ` (with `Fin k` projections) makes type lookup and update total. `VPath v` makes value read and write total once a path is resolved. Plain `Nat` paths are converted once, by `TyPath.ofList` and `Referent.resolve`.
- **`MTy` indexed by its declared type:** `MTy.Of τ` is `init`, `dead`, or a tuple with one state per field. `mkTuple` turns an all-`init` tuple into `init`, so there is one encoding.
- **Global functions by signature:** terms are `Term sig Γ`, `Value.fn` holds an index `FnIdx sig`, and `GlobalEnv sig` has exactly one body per declared function, so lookup always succeeds. `GlobalWF` checks every body against the signature, and the metatheory statements assume it.
- **Smaller items:**
  - continuations store `Fin i → Value` / `Fin j → Term` for the done and remaining elements;
  - slices are stored as a start and a length;
  - literals are `Prim b` with `UInt32` numbers;
  - call type arguments are one `TArgs` bundle, reused by substitution;
  - `Slots.runtime` proves that stacks only exist over runtime scopes;
  - the placeholder `dead unit` entries for type-level binders are gone.

**Former counterexamples, now regression files** (all proved):
- `Metatheory/Regressions/MoveCopy.lean`: `let x : bool = true; copy x; if copy x {…} else {…}` is well typed (`ts_typed`), a copy step never changes the stack (`Step.copy_inv`), and the program runs to `()` (`ts_runs`, `ts_final`).
- `Metatheory/Regressions/ClosureScopes.lean`: the program with a closure that mentions `r` in its body but not in its type is ill typed (`tp_closure_untyped`, `tp_prog_untyped`). The closure value and the configuration that used to get stuck are ill typed too (`tp_closure_value_untyped`, `tp_stuck_untyped`).

The old refutation theorems (`not_progress`, `not_preservation`, `not_type_safety`, `not_type_safety_scope`) were about the previous rules and have been removed.

**Concrete syntax** (`ConcreteSyntax/Notation.lean`, `Examples.lean`):
- A bare place without a dereference becomes a move, and a place through a dereference becomes a copy. `copy!(p)` and `move!(p)` choose explicitly.
- Global functions must be listed in signature order: `[OXIDE{f, g}| … ]`.
- A closure's captures and outer binders are computed from what its body uses.
- Number literals of \(2^{32}\) or more are rejected.

All examples are checked by `rfl`, including the two regression programs. One machine run is included.

**Where the code departs from the proposals:**
- `T-Move` also accepts copyable types, unlike the paper.
- `Inst.Covered` is a semantic condition (stated via strengthening), not a decidable syntactic check.
- Projection indices in the surface syntax stay `Nat`, as the proposal suggested.
- Writing through a slice referent only changes the elements when the written value is a slice of the same length.

README, READING_GUIDE, MISSING, GAPS_AND_GRAMMAR_DIFFERENCES and the status note in PROPOSAL are updated, and the Properties table matches the final code. All work is committed.

# Summary of changes for run b0f50c89-b356-4d9c-8dfa-fef1d8b651c2
As you asked, I changed no files. Everything below comes from reading the current sources (mainly `Syntax/Places.lean`, `Types.lean`, `Terms.lean`, `Runtime.lean`, `Environments.lean`, and the place helpers in `Metafunctions/Places.lean` and `Metafunctions/Stacks.lean`). None of it has been built or checked in Lean.

## Making `POp` correct by construction

`POp` has only two cases, so the type itself has little room for error. The problems come from how it is used:

1. **Out-of-range projections.** `proj (i : Nat)` can name a field that doesn't exist. Whether `.i` is valid depends on the type of what is being projected. Turning `i` into `Fin k` needs that `k`.
2. **Unstructured lists.** `List POp` mixes dereferences and projections freely. Yet most code wants a structure, "a place, then a dereference, then the rest". As a result:
   - `APlaceExpr.base` and `splitDeref` use `takeWhile`/`dropWhile`/`filterMap`;
   - `IsPlace` is `POp.deref ∉ p.ops`;
   - the machine's `E-Move` carries the premise `hplace : POp.deref ∉ p.ops`.

**Fix for problem 2 (cheap, recommended): structure place expressions by their dereferences.** In the paper, `p` is always a place `π₀` followed by groups of the form "dereference, then projections". Encode exactly that:
```
structure Place (Γ) where root : In .var Γ; path : List Nat        -- today's APlace
inductive PExpr (Γ) | place (π : Place Γ) | deref (p : PExpr Γ) (path : List Nat)
```
The dereference becomes structure rather than an element of a list, so:
- `base` and `splitDeref` become plain pattern matches;
- `IsPlace p` becomes "`p` is `.place π`";
- plugging a place expression into a context becomes structural.

Two further steps follow from it:
- Let `Term.place` (or a separate `move` constructor) take a `Place` where a place is required. Then the `hplace` premise disappears.
- Apply the same reshaping to term-level places (rooted at a current-frame variable) and to `Referent`/`RStep`.

A literal mirror of the paper grammar (`x | *p | p.n`) would also work. The grouped form fits better because every helper splits at a dereference.

**Fix for problem 1: projection paths indexed by a type.** A `Fin` index needs the arity. A term doesn't have it, because a variable's type is not part of the scope:
- it changes as the program runs (moves);
- it can be an opaque type variable;
- dereferencing can land in a slice.

Putting types into the scope would make terms intrinsically typed, which the earlier proposal argued against. Typed paths do fit where the type is already known:
- **Type lookup and update** (`Γ(π)`, `Γ[π ↦ τ]`) can use a `Ty.Path τ`, with a case `proj (i : Fin k) : Path (τs i) → Path (tuple k τs)`.
- **Value read and write** can use a similar path into the value. `readSteps` and `modifySteps` would then always succeed.

Untyped `Nat` paths would be converted once, with a function returning `Option (Path τ)`, inside the typing rule that already checks the place. So the place syntax stays untyped, and the code behind it stops returning `Option` for out-of-range indices.

## Other things that could be made correct by construction or improved

1. **Move vs. copy (fixes a known counterexample).** Mark each use of a place in the term as move or copy, as Rust's MIR does with `Operand::Move`/`Copy`. The typing rule then requires a copyable type for `copy`. This is the type-directed choice behind `not_preservation` and `not_type_safety`, built into the syntax.
2. **Closures and regions (targets the `not_progress` counterexample).** Give `Term.closure` a selection of the binders the body may see: its parameters, what it captures, and the regions in its type. The `Sel` machinery from `Syntax/Scopes.lean` could do this, with the body typed in that smaller scope. Then the body cannot mention a region that is missing from the closure's type, which is exactly how `not_progress` arises.
3. **`MTy` indexed by its declared type.** Use `MTy.Of (τ : Ty Γ)` with cases `init`, `dead`, and a tuple case taking one `MTy.Of (τs i)` per field. Two invariants then hold structurally:
   - a partially moved variable always keeps its declared type;
   - the typed path `Ty.Path τ` from above applies to it directly.

   The duplicate encodings of a fully initialized tuple (`init (tuple …)` and `tuple (init …)`) would also go away: either forbid an all-`init` tuple case or normalize with a smart constructor.
4. **Global functions.** Today `Value.fn (f : String)` can name a function that doesn't exist, `GlobalEnv` is a `List` that may contain duplicate names, and `lookup` returns `Option`. Instead, index terms by a global signature, the list of declared function types. Then:
   - `Value.fn` holds an index into that list;
   - `FnDef` bodies are typed against the signature (mutual recursion still works);
   - lookup always succeeds and names are unique by construction.
5. **Argument and element lists in continuations.** `Cont.appArg`, `Cont.tuple` and `Cont.array` store `done : List (Value S)` and `rest : List (Term S)` with no link to the arity. Use `Fin i → Value` and `Fin j → Term` with `k = i + 1 + j`, or a length-indexed zipper. The machine's arity checks become types.
6. **Slices and indexing.**
   - `RStep.slice i j` needs `i ≤ j`, which is why `spliceFin` takes `hm : m = j - i`. Storing a start and a length instead removes that side condition.
   - Index bounds can only become `Fin n` with the typed value paths from above.
7. **Literals.** `Prim.num (n : Nat)` is typed as `u32` but is unbounded. Use `UInt32` or `Fin (2^32)`, or index `Prim` by `BaseTy` so a literal carries its base type.
8. **Type arguments of calls.** `Term.app` and `Cont.appFn` both pass three separate functions `Φs`, `ρs`, `τs` for the same `Binders`. Bundle them into one structure, essentially a type-level substitution out of `b.ctx`. It can then be reused directly by `Metafunctions/Substitution.lean`.
9. **Runtime scopes.** `Slots` has no case for type variables, abstract regions or frame variables, so a `Stack S` over such a scope is simply empty. That is already correct, but implicit. A separate runtime-scope type (only variables, regions and frames) would state it, and would remove the placeholder `dead unit` entries that `SlotTys.markers` invents.
10. **Cost to keep in mind.** Every `Fin k → _` or type-indexed field takes away derived `DecidableEq` and makes renaming proofs heavier. The cheapest steps with the largest effect are the place-expression reshaping (first fix above) and the move/copy and closure items (1 and 2). Items 1 and 2 also target the two kinds of counterexample in the current development.

# Summary of changes for run b85312ae-ce47-4ab4-be70-87d6663ef10b
I implemented `RequestProject/Oxide/Proposal/PROPOSAL.md` with your choices: a continuation-based machine, `Fin k → _` fields, split type sorts, and replacing the old development. It is now the only grammar, and the old `Nat`-indexed files are gone. `lake build` passes with no `sorry`, and the main theorems use only the standard axioms. The catch: I did not reprove progress. It turns out to be false for the new rules, and Lean now proves that.

**The grammar.** Everything is indexed by a scope `Γ : List Bnd`, the binders in scope, most recent first. A closed program is `Term []`, and `Term (vars n)` is the plain `Term n` case.
- Typed indices: `In b Γ` points at a binder of a given sort; `TVar Γ` points at a variable of the current frame and cannot cross a frame boundary.
- Types are three families: `Ty` (sized, initialized), `XTy` (maybe unsized) and `MTy` (maybe dead).
- Borrows only take concrete regions. Calls carry their binders, and their argument counts match by construction.
- Stack typings (with `Δ` folded in) and stacks use the same scope, so lookups are total.

**Built on top of it:** type-level substitution, the metafunctions, ownership safety, outlives and region rewriting, the typing rules, stack validity, and the machine (`OperationalSemantics/Machine.lean`). The machine has no `framed`/`shift` forms: its continuation records the pops. Continuations get their own typing judgment (`ContOK`, `ConfigTyped`), and progress, preservation and type safety are stated for the machine.

**Concrete syntax.** `[OXIDE| … ]`, `[OXIDE_TY| … ]` and `[OXIDE_FN| … ]` were ported. They turn names into typed indices and reject unbound names, borrows at abstract regions, and variables of another frame. `ConcreteSyntax/Examples.lean` checks the examples by `rfl` and runs `let x : u32 = 5; x` on the machine to a final state.

**Results (all proved):**
- `canonical_forms`, and `type_safety_of_progress_preservation`.
- `not_type_safety` and `not_preservation`: the `E-Move` program `let x : bool = true; x; if x {()} else {()}` refutes both. Scoping plays no part here.
- `not_progress` and `not_type_safety_scope`: these are new and caused by the scoping. A closure body may mention a region in an annotation without that region appearing in the closure's type. So `` letrgn<`r> { || -> () { Right::<&`r shrd (), ()>(()); () } } `` is well typed, but popping `` `r `` then fails, and the machine gets stuck. The stuck configuration is itself well typed. With the paper's named regions this would just leave a harmless dangling name. Proposal §3.3 predicted the problem would move to progress; this confirms it.

**Not done.** Progress isn't proved: the old proof, written for the old grammar, was removed with it, and the statement is now false anyway. No repaired system and no supporting lemmas exist yet. A repair would need at least:
- a type-directed choice between move and copy;
- closure bodies mentioning only regions that appear in their type or that they capture;
- an invariant linking pointer values to loans.

**Design choices beyond the proposal:**
- The result value is strengthened strictly when a binder is popped; leftover values in older stack slots become `dead` instead.
- The typing rules check that nothing escapes when a binder's scope ends.
- Closure capture is an explicit selection, so the machine can choose what a closure captures.

**Docs.** `RequestProject/Oxide/README.md`, `READING_GUIDE.md`, `MISSING.md` and `GAPS_AND_GRAMMAR_DIFFERENCES.md` are rewritten. `PROPOSAL.md` has a status note recording what was decided and what differs from its text. The Properties table is updated: stale entries removed, the new results added.

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