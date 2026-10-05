# Oxide: The Essence of Rust — Lean 4 formalization (scope-indexed)

This directory formalizes the language Oxide (Weiss, Gierczak, Patterson, Ahmed,
*Oxide: The Essence of Rust*) following the paper's appendix sources.

The development implements `Proposal/PROPOSAL.md`. There is only one grammar:
every syntactic class is indexed by a **scope** `Γ : Ctx := List Bnd`, the list
of the sorts of all binders in scope, most recent first. The sorts are frame
variables, abstract regions, type variables, term variables, concrete regions
and frame boundaries. A closed program is an `Oxide.Term sig []` (over a global signature `sig`),
and the `Term n`
of a calculus with only term variables is the special case `Γ = vars n`.

**Terms are in A-normal form** (`Syntax/Terms.lean`). There are three
syntactic classes:

```
a ::= v | move π | copy p                                     (Atom)
c ::= a | &r ω p | &r ω p[a] | &r ω p[a₁..a₂] | p[a] | p := a
    | |x̄ : τ̄| → τ { e } | a::<Φ̄, ρ̄, τ̄>(ā) | (ā) | [ā]
    | Left::<τ₁, τ₂>(a) | Right::<τ₁, τ₂>(a) | abort!(s)
    | letrgn<r> { e } | if a { e } else { e } | for x in a { e }
    | while e { e } | match a { Left(x) => e, Right(y) => e }      (Comp)
e ::= let x : τ = c; e | c; e | c                             (Term)
```

Every operand is an atom, and every intermediate result is named by a `let`
whose right-hand side is a computation (never another `let` or a sequence).
Control constructs are computations, so they can be bound by a `let`; this is
the usual relaxation of A-normal form for languages with blocks (strict
A-normal form would need join points). The condition of `while` is a term, since
it is re-evaluated at every iteration. The typing judgment is split accordingly
(atoms, computations, terms), the machine evaluates the atoms of a computation in
one step (`EvalAtom`, `EvalAtoms`), and the concrete syntax only accepts
programs in A-normal form.

The open choices of §6 of the proposal were decided as follows:

| Choice | Decision |
| --- | --- |
| runtime forms `framed`/`shift` in terms, or a continuation-based machine | **continuation-based (CK) machine**: there are no runtime term forms; the continuation records the bindings and frames to pop |
| `Fin k → _` fields or length-indexed lists | **`Fin k → _`** (tuples, arrays, closure parameters, call arguments, type arguments and continuation zippers) |
| split the type sorts in the first step | **split**: `Ty` (sized, initialized), `XTy` (maybe unsized), `MTy` (maybe dead) |
| replace the old development or build beside it | **replace**: the old `Nat`-indexed development has been removed |

## Files

`READING_GUIDE.md` gives the file-by-file map; `RequestProject/Oxide.lean`
imports everything.

| Folder | Content |
| --- | --- |
| `Syntax/` | scopes and typed de Bruijn indices (`Scopes.lean`); places, types, terms, stack typings, stacks, continuations and configurations |
| `Metafunctions/` | type-level substitution (instantiating a polymorphic function), metafunctions on types, places, stack typings and stacks (appendix C) |
| `AliasManagement/` | place typing and ownership safety (§3.4) |
| `Typechecking/` | outlives and region rewriting, the typing judgment, stack validity and well-formed global environments, typing of continuations and configurations (§3.5, appendix B) |
| `OperationalSemantics/` | the abstract machine (§3.6, appendix D) |
| `Metatheory/` | statements of §3.7 and regression tests for the former counterexamples |
| `ConcreteSyntax/` | `[OXIDE| … ]`, `[OXIDE_TY| … ]`, `[OXIDE_FN| … ]` and examples |
| `Proposal/` | the proposal that this development implements |

## What scope-indexing enforces

* `In b Γ` is a typed de Bruijn index: it is always in range and points at a
  binder of sort `b`. Term variables (`TVar Γ`) can only reach the current
  frame, because no constructor skips a frame boundary.
* Regions are `Region.abs (i : In .abs Γ)` or `Region.conc (r : In .rgn Γ)`.
  `letrgn` binds a `.rgn`, so there is no "opening" of regions. Borrows take a
  concrete region `In .rgn Γ`.
* A function type `Ty.fn b k params ret env bounds` binds `b.ctx` in its
  parameters, result and environment. Its bounds are `Fin b.nϱ` pairs.
* A call `Comp.app f b θ k args` carries one bundle `θ : TArgs b Γ` of exactly
  `b.nφ` frames, `b.nϱ` regions and `b.nα` types; `TArgs.toTSub` turns it into
  the type-level substitution used to instantiate the callee.
* Loans, places in loans and referents (pointers) are rooted at `In .var Γ`, so
  they can point into older frames but never past the end of the stack.
* The stack typing `StackTy S` and the stack `Stack S` are indexed by the same
  scope as the term in focus, so lookups (`varTy`, `loans`, `get`) are total.
  The type environment `Δ` is folded into the stack typing: type-level binders
  are entries of it, and outlives constraints are pairs of `In .abs S`.
* The sorts of types are separate families, so the paper's sort premises
  (`τ^SI`, `τ^XI`, `τ^SD`, `τ^SX`) and the length premises are gone from the
  typing rules.

## The type-safety refinements

The development also implements the "correct by construction" refinements of
the earlier analysis:

| Proposal | Where | What it does |
| --- | --- | --- |
| place expressions structured by their dereferences | `Syntax/Places.lean` | a place is a root and a projection path (`APlace`, `TPlace`); a place expression is `PExpr.place π` or `PExpr.deref p q` (`(*p).q`). `base`, `splitDeref`, plugging into a context (`PCtx`) and `IsPlace` are structural; there is no `List POp` any more |
| places where a place is required | `Syntax/Terms.lean`, `OperationalSemantics/Machine.lean` | `Atom.move` takes a `TPlace`, so `E-Move` needs no "no dereference" premise |
| referents by structure | `Syntax/Places.lean` | `Referent.place π`, `Referent.index R i q`, `Referent.slice R start len` |
| typed projection paths | `Syntax/Types.lean`, `Metafunctions/StackTypings.lean` | `TyPath τ` (`proj (i : Fin k) : TyPath (τs i) → TyPath (tuple k τs)`); untyped `Nat` paths are converted once (`TyPath.ofList`), and type lookup and update along a `TyPath` are total |
| typed value paths | `Metafunctions/Stacks.lean` | `VPath v`: reading and writing along a resolved path are total (`VPath.get`/`VPath.set`); `Referent.resolve` is the only partial step |
| move vs. copy | `Syntax/Terms.lean`, `Typechecking/Typing.lean` | `Atom.move π` and `Atom.copy p`; `T-Copy` requires a copyable type, `E-Move` only applies to `move` |
| closures in their own scope | `Syntax/Terms.lean`, `Syntax/TypeSubst.lean`, `Typechecking/Typing.lean` | `Comp.closure f c o θ k ps ret body`: the capture list `c : Cap Γ f`, outer binders `o` with explicit entries `θ : Inst o Γ`, and a body in `vars k ++ (f ++ .frame :: o)`. `T-Closure`/`T-ClosureValue` require `Inst.Covered`: every binder reachable through `θ` occurs in the closure's type. `E-Closure` is deterministic |
| `MTy` indexed by its declared type | `Syntax/Types.lean` | `MTy.Of τ` with `init`, `dead` and `tuple` (one `MTy.Of (τs i)` per field); `MTy` is the pair of a type and its state, so a partially moved variable keeps its declared type; `MTy.Of.mkTuple` normalizes an all-`init` tuple to `init` |
| global functions by signature | `Syntax/Terms.lean`, `Typechecking/Validity.lean` | terms are indexed by a signature `sig : Sig` (a list of `FnSig`); `Value.fn` holds an index `FnIdx sig`; `GlobalEnv sig` has exactly one body per declared function (`Defs`), so lookup is total; bodies are typed against the whole signature (`GlobalWF`) |
| A-normal form | `Syntax/Terms.lean`, `Typechecking/Typing.lean`, `OperationalSemantics/Machine.lean`, `Typechecking/Continuations.lean` | operands are atoms (`Atom`), so the machine needs no continuation frames for partially evaluated operands: the only frames are `letE`, `seq`, `whileE` and the pops |
| slices by start and length | `Syntax/Places.lean`, `Metafunctions/Stacks.lean` | `Referent.slice R start len`; value paths carry `start + len ≤ k` |
| literals | `Syntax/Places.lean` | `Prim : BaseTy → Type`, `Prim.num (n : UInt32)`; constants carry their base type |
| bundled type arguments | `Syntax/TypeSubst.lean` | `TArgs b Γ` (used by `Comp.app` and `Call`) |
| runtime scopes | `Syntax/Scopes.lean`, `Syntax/Runtime.lean`, `Syntax/Environments.lean` | `Ctx.Runtime`; `Slots.runtime` proves that stacks only exist over runtime scopes; signature environments use explicit entries for type-level binders (`SlotTys.ofBinders`) instead of placeholder `dead unit` slots |

## Results

All the results below are proved without `sorry`, using only the standard
axioms (`propext`, `Classical.choice`, `Quot.sound`).

* `canonical_forms` — proved for the value typing.
* `type_safety_of_progress_preservation` — the paper's derivation of type
  safety from progress and preservation, for the machine (assuming a
  well-formed global environment, `GlobalWF G`).
* Regression for the move/copy counterexample
  (`Metatheory/Regressions/MoveCopy.lean`). The program
  `let x : bool = true; copy x; if copy x { () } else { () }` is well typed
  (`ts_typed`), a `copy` step never changes the stack (`Step.copy_inv`), and the
  program runs to its final value `()` (`ts_runs`, `ts_final`). In the previous
  version the first use of `x` could step by `E-Move` and the program got stuck
  at `if dead`; this is no longer possible, because only `move` steps by
  `E-Move`.
* Regression for the closure-scope counterexample
  (`Metatheory/Regressions/ClosureScopes.lean`). The closure
  `` || -> () { Right::<&`r shrd (), ()>(()); () } `` mentions `` `r `` in its
  body but not in its type `() → ()`. Its entries are not covered by its type
  (`tp_not_covered`), so the closure term is not well typed in any stack typing
  (`tp_closure_untyped`), neither is the program
  `` letrgn<`r> { … } `` (`tp_prog_untyped`), the closure value is not well typed
  (`tp_closure_value_untyped`), and the configuration that used to be stuck is
  not well typed (`tp_stuck_untyped`).
* Regression for the duplicate-capture counterexample
  (`Metatheory/Regressions/DuplicateCaptures.lean`). In
  `` fn dup<`ϱ>(y : &`ϱ uniq u32) -> () { let f : τ_f = || -> () { … }; f() } `` the closure
  captures `y` twice, as `c₁` and `c₂`, both of type `` &`ϱ uniq u32 ``. Its
  body takes `a = &r₁ uniq *c₁` and `b = &r₂ uniq *c₂`, two simultaneously live
  unique borrows of the same location, writes through `b` and then through `a`.
  Without the new premise this body type checks (`dcBody_typed`): the loan
  `uniq *c₁` and the place `*c₂` have different roots, so ownership safety sees
  them as disjoint. Every other premise of `T-Closure` holds
  (`dc_closure_other_premises`). At runtime both slots hold the pointer stored in
  `y` (`dc_env_aliases`). `T-Closure` now requires a duplicate-free capture list
  (`Cap.Nodup`), so the closure term is ill typed (`dc_closure_untyped`), the
  function is not well formed (`dc_fn_not_wf`), and neither is a global
  environment containing it (`dcG_not_wf`).

Not done: progress, preservation and type safety (`Progress G`,
`Preservation G`, `TypeSafety G` in `Metatheory/Statements.lean`) are stated but
neither proved nor refuted for the refined system. The counterexamples of
the previous versions are ruled out (see the regressions above). A full proof
would also need an invariant tying pointer values to the loans of the stack
typing, so that the no-escape checks made when a binder is popped also cover
the values the machine pops.

## Representation choices and deviations from the paper

* **Continuation-based machine.** A configuration `⟨S, σ, e, κ⟩` has a stack
  `σ : Stack S`, a focus `e : Term S` and a continuation `κ : Cont S`.
  `let x : τ = c; e` and `c; e` put `c` in focus and push the rest on the
  continuation; a computation evaluates its atoms and reduces in one step; the
  resulting value (`Term.val v`) is consumed by the top frame. `let`, `for`, `match`, `letrgn` and calls push a binding or a frame on
  the stack, together with a `popVar`, `popRgn` or `popFrame k f` continuation
  frame. These replace the paper's `shift e`, `shiftprov e` and `framed e`.
* **Popping.** When the result value reaches a pop frame, it is strengthened
  past the popped binders. If it still mentions them, the machine is stuck.
  The remaining stack entries are strengthened leniently: values left in older
  slots that mention a popped binder become `dead` (`Value.prenameD`). Only
  slots whose type is already dead can hold such values.
* **No-escape checks in typing.** Where a binder's scope ends (`T-Let`,
  `T-LetRegion`, `T-ForArray`, `T-ForSlice`, `T-Match`, a closure body's frame
  in `T-Closure`/`T-ClosureValue`, and the `pop*` continuation rules), the
  rules first garbage-collect loans, keeping the regions of the result type.
  They then require the result type and every remaining type and loan to be
  strengthenable past the binder. The paper leaves this implicit. It is the
  missing no-escape condition of `T-Framed`.
* **Closure captures.** A closure term lists what it captures (`c : Cap Γ f`:
  variables and concrete regions of the current frame) and its outer binders
  (`θ : Inst o Γ`). `E-Closure` reads the captured values off the stack
  (`Env.ofCap`); it does not overwrite non-copyable captures with `dead`
  (non-copyability is a property of types). `T-Closure` marks them dead
  statically (`killNC`), and requires the capture list to name every variable
  and region at most once (`Cap.Nodup`), since `killNC` kills each original only
  once. The premise is a typing condition rather than part of the grammar
  because renamings of terms (`Ren`, `Sub`) need not be injective, so a
  duplicate-free capture list is not preserved by renaming in general. The coverage premise `Inst.Covered` is stated
  semantically (strengthenability of the type implies that of `θ`).
* **`T-Move` on copyable types.** The paper restricts `T-Move` to non-copyable
  types. Here `T-Move` accepts any type, since a move of a copyable value is
  harmless (as `Operand::Move` in Rust's MIR); `T-Copy` requires a copyable
  type. The concrete syntax elaborates a bare place without dereference to a
  move and a place through a dereference to a copy; `copy!(p)` and `move!(p)`
  choose explicitly.
* **Continuation typing.** `ContOK G Θ Γ τ κ` types a continuation, using each
  typing rule minus the premise for the subterm in focus. `ConfigTyped` says
  the stack is valid for a stack typing, the focus is typed and the
  continuation accepts the result. `Progress`, `Preservation` and `TypeSafety`
  are stated for this machine.
* **Function names are values** (`Value.fn f`, `f : FnIdx sig`).
  `E-AppFunction` takes the body from `Σ` (total) and instantiates it with
  type-level substitution (`GlobalEnv.instBody`).
* **Values are a separate syntactic class**, embedded as atoms with
  `Atom.val` (`Term.val v` abbreviates the term `ret (atom (val v))`). They
  live in the scope of the stack. Tuples, arrays and injections of atoms take
  one step to become values.
* **Slices** are given by a start and a length (the syntax `p[a₁..a₂]` is
  the half-open range `[a₁, a₂)`). Referent typing adds the bound check
  against the designated slice. Writing a value through a slice referent
  replaces the elements only if the value is a slice of the same length
  (slices are unsized and are never assigned as a whole).
* **Outlives bounds** of a polymorphic function, `ϱ₁ : ϱ₂`, are checked as
  `δ(ϱ₁) :> δ(ϱ₂)` at the call site.
* **`MTy`** is a declared type with a state `MTy.Of τ`; `MTy.Of.mkTuple`
  normalizes a tuple whose fields are all initialized to `init`.
* **Judgments as single inductive families**: `Typing` (atoms, computations,
  terms, argument lists, values, maybe-unsized values, maybe-dead values, lists of values,
  captured environments), `OutlivesJ` and `RewriteJ`. The paper's judgments are
  abbreviations (`HasTypeA`, `HasTypeC`, `HasType`, `HasTypeV`, …).

## Concrete syntax

```lean
example : ([OXIDE| let x : u32 = 1; let y : u32 = 2; (copy!(x), y) ] : Program []) =
    Term.letE Ty.u32 (.atom (.val (Value.num 1))) (.letE Ty.u32 (.atom (.val (Value.num 2)))
      (.ret (.tuple 2 ![.copy (.place ⟨.skipVar .here, []⟩), .move ⟨.here, []⟩]))) := rfl
```

The concrete syntax follows the A-normal form: an operand that is not an atom
(for example the nested tuple in `(1, (2,))`) is rejected with a message asking
to bind it with `let` first.

Names are resolved to typed indices when the macro expands. Unbound names,
borrows at abstract regions and references to variables of another frame are
rejected. Regions are written as Lean name literals (`` `a `` for `'a`), and
frame variables and literal frames with `@`. The types of a literal frame
`` @{x : u32, `s ↦ {}, y : &`s shrd u32} `` live in the frame's own scope.
Dead types and bare slice types cannot be written, because they belong to the
other sorts. See `ConcreteSyntax/Notation.lean` for the grammar and
`ConcreteSyntax/Examples.lean` for examples, including a machine run of
`let x : u32 = 5; x` and the regression programs in concrete syntax. Global
functions are listed in signature order: `[OXIDE{f, g}| … ]`.
