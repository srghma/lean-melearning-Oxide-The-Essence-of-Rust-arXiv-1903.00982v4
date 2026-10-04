# Oxide: The Essence of Rust — Lean 4 formalization (scope-indexed)

This directory formalizes the language Oxide (Weiss, Gierczak, Patterson, Ahmed,
*Oxide: The Essence of Rust*) following the paper's appendix sources.

The development implements `Proposal/PROPOSAL.md`. There is only one grammar:
every syntactic class is indexed by a **scope** `Γ : Ctx := List Bnd`, the list
of the sorts of all binders in scope, most recent first. The sorts are frame
variables, abstract regions, type variables, term variables, concrete regions
and frame boundaries. A closed program is an `Oxide.Term []`, and the `Term n`
of a calculus with only term variables is the special case `Γ = vars n`.

The open choices of §6 of the proposal were decided as follows:

| Choice | Decision |
| --- | --- |
| runtime forms `framed`/`shift` in terms, or a continuation-based machine | **continuation-based (CK) machine**: there are no runtime term forms; the continuation records the bindings and frames to pop |
| `Fin k → _` fields or length-indexed lists | **`Fin k → _`** (tuples, arrays, closure parameters, call arguments and instantiations) |
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
| `Metatheory/` | statements of §3.7 and counterexamples |
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
* A call `Term.app f b Φs ρs τs k args` carries exactly `b.nφ` frames, `b.nϱ`
  regions and `b.nα` types.
* Closure bodies are `Term (vars k ++ Γ)`. Closure values carry their captured
  frame `Env Γ f` and a body in `vars k ++ (f ++ .frame :: Γ)`. Global function
  bodies are `Term (vars k ++ .frame :: b.ctx)`.
* Loans, places in loans and referents (pointers) are rooted at `In .var Γ`, so
  they can point into older frames but never past the end of the stack.
* The stack typing `StackTy S` and the stack `Stack S` are indexed by the same
  scope as the term in focus, so lookups (`varTy`, `loans`, `get`) are total.
  The type environment `Δ` is folded into the stack typing: type-level binders
  are entries of it, and outlives constraints are pairs of `In .abs S`.
* The sorts of types are separate families, so the paper's sort premises
  (`τ^SI`, `τ^XI`, `τ^SD`, `τ^SX`) and the length premises are gone from the
  typing rules.

## Results

All the results below are proved without `sorry`, using only the standard
axioms (`propext`, `Classical.choice`, `Quot.sound`).

* `canonical_forms` — proved for the new value typing.
* `type_safety_of_progress_preservation` — the paper's derivation of type
  safety from progress and preservation, for the machine.
* `not_type_safety : ¬ TypeSafety G` and `not_preservation : ¬ Preservation G`,
  for every `G` (`Metatheory/Counterexamples/TypeSafety.lean`). The program
  `let x : bool = true; x; if x { () } else { () }` is well typed (`ts_typed`).
  `E-Move` has no copyability side condition, so the first use of `x` may move
  it. The second use then reads `dead`, and the machine is stuck at `if dead`.
  The stuck configuration is not well typed, which refutes preservation too.
  Scoping plays no role in this counterexample.
* `not_progress : ¬ Progress G` and `not_type_safety_scope : ¬ TypeSafety G`,
  for every `G` (`Metatheory/Counterexamples/Progress.lean`). This failure is
  new, and it comes from the scoping. The paper's `T-Closure` and
  `T-ClosureValue` do not restrict the regions that occur in type annotations
  inside a closure body. So the closure
  `` || -> () { Right::<&`r shrd (), ()>(()); () } `` has type `() → ()`, which
  does not mention `` `r ``, and it may leave the scope of `` `r ``. In the
  program `` letrgn<`r> { || -> () { Right::<&`r shrd (), ()>(()); () } } ``,
  popping `` `r `` would have to strengthen the closure value past `` `r ``.
  That fails, so the machine is stuck. The program is well typed
  (`tp_prog_typed`) and reaches that configuration (`tp_steps`). The stuck
  configuration is well typed itself (`tp_typed`), so progress fails as well.
  With named regions, as in the paper, the body would just keep a dangling name
  in an annotation, which is never evaluated.
* The old development's results about level-based pointers
  (`not_type_safety_closure`, `not_preservationReach`) have no counterpart:
  pointers are typed indices, and a dangling pointer cannot be built. Popping
  a binder that the result value still points to blocks the machine instead.

Not done: there is no proof of progress, preservation or type safety for a
repaired system. Repairing them needs at least three changes:
(i) a type-directed choice between `E-Move` and `E-Copy`;
(ii) requiring that the regions of the enclosing scope that occur in a closure
body also occur in the closure's type, or are captured by it;
(iii) an invariant tying pointer values to the loans of the stack typing, so
that the no-escape checks made when a binder is popped also cover the values
the machine pops.
The old development's progress proof was about the old grammar and was removed
with it. It has not been ported.

## Representation choices and deviations from the paper

* **Continuation-based machine.** A configuration `⟨S, σ, e, κ⟩` has a stack
  `σ : Stack S`, a focus `e : Term S` and a continuation `κ : Cont S`.
  Compound terms push a continuation frame, and values are consumed by the top
  frame. `let`, `for`, `match`, `letrgn` and calls push a binding or a frame on
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
* **Closure captures.** `T-Closure` and `E-Closure` take an explicit selection
  `s : Sel f Γ` of the entries of the current frame that are captured. The body
  as written is the captured body renamed back (`body = body'.rename s.ren`).
  The selection is relational, so the machine is nondeterministic in what it
  captures. `E-Closure` copies the captured values and does not overwrite
  non-copyable captures with `dead` (non-copyability is a property of types).
  `T-Closure` marks them dead statically (`killNC`).
* **Continuation typing.** `ContOK G Θ Γ τ κ` types a continuation, using each
  typing rule minus the premise for the subterm in focus. `ConfigTyped` says
  the stack is valid for a stack typing, the focus is typed and the
  continuation accepts the result. `Progress`, `Preservation` and `TypeSafety`
  are stated for this machine.
* **Function names are values** (`Value.fn f`). `E-AppFunction` looks the name
  up in `Σ` and instantiates the body with type-level substitution
  (`FnDef.instBody`).
* **Values are a separate syntactic class**, embedded with `Term.val`. They
  live in the scope of the stack. Tuples, arrays and injections take an
  administrative step to become values.
* **Slices use half-open bounds** `[n₁, n₂)`. Referent typing adds the bound
  check against the designated slice.
* **Outlives bounds** of a polymorphic function, `ϱ₁ : ϱ₂`, are checked as
  `δ(ϱ₁) :> δ(ϱ₂)` at the call site.
* **`MTy`** has two representations of a fully initialized tuple, as in the
  paper's grammar. `MTy.toTy?` identifies them.
* **Judgments as single inductive families**: `Typing` (expressions, argument
  lists, values, maybe-unsized values, maybe-dead values, lists of values,
  captured environments), `OutlivesJ` and `RewriteJ`. The paper's judgments are
  abbreviations (`HasType`, `HasTypeV`, …).

## Concrete syntax

```lean
example : [OXIDE| let x : u32 = 1; let y : u32 = 2; (x, y) ] =
    Term.letE Ty.u32 (.val (Value.num 1)) (.letE Ty.u32 (.val (Value.num 2))
      (.tuple 2 ![.place ⟨.skipVar .here, []⟩, .place ⟨.here, []⟩])) := rfl
```

Names are resolved to typed indices when the macro expands. Unbound names,
borrows at abstract regions and references to variables of another frame are
rejected. Regions are written as Lean name literals (`` `a `` for `'a`), and
frame variables and literal frames with `@`. The types of a literal frame
`` @{x : u32, `s ↦ {}, y : &`s shrd u32} `` live in the frame's own scope.
Dead types and bare slice types cannot be written, because they belong to the
other sorts. See `ConcreteSyntax/Notation.lean` for the grammar and
`ConcreteSyntax/Examples.lean` for examples, including a machine run of
`let x : u32 = 5; x` and the counterexample programs in concrete syntax.
