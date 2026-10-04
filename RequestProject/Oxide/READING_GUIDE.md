# How to read the Oxide formalization

This guide maps the Lean files to the paper *Oxide: The Essence of Rust*
(Weiss, Gierczak, Patterson, Ahmed) and suggests an order for reading them.
`RequestProject/Oxide.lean` imports every file, in the order given below.

Other documents in this directory:
- `README.md`: the design decisions, the results and the deviations from the paper.
- `GAPS_AND_GRAMMAR_DIFFERENCES.md`: the paper's grammar side by side with ours.
- `MISSING.md`: what is not formalized.
- `Proposal/PROPOSAL.md`: the design that this development implements.

---

## 0. Before you start: one convention

**Everything is indexed by its scope.** `Ctx = List Bnd` lists the sorts of the
binders in scope, most recent first:

| Sort | Bound by |
| --- | --- |
| `.fvar` | frame variables `φ` of a polymorphic signature |
| `.abs` | abstract regions `ϱ` of a polymorphic signature |
| `.tvar` | type variables `α` of a polymorphic signature |
| `.var` | `let`, `for`, `match`, parameters; at runtime, a stack slot |
| `.rgn` | `letrgn`; at runtime, a region marker on the stack |
| `.frame` | a call (frame boundary `‡`) |

The indices are typed:
- `In b Γ` points at a binder of sort `b`, and it may cross frames.
- `TVar Γ` points at a term variable of the current frame.

For example:
- `let x : τ = e₁; e₂` is `Term.letE τ e₁ e₂` with `e₂ : Term (.var :: Γ)`;
- `letrgn<r> { e }` is `Term.letrgn e` with `e : Term (.rgn :: Γ)`;
- a closed program is a `Term []`.

The stack typing and the stack use the same scope as the term in focus, so the
same index works for all three.

You do not need to decode the indices by hand. `[OXIDE| … ]` accepts named
Oxide code, and `ConcreteSyntax/Examples.lean` shows each program next to the
term it denotes.

---

## 1. Map: paper section → Lean files

| Paper | File | Main declarations |
| --- | --- | --- |
| (scopes; the paper uses names) | `Syntax/Scopes.lean` | `Bnd`, `Ctx`, `In`, `TVar`, renamings `TRen`/`Ren`, partial renamings (strengthening) `PRen`/`PRenT`, capture selections `Sel` |
| §3.1 "Places and Place Expressions", "Annotations for References"; referents from §3.6 | `Syntax/Places.lean` | `Own`, `PlaceExpr` (root `TVar`), `APlaceExpr`, `APlace`, `Loan`, `Prim`, `RStep`, `Referent` |
| §3.2 *Types in Oxide*; frame expressions from §3.3 | `Syntax/Types.lean` | `Region`, `Binders`, `Ty`/`XTy`/`FrameExpr`/`FrameTy` (mutual), `MTy` |
| §3.1 "Expressions"; values from §3.6 | `Syntax/Terms.lean` | `Term`, `Value`, `Env`, `Program`, `FnDef`, `GlobalEnv` |
| §3.3 *Environments* (Γ with Δ folded in, Θ) | `Syntax/Environments.lean` | `SlotTys`, `StackTy`, `TempTy`, total lookups, `push*`/`pop*` |
| §3.6 runtime stacks; the machine's continuations | `Syntax/Runtime.lean` | `Slots`, `Stack`, `Cont`, `Config`, `Config.init` |
| (type-level instantiation at a call) | `Metafunctions/Substitution.lean` | `TSub`, `Sub`, `Ty.inst`, `FnDef.ty`, `FnDef.instBody` |
| App. C, metafunctions on types | `Metafunctions/Types.lean` | `Ty.frgns`, `Ty.noncopyable`, `MTy.toTy?`, `MTy.atPath`, `MTy.setPath`, `explode` |
| App. C, places | `Metafunctions/Places.lean` | `APlace.IsPrefix`, `APlace.Disjoint`, `APlaceExpr.splitDeref` |
| App. C, stack typings | `Metafunctions/StackTypings.lean` | `placeTy`, `setPlaceTy`, `gcLoans`, `NotReborrowed`, `NotInClosure`, `capturedFrame`, `killNC` |
| App. C, stacks | `Metafunctions/Stacks.lean` | `Stack.read`, `Stack.write`, `Stack.evalPlace`, `Stack.push*`, `Stack.popL`, `Stack.popFrame` |
| §3.4 *Region-Based Alias Management*; App. B.3 | `AliasManagement/OwnershipSafety.lean` | `PlaceTy` (`TC-*`), `OwnSafe` (`O-*`) |
| §3.5 "Region Rewriting and Outlives"; App. B.2 | `Typechecking/RegionRewriting.lean` | `Mode`, `OutlivesJ`/`Outlives`, `RewriteJ`/`Rewrite` |
| §3.5 *Typechecking Oxide Programs*; App. B.1, B.4, B.5 | `Typechecking/Typing.lean` | `RefTy`, `TyWF`, `EnvWF`, `StackWF`, **`Typing`**, `HasType`, `HasTypeV` |
| App. B.1, B.5 | `Typechecking/Validity.lean` | `StoreValid`, `FnDefWF`, `GlobalWF` |
| (typing the machine's continuations) | `Typechecking/Continuations.lean` | `ContOK`, `ConfigTyped` |
| §3.6 *Operational Semantics*; App. D | `OperationalSemantics/Machine.lean` | `Call`, **`Step`**, `Steps`, `Config.IsFinal` |
| §3.7; App. E (statements) | `Metatheory/Statements.lean` | `canonical_forms`, `Progress`, `Preservation`, `TypeSafety`, `type_safety_of_progress_preservation` |
| counterexamples | `Metatheory/Counterexamples/TypeSafety.lean` | `ts_typed`, `ts_steps`, `ts_stuck`, `not_type_safety`, `not_preservation` |
| | `Metatheory/Counterexamples/Progress.lean` | `tp_typed`, `tp_stuck`, `not_progress`, `tp_prog_typed`, `tp_steps`, `not_type_safety_scope` |
| (not in the paper) | `ConcreteSyntax/Notation.lean`, `ConcreteSyntax/Examples.lean` | `[OXIDE| … ]`, `[OXIDE_TY| … ]`, `[OXIDE_FN| … ]` |

---

## 2. Suggested reading order

1. `Syntax/Scopes.lean`, up to `TVar`, then `Syntax/Types.lean` and
   `Syntax/Terms.lean` (the inductive types only), then
   `ConcreteSyntax/Examples.lean` to see programs and their scoped terms.
2. `Syntax/Environments.lean` and `Syntax/Runtime.lean`: the stack typing, the
   stack and the configurations, all indexed by the same scope. Note how
   `pushVar` weakens every entry and `popL` strengthens them.
3. `OperationalSemantics/Machine.lean`: the machine. Read the `let` rules
   (`letPush`, `letE`, `popVar`) first, then calls (`Call`, `popFrame`).
4. `AliasManagement/OwnershipSafety.lean` and `Typechecking/Typing.lean`: the
   typing rules. `T-Let`, `T-LetRegion` and `T-Closure` show the no-escape
   checks at the end of a binder's scope.
5. `Typechecking/Continuations.lean` and `Metatheory/Statements.lean`: how the
   paper's theorems are stated for the machine.
6. The two counterexample files.

---

## 3. Status

The project builds with `lake build` and contains no `sorry`. See `README.md`
for the list of results and `MISSING.md` for what is not done.
