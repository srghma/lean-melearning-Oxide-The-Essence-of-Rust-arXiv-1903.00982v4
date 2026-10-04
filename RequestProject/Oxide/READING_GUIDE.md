# How to read the Oxide formalization

This guide explains how the Lean files relate to the paper *Oxide: The Essence of
Rust* (Weiss, Gierczak, Patterson, Ahmed) and suggests an order for reading them.

The files are grouped into folders by paper section. The main text's §3
("Oxide, Formally") gives the narrative. The appendices give the complete
definitions: A Syntax, B Statics, C Metafunctions, D Dynamics, E Metatheory.
`RequestProject/Oxide.lean` imports every file, in the order given below.

Other documents in this directory:
- `README.md`: the results, and the deviations from the paper.
- `GAPS_AND_GRAMMAR_DIFFERENCES.md`: a side-by-side comparison of our grammar with
  the paper's, and a list of what is not formalized.

---

## 0. Before you start: three conventions

1. **De Bruijn indices for term variables.** `Term n` is the type of expressions
   with at most `n` free variables, so `Term 0` is a closed program. Index `0` is
   the most recently bound variable. `let x : τ = e₁; e₂` is
   `Term.letE τ e₁ e₂` with `e₂ : Term (n+1)`.
2. **De Bruijn levels for anything that points into the stack.** Loans,
   absolute places and referents (`ptr 𝓡`) name a stack slot by its position
   counted from the bottom of the whole stack (its *level*). Levels do not change
   when frames are pushed or popped above them.
3. **Nameless type-level binders.** A function type records only how many frame
   variables, abstract regions and type variables it binds. `letrgn<'r>{e}` binds
   its region as `Region.bound 0`; once the region is allocated it becomes
   `Region.conc ℓ`.

You do not need to decode de Bruijn terms by hand. The `[OXIDE| … ]` syntax in
`ConcreteSyntax/` accepts named Oxide code, and `ConcreteSyntax/Examples.lean`
shows each program next to the term it denotes.

---

## 1. Map: paper section → Lean files

| Paper | Folder / file | Main declarations |
| --- | --- | --- |
| §3.1 *The Syntax of Oxide*: "Places and Place Expressions", "Annotations for References" | `Syntax/Places.lean` | `Own`, `Own.Le`, `Region`, `PlaceExpr`, `APlaceExpr`, `APlace`, `Loan` |
| §3.2 *Types in Oxide* (Fig. "Type Syntax") | `Syntax/Types.lean` | `BaseTy`, `Ty`, `FrameExpr`, `FrameEntry` |
| §3.3 *Environments for Typechecking* (Fig. "Environments") | `Syntax/Environments.lean` | `FrameTy` (Φ), `StackTy` (Γ), `TempTy` (Θ), `TyEnv` (Δ) |
| §3.1 "Expressions" (Fig. "Term Syntax"); runtime values from §3.6 | `Syntax/Terms.lean` | `Term : Nat → Type`, `Terms`, `Value`, `Referent`, `FnDef`, `GlobalEnv` (Σ) |
| §3.6, Fig. "Syntax Extensions for Dynamics" | `Syntax/Runtime.lean` | `StackEntry`, `StackFrame` (ς), `Stack` (σ) |
| App. C *Metafunctions* (types) and §3.2 "Sized and Unsized Types", "Initialized and Dead Types" | `Metafunctions/Types.lean` | `Ty.SI`/`XI`/`SD`/`SX`, `Ty.shift`, `Ty.inst`, `Ty.openRgns`, `Ty.frgns`, `Ty.copyable`, `Ty.atPath` |
| App. C (`places.tex`) | `Metafunctions/Places.lean` | `APlace.IsPrefix`, `APlace.Disjoint`, `APlaceExpr.splitDeref` |
| App. C (type lookup and update, `explode`, `gc-loans`, …) | `Metafunctions/StackTypings.lean` | `StackTy.varTy`, `placeTy`, `setPlaceTy`, `loans?`, `gcLoans`, `NotReborrowed`, `NotInClosure` |
| App. C (value lookup and update) | `Metafunctions/Stacks.lean` | `Stack.get?`, `Stack.read`, `Stack.write`, `Stack.evalPlace` |
| (de Bruijn bookkeeping for terms; the paper uses names instead) | `Metafunctions/Terms.lean` | `Term.rename`, `Term.occurs`, `Term.openRgns`, `Term.inst` |
| §3.4 *Region-Based Alias Management* (Fig. "Ownership Safety"); App. B.3 | `AliasManagement/OwnershipSafety.lean` | `PlaceTy` (`TC-*`), `OwnSafe` (`O-*`) |
| §3.5 "Region Rewriting and Outlives"; App. B.2 | `Typechecking/RegionRewriting.lean` | `Mode` (μ), `OutlivesJ`/`Outlives` (`OL-*`), `RewriteJ`/`Rewrite` (`RR-*`) |
| §3.5 *Typechecking Oxide Programs* (Figs. "Selected Typing Rules", "Typing Rule for Application"); App. B.1, B.4, B.5 | `Typechecking/Typing.lean` | `RefTy`, `RgnWF`, `TyWF`, `EnvWF`, `StackWF`, **`Typing`**, `HasType`, `HasTypeV` |
| App. B.1 *Well-Formedness*, B.5 *Additional Judgments* | `Typechecking/Validity.lean` | `StoreValid` (Σ ⊢ σ : Γ), `TempValid`, `FnDefWF`, `GlobalWF` |
| §3.6 *Operational Semantics*; App. D *Dynamics* | `OperationalSemantics/Dynamics.lean` | `ECtx`, **`Step`** (`E-*`), `Steps`, `Term.IsFinal` |
| §3.7 *Well-typed Oxide programs won't go wrong!*; App. E (statements) | `Metatheory/Statements.lean` | `canonical_forms`, `Progress`, `Preservation`, `TypeSafety`, `type_safety_of_progress_preservation` |
| App. E.14 *Progress* (`progress_proof.tex`) | `Metatheory/Progress/*.lean` | `progress_aux`, plus the lemmas used in the proof |
| App. E.3–E.6 (supporting lemmas, `proofs.tex`; see the file docstring for which ones) | `Metatheory/SupportingLemmas.lean` | `StoreValid.pop`, `HasType.val_output`, `PlaceTy.rewrite`, `PlaceTy.gcLoans`, `PlaceTy.push_var`, … |
| App. E.15 *Preservation* | `Metatheory/Counterexamples/Preservation.lean` | `not_preservation` |
| App. E.16 *Type Safety* | `Metatheory/Counterexamples/TypeSafety.lean`, `…/Closure.lean` | `not_type_safety`, `not_type_safety_closure` |
| (a proposed repair of Preservation) | `Metatheory/Counterexamples/Reachability.lean` | `PreservationReach`, `ReachableTyped`, `not_preservationReach` |
| §3.7, the final results | `Metatheory/Safety.lean` | `progress`, `type_safety_false` |
| not in the paper | `ConcreteSyntax/Notation.lean`, `ConcreteSyntax/Examples.lean` | `[OXIDE| … ]`, `[OXIDE_TY| … ]`, `[OXIDE_FN| … ]` |

Notes on the grouping:
- **Lean definition order vs. paper order.** The files can only be read in
  dependency order, which sometimes differs from the paper's order. Types
  (§3.2) come before terms (§3.1), because terms contain type annotations. Frame
  entries (§3.3) are defined in `Syntax/Types.lean`, because closure types contain
  frames. The appendix C metafunctions come before the statics, which use them.
- **Well-formedness of types sits inside `Typechecking/Typing.lean`.** The
  judgments for types, frames and stack typings (`TyWF`, `EnvWF`, `StackWF`) are
  mutually inductive with each other, because a function type contains its
  captured frame. The typing rules use them as premises. All typing judgments are
  packed into one inductive family `Typing` (selected by `TyJ`), so that one
  induction covers expressions, argument lists and values together. `HasType`,
  `HasTypeV`, `HasTypeArgs`, … are abbreviations for its instances.
- **Rule names.** Constructors carry the paper's rule names in their docstrings
  (`T-Move`, `E-Framed`, `O-Deref`, …). To find a rule, search for its name, e.g.
  `rg "T-Borrow" RequestProject/Oxide`.

---

## 2. Suggested reading order

### Pass 1: the language

1. `Syntax/Places.lean`. Its module docstring explains every representation
   choice; read it first.
2. `Syntax/Types.lean`, `Syntax/Environments.lean`, `Syntax/Terms.lean`. Compare
   each with the paper's Figures "Type Syntax", "Environments" and "Term Syntax".
3. `ConcreteSyntax/Examples.lean`. This shows what familiar Oxide programs look
   like as de Bruijn terms. Skim `ConcreteSyntax/Notation.lean` only for the
   grammar in its docstring; the rest of that file is macro machinery.
4. `Syntax/Runtime.lean`, then `OperationalSemantics/Dynamics.lean`. Read the
   `Step` relation next to §3.6 and appendix D. Skip the `Metafunctions/` files
   at first, and look up an operation (`Stack.read`, `Stack.evalPlace`, …) when a
   rule uses it.

### Pass 2: the type system

5. `AliasManagement/OwnershipSafety.lean` with §3.4. `PlaceTy` computes the type
   of a place expression. `OwnSafe` is the core of the borrow checker: it checks
   that a borrow does not conflict with existing loans.
6. `Typechecking/RegionRewriting.lean` with §3.5 "Region Rewriting and Outlives".
7. `Typechecking/Typing.lean`, the typing judgment
   `Σ; Δ; Γ; Θ ⊢ e : τ ⇒ Γ'` (`HasType G Δ Θ Γ e τ Γ'`). Read the constructors
   for `T-Move`, `T-Borrow`, `T-Let`, `T-Assign`, `T-App` and `T-Closure` in the
   order §3.5 discusses them.
8. `Typechecking/Validity.lean`: stack validity `StoreValid`, which links the
   runtime stack to the stack typing.
9. Use `Metafunctions/*.lean` as reference material for the side conditions you
   meet in steps 5–8 (`gcLoans`, `NotReborrowed`, `Ty.noncopyable`, …).

### Pass 3: the metatheory (§3.7, appendix E)

10. `Metatheory/Statements.lean`. Read the three statements `Progress`,
    `Preservation` and `TypeSafety` next to the paper's lemmas. This file also
    proves `canonical_forms` and records the paper's argument
    `type_safety_of_progress_preservation`.
11. `Metatheory/Safety.lean`: the final results. **`progress` is proved.** Type
    safety as stated in the paper is **false** (`type_safety_false`).
12. Why it is false, in `Metatheory/Counterexamples/`:
    - `Preservation.lean`: `framed (ptr x)` pops the frame that `x` lives in, so
      the paper's Preservation fails for arbitrary well-typed configurations.
    - `TypeSafety.lean`: `E-Move` has no side condition requiring a non-copyable
      type. In `let x : bool = true; x; if x {()} else {()}` the first use of `x`
      may move it, and the `if` then gets stuck on `dead`.
    - `Closure.lean`: a closure returns a pointer into its own popped frame. This
      failure comes from our de Bruijn-level representation of pointers; the
      paper's named version would not show it (see the file's docstring).
    - `Reachability.lean`: restricting Preservation to configurations reachable
      from closed programs does not help.
13. Optional, the proof of progress, in dependency order:
    `Progress/Store.lean` → `Refine.lean` → `Values.lean` → `Places.lean` →
    `Helpers.lean` → `Main.lean`. The key idea is in the docstring of
    `Progress/Refine.lean`: `T-Drop` makes the stack typing a *refinement* of the
    one the stack satisfies, so the induction is generalized over refinements.
14. Optional: `Metatheory/SupportingLemmas.lean`, the lemmas of appendix E that
    still hold here.

---

## 3. Dependency graph

Each folder's files form a chain in the order listed in section 1; arrows show
the imports between folders.

```
Syntax/*  ──────────────►  ConcreteSyntax/Notation
   │                                │
   ▼                                ▼
Metafunctions/*  ──►  OperationalSemantics/Dynamics  ──►  ConcreteSyntax/Examples
   │                                │
   ▼                                │
AliasManagement/OwnershipSafety     │
   │                                │
   ▼                                │
Typechecking/*                      │
   │                                │
   ▼                                ▼
Metatheory/Statements  ◄────────────┘
   │
   ▼
Metatheory/Progress/*  ──►  Metatheory/SupportingLemmas
   │
   ▼
Metatheory/Counterexamples/Preservation → TypeSafety → Closure → Reachability
   │
   ▼
Metatheory/Safety
```

## 4. Status at a glance

| Result | Status |
| --- | --- |
| Canonical forms (`canonical_forms`) | proved |
| Progress (`progress`) | proved, for every global environment |
| Preservation as stated in the paper | refuted (`not_preservation`) |
| Type safety as stated in the paper | refuted (`not_type_safety`, `not_type_safety_closure`, `type_safety_false`) |
| Preservation restricted to reachable configurations | refuted (`not_preservationReach`) |

The project builds with `lake build`. The only occurrences of `sorry` are in
comments, inside the commented-out original statements of `preservation` and
`type_safety` in `Metatheory/Safety.lean`.
