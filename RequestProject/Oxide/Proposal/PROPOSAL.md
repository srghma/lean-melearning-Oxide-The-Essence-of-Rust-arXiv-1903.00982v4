# Proposal: correct-by-construction `Term` and `Ty` for Oxide

This proposal answers four questions:

1. How should `Term` be improved so that it is correct by construction?
2. Should `Term` be parametrized by more than a `Nat`?
3. Should `Ty` be parametrized too?
4. Should `Term` carry contexts, and if so which ones?

> **Status: implemented.** This design is now the only grammar of the
> formalization, and the old `Nat`-indexed development has been removed. The
> prototype files that used to sit in this folder were folded into
> `Syntax/` and `Metafunctions/`.
>
> The open questions of §6 were decided as follows: a **continuation-based
> machine** (R2), **`Fin k → _`** fields, the **type-sort split** in the first
> step, and **replacing** the old development.
>
> Differences from the text below:
> * There are no runtime forms (`framed`, `shift`, `shiftRgn`) in `Term`; the
>   continuation (`Cont`) records the pops.
> * Popping strengthens the result value strictly: the machine is stuck if the
>   value mentions a popped binder. Garbage left in older stack slots is
>   strengthened leniently, becoming `dead`.
> * The typing rules require the result type and the remaining stack typing to
>   be strengthenable at the end of every binder's scope (§3.3).
> * Closures are written in their own scope: a capture list `Cap Γ f`, outer
>   binders `o` with explicit entries `Inst o Γ`, and a body in
>   `vars k ++ (f ++ .frame :: o)`.
> * `framedPop_dangling`/`framedPop_ok` are subsumed by the machine's `popFrame`.
> * Global functions are indices into a signature (§4.3 was adopted).
>
> The question raised in §3.3 was first answered negatively for the earlier
> rules: a closure body could mention a region missing from the closure's
> type, which refuted progress. A later round of refinements (place
> expressions grouped by dereferences, explicit move/copy, closures in their own
> scope with a coverage premise, typed paths, `MTy` indexed by its declared
> type, signature-indexed global functions, and others; see
> `../README.md`, § The type-safety refinements) rules out both earlier
> counterexamples; see `Metatheory/Regressions/`. Progress and preservation for
> the refined rules are stated but not proved.
>
> The rest of this document is the original proposal. It refers to files of the
> removed development.

---

## 0. Short answers

| Question | Answer |
| --- | --- |
| Index `Term` by more than `Nat`? | **Yes.** Index it by a *scope* `Γ : List Bnd`: the sorts of all binders in scope, most recent first. The sorts are frame variables `φ`, abstract regions `ϱ`, type variables `α`, term variables `x`, concrete regions `r`, and frame boundaries `‡`. `Term n` is the special case where `Γ` is `n` copies of `.var`, and a closed program is a `Term []`. |
| Index `Ty` too? | **Yes, by the same scope**, because types mention regions, type variables, frame variables and (through closure environments) loans. Also split `Ty` by the paper's *sorts* (sized `SI`, maybe-unsized `XI`, maybe-dead `SX`) into separate families. That removes about 40 sort premises from the typing rules. |
| Index `Term` by a context? | **By the scope only, i.e. the context with the types erased.** Do not index it by the typing context (intrinsically typed terms). Oxide's typing is flow-sensitive (`Γ ⇒ Γ'`), not syntax-directed (`T-Drop`), and checks ownership conditions on `Γ`. Most importantly, Preservation is false for the current rules, so a type-preserving step function cannot even be defined. Instead, index the *contexts* by the scope: the stack typing (which also absorbs `Δ`) and the runtime stack. Lookups then become total. |
| Global environment `Σ`? | Keep function names as `String`s, checked by the typing judgment, for now. Section 4.3 discusses indexing by a signature. |

---

## 1. What the current `Term n` does not enforce

`Term n` (`Syntax/Terms.lean`) only makes *term variables of the top frame*
well scoped. Everything else is a raw `Nat` or an unchecked list, and its
validity is a premise of the typing rules or of the metatheory:

| Unenforced invariant | Where it is checked today |
| --- | --- |
| `Region.abs i`, `Region.bound i`, `Region.conc ℓ`, `Ty.tvar i`, `FrameExpr.var i` are raw `Nat`s | `RgnWF`, `TyWF`, `EnvWF`; `T-LetRegion` and `T-Closure` *open* `bound` into `conc` levels (`openRgns`, `closeRgns`, `newLevels`: 17 uses) |
| `Ty.fn nφ nϱ nα … bounds`: the bounds are `Nat × Nat` pairs | `TyWF.fn` (`hbs`) |
| `Term.closure k params …` with `params.length = k` | `T-Closure` (`hk`) |
| `Value.closure m k q frame …` with `frame.length = m`, plus `q` captured regions | `T-ClosureValue` (`hk`, `hm`, `hΦm`, `hq`) |
| `Term.app f Φs ρs τs args`: the number of instantiations matches the binders | `T-AppFunction` (`hlenΦ`, `hlenρ`, `hlenτ`) |
| `Term.borrow r …` accepts any `Region`, but only concrete ones type | `T-Borrow*` (pattern `.conc r`) |
| Sized / unsized / dead / maybe-dead types are predicates on one `Ty` | about 40 `SI`/`XI`/`SD`/`SX` premises in `Typing.lean` |
| `framed m e`: `m` has no relation to the stack frame being pushed | `T-Framed`, the dynamics |
| Loans, places and referents use absolute `Nat` levels | `idxToLevel`, `varTy`, `loans?` return `Option` (38 uses) |
| `Terms n` exists only because `List (Term n)` is rejected as a nested inductive | — |

The level-based referents are also the cause of the closure counterexample
(`not_type_safety_closure`). There, a level that pointed into a popped frame gets
reused by the next push.

---

## 2. The proposed design

### 2.1 Scopes and typed de Bruijn indices (`Scopes.lean`)

```lean
inductive Bnd | fvar | abs | tvar | var | rgn | frame
abbrev Ctx := List Bnd                    -- most recent binder first

inductive In (b : Bnd) : Ctx → Type       -- de Bruijn index to a binder of sort b
  | here  : In b (b :: Γ)
  | there : In b Γ → In b (c :: Γ)

inductive TVar : Ctx → Type               -- term variables: top frame only
  | here    : TVar (.var :: Γ)
  | skipVar : TVar Γ → TVar (.var :: Γ)
  | skipRgn : TVar Γ → TVar (.rgn :: Γ)   -- no way to skip a `.frame`
```

* An index can never be out of range, and it can never point at a binder of the wrong sort.
* `TVar` cannot cross a frame boundary. A term inside `framed` therefore cannot
  name a caller's variable, while regions, loans and pointers (`In`) can.
* There are two kinds of renamings. `TRen` acts on indices of every sort and is
  used for types and values. `Ren` additionally maps term variables and is used
  for terms. Weakening a term by a `.frame` is impossible by construction,
  because the new frame hides the term's variables.
* **Why a list of sorts rather than a record of counts?** With
  `⟨nφ, nϱ, nα, nr, nx⟩` you get `Fin` arithmetic, but you cannot express:
  - which frame a variable lives in, which `framed` and loans need;
  - the interleaving of variables and regions in a frame, which a stack frame
    has;
  - the fact that a closure body's scope is "its parameters, then its captured
    frame, then a frame boundary".

  The list is also exactly the erasure of the stack typing and of the stack (§3),
  so the same index works for all three.

### 2.2 Types (`Types.lean`)

```lean
inductive Region (Γ : Ctx) | abs (i : In .abs Γ) | conc (r : In .rgn Γ)

mutual
inductive Ty : Ctx → Type                 -- τ^SI
  | base | tvar (α : In .tvar Γ) | ref (ρ : Region Γ) (ω : Own) (τ : XTy Γ)
  | array (τ : Ty Γ) (n : Nat) | tuple (k : Nat) (τs : Fin k → Ty Γ) | sum (τ₁ τ₂ : Ty Γ)
  | fn (b : Binders) (k : Nat) (params : Fin k → Ty (b.ctx ++ Γ)) (ret : Ty (b.ctx ++ Γ))
       (env : FrameExpr (b.ctx ++ Γ)) (bounds : List (Fin b.nϱ × Fin b.nϱ))
inductive XTy : Ctx → Type | sized (τ : Ty Γ) | slice (τ : Ty Γ)      -- τ^XI
inductive FrameExpr : Ctx → Type
  | var (φ : In .fvar Γ) | frame (f : Ctx) (Φ : FrameTy (f ++ .frame :: Γ) f)
inductive FrameTy : Ctx → Ctx → Type      -- only .var/.rgn entries can be built
  | nil | var (τ : Ty Γ) (Φ : FrameTy Γ f) | rgn (loans : List (Loan Γ)) (Φ : FrameTy Γ f)
end
inductive MTy (Γ : Ctx) | init (τ : Ty Γ) | dead (τ : Ty Γ) | tuple (k) (τs : Fin k → MTy Γ)  -- τ^SX
```

* The binders of a function type extend the scope (`b.ctx ++ Γ`). Its bounds
  can only name its own abstract regions.
* `letrgn` binds a `.rgn`. The three region forms `abs`/`bound`/`conc` collapse
  to two, and *opening* (`openRgns` with stack levels) disappears. `T-LetRegion`
  types the body in the extended scope, as `T-Let` does.
* Sorts become families, so these are no longer expressible:
  - an array of slices, e.g. `[[τ]; n]`;
  - a dead `let` annotation;
  - a slice as a closure parameter.

  The stack typing stores `MTy`, the only place where dead and partially moved
  types belong.

  Caveat: as in the paper's grammar, `MTy` has two representations of a fully
  initialized tuple, `init (tuple …)` and `tuple (init …)`. Either normalize
  (`MTy.tuple` only when some component is not `init`) or compare up to an
  equivalence.
* **Why `Ty` shares the scope of terms, and not only `Δ`:** concrete regions are
  bound by terms (`letrgn`) and live on the stack, and closure types carry loan
  sets (`r ↦ {ω p}`) that name stack places. A `Ty` indexed only by `Δ` would
  need the levels back.

### 2.3 Terms, values, functions (`Terms.lean`)

```lean
mutual
inductive Term : Ctx → Type
  | val (v : Value Γ) | place (p : PlaceExpr Γ)            -- PlaceExpr root : TVar Γ
  | borrow (r : In .rgn Γ) (ω : Own) (p : PlaceExpr Γ)      -- concrete regions only
  | letrgn (e : Term (.rgn :: Γ))
  | letE (τ : Ty Γ) (e₁ : Term Γ) (e₂ : Term (.var :: Γ))
  | closure (k : Nat) (params : Fin k → Ty Γ) (ret : Ty Γ) (body : Term (vars k ++ Γ))
  | app (f : Term Γ) (b : Binders) (Φs : Fin b.nφ → FrameExpr Γ) (ρs : Fin b.nϱ → Region Γ)
        (τs : Fin b.nα → Ty Γ) (k : Nat) (args : Fin k → Term Γ)
  | framed (f : Ctx) (e : Term (f ++ .frame :: Γ))           -- runtime
  | shift (e : Term (.var :: Γ)) | shiftRgn (e : Term (.rgn :: Γ))   -- runtime
  | …                                                         -- the remaining constructors as today
inductive Value : Ctx → Type
  | ptr (R : Referent Γ)                                      -- root : In .var Γ
  | closure (f : Ctx) (env : Env Γ f) (k : Nat) (params : Fin k → Ty Γ) (ret : Ty Γ)
            (body : Term (vars k ++ (f ++ .frame :: Γ)))
  | …
inductive Env : Ctx → Ctx → Type                              -- captured frame of shape f
end

structure FnDef where
  binders : Binders; k : Nat
  params : Fin k → Ty binders.ctx; ret : Ty binders.ctx
  bounds : List (Fin binders.nϱ × Fin binders.nϱ)
  body : Term (vars k ++ .frame :: binders.ctx)
```

* **Arity as data.** Components are `Fin k → _`, which removes the length side
  conditions and the auxiliary `Terms`. (`List (Term Γ)` is still rejected by
  the kernel as a nested inductive with an index. A length-indexed mutual list
  `Terms Γ k` is the alternative if `DecidableEq` deriving or `List` API reuse
  matter more than brevity.)
* **Calls carry their binders.** `T-AppFunction` then matches `app f b …`
  against `fn b …` with the same `b`, with no length premises.
* **Runtime forms have exact scopes.** `framed f e` says which frame it pushes;
  `shift` and `shiftRgn` pop exactly the binder their body has.
* **Values are no longer closed.** They live in the scope of the stack, so
  pointers are typed indices, and a closure value's body is scoped by its
  captured frame. `TRen.enterFrame` is the one renaming used to go under a
  `framed` or into a closure body.
* All the operations are total and structurally recursive: renaming
  (`Term.rename`, `Ty.rename`, …) and strengthening
  (`Strengthening.lean`, which returns `Option`).

---

## 3. Which contexts?

### 3.1 Not intrinsic typing

You could index terms by the typing context (`Term Γ τ` or
`Term Δ Γ Θ τ Γ'`). This proposal argues against it:

* **Typing is flow-sensitive.** A term has an input and an output stack typing,
  and the output depends on the typing derivation (`T-Drop`, rewriting,
  `T-Branch` union, `T-Let`'s garbage collection of loans). A term would have to
  fix one derivation.
* **Side conditions are propositions on `Γ`.** These include ownership safety,
  `NotInClosure`, `RgnUniqueTo` and outlives. They would become proof fields of
  constructors, and every operation on terms would have to transport them.
* **Evaluation would have to preserve types by construction.** The project
  proves that it does not, for the paper's rules (`not_preservation`,
  `not_type_safety`, `not_type_safety_closure`, `not_preservationReach`). The
  step function of an intrinsically typed Oxide could not be defined until the
  type system is repaired. A well-scoped syntax lets you state, test and refute
  candidate repairs.

### 3.2 Scope-indexed contexts (`Contexts.lean`)

What *is* worth indexing is the contexts, by the same scope as the term:

```lean
inductive Slots (Γ : Ctx) : Ctx → Type    -- runtime stack: slots of shape S, values in scope Γ
  | nil | var (v : Value Γ) (σ : Slots Γ S) | rgn (σ : Slots Γ S) | frame (σ : Slots Γ S)
abbrev Stack (S : Ctx) := Slots S S

inductive SlotTys (Γ : Ctx) : Ctx → Type  -- stack typing, with Δ folded in
  | nil | var (τ : MTy Γ) … | rgn (loans : List (Loan Γ)) … | frame … | fvar … | abs … | tvar …
structure StackTy (S : Ctx) where
  slots : SlotTys S S
  outlives : List (In .abs S × In .abs S)

Slots.get    : Slots Γ S → In .var S → Value Γ              -- total
SlotTys.varTy : SlotTys Γ S → In .var S → MTy Γ             -- total
SlotTys.loans : SlotTys Γ S → In .rgn S → List (Loan Γ)     -- total
```

* **One telescope for `Δ` and `Γ`.** Type-level binders are entries of the stack
  typing, and the outlives constraints refer to them by index.
* **Flat, not telescopic.** Every entry lives in the scope of the *whole*
  stack, because newer slots can legitimately be referenced by older ones:
  - `letrgn<r> { let x = …; &r x }` puts a loan to the newer `x` into the older
    region `r`;
  - an older variable can be assigned a pointer to a newer one.

  Consequences:
  - pushing weakens every stored value or type (`Stack.pushVar`);
  - popping *strengthens* them and may fail (`Stack.popVar`, `Stack.popFrame`).

### 3.3 Popping makes the counterexamples visible

`E-Framed` becomes `Stack.popFrame : Stack (f ++ .frame :: S) → Value (f ++ .frame :: S) → Option (Stack S × Value S)`.
The configuration of `not_preservation`, `framed (ptr x)` with `x` in the popped
frame, now fails to pop (`framedPop_dangling`, proved by `rfl`); a value that does
not mention the frame pops fine (`framedPop_ok`). The level reuse behind the
closure counterexample cannot be represented at all.

The problem does not go away, though. It moves from *Preservation* to
*Progress*: `E-Framed` gets a premise, and the type system has to guarantee that
it holds. That is the `T-Framed`/closure-escape repair already identified in
`MISSING.md`. The difference is that Lean now forces the question to be answered.

The design raises one more question of the same kind, which this proposal has
not investigated. `T-Assign` gives the assigned place the type of the right-hand
side (`setPlaceTy π τ`), and `T-LetRegion` checks freshness of the popped region
only against the result type, not against the output stack typing. With a
scoped `StackTy`, popping the region forces a check that no remaining entry
mentions it. Whether today's rules guarantee this is unknown.

### 3.4 Runtime configurations

The term in focus is at the *base* scope `S₀`, while the stack also contains
what its runtime forms (`shift`, `shiftRgn`, `framed`) have pushed. There are
two options:

* **R1 (paper-faithful, recommended first).** Keep the runtime forms in `Term`.
  A configuration is `Σ S₀ (e : Term S₀), Stack (e.ext ++ S₀)`, where `e.ext` is
  computed along the evaluation spine:
  - `ext (shift e) = ext e ++ [.var]`;
  - `ext (framed f e) = ext e ++ f ++ [.frame]`;
  - `ext (seq e₁ e₂) = ext e₁`, and similarly for the other evaluation positions.

  The paper's lemmas about `framed` keep their shape.
* **R2 (CK machine).** Remove the runtime forms from source terms. A
  configuration is a stack `Stack S`, a continuation `Cont S S₀` whose frames
  record the scope changes, and a focus `Term S`. This is fully correct by
  construction, but it departs from the paper's small-step presentation and
  changes every metatheory statement.

---

## 4. Alternatives considered

| Option | By construction? | Cost |
| --- | --- | --- |
| A. Status quo (`Term n`, raw `Nat` elsewhere) | term variables only | — |
| B. Record of counts `⟨nφ, nϱ, nα, nr, nx⟩` with `Fin` | indices in range, but frame membership and interleaving cannot be expressed | low |
| **C. List of sorts + typed indices (this proposal)** | all binders, frames, contexts | medium/high (rewrite of the existing development) |
| D. Raw syntax + `WellScoped` predicate, bundled as a subtype | only through proofs | low; weakening is the identity on raw terms |
| E. Intrinsically typed terms | everything | not definable while Preservation fails (§3.1) |

D is a reasonable *stepping stone*. Prove a `WellScoped` predicate for the
current syntax first, and use it to state the scoping invariants the metatheory
needs. Pattern matching then still exposes raw `Nat`s.

### 4.1 Costs and risks of C

* **Weakening is no longer free.** Every push renames the stack typing. You need
  the functor laws (`rename_id`, `rename_comp`, `prename` after `rename`);
  structure-wise these are routine, and `funext` handles the `Fin k → _` fields.
* **Dependent pattern matching in proofs.** `cases` on `In b (c :: Γ)` with
  index equations sometimes needs `generalize`. Keep the scope arguments of
  lemmas as variables.
* **Equalities between scopes.** `(xs ++ ys) ++ Γ` and `xs ++ (ys ++ Γ)` are not
  definitionally equal for variable `xs`. The prototype avoids casts by lifting
  in stages (`(ρ.enterFrame.liftN f).liftN (vars k)`). Keep scopes in
  right-nested form.
* **`DecidableEq` and `Repr`** cannot be derived for families with
  `Fin k → _` fields. Write them by hand, or use length-indexed lists.
* **The `[OXIDE| … ]` elaborator** must turn names into typed indices. It already
  resolves names to positions, so it now emits `In`/`TVar` constructor chains
  instead.
* **The existing proofs have to be ported:** progress (about 1,400 lines), the
  counterexamples and the supporting lemmas.

### 4.2 Smaller, independent improvements

Each of these is worth doing even without C:

* `params : Vector Ty k`, or `body : Term (n + params.length)` as `FnDef` already
  does;
* `app` carrying its binder counts;
* `borrow` taking a concrete region;
* `framed` taking the frame shape;
* separate `Ty`/`XTy`/`MTy` families.

### 4.3 Indexing by `Σ`

Function names could become indices into a signature `Sig := List FnSig`, so
that `Value.fn` can only name existing functions. Functions are mutually
recursive and `Σ` is checked once (`⊢ Σ`). That means a signature-indexed term
type gains little over a single `GlobalEnv.lookup` premise, and it complicates
every statement. Not recommended now.

---

## 5. Suggested migration plan

1. **Syntax.** Replace `Syntax/{Places,Types,Terms}` with the scoped families.
   Keep `abbrev Program := Term []`. Port `[OXIDE| … ]` and `Examples.lean`.
2. **Contexts.** Use the scoped stack typing (with `Δ` folded in) and the scoped
   stack. Remove the `Option`-returning lookups (`idxToLevel`, `varTy`, `loans?`)
   and the region opening (`openRgns`, `closeRgns`, `newLevels`).
3. **Statics.** Port the typing rules. The `SI`/`XI`/`SX` and length premises
   disappear. Decide how `T-LetRegion` and `T-Framed` strengthen the output
   stack typing (§3.3).
4. **Dynamics.** Choose R1 or R2. `E-Framed`, `E-Shift` and `E-ShiftRgn` use
   `popFrame`, `popVar` and `popRgn`.
5. **Metatheory.** Prove the renaming and strengthening laws. Re-prove canonical
   forms and progress. Re-check the counterexamples: some become unstatable
   (§3.3), and `not_type_safety` (the move/copy one) is unaffected by scoping.
   Then attempt a corrected preservation proof.

## 6. Open questions for you

* R1 (keep `framed`/`shift` in terms, paper-faithful) or R2 (CK machine)?
* `Fin k → _` (short, no deriving) or length-indexed lists (more boilerplate,
  deriving and `List` API)?
* Should the type-sort split (`Ty`/`XTy`/`MTy`) be part of the first step, or
  come later?
* Should the migration replace the current development, or live beside it until
  progress is re-proved?

## 7. What the prototype contains

| File | Content |
| --- | --- |
| `Scopes.lean` | `Bnd`, `Ctx`, `In`, `TVar`, renamings `TRen`/`Ren`, lifting, weakening, `enterFrame` |
| `Types.lean` | `Region`, `Loan`, `Ty`/`XTy`/`FrameExpr`/`FrameTy`, `MTy`, renaming |
| `Terms.lean` | `PlaceExpr`, `Referent`, `Term`/`Value`/`Env`, `Program`, renaming, `FnDef` |
| `Strengthening.lean` | partial renamings (`PRen`, `PRenT`) and `prename` for all syntax |
| `Contexts.lean` | `Stack`, `StackTy` (with `Δ`), total lookups, `pushVar`/`pushRgn`/`popVar`/`popFrame`, example program `exLet`, and the theorems `framedPop_dangling` / `framedPop_ok` |

Not in the prototype:
* type-level substitution (instantiating `FnDef.body` at a call), which is
  routine given `rename`;
* the renaming laws;
* typing rules, dynamics and notation.
