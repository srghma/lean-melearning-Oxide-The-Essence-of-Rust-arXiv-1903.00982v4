# Making the grammar more correct by construction

This note lists the places where the current grammar can still express syntax
that the paper's grammar rules out, or syntax that only a typing rule or an
invariant rejects. For each one it gives a fix. The witnesses and prototypes
mentioned below are in `Proposal/CorrectByConstruction.lean`. That file builds and
contains no `sorry`, and it does not change the grammar the rest of the
development uses.

Many things are already correct by construction: scopes, top-frame variables,
sorts of types, move vs. copy, places vs. place expressions, closure scopes,
typed paths, `MTy` indexed by its declared type, global functions by signature,
`Prim b` with `UInt32`, and arities as `Fin k → _`. The sections below are what
remains, most valuable first.

The general rule behind all of them is this: **every invariant that is (a) about
syntax alone and (b) preserved by renaming and substitution belongs in the type.
Everything that depends on the stack typing belongs in the typing rules.**

---

## 1. Keep runtime values out of source programs

**Problem.** `Term.val (v : Value sig Γ)` accepts every value, so a source program
can contain `dead`, `ptr 𝓡`, slices and closure values. These are runtime-only
forms in the paper. The witnesses `srcWithPtr` (a raw pointer to a local variable,
which bypasses `&r ω p` and the loans) and `srcWithDead` type check today.

**Why it is cheap to fix here.** The machine never substitutes values into terms,
because variables are stack slots. Values only enter terms because the machine's
*focus* is a term. Splitting the focus, as a CEK machine does, removes the need
for `Term.val` to hold runtime values:

```lean
inductive SrcVal (sig : Sig) where            -- what a programmer can write
  | prim {b} (c : Prim b) | fn (f : FnIdx sig)

-- in `Term`:   | const (c : SrcVal sig) : Term sig Γ     (replaces `val`)

inductive Focus (sig : Sig) (S : Ctx) where
  | eval (e : Term sig S)      -- evaluate a term
  | ret  (v : Value sig S)     -- return a value to the continuation
structure Config (sig) where S : Ctx; stack : Stack sig S; focus : Focus sig S; cont : Cont sig S
```

The `E-*` rules that now produce `.val v` produce `.ret v`. The only rule that puts
a value *back into* a term is the `for` unrolling (`.forE (.val (.ptr …)) e₂`, in
`Machine.lean`). It becomes a continuation frame
`Cont.forIter (R : Referent S) (start len : Nat) (e₂ : Term sig (.var :: S))`.
Typing splits the same way: `T-Val` becomes a rule for `const`, and the value
judgment is used for `Focus.ret`.

An alternative is to index `Term`/`Value` by a `Phase := src | rt` and give
runtime-only constructors the index `rt`. That is more general, but every function
on terms then has to be phase-polymorphic. The `Focus` split is the smaller change.

## 2. Split values by sort, as types already are

**Problem.** Types are split into `Ty` (sized), `XTy` (maybe unsized) and `MTy`
(maybe dead), but there is a single `Value`. So a slice can be a tuple component
(`tupleOfSlice`), `dead` can be the result of an expression, and the typing has to
reject these.

**Fix** (prototype `SVal`/`XVal`/`MVal`):

| type sort | value family | holds |
| --- | --- | --- |
| `Ty`  | `SVal`  | constants, functions, tuples, arrays, `ptr`, closures, injections |
| `XTy` | `XVal`  | `sized v` or `slice k vs`: what a pointer designates |
| `MTy` | `MVal`  | `init v`, `dead`, or a tuple of `MVal`: what a stack slot holds |

Then:
- `Stack` slots hold `MVal`;
- `σ.read R` returns `XVal`;
- `Focus.ret` and `Cont`'s `done` vectors hold `SVal`;
- the value judgments line up one-to-one with the type sorts (`val`/`xval`/`mval`
  in `Typing.lean`).

`MVal` can be indexed by the declared type like `MTy.Of`, so that a slot's value
and its typing have the same shape.

## 3. Captures: an order-preserving selection of the current frame

**Problem.** `Cap Γ f` is a list of `TVar`s and regions, so it can name the same
variable twice (`dupCap`, `dupCap_not_nodup`). `Cap.frameTy` then gives *both*
copies the variable's type, and `killNC` kills the original only once. For a
non-copyable variable such as a `&uniq` reference, the closure's frame would hold
two copies of one owned value.

This did let two unique references alias inside a closure body: see
`Metatheory/Regressions/DuplicateCaptures.lean`, where a closure body taking two
simultaneously live unique borrows of one location type checks (`dcBody_typed`).
The concrete syntax never produces duplicate captures, but the abstract syntax
allows them.

**Status: fixed by a typing premise.** `T-Closure` now requires `Cap.Nodup`
(every variable and region captured at most once). The thinning below was not
adopted: `Cap.rename` and `Cap.subst` act through arbitrary functions on term
variables (`Ren.tvar`, `Sub.tv`), which need not be injective or order
preserving, so a thinning is not stable under them. By the rule of thumb of this
note, the condition therefore belongs to the typing rules.

**Fix** (prototype `TopSel`, theorem `TopSel.toCap_vars_nodup`): captures are a
thinning of the top frame, with constructors `keepVar`/`keepRgn`/`skipVar`/`skipRgn`
and no constructor that crosses a `.frame` or a type-level binder. Captures are
then in frame order and duplicate-free by construction. `Cap.inv` and `findVar`
become the thinning's inverse, with no "first match" choice. It is stable under
order-preserving injective renamings (such as weakenings), but not under the
arbitrary renamings the syntax currently allows.

## 4. Unique encoding of initialization states

**Problem.** `MTy.Of (.tuple k τs)` has two encodings of "fully initialized"
(`.init` and `.tuple fun _ => .init`), and the same holds for "dead" (`initPair_ne`).
`mkTuple` normalizes, but that is an invariant every update has to maintain.

**Fix** (prototype `MSt`): index the state by its `Kind` (`init | dead | mixed`).
The tuple constructor lists its fields' kinds and carries proofs that the tuple is
genuinely mixed (`∃ i, ks i ≠ .init` and `∃ i, ks i ≠ .dead`). The proofs are about
the *data* `ks`, so the inductive is accepted. Each type then has exactly one fully
initialized state and exactly one dead state (the `Subsingleton` instances), and
`MSt.mkTuple` becomes total and type-directed. `MTy.toTy?`, `full` and `allDead`
reduce to reading the kind index.

## 5. Make the coverage premise of closures syntactic

**Problem.** `T-Closure` needs `Inst.Covered`, a semantic condition ("θ survives
every strengthening that the closure type survives"). It is not decidable as
stated.

**Fix options:**
- *Decidable check (recommended).* Compute the free binders of the closure type
  (`Ty.fvs : Ty Γ → List (Σ b, In b Γ)`, an extension of the existing `Ty.frgns`).
  Then require `∀ e ∈ θ, fvs e ⊆ fvs (closureTy …)`, which `decide` can check.
  It is meant to replace `Covered`, but I have not proved the two equivalent.
- *Fully by construction* would make `o` the free-binder set of the closure's type.
  But `θ : Inst o Γ` has to stay a general substitution, because it must be closed
  under type substitution when a polymorphic body is instantiated. A thinning would
  break `Inst.subst`. So a syntactic check is the right level here.

## 6. Type-directed move/copy in the concrete syntax

The abstract syntax is right (`move π` vs `copy p`). The concrete notation still
picks one *syntactically*: a bare place becomes a move. So a program the paper
accepts, `let x : bool = true; x; if x {…}`, has to be written with `copy!(x)`.

Elaborate move/copy *by type*, as rustc does when it builds MIR. Add an
elaboration pass `Surface.Term → StackTy S → Option (Term sig S)`: a bare place of
copyable type becomes `copy`, otherwise `move`. The `[OXIDE| … ]` macro would emit
the surface term, and `rfl`/`decide` would run the elaborator. If you also add the
paper's premise `τ.copyable = false` to `T-Move`, every well-typed paper program
has exactly one well-typed marked version.

## 7. Smaller items

- **Redundant annotations on injections.** `Value.inl τ₁ τ₂ v` stores `τ₁`, which
  must be the type of `v`. In values (not terms), only the *other* side's type is
  needed (`inl (τ₂ : Ty Γ) v`), so the two cannot disagree.
- **Place-expression contexts.** `PCtx` is `List Nat × List (List Nat)`. Defining
  it as a structured inductive (`hole q | deref c q`) makes plugging a fold over
  the same shape as `PExpr`.
- **Index expressions.** `borrowIdx`/`borrowSlice`/`index` take arbitrary
  `Term`s for indices. A `u32` result is a typing fact and cannot be syntactic
  without intrinsic typing, so leave it as is.

## What should *not* be moved into the grammar

- **Array lengths vs. literal arity, projection indices in terms, ownership
  safety, loans.** All of them depend on the stack typing, which changes as the
  program runs (moves, reborrows). Encoding them in the syntax would make terms
  intrinsically typed. Renaming, strengthening and the machine's frame pops would
  then all need typing proofs. The current split (syntax indexed by *scope*,
  typing as a relation) is the right line.
- **Cost of each step.** Every `Fin k → _` or indexed field removes derived
  `DecidableEq` and makes renaming lemmas heavier. Items 1, 3 and 5 have the best
  ratio of benefit to cost. Item 1 also shrinks the machine (no runtime forms in
  terms), and item 3 closes a suspected hole.
