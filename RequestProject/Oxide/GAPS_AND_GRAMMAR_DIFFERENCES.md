# Oxide formalization: what is missing, and how our grammar differs from the paper's

This compares the Lean development in this directory with the paper sources
(`essence-full.tex`, which redefines some grammars "for formatting reasons",
`formalization.tex`, `full-lang.tex` and the macro files `oxide/*.sty`).
The project builds (`lake build`) without `sorry`.

## 1. Status of the remaining items

| Item | Status |
| --- | --- |
| **Type safety** | **Refuted.** `not_type_safety` (`Metatheory/Counterexamples/TypeSafety.lean`): `let x : bool = true; x; if x { () } else { () }` is well typed, but `E-Move` may be applied to the copyable `x` (the paper's `E-Move` has no copyability side condition), after which the `if` is stuck on `dead`. `not_type_safety_closure` (`Metatheory/Counterexamples/Closure.lean`) is independent of `E-Move`: a closure borrows its copy of a captured variable into an outer region and returns the pointer, which dangles once the closure's frame is popped (with de Bruijn levels it then designates a later variable). The statement `type_safety` is commented out and replaced by `type_safety_false` (`Safety.lean`). |
| **A corrected preservation lemma** | The suggested repair "restrict to configurations reachable from a closed program run on the empty stack" is stated as `PreservationReach` and **refuted** (`not_preservationReach`, `Metatheory/Counterexamples/Reachability.lean`): it would make every reachable configuration well typed (`ReachableTyped`), which together with `progress` gives type safety. The move counterexample contains no `framed`, so an extra condition on `T-Framed` alone cannot repair preservation either. No corrected system or corrected preservation theorem is proved; the README sketches what a repair has to address. |
| **The paper's supporting lemmas** (`proofs.tex`) | Partly formalized (`Metatheory/SupportingLemmas.lean`, besides the progress lemmas in `Metatheory/Progress/*.lean`): popping a frame, "value typing fixed on output environments", "values change environments in limited ways", type computation and referent well-formedness preserved under region rewriting, outlives and garbage collection of loans (these only change loan sets), and under well-typed extensions. The lemmas about ownership safety, value typing and stack validity under rewriting, extension and assignment are not formalized: they are steps of the preservation proof, and preservation fails. |
| **`E-Closure` marking moved captures dead at runtime** | Not modelled. The paper's `free-nc-vars_σ(e)` is "the variables bound to values that are non-copyable", but non-copyability is a property of types that runtime values do not determine (a pointer does not record whether it is shared or unique). As with `E-Move`, marking variables dead without type information would let well-typed programs get stuck. `T-Closure` marks the captures dead statically. |
| **`E-Function` / function values `⟨•, fn …⟩`** | Not modelled, by design: a global function name `f` is a value (`Value.fn f`) and `E-AppFunction` looks it up in `Σ`. The paper's main dynamics figure (`full-lang.tex`) does not use `E-Function` either. |
| **Concrete syntax `[OXIDE\| … ]`** | Completed. Calls take frame arguments (`` f::<@φ, @{x : u32, `r ↦ {}}, `a; τ>(…) ``); function types have quantifiers, a captured environment and bounds (`` fn<@φ, `a, `b; T>(τ̄)[@φ] -> τ where `a : `b ``); `[OXIDE_FN\| … ]` binds frame variables (`` fn f<@φ, `a; T>(…) ``); there are 1-tuples `(e,)`/`(τ,)`, dead types `τ†` and the runtime forms `framed![x, …] { e }`, `shift! x { e }`, `shiftprov! { e }`, `ptr!(ℓ .n [i] [i..j])`, `dead!`, `val!(v)` and closure values `` closure![a = v, … \| `r] \|x : τ\| -> τ { e } ``. Region entries of concrete frames have empty loan sets (loans refer to absolute places). |
| **Struct/enum/pattern extensions** (`T-TupleStruct`, `WF-RecordStruct`, …) | Not formalized. They exist in the `.sty` macros but are not part of the language presented in the paper (they are marked `TODO` there). The same goes for the stand-alone `T-GarbageCollectLoans` rule. Garbage collection of loans happens only where the paper's figures use it, through `gc-loans` in `T-Seq`/`T-Let`. |
| "Tested Semantics" section (testing against `rustc`) | Out of scope. |

## 2. Grammar differences (paper vs. Lean)

### Names, binders and scoping

| Paper | Lean | Comment |
| --- | --- | --- |
| Variables `x` (named) | de Bruijn indices: `Term n`, `PlaceExpr n` with `root : Fin n` | You asked for this. `Term 0` means closed. |
| `letrgn<r> { e }` binds a named concrete region `r` | `Term.letrgn e`, and `e` refers to the region as `Region.bound 0` | Nameless. |
| Regions `ρ ::= ϱ \| r` | `Region.abs i \| Region.bound i \| Region.conc ℓ` | There is a third form. `bound i` is a syntactic binder occurrence. `conc ℓ` is an opened region, identified by its stack-typing level (locally nameless style). |
| Type variables `α`, frame variables `φ`, abstract regions `ϱ` (named) | de Bruijn indices, with one index space per sort | `Ty.fn nφ nϱ nα …` only records how many binders of each sort there are. |
| Type environment `Δ`: an ordered list of `α : TYPE`, `ϱ : RGN`, `φ : FRM`, `ϱ :> ϱ'` | `TyEnv`: three counts plus a list of outlives pairs | Kinds are implicit. |
| Loans `ω p`, places `π = x.q`, referents rooted at a name `x` | Rooted at absolute de Bruijn **levels** (`APlaceExpr`, `APlace`, `Referent`) | Levels stay valid when the stack grows or shrinks above them. |
| Frame typing `Φ ::= • \| Φ, x : τ^SX \| Φ, r ↦ {ℓ̄}` | `List FrameEntry` with `var τ \| rgn loans`, most recent first | Nameless. |
| Stack frame `ς ::= • \| ς, x ↦ v` | `List StackEntry` with `val v \| rgn` | We add **region markers** to runtime frames, so that region levels in the stack and in the stack typing line up. |

### Expressions

| Paper | Lean | Comment |
| --- | --- | --- |
| A single expression grammar; values are a sub-grammar of runtime expressions | `Value` is a separate type, embedded into terms by `Term.val` | Constants `()`, `n`, `true`, `false` and function names `f` are written as values. |
| `&r ω p` etc.: only **concrete** regions `r` | `Term.borrow (r : Region) …`: any region is allowed syntactically | Typing only accepts `Region.conc` (`T-Borrow*`). |
| `let x : τ^SI = e₁; e₂`, closure parameters `x : τ^SI`, `Left::<τ^SI, τ^SI>` | `Ty` everywhere | The sort restrictions are premises of the typing rules (`Ty.SI`, …), not part of the syntax. |
| `\|x₁:τ₁, …, xₖ:τₖ\| → τ_r { e }` | `Term.closure k params ret (body : Term (n+k))` | `k` is stored separately. Typing requires `params.length = k`. |
| `e_f::<Φ̄, ρ̄, τ̄>(e₁, …, eₙ)` | `Term.app f envs rgns tys (args : Terms n)` | `Terms n` is an auxiliary list type, because Lean does not accept nested `List (Term n)` here. |
| Runtime forms: `framed e`, `shift e`, `\|v̄\|`, `dead`, `ptr 𝓡`, `⟨ς, closure⟩` (`shiftprov` appears only in evaluation contexts) | `framed m e` (`e : Term m`), `shift (e : Term (n+1))`, `shiftRgn e`, and runtime values through `Term.val` | `framed` records how many variables the new frame has. `shiftRgn` (= `shiftprov`) is a full term with its own reduction rule (`Step.shiftRgn`). |
| Expressions `ê` in evaluation contexts (`noseqexpr`) | ordinary `Term n` | |

### Values

| Paper | Lean | Comment |
| --- | --- | --- |
| `v ::= c \| f \| dead \| (v̄) \| [v̄] \| \|v̄\| \| ptr 𝓡 \| ⟨ς, \|x̄:τ̄\| → τ { e }⟩` | the same, **plus `inl τ₁ τ₂ v` and `inr τ₁ τ₂ v`** | The paper's value grammar leaves out injections, but `E-MatchLeft`/`E-MatchRight` need them. |
| Closure value `⟨ς, …⟩` (named frame) | `Value.closure m k q frame params ret body` | `m` captured values, `k` parameters, `q` captured regions (bound in the body). |
| `(e₁, …, eₙ)` with value components is already a value | `Term.tuple (values)` takes one administrative step (`Step.tupleVal`) to become `Term.val (.tuple …)` | The same holds for arrays and injections. This comes from keeping `Value` separate. |

### Types

| Paper | Lean | Comment |
| --- | --- | --- |
| Separate sorts `τ^SI`, `τ^XI ::= τ^SI \| [τ^SI]`, `τ^SD ::= τ^SI† \| (τ^SD, …)`, `τ^SX`, `τ` | One `Ty` datatype; the sorts are the predicates `Ty.SI`, `Ty.XI`, `Ty.SD`, `Ty.SX` | So `Ty` contains ill-sorted types such as `dead (slice _)` or `slice (slice _)`. The typing rules rule them out. |
| `∀<φ̄, ϱ̄, ᾱ>(τ̄) →^Φ τ_r where ϱ₁ : ϱ₂` | `Ty.fn nφ nϱ nα params ret env bounds` | `bounds` are pairs of abstract-region indices. A closure type is `Ty.fn 0 0 0 … []`. |
| Frame expression `Φ ::= φ \| Φ_frame` | `FrameExpr.var i \| FrameExpr.frame entries` | In a captured frame inside a type, the frame's own regions are `Region.bound j`. |
| `u32` | `Ty.u32`, with values in `Nat` | No overflow; the language has no arithmetic anyway. |

### Referents and slices

| Paper | Lean |
| --- | --- |
| `𝓡[n₁..n₂]` is **inclusive** (`ER-SliceArray` yields `\|v_i, …, v_j\|`, `j-i+1` elements) | **half-open** `[n₁, n₂)`. This applies to `RStep.slice` and to the concrete syntax `&r ω p[e₁..e₂]`. |
| `WF-RefIndexSlice`/`WF-RefSliceSlice` have no bound check | adds a bound check against the designated slice (the progress proof needs it) |
| `T-BorrowSlice` only for slices | also accepts arrays |

### Evaluation contexts

* `essence-full.tex` lists `while e₁ { e₂ }` as an evaluation context, but it contains no hole. This looks like a typo in the paper. We have no `while` context, because `E-While` unfolds the loop directly.
* `essence-full.tex` leaves out the `for x in E { e }` and `[v̄, E, ê]` contexts. The tech-report grammar (`oxide-grammars.sty`, `full-lang.tex`) includes both, and so do we (`ECtx.forE`, `ECtx.array`).
* `letrgn<r> { E }`: the paper reduces *inside* `letrgn` and then applies `E-LetRegion : letrgn<r>{v} → v`. We instead step `letrgn e` at once to `shiftRgn e'`: this pushes a region marker and opens the binder at a fresh level. `shiftRgn v` then pops the marker. The context is `ECtx.shiftRgn`.

### Judgments (presentation only)

The expression, argument-list, value and value-list typing judgments are one inductive family `Typing` indexed by `TyJ`. Outlives (`OutlivesJ`) and rewriting (`RewriteJ`) are handled the same way. The paper's separate judgments are recovered as abbreviations (`HasType`, `HasTypeV`, …).
