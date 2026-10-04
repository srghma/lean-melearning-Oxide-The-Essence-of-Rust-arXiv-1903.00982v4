# How our grammar differs from the paper's

This file compares the scope-indexed Lean grammar with the paper's grammar
(`essence-full.tex`, `formalization.tex`, `full-lang.tex` and the macro files
`oxide/*.sty`). For the results and for what is not formalized, see `README.md`
and `MISSING.md`.

## Names, binders and scoping

| Paper | Lean | Comment |
| --- | --- | --- |
| Named variables `x` | `TVar Γ`: a typed index into the current frame | It cannot cross a frame boundary, so a function body cannot name its caller's variables. |
| `letrgn<r> { e }` binds a named concrete region | `Term.letrgn (e : Term (.rgn :: Γ))` | The region is a binder of the scope. |
| Regions `ρ ::= ϱ \| r` | `Region.abs (i : In .abs Γ) \| Region.conc (r : In .rgn Γ)` | Same two forms as the paper. No locally nameless opening. |
| Named `α`, `φ`, `ϱ` in signatures | binders of the scope, `Binders.ctx = ᾱ ++ ϱ̄ ++ φ̄` | `Ty.fn b …` binds `b.ctx` in its parameters, result and environment. |
| Type environment `Δ` | entries `.fvar`/`.abs`/`.tvar` of the stack typing, plus `StackTy.outlives : List (In .abs S × In .abs S)` | One telescope for `Δ` and `Γ`. |
| Loans `ω p`, places `π`, referents rooted at a name | rooted at `In .var Γ` | Can point into older frames. Always in range. |
| Frame typing `Φ` | `FrameTy Γ f`: one entry per binder of the frame shape `f` | Only variable and region entries can be built. |
| Stack `σ` of frames | `Stack S = Slots S S`, flat, with region markers and frame boundaries | Every value lives in the scope of the whole stack. |

## Expressions

| Paper | Lean | Comment |
| --- | --- | --- |
| One expression grammar; values are a sub-grammar of runtime expressions | `Value Γ` is separate, embedded by `Term.val` | |
| `&r ω p`: concrete regions only | `Term.borrow (r : In .rgn Γ) …` | Enforced by the syntax. |
| `let x : τ^SI`, closure parameters `τ^SI`, `Left::<τ^SI, τ^SI>` | `Ty Γ` | `Ty` only contains sized initialized types. |
| `\|x₁:τ₁, …, xₖ:τₖ\| → τ_r { e }` | `Term.closure k (params : Fin k → Ty Γ) ret (body : Term (vars k ++ Γ))` | Parameter `i` is the `i`-th most recent binder. |
| `e_f::<Φ̄, ρ̄, τ̄>(e₁, …, eₙ)` | `Term.app f b (Φs : Fin b.nφ → _) (ρs : Fin b.nϱ → _) (τs : Fin b.nα → _) k (args : Fin k → _)` | The arities match the binders by construction. |
| `(e₁, …, eₙ)`, `[e₁, …, eₙ]` | `Term.tuple k (es : Fin k → Term Γ)`, `Term.array k es` | |
| Runtime forms `framed e`, `shift e`, `shiftprov e` | none | The machine's continuation frames `popFrame k f`, `popVar` and `popRgn` take their place. |

## Values

| Paper | Lean | Comment |
| --- | --- | --- |
| `v ::= c \| f \| dead \| (v̄) \| [v̄] \| \|v̄\| \| ptr 𝓡 \| ⟨ς, closure⟩` | the same, **plus `inl`/`inr`** | The paper's value grammar leaves out injections, but `E-Match*` needs them. |
| Closure value `⟨ς, \|x̄:τ̄\| → τ { e }⟩` | `Value.closure f (env : Env Γ f) k params ret (body : Term (vars k ++ (f ++ .frame :: Γ)))` | `f` is the shape of the captured frame. |
| `ptr 𝓡` | `Value.ptr (R : Referent Γ)` | A typed index into the stack. |

## Types

| Paper | Lean | Comment |
| --- | --- | --- |
| Sorts `τ^SI`, `τ^XI`, `τ^SD`, `τ^SX` | separate families `Ty` (SI), `XTy` (XI), `MTy` (SX, which includes SD) | Ill-sorted types cannot be written. |
| `∀<φ̄, ϱ̄, ᾱ>(τ̄) →^Φ τ_r where ϱ₁ : ϱ₂` | `Ty.fn b k params ret env (bounds : List (Fin b.nϱ × Fin b.nϱ))` | A closure type is `Ty.fn {} …` (`Ty.closure`). |
| `Φ ::= φ \| Φ_frame` | `FrameExpr.var (In .fvar Γ) \| FrameExpr.frame f (FrameTy (f ++ .frame :: Γ) f)` | The types of a literal frame live in the frame's own scope. |
| `u32` | `Ty.u32`, with values in `Nat` | No overflow. The language has no arithmetic. |

## Referents and slices

| Paper | Lean |
| --- | --- |
| `𝓡[n₁..n₂]` is inclusive | half-open `[n₁, n₂)`, in `RStep.slice` and in the concrete syntax |
| `WF-RefIndexSlice`/`WF-RefSliceSlice` have no bound check | bound check against the designated slice |

## Evaluation contexts

Evaluation contexts are the machine's continuation frames (`Cont`):
- `while` unfolds directly;
- `for x in E { e }` and `[v̄, E, ê]` are included, as in the tech-report grammar;
- `letrgn` pushes a region marker together with a `popRgn` frame.

## Judgments (presentation only)

The typing judgments are one inductive family, `Typing`, indexed by `TyJ`. It
covers expressions, argument lists, values, maybe-unsized values, maybe-dead
values, value lists and captured environments. Outlives (`OutlivesJ`) and
rewriting (`RewriteJ`) are handled the same way. Continuations get their own
judgment, `ContOK`.
