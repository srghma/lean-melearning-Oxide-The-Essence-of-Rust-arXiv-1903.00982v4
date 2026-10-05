# How our grammar differs from the paper's

This file compares the scope-indexed Lean grammar with the paper's grammar
(`essence-full.tex`, `formalization.tex`, `full-lang.tex` and the macro files
`oxide/*.sty`). For the results and for what is not formalized, see `README.md`
and `MISSING.md`.

## Names, binders and scoping

| Paper | Lean | Comment |
| --- | --- | --- |
| Named variables `x` | `TVar Γ`: a typed index into the current frame | It cannot cross a frame boundary, so a function body cannot name its caller's variables. |
| `letrgn<r> { e }` binds a named concrete region | `Comp.letrgn (e : Term (.rgn :: Γ))` | The region is a binder of the scope. |
| Regions `ρ ::= ϱ \| r` | `Region.abs (i : In .abs Γ) \| Region.conc (r : In .rgn Γ)` | Same two forms as the paper. No locally nameless opening. |
| Named `α`, `φ`, `ϱ` in signatures | binders of the scope, `Binders.ctx = ᾱ ++ ϱ̄ ++ φ̄` | `Ty.fn b …` binds `b.ctx` in its parameters, result and environment. |
| Type environment `Δ` | entries `.fvar`/`.abs`/`.tvar` of the stack typing, plus `StackTy.outlives : List (In .abs S × In .abs S)` | One telescope for `Δ` and `Γ`. |
| Loans `ω p`, places `π`, referents rooted at a name | rooted at `In .var Γ` | Can point into older frames. Always in range. |
| Frame typing `Φ` | `FrameTy Γ f`: one entry per binder of the frame shape `f` | Only variable and region entries can be built. |
| Stack `σ` of frames | `Stack sig S = Slots sig S S`, flat, with region markers and frame boundaries | Every value lives in the scope of the whole stack; stacks only exist over runtime scopes (`Slots.runtime`). |
| Global environment `Σ` (list of named functions) | a signature `sig : Sig` indexing terms; `GlobalEnv sig` has one body per declared function | Function names are indices `FnIdx sig`; lookup is total. |
| Place expressions `p ::= x \| *p \| p.n` | `PExpr.place ⟨x, path⟩ \| PExpr.deref p path` | Grouped by dereferences; a place `π` is a root and a path. |

## Expressions

| Paper | Lean | Comment |
| --- | --- | --- |
| One expression grammar, subexpressions anywhere | **A-normal form**: atoms `Atom` (`val`, `move`, `copy`), computations `Comp` (one operation on atoms, or a control construct with term blocks) and terms `Term` (`letE τ c e`, `seq c e`, `ret c`) | Every operand is an atom and every intermediate result is named by a `let`. Control constructs are computations, so `let x : τ = if a { e₁ } else { e₂ }; e` is allowed (strict A-normal form would need join points). The condition of `while` is a term. |
| One expression grammar; values are a sub-grammar of runtime expressions | `Value Γ` is separate, embedded by `Atom.val` (`Term.val v` abbreviates `ret (atom (val v))`) | |
| `&r ω p`: concrete regions only | `Comp.borrow (r : In .rgn Γ) …` | Enforced by the syntax. |
| `&r ω p[e]`, `&r ω p[e₁..e₂]`, `p[e]`, `p := e` | `Comp.borrowIdx r ω p (a : Atom Γ)`, `Comp.borrowSlice r ω p a₁ a₂`, `Comp.index p a`, `Comp.assign p a` | Operands are atoms. |
| `if e₁ { e₂ } else { e₃ }`, `for x in e₁ { e₂ }`, `match e { … }` | `Comp.ite (a : Atom Γ) e₂ e₃`, `Comp.forE a e`, `Comp.matchE a e₁ e₂` | The scrutinee is an atom; the blocks are terms. |
| `let x : τ^SI`, closure parameters `τ^SI`, `Left::<τ^SI, τ^SI>` | `Ty Γ` | `Ty` only contains sized initialized types. |
| `\|x₁:τ₁, …, xₖ:τₖ\| → τ_r { e }` | `Comp.closure f (c : Cap Γ f) o (θ : Inst o Γ) k (params : Fin k → Ty o) ret (body : Term (vars k ++ (f ++ .frame :: o)))` | The body is written in its own scope: parameters (parameter `i` is the `i`-th most recent binder), captured frame `f` (listed by `c`), and outer binders `o` with entries `θ`. |
| A place used as an operand `p` | `Atom.move (π : TPlace Γ)` or `Atom.copy (p : PExpr Γ)` | Move or copy is explicit, as in Rust's MIR. |
| `e_f::<Φ̄, ρ̄, τ̄>(e₁, …, eₙ)` | `Comp.app (f : Atom Γ) b (θ : TArgs b Γ) k (args : Fin k → Atom Γ)` | `TArgs` bundles `Fin b.nφ → _`, `Fin b.nϱ → _`, `Fin b.nα → _`; the arities match the binders by construction. |
| `(e₁, …, eₙ)`, `[e₁, …, eₙ]` | `Comp.tuple k (as : Fin k → Atom Γ)`, `Comp.array k as` | |
| Runtime forms `framed e`, `shift e`, `shiftprov e` | none | The machine's continuation frames `popFrame k f`, `popVar` and `popRgn` take their place. |

## Values

| Paper | Lean | Comment |
| --- | --- | --- |
| `v ::= c \| f \| dead \| (v̄) \| [v̄] \| \|v̄\| \| ptr 𝓡 \| ⟨ς, closure⟩` | the same, **plus `inl`/`inr`** | The paper's value grammar leaves out injections, but `E-Match*` needs them. Constants are `Prim b`, indexed by their base type. |
| Closure value `⟨ς, \|x̄:τ̄\| → τ { e }⟩` | `Value.closure f (env : Env sig Γ f) o (θ : Inst o Γ) k params ret (body : Term sig (vars k ++ (f ++ .frame :: o)))` | `f` is the shape of the captured frame. |
| `ptr 𝓡` | `Value.ptr (R : Referent Γ)` | A typed index into the stack. |

## Types

| Paper | Lean | Comment |
| --- | --- | --- |
| Sorts `τ^SI`, `τ^XI`, `τ^SD`, `τ^SX` | separate families `Ty` (SI), `XTy` (XI), `MTy` (SX, which includes SD) | Ill-sorted types cannot be written. `MTy` is a declared type `τ` with a state `MTy.Of τ` (`init`, `dead`, or a tuple of field states). |
| `∀<φ̄, ϱ̄, ᾱ>(τ̄) →^Φ τ_r where ϱ₁ : ϱ₂` | `Ty.fn b k params ret env (bounds : List (Fin b.nϱ × Fin b.nϱ))` | A closure type is `Ty.fn {} …` (`Ty.closure`). |
| `Φ ::= φ \| Φ_frame` | `FrameExpr.var (In .fvar Γ) \| FrameExpr.frame f (FrameTy (f ++ .frame :: Γ) f)` | The types of a literal frame live in the frame's own scope. |
| `u32` | `Ty.u32`, with constants `Prim.num (n : UInt32)` | The language has no arithmetic. |

## Referents and slices

| Paper | Lean |
| --- | --- |
| `𝓡[n₁..n₂]` is inclusive | `Referent.slice R start len`; the concrete syntax `p[a₁..a₂]` is half-open `[a₁, a₂)` |
| `𝓡[n].q` | `Referent.index R n q` |
| `WF-RefIndexSlice`/`WF-RefSliceSlice` have no bound check | bound check against the designated slice |

## Evaluation contexts

Evaluation contexts are the machine's continuation frames (`Cont`). Since terms
are in A-normal form, operands are atoms, evaluated in one go when their
computation reduces (`EvalAtom`, `EvalAtoms`), so no frame for a partially
evaluated operand is needed. The frames are:
- `let x : τ = □; e` and `□; e`;
- `while □ { e₂ }`, holding the condition being evaluated;
- `popVar`, `popRgn` and `popFrame k f` (`letrgn` pushes a region marker together
  with a `popRgn` frame).

## Judgments (presentation only)

The typing judgments are one inductive family, `Typing`, indexed by `TyJ`. It
covers atoms, computations, terms, argument lists (of atoms), values, maybe-unsized values, maybe-dead
values, value lists and captured environments. Outlives (`OutlivesJ`) and
rewriting (`RewriteJ`) are handled the same way. Continuations get their own
judgment, `ContOK`.
