module
public meta import Lean.Elab.Term
public import Mathlib.Data.Fin.VecNotation
public import RequestProject.Oxide.Syntax.Runtime

/-!
# Oxide: concrete syntax `[OXIDE| … ]`

A concrete-syntax embedding of Oxide in Lean.  `[OXIDE| e ]` elaborates the
Oxide expression `e` to a closed, scope-indexed term `Oxide.Term sig []`; named
variables, regions, type variables and frame variables are resolved to typed de
Bruijn indices at macro-expansion time (`In.there (… In.here)` for any binder,
`TVar.skipVar`/`TVar.skipRgn` chains for term variables).  An ill-scoped program
(an unbound name, a borrow at an abstract region, a term variable of an older
frame) is rejected at expansion time, or fails to elaborate.

`[OXIDE_TY| τ ]` elaborates a closed type `Oxide.Ty []`, and
`[OXIDE_FN| fn f<…>(…) -> τ { e } ]` a global function definition `Oxide.FnDef sig`.

Global functions are indices into the signature `sig` (`Oxide.FnIdx sig`): the
names of the declared functions are listed, in signature order, as
`[OXIDE{f, g, …}| e ]` and `[OXIDE_FN{f, g, …}| … ]`; any other identifier that
is not a bound variable is rejected.

Moves and copies: a bare place without dereference (`x`, `x.1`) elaborates to
`Term.move` (which takes a `TPlace`, so it cannot dereference); a place through a
dereference (`*r`, `(*r).0`) to `Term.copy`.  `copy!(p)` and `move!(p)` choose
explicitly (`move!` rejects a place with a dereference).

Closures are written in their own scope: the translation computes which
variables and regions of the current frame the body uses (the captured frame,
`Cap`), and which outer binders it uses (the outer scope `o` together with the
entries `θ : Inst o Γ`).

Number literals are `u32` constants (`UInt32`); a literal `≥ 2^32` is rejected.

Since `'a` is lexed by Lean as the start of a character literal, regions are
written as Lean name literals: `` `a `` stands for the region `'a`.

Grammar:
* types: `u32`, `bool`, `unit`, `()`, type variables `T`, `` &`a uniq τ ``,
  `` &`a shrd τ ``, `` &`a ω [τ] `` (reference to a slice), `[τ; n]`, `(τ,)`,
  `(τ₁, …, τₙ)`, `Either<τ₁, τ₂>`, and function types
  `` fn<@φ, …, `a, …; T, …>(τ₁, …, τₙ)[Φ] -> τ where `a : `b, … `` (the binders,
  the captured environment `[Φ]` and the bounds are optional; without `[Φ]` the
  environment is the empty frame).  Dead types `τ†` and unsized types `[τ]` are
  not types of this grammar (they belong to the separate sorts of maybe-dead and
  maybe-unsized types), so they cannot be written here;
* frame expressions `Φ`: frame variables `@φ` and literal frames
  `` @{ x : τ, `r ↦ {}, … } `` (entries oldest first; the types of a literal frame
  live in the scope of the frame itself, so they may mention its regions; region
  entries have empty loan sets);
* place expressions: `x`, `*p`, `p.n`, `(p)` (nested projections are written
  `(p.0).1`, since `0.1` is lexed as a decimal literal);
* expressions: `()`, `n`, `true`, `false`, `p`, `` &`r ω p ``, `` &`r ω p[e] ``,
  `` &`r ω p[e₁..e₂] `` (borrows name a *concrete* region, bound by `letrgn`),
  `p[e]`, `p := e`, `` letrgn<`r> { e } ``, `let x : τ = e₁; e₂`, `e₁; e₂`,
  `|x₁ : τ₁, …| -> τ { e }`, `|| -> τ { e }`, `f(e₁, …)`,
  `` f::<Φ, …, `a, …; τ, …>(e₁, …) ``, `if e { e₁ } else { e₂ }`, `(e,)`,
  `(e₁, …, eₙ)`, `[e₁, …]`, `for x in e { e' }`, `while e { e' }`,
  `abort!("msg")`, `Left::<τ₁, τ₂>(e)`, `Right::<τ₁, τ₂>(e)`,
  `match e { Left(x) => e₁, Right(y) => e₂ }` and blocks `{ e }`.
  An identifier that is not a bound variable denotes a global function, which
  must be listed in `[OXIDE{…}| … ]`.  `copy!(p)` and `move!(p)` mark a use of a
  place explicitly.
* values (as they appear at runtime): `val!(v)` where `v` is built from
  constants, function names, `dead!`, pointers `ptr!(x steps)` to a variable `x`
  in scope with steps `.n`, `[n]`, `[n₁..n₂]`, tuples `(v,)`/`(v₁, …)`, arrays
  `[v, …]`, slices `|v, …|` and injections `Left::<τ₁, τ₂>(v)`/`Right::<…>(v)`.
  There are no runtime term forms: the machine keeps frames and pending pops in
  its continuation.
* global functions: `` fn f<@φ, …, `a, …; T, …>(x : τ, …) -> τ where `a : `b { e } ``.

Ownership qualifiers `uniq`/`shrd` and the base types are parsed as identifiers
(so that they do not become reserved keywords of Lean).

Scopes: closure and function parameters `x₁, …, x_k` are pushed so that `xᵢ` is
the `i`-th most recent binder (`x₁` is the most recent); the binders
`<@φ̄, `ϱ̄; ᾱ>` of a signature are pushed as `ᾱ` (`α₁` most recent), then `ϱ̄`,
then `φ̄`, matching `Oxide.Binders.ctx`.
-/

public section

namespace Oxide.Notation

declare_syntax_cat oxide_rgn
declare_syntax_cat oxide_ty
declare_syntax_cat oxide_place
declare_syntax_cat oxide
declare_syntax_cat oxide_param
declare_syntax_cat oxide_fn
declare_syntax_cat oxide_frm
declare_syntax_cat oxide_fentry
declare_syntax_cat oxide_gbinder
declare_syntax_cat oxide_garg
declare_syntax_cat oxide_val
declare_syntax_cat oxide_rstep

syntax name : oxide_rgn

syntax "@" ident : oxide_frm
syntax "@" "{" oxide_fentry,* "}" : oxide_frm

syntax ident " : " oxide_ty : oxide_fentry
syntax oxide_rgn " ↦ " "{" "}" : oxide_fentry

syntax "@" ident : oxide_gbinder
syntax oxide_rgn : oxide_gbinder

syntax oxide_frm : oxide_garg
syntax oxide_rgn : oxide_garg

syntax ident : oxide_ty
syntax "(" ")" : oxide_ty
syntax "(" oxide_ty ")" : oxide_ty
syntax "(" oxide_ty "," oxide_ty,+ ")" : oxide_ty
syntax "(" oxide_ty "," ")" : oxide_ty
syntax "&" oxide_rgn ident "[" oxide_ty "]" : oxide_ty
syntax "&" oxide_rgn ident oxide_ty : oxide_ty
syntax "[" oxide_ty ";" num "]" : oxide_ty
syntax "Either" "<" oxide_ty "," oxide_ty ">" : oxide_ty
syntax "fn" ("<" oxide_gbinder,* (";" ident,*)? ">")? "(" oxide_ty,* ")" ("[" oxide_frm "]")?
  " -> " oxide_ty (" where " sepBy1(oxide_rgn " : " oxide_rgn, ","))? : oxide_ty

syntax:max ident : oxide_place
syntax "*" oxide_place : oxide_place
syntax:max "(" oxide_place ")" : oxide_place
syntax:max oxide_place:max noWs "." noWs num : oxide_place

syntax ident " : " oxide_ty : oxide_param

syntax:max num : oxide
syntax:max "(" ")" : oxide
syntax:max oxide_place : oxide
syntax "&" oxide_rgn ident oxide_place : oxide
syntax "&" oxide_rgn ident oxide_place "[" oxide "]" : oxide
syntax "&" oxide_rgn ident oxide_place "[" oxide ".." oxide "]" : oxide
syntax oxide_place "[" oxide "]" : oxide
syntax:1 oxide_place " := " oxide:1 : oxide
syntax "letrgn" "<" oxide_rgn ">" "{" oxide "}" : oxide
syntax:0 "let " ident " : " oxide_ty " = " oxide:1 "; " oxide:0 : oxide
syntax:0 oxide:1 "; " oxide:0 : oxide
syntax "|" oxide_param,* "|" " -> " oxide_ty "{" oxide "}" : oxide
syntax "||" " -> " oxide_ty "{" oxide "}" : oxide
syntax:max oxide:max noWs "(" oxide,* ")" : oxide
syntax:max oxide:max noWs "::<" oxide_garg,* ";" oxide_ty,* ">" "(" oxide,* ")" : oxide
syntax "if " oxide " {" oxide "}" " else " "{" oxide "}" : oxide
syntax "(" oxide "," oxide,+ ")" : oxide
syntax "(" oxide "," ")" : oxide
syntax "[" oxide,* "]" : oxide
syntax "for " ident " in " oxide " {" oxide "}" : oxide
syntax "while " oxide " {" oxide "}" : oxide
syntax "abort!" "(" str ")" : oxide
syntax "Left" "::<" oxide_ty "," oxide_ty ">" "(" oxide ")" : oxide
syntax "Right" "::<" oxide_ty "," oxide_ty ">" "(" oxide ")" : oxide
syntax "match " oxide " {" "Left" "(" ident ")" " => " oxide "," "Right" "(" ident ")" " => " oxide "}" :
  oxide
syntax "{" oxide "}" : oxide

syntax "." num : oxide_rstep
syntax "[" num "]" : oxide_rstep
syntax "[" num ".." num "]" : oxide_rstep

syntax num : oxide_val
syntax "(" ")" : oxide_val
syntax ident : oxide_val
syntax "dead!" : oxide_val
syntax "ptr!" "(" ident oxide_rstep* ")" : oxide_val
syntax "(" oxide_val "," oxide_val,+ ")" : oxide_val
syntax "(" oxide_val "," ")" : oxide_val
syntax "[" oxide_val,* "]" : oxide_val
syntax "|" oxide_val,* "|" : oxide_val
syntax "Left" "::<" oxide_ty "," oxide_ty ">" "(" oxide_val ")" : oxide_val
syntax "Right" "::<" oxide_ty "," oxide_ty ">" "(" oxide_val ")" : oxide_val

syntax "val!" "(" oxide_val ")" : oxide
syntax "copy!" "(" oxide_place ")" : oxide
syntax "move!" "(" oxide_place ")" : oxide

syntax "fn " ident ("<" oxide_gbinder,* (";" ident,*)? ">")? "(" oxide_param,* ")" " -> " oxide_ty
  (" where " sepBy1(oxide_rgn " : " oxide_rgn, ","))? "{" oxide "}" : oxide_fn

end Oxide.Notation

end

public meta section

namespace Oxide.Notation

open Lean

/-- Sorts of binders, as seen by the translation. -/
inductive Sort' where
  | fvar | abs | tvar | var | rgn | frame
  deriving BEq, Inhabited

/-- A named binder of the translation scope, with a unique identifier (so that the
binders a closure body uses can be recorded). -/
structure Bind where
  name : Name
  sort : Sort'
  id : Nat
  deriving Inhabited

/-- The scope during the translation: named binders, most recent first (frame
boundaries have the anonymous name). -/
abbrev Scope := List Bind

/-- The state of the translation: a supply of identifiers, the identifiers of the
binders used so far, and the names of the global functions. -/
structure TState where
  next : Nat := 0
  used : List Nat := []
  globals : List Name := []

abbrev TransM := ReaderT Scope (StateT TState MacroM)

/-- Run a translation with the given global function names. -/
def TransM.run' {α : Type} (m : TransM α) (globals : List Name) (s : Scope := []) : MacroM α :=
  (m.run s).run' { globals }

/-- Record the use of a binder. -/
def use (b : Bind) : TransM Unit := modify fun st => { st with used := b.id :: st.used }

/-- Push named binders (most recent first) with fresh identifiers. -/
def withBinders {α : Type} (bs : List (Name × Sort')) (m : TransM α) : TransM α := do
  let st ← get
  let binds := bs.zipIdx.map fun ((x, b), i) => ({ name := x, sort := b, id := st.next + i } : Bind)
  set { st with next := st.next + bs.length }
  withReader (binds ++ ·) m

/-- The position and the binder of the most recent binder named `x` with a sort
satisfying `p`. -/
def lookup (s : Scope) (x : Name) (p : Sort' → Bool) : Option (Nat × Bind) :=
  go s 0
where
  go : Scope → Nat → Option (Nat × Bind)
    | [], _ => none
    | b :: s, n => if b.name == x && p b.sort then some (n, b) else go s (n + 1)

/-- The position of the binder with identifier `i`. -/
def posOf (s : Scope) (i : Nat) : Option Nat := s.findIdx? (·.id == i)

/-- The typed de Bruijn index `In.there^n In.here`. -/
def mkIn : Nat → MacroM Lean.Term
  | 0 => `(Oxide.In.here)
  | n + 1 => do `(Oxide.In.there $(← mkIn n))

/-- The index of the binder named `x` of sort `b`. -/
def inIdx (x : Ident) (b : Sort') (what : String) : TransM Lean.Term := do
  match lookup (← read) x.getId (· == b) with
  | some (n, bd) => use bd; mkIn n
  | none => Macro.throwErrorAt x s!"unknown {what} {x.getId}"

/-- A term variable of the top frame, given by its identifier: a chain of
`TVar.skipVar`/`TVar.skipRgn` ending in `TVar.here`. -/
def tvarOfId (ref : Syntax) (s : Scope) (i : Nat) : MacroM Lean.Term :=
  go s
where
  go : Scope → MacroM Lean.Term
    | [] => Macro.throwErrorAt ref "unknown variable"
    | b :: s =>
      if b.id == i then `(Oxide.TVar.here)
      else match b.sort with
        | .var => do `(Oxide.TVar.skipVar $(← go s))
        | .rgn => do `(Oxide.TVar.skipRgn $(← go s))
        | _ => Macro.throwErrorAt ref "not a variable of the current frame"

/-- A term variable of the top frame. -/
def tvarIdx (x : Ident) : TransM Lean.Term := do
  let s ← read
  match lookup s x.getId (· == .var) with
  | some (_, b) =>
      use b
      let rec ok : Scope → Bool
        | [] => false
        | b' :: s => if b'.id == b.id then true
          else match b'.sort with
            | .var | .rgn => ok s
            | _ => false
      if ok s then tvarOfId x s b.id
      else Macro.throwErrorAt x s!"variable {x.getId} is not a variable of the current frame"
  | none => Macro.throwErrorAt x s!"unknown variable {x.getId}"

def rgnName : TSyntax `oxide_rgn → MacroM Name
  | `(oxide_rgn| $n:name) => pure n.getName
  | stx => Macro.throwErrorAt stx "ill-formed region"

/-- A region: the most recent binder of that name, concrete (`letrgn`) or
abstract (signature). -/
def transRgn (r : TSyntax `oxide_rgn) : TransM Lean.Term := do
  let x ← rgnName r
  match lookup (← read) x (fun b => b == .rgn || b == .abs) with
  | some (n, b) =>
      use b
      if b.sort == .rgn then `(Oxide.Region.conc $(← mkIn n)) else `(Oxide.Region.abs $(← mkIn n))
  | none => Macro.throwErrorAt r s!"unknown region {x}"

/-- A concrete region (for borrows). -/
def transConcRgn (r : TSyntax `oxide_rgn) : TransM Lean.Term := do
  let x ← rgnName r
  match lookup (← read) x (fun b => b == .rgn || b == .abs) with
  | some (n, b) =>
      if b.sort == .rgn then do use b; mkIn n
      else Macro.throwErrorAt r s!"borrows need a concrete region, but {x} is abstract"
  | none => Macro.throwErrorAt r s!"unknown region {x}"

def transOwn (o : Ident) : TransM Lean.Term :=
  match o.getId with
  | `uniq => `(Oxide.Own.uniq)
  | `shrd => `(Oxide.Own.shrd)
  | _ => Macro.throwErrorAt o "expected `uniq` or `shrd`"

/-- `![t₁, …, tₙ]`. -/
def mkVec (ts : List Lean.Term) : MacroM Lean.Term := `(![$(ts.toArray),*])

/-- A `u32` literal (rejected if it does not fit in 32 bits). -/
def mkNum (n : TSyntax `num) : MacroM Lean.Term := do
  if n.getNat < 2 ^ 32 then `(Oxide.Value.num $n)
  else Macro.throwErrorAt n "u32 literal out of range"

/-- A global function: its index in the signature. -/
def transGlobal (x : Ident) : TransM Lean.Term := do
  match (← get).globals.idxOf? x.getId with
  | some i =>
      let rec mk : Nat → MacroM Lean.Term
        | 0 => `(Oxide.FnIdx.here)
        | n + 1 => do `(Oxide.FnIdx.there $(← mk n))
      mk i
  | none => Macro.throwErrorAt x s!"unknown variable or global function {x.getId}"

/-- Split generic binders `@φ, …, `a, …` into frame variables and abstract regions. -/
def splitBinders (bs : List (TSyntax `oxide_gbinder)) : MacroM (List Name × List Name) := do
  let mut frms : List Name := []
  let mut rgns : List Name := []
  for b in bs do
    match b with
    | `(oxide_gbinder| @ $x:ident) => frms := frms ++ [x.getId]
    | `(oxide_gbinder| $r:oxide_rgn) => rgns := rgns ++ [← rgnName r]
    | _ => Macro.throwErrorAt b "ill-formed binder"
  pure (frms, rgns)

/-- The scope extension made by signature binders (cf. `Oxide.Binders.ctx`). -/
def binderScope (frms rgns αs : List Name) : List (Name × Sort') :=
  αs.map (·, .tvar) ++ rgns.map (·, .abs) ++ frms.map (·, .fvar)

/-- The `Oxide.Binders` record. -/
def mkBinders (frms rgns αs : List Name) : MacroM Lean.Term :=
  `(({ nφ := $(quote frms.length), nϱ := $(quote rgns.length), nα := $(quote αs.length) } :
      Oxide.Binders))

/-- Bounds `ϱᵢ : ϱⱼ` as pairs of indices among the signature's regions. -/
def mkBounds (rgns : List Name) (b₁ b₂ : Option (Array (TSyntax `oxide_rgn))) :
    MacroM Lean.Term := do
  let bnds ← match b₁, b₂ with
    | some b₁, some b₂ => (b₁.toList.zip b₂.toList).mapM fun (x, y) => do
        let ix ← rgnName x
        let iy ← rgnName y
        let some i := rgns.idxOf? ix | Macro.throwErrorAt x s!"unknown abstract region {ix}"
        let some j := rgns.idxOf? iy | Macro.throwErrorAt y s!"unknown abstract region {iy}"
        `((⟨$(quote i), by decide⟩, ⟨$(quote j), by decide⟩))
    | _, _ => pure []
  `([$(bnds.toArray),*])

/-- The sort and name of a frame entry. -/
def fentryInfo : TSyntax `oxide_fentry → MacroM (Name × Sort')
  | `(oxide_fentry| $x:ident : $_t:oxide_ty) => pure (x.getId, .var)
  | `(oxide_fentry| $r:oxide_rgn ↦ { }) => do pure (← rgnName r, .rgn)
  | stx => Macro.throwErrorAt stx "ill-formed frame entry"

/-- The sort as an `Oxide.Bnd`. -/
def mkBnd : Sort' → MacroM Lean.Term
  | .fvar => `(Oxide.Bnd.fvar)
  | .abs => `(Oxide.Bnd.abs)
  | .tvar => `(Oxide.Bnd.tvar)
  | .var => `(Oxide.Bnd.var)
  | .rgn => `(Oxide.Bnd.rgn)
  | .frame => `(Oxide.Bnd.frame)

mutual
partial def transTy : TSyntax `oxide_ty → TransM Lean.Term
  | `(oxide_ty| $x:ident) => do
      match x.getId with
      | `u32 => `(Oxide.Ty.u32)
      | `bool => `(Oxide.Ty.bool)
      | `unit => `(Oxide.Ty.unit)
      | _ => do `(Oxide.Ty.tvar $(← inIdx x .tvar "type variable"))
  | `(oxide_ty| ( )) => `(Oxide.Ty.unit)
  | `(oxide_ty| ( $t:oxide_ty )) => transTy t
  | `(oxide_ty| ( $t:oxide_ty , )) => do `(Oxide.Ty.tuple 1 $(← mkVec [← transTy t]))
  | `(oxide_ty| ( $t:oxide_ty, $ts:oxide_ty,* )) => do
      let ts ← (t :: ts.getElems.toList).mapM transTy
      `(Oxide.Ty.tuple $(quote ts.length) $(← mkVec ts))
  | `(oxide_ty| & $r:oxide_rgn $o:ident [ $t:oxide_ty ]) => do
      `(Oxide.Ty.ref $(← transRgn r) $(← transOwn o) (Oxide.XTy.slice $(← transTy t)))
  | `(oxide_ty| & $r:oxide_rgn $o:ident $t:oxide_ty) => do
      `(Oxide.Ty.ref $(← transRgn r) $(← transOwn o) (Oxide.XTy.sized $(← transTy t)))
  | `(oxide_ty| [ $t:oxide_ty ; $n:num ]) => do `(Oxide.Ty.array $(← transTy t) $n)
  | `(oxide_ty| Either < $t₁:oxide_ty , $t₂:oxide_ty >) => do
      `(Oxide.Ty.sum $(← transTy t₁) $(← transTy t₂))
  | `(oxide_ty| fn $[< $bs:oxide_gbinder,* $[; $αs:ident,*]? >]? ( $ts:oxide_ty,* )
        $[[ $Φ:oxide_frm ]]? -> $r:oxide_ty $[where $[$b₁:oxide_rgn : $b₂:oxide_rgn],*]?) => do
      let (frms, rgns) ← match bs with
        | some bs => splitBinders bs.getElems.toList
        | none => pure ([], [])
      let αs : List Name := match αs with
        | some (some αs) => αs.getElems.toList.map (·.getId)
        | _ => []
      let inner {β : Type} (m : TransM β) : TransM β := withBinders (binderScope frms rgns αs) m
      let ts ← inner (ts.getElems.toList.mapM transTy)
      let r ← inner (transTy r)
      let Φ ← match Φ with
        | some Φ => inner (transFrm Φ)
        | none => `(Oxide.FrameExpr.empty)
      `(Oxide.Ty.fn $(← mkBinders frms rgns αs) $(quote ts.length) $(← mkVec ts) $r $Φ
          $(← mkBounds rgns b₁ b₂))
  | stx => Macro.throwErrorAt stx "ill-formed Oxide type"

/-- Frame expressions: a frame variable `@φ`, or a literal frame
`@{ x : τ, `r ↦ {}, … }` (entries oldest first), whose types are translated in the
scope of the frame itself. -/
partial def transFrm : TSyntax `oxide_frm → TransM Lean.Term
  | `(oxide_frm| @ $x:ident) => do `(Oxide.FrameExpr.var $(← inIdx x .fvar "frame variable"))
  | `(oxide_frm| @ { $es:oxide_fentry,* }) => do
      let es := es.getElems.toList.reverse
      let infos ← es.mapM fun e => (fentryInfo e : MacroM _)
      let inner {β : Type} (m : TransM β) : TransM β :=
        withBinders (infos ++ [(Name.anonymous, .frame)]) m
      let shape ← infos.mapM fun (_, b) => mkBnd b
      let mut acc ← `(Oxide.FrameTy.nil)
      for e in es.reverse do
        match e with
        | `(oxide_fentry| $_x:ident : $t:oxide_ty) =>
            acc ← `(Oxide.FrameTy.var $(← inner (transTy t)) $acc)
        | _ => acc ← `(Oxide.FrameTy.rgn [] $acc)
      `(Oxide.FrameExpr.frame [$(shape.toArray),*] $acc)
  | stx => Macro.throwErrorAt stx "ill-formed frame expression"
end

/-- A place expression: its root, the projections applied to the root, and the
groups "dereference, then projections" (innermost first). -/
partial def transPlace : TSyntax `oxide_place → TransM (Ident × List Nat × List (List Nat))
  | `(oxide_place| $x:ident) => pure (x, [], [])
  | `(oxide_place| ( $p:oxide_place )) => transPlace p
  | `(oxide_place| * $p:oxide_place) => do
      let (x, q, gs) ← transPlace p
      pure (x, q, gs ++ [[]])
  | `(oxide_place| $p:oxide_place.$i:num) => do
      let (x, q, gs) ← transPlace p
      match gs.getLast? with
      | none => pure (x, q ++ [i.getNat], gs)
      | some g => pure (x, q, gs.dropLast ++ [g ++ [i.getNat]])
  | stx => Macro.throwErrorAt stx "ill-formed place expression"

/-- A list of natural numbers as a term. -/
def mkNats (q : List Nat) : MacroM Lean.Term := do
  let xs : Array Lean.Term := (q.map fun n => (quote n : Lean.Term)).toArray
  `([$xs,*])

/-- The place expression `p` as an `Oxide.PExpr`. -/
def mkPlace (p : TSyntax `oxide_place) : TransM Lean.Term := do
  let (x, q, gs) ← transPlace p
  let mut acc ← `(Oxide.PExpr.place ⟨$(← tvarIdx x), $(← mkNats q)⟩)
  for g in gs do
    acc ← `(Oxide.PExpr.deref $acc $(← mkNats g))
  pure acc

/-- The place `p` (no dereference) as an `Oxide.TPlace`. -/
def mkTPlace (p : TSyntax `oxide_place) : TransM Lean.Term := do
  let (x, q, gs) ← transPlace p
  unless gs.isEmpty do Macro.throwErrorAt p "cannot move out of a dereference"
  `((⟨$(← tvarIdx x), $(← mkNats q)⟩ : Oxide.TPlace _))

/-- Whether a place expression contains a dereference. -/
def hasDeref (p : TSyntax `oxide_place) : TransM Bool := do
  let (_, _, gs) ← transPlace p
  pure !gs.isEmpty

def withVar {α : Type} (x : Name) (m : TransM α) : TransM α := withBinders [(x, .var)] m

/-- Push parameters `x₁, …, x_k` (`x₁` most recent). -/
def withParams {α : Type} (xs : List Name) (m : TransM α) : TransM α :=
  withBinders (xs.map (·, .var)) m

def transParam : TSyntax `oxide_param → TransM (Name × TSyntax `oxide_ty)
  | `(oxide_param| $x:ident : $t:oxide_ty) => pure (x.getId, t)
  | stx => Macro.throwErrorAt stx "ill-formed parameter"

/-- Referent steps. -/
inductive RStep' where
  | proj (n : Nat)
  | idx (n : Nat)
  | slice (a b : Nat)

def rstepOf : TSyntax `oxide_rstep → MacroM RStep'
  | `(oxide_rstep| . $i:num) => pure (.proj i.getNat)
  | `(oxide_rstep| [ $i:num ]) => pure (.idx i.getNat)
  | `(oxide_rstep| [ $i:num .. $j:num ]) => pure (.slice i.getNat j.getNat)
  | stx => Macro.throwErrorAt stx "ill-formed referent step"

/-- Build a referent from its root and its steps: leading projections form the
place; each index starts a new group of projections; `[a..b]` is the slice of
length `b - a` starting at `a`. -/
def mkReferent (root : Lean.Term) (steps : List RStep') : MacroM Lean.Term := do
  let leading := steps.takeWhile fun | .proj _ => true | _ => false
  let rest := steps.drop leading.length
  let path := leading.filterMap fun | .proj n => some n | _ => none
  let mut acc ← `(Oxide.Referent.place ⟨$root, $(← mkNats path)⟩)
  let mut pending : Option (Nat × List Nat) := none
  for st in rest do
    match st, pending with
    | .proj n, some (i, q) => pending := some (i, q ++ [n])
    | .proj _, none => Macro.throwUnsupported
    | .idx i, p => do
        if let some (j, q) := p then acc ← `(Oxide.Referent.index $acc $(quote j) $(← mkNats q))
        pending := some (i, [])
    | .slice a b, p => do
        if let some (j, q) := p then acc ← `(Oxide.Referent.index $acc $(quote j) $(← mkNats q))
        pending := none
        acc ← `(Oxide.Referent.slice $acc $(quote a) $(quote (b - a)))
  if let some (j, q) := pending then acc ← `(Oxide.Referent.index $acc $(quote j) $(← mkNats q))
  pure acc

/-- Runtime values. -/
partial def transVal : TSyntax `oxide_val → TransM Lean.Term
  | `(oxide_val| $n:num) => mkNum n
  | `(oxide_val| ( )) => `(Oxide.Value.unit)
  | `(oxide_val| $x:ident) => match x.getId with
      | `true => `(Oxide.Value.tt)
      | `false => `(Oxide.Value.ff)
      | _ => do `(Oxide.Value.fn $(← transGlobal x))
  | `(oxide_val| dead!) => `(Oxide.Value.dead)
  | `(oxide_val| ptr!( $x:ident $steps:oxide_rstep* )) => do
      let steps ← steps.toList.mapM fun st => (rstepOf st : MacroM RStep')
      `(Oxide.Value.ptr $(← mkReferent (← inIdx x .var "variable") steps))
  | `(oxide_val| ( $v:oxide_val , )) => do `(Oxide.Value.tuple 1 $(← mkVec [← transVal v]))
  | `(oxide_val| ( $v:oxide_val, $vs:oxide_val,* )) => do
      let vs ← (v :: vs.getElems.toList).mapM transVal
      `(Oxide.Value.tuple $(quote vs.length) $(← mkVec vs))
  | `(oxide_val| [ $vs:oxide_val,* ]) => do
      let vs ← vs.getElems.toList.mapM transVal
      `(Oxide.Value.array $(quote vs.length) $(← mkVec vs))
  | `(oxide_val| | $vs:oxide_val,* |) => do
      let vs ← vs.getElems.toList.mapM transVal
      `(Oxide.Value.slice $(quote vs.length) $(← mkVec vs))
  | `(oxide_val| Left::<$t₁:oxide_ty, $t₂:oxide_ty>($v:oxide_val)) => do
      `(Oxide.Value.inl $(← transTy t₁) $(← transTy t₂) $(← transVal v))
  | `(oxide_val| Right::<$t₁:oxide_ty, $t₂:oxide_ty>($v:oxide_val)) => do
      `(Oxide.Value.inr $(← transTy t₁) $(← transTy t₂) $(← transVal v))
  | stx => Macro.throwErrorAt stx "ill-formed Oxide value"

/-- Run a translation, returning its result and the identifiers of the binders it
used, without recording them in the enclosing translation. -/
def collectUsed {α : Type} (m : TransM α) : TransM (α × List Nat) := do
  let saved := (← get).used
  modify fun st => { st with used := [] }
  let a ← m
  let used := (← get).used
  modify fun st => { st with used := saved }
  pure (a, used)

/-- The entry of an outer binder of a closure, in the enclosing scope. -/
def mkEntry (s : Scope) (b : Bind) : TransM Lean.Term := do
  let some n := posOf s b.id | Macro.throwUnsupported
  use b
  let i ← mkIn n
  match b.sort with
  | .rgn => `(($i : Oxide.In Oxide.Bnd.rgn _))
  | .abs => `(Oxide.Region.abs $i)
  | .tvar => `(Oxide.Ty.tvar $i)
  | .fvar => `(Oxide.FrameExpr.var $i)
  | _ => Macro.throwUnsupported

mutual
/-- Closures `|x₁ : τ₁, …| -> τ { e }`: the captured frame consists of the
variables of the current frame that the body uses; the outer binders of the
closure are the regions, type variables, abstract regions and frame variables
that the body or the signature use. -/
partial def transClosure (ps : List (Name × TSyntax `oxide_ty)) (r : TSyntax `oxide_ty)
    (e : TSyntax `oxide) : TransM Lean.Term := do
  let s ← read
  let (_, used) ← collectUsed do
    let _ ← ps.mapM fun p => transTy p.2
    let _ ← transTy r
    withParams (ps.map (·.1)) (transExpr e)
  let top := s.takeWhile fun b => b.sort == .var || b.sort == .rgn
  let fBinds := top.filter fun b => b.sort == .var && used.contains b.id
  let oBinds := s.filter fun b =>
    (b.sort == .rgn || b.sort == .abs || b.sort == .tvar || b.sort == .fvar) && used.contains b.id
  -- captures and entries, in the enclosing scope
  let mut cap ← `(Oxide.Cap.nil)
  for b in fBinds.reverse do
    cap ← `(Oxide.Cap.var $(← tvarOfId e s b.id) $cap)
  for b in fBinds do use b
  let mut inst ← `(Oxide.Inst.nil)
  for b in oBinds.reverse do
    inst ← `(Oxide.Inst.cons (b := $(← mkBnd b.sort)) $(← mkEntry s b) $inst)
  let fShape ← fBinds.mapM fun b => mkBnd b.sort
  let oShape ← oBinds.mapM fun b => mkBnd b.sort
  -- the closure's own scope
  let oScope := oBinds.map fun b => (b.name, b.sort)
  let fScope := fBinds.map fun b => (b.name, b.sort)
  let (tys, ret, body) ← withReader (fun _ => []) <| withBinders oScope do
    let tys ← ps.mapM fun p => transTy p.2
    let ret ← transTy r
    let body ← withBinders (fScope ++ [(Name.anonymous, .frame)]) <|
      withParams (ps.map (·.1)) (transExpr e)
    pure (tys, ret, body)
  `(Oxide.Term.closure [$(fShape.toArray),*] $cap [$(oShape.toArray),*] $inst
      $(quote ps.length) $(← mkVec tys) $ret $body)

partial def transExpr : TSyntax `oxide → TransM Lean.Term
  | `(oxide| $n:num) => do `(Oxide.Term.val $(← mkNum n))
  | `(oxide| ( )) => `(Oxide.Term.val Oxide.Value.unit)
  | `(oxide| $p:oxide_place) => do
      match p with
      | `(oxide_place| $x:ident) =>
          if (lookup (← read) x.getId (· == .var)).isSome then `(Oxide.Term.move $(← mkTPlace p))
          else match x.getId with
            | `true => `(Oxide.Term.val Oxide.Value.tt)
            | `false => `(Oxide.Term.val Oxide.Value.ff)
            | _ => do `(Oxide.Term.val (Oxide.Value.fn $(← transGlobal x)))
      | _ =>
          if ← hasDeref p then `(Oxide.Term.copy $(← mkPlace p))
          else `(Oxide.Term.move $(← mkTPlace p))
  | `(oxide| copy!( $p:oxide_place )) => do `(Oxide.Term.copy $(← mkPlace p))
  | `(oxide| move!( $p:oxide_place )) => do `(Oxide.Term.move $(← mkTPlace p))
  | `(oxide| & $r:oxide_rgn $o:ident $p:oxide_place) => do
      `(Oxide.Term.borrow $(← transConcRgn r) $(← transOwn o) $(← mkPlace p))
  | `(oxide| & $r:oxide_rgn $o:ident $p:oxide_place [ $e:oxide ]) => do
      `(Oxide.Term.borrowIdx $(← transConcRgn r) $(← transOwn o) $(← mkPlace p) $(← transExpr e))
  | `(oxide| & $r:oxide_rgn $o:ident $p:oxide_place [ $e₁:oxide .. $e₂:oxide ]) => do
      `(Oxide.Term.borrowSlice $(← transConcRgn r) $(← transOwn o) $(← mkPlace p)
          $(← transExpr e₁) $(← transExpr e₂))
  | `(oxide| $p:oxide_place [ $e:oxide ]) => do
      `(Oxide.Term.index $(← mkPlace p) $(← transExpr e))
  | `(oxide| $p:oxide_place := $e:oxide) => do
      `(Oxide.Term.assign $(← mkPlace p) $(← transExpr e))
  | `(oxide| letrgn < $r:oxide_rgn > { $e:oxide }) => do
      let x ← rgnName r
      `(Oxide.Term.letrgn $(← withBinders [(x, .rgn)] (transExpr e)))
  | `(oxide| let $x:ident : $t:oxide_ty = $e₁:oxide; $e₂:oxide) => do
      let t ← transTy t
      let e₁ ← transExpr e₁
      let e₂ ← withVar x.getId (transExpr e₂)
      `(Oxide.Term.letE $t $e₁ $e₂)
  | `(oxide| $e₁:oxide; $e₂:oxide) => do
      `(Oxide.Term.seq $(← transExpr e₁) $(← transExpr e₂))
  | `(oxide| | $ps:oxide_param,* | -> $r:oxide_ty { $e:oxide }) => do
      transClosure (← ps.getElems.toList.mapM transParam) r e
  | `(oxide| || -> $r:oxide_ty { $e:oxide }) => transClosure [] r e
  | `(oxide| $f:oxide($args:oxide,*)) => do
      let args ← args.getElems.toList.mapM transExpr
      `(Oxide.Term.app $(← transExpr f) {} Oxide.TArgs.none $(quote args.length) $(← mkVec args))
  | `(oxide| $f:oxide::<$gs:oxide_garg,*; $ts:oxide_ty,*>($args:oxide,*)) => do
      let mut Φs : List Lean.Term := []
      let mut rs : List Lean.Term := []
      for g in gs.getElems do
        match g with
        | `(oxide_garg| $Φ:oxide_frm) => Φs := Φs ++ [← transFrm Φ]
        | `(oxide_garg| $r:oxide_rgn) => rs := rs ++ [← transRgn r]
        | _ => Macro.throwErrorAt g "ill-formed generic argument"
      let ts ← ts.getElems.toList.mapM transTy
      let args ← args.getElems.toList.mapM transExpr
      `(Oxide.Term.app $(← transExpr f)
          ({ nφ := $(quote Φs.length), nϱ := $(quote rs.length), nα := $(quote ts.length) } :
            Oxide.Binders)
          ⟨$(← mkVec Φs), $(← mkVec rs), $(← mkVec ts)⟩ $(quote args.length) $(← mkVec args))
  | `(oxide| if $c:oxide { $e₁:oxide } else { $e₂:oxide }) => do
      `(Oxide.Term.ite $(← transExpr c) $(← transExpr e₁) $(← transExpr e₂))
  | `(oxide| ( $e:oxide , )) => do
      `(Oxide.Term.tuple 1 $(← mkVec [← transExpr e]))
  | `(oxide| ( $e:oxide, $es:oxide,* )) => do
      let es ← (e :: es.getElems.toList).mapM transExpr
      `(Oxide.Term.tuple $(quote es.length) $(← mkVec es))
  | `(oxide| [ $es:oxide,* ]) => do
      let es ← es.getElems.toList.mapM transExpr
      `(Oxide.Term.array $(quote es.length) $(← mkVec es))
  | `(oxide| for $x:ident in $e₁:oxide { $e₂:oxide }) => do
      `(Oxide.Term.forE $(← transExpr e₁) $(← withVar x.getId (transExpr e₂)))
  | `(oxide| while $e₁:oxide { $e₂:oxide }) => do
      `(Oxide.Term.whileE $(← transExpr e₁) $(← transExpr e₂))
  | `(oxide| abort!($s:str)) => `(Oxide.Term.abort $s)
  | `(oxide| Left::<$t₁:oxide_ty, $t₂:oxide_ty>($e:oxide)) => do
      `(Oxide.Term.inl $(← transTy t₁) $(← transTy t₂) $(← transExpr e))
  | `(oxide| Right::<$t₁:oxide_ty, $t₂:oxide_ty>($e:oxide)) => do
      `(Oxide.Term.inr $(← transTy t₁) $(← transTy t₂) $(← transExpr e))
  | `(oxide| match $e:oxide { Left($x:ident) => $e₁:oxide, Right($y:ident) => $e₂:oxide }) => do
      `(Oxide.Term.matchE $(← transExpr e) $(← withVar x.getId (transExpr e₁))
          $(← withVar y.getId (transExpr e₂)))
  | `(oxide| { $e:oxide }) => transExpr e
  | `(oxide| val!( $v:oxide_val )) => do `(Oxide.Term.val $(← transVal v))
  | stx => Macro.throwErrorAt stx "ill-formed Oxide expression"
end

def transFn (globals : List Name) : TSyntax `oxide_fn → MacroM Lean.Term
  | `(oxide_fn| fn $f:ident $[< $bs:oxide_gbinder,* $[; $αs:ident,*]? >]? ( $ps:oxide_param,* )
        -> $r:oxide_ty $[where $[$b₁:oxide_rgn : $b₂:oxide_rgn],*]? { $e:oxide }) => do
      let (frms, rs) ← match bs with
        | some bs => splitBinders bs.getElems.toList
        | none => pure ([], [])
      let αs : List Name := match αs with
        | some (some αs) => αs.getElems.toList.map (·.getId)
        | _ => []
      let (ps, r, body) ← TransM.run' (globals := globals) <| withBinders (binderScope frms rs αs) do
        let ps ← ps.getElems.toList.mapM transParam
        let tys ← ps.mapM fun p => transTy p.2
        let r ← transTy r
        let body ← withBinders [(Name.anonymous, .frame)] <| withParams (ps.map (·.1)) (transExpr e)
        pure (ps.map (·.1) |>.zip tys, r, body)
      let bs ← mkBinders frms rs αs
      let ps' ← mkVec (ps.map (·.2))
      let bds ← mkBounds rs b₁ b₂
      `((Oxide.FnDef.mk (Oxide.FnSig.mk $(quote f.getId.toString) $bs $(quote ps.length) $ps' $r
          $bds) $body : Oxide.FnDef _))
  | stx => Macro.throwErrorAt stx "ill-formed Oxide function definition"

end Oxide.Notation

/-- `[OXIDE| e ]`: the closed Oxide expression `e` as a scoped term `Oxide.Term sig []`
(no global functions). -/
macro "[OXIDE| " e:oxide " ]" : term => do
  let t ← (Oxide.Notation.transExpr e).run' []
  `(($t : Oxide.Term _ []))

/-- `[OXIDE{f, g, …}| e ]`: the closed Oxide expression `e`, whose global
functions are `f, g, …` (in this order in the signature). -/
macro "[OXIDE{" gs:ident,* "}| " e:oxide " ]" : term => do
  let t ← (Oxide.Notation.transExpr e).run' (gs.getElems.toList.map (·.getId))
  `(($t : Oxide.Term _ []))

/-- `[OXIDE_TY| τ ]`: a closed Oxide type `Oxide.Ty []`. -/
macro "[OXIDE_TY| " t:oxide_ty " ]" : term => do
  let t ← (Oxide.Notation.transTy t).run' []
  `(($t : Oxide.Ty []))

/-- `[OXIDE_FN| fn f<…>(…) -> τ { e } ]`: a global function definition (calling no
global function). -/
macro "[OXIDE_FN| " d:oxide_fn " ]" : term => Oxide.Notation.transFn [] d

/-- `[OXIDE_FN{f, g, …}| fn f<…>(…) -> τ { e } ]`: a global function definition
whose body may call the global functions `f, g, …`. -/
macro "[OXIDE_FN{" gs:ident,* "}| " d:oxide_fn " ]" : term =>
  Oxide.Notation.transFn (gs.getElems.toList.map (·.getId)) d

end
