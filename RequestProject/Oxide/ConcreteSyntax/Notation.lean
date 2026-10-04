module
public meta import Lean.Elab.Term
public import Mathlib.Data.Fin.VecNotation
public import RequestProject.Oxide.Syntax.Runtime

/-!
# Oxide: concrete syntax `[OXIDE| … ]`

A concrete-syntax embedding of Oxide in Lean.  `[OXIDE| e ]` elaborates the
Oxide expression `e` to a closed, scope-indexed term `Oxide.Term []`; named
variables, regions, type variables and frame variables are resolved to typed de
Bruijn indices at macro-expansion time (`In.there (… In.here)` for any binder,
`TVar.skipVar`/`TVar.skipRgn` chains for term variables).  An ill-scoped program
(an unbound name, a borrow at an abstract region, a term variable of an older
frame) is rejected at expansion time, or fails to elaborate.

`[OXIDE_TY| τ ]` elaborates a closed type `Oxide.Ty []`, and
`[OXIDE_FN| fn f<…>(…) -> τ { e } ]` a global function definition `Oxide.FnDef`.

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
  An identifier that is not a bound variable denotes a global function.
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

/-- The scope during the translation: named binders, most recent first (frame
boundaries have the anonymous name). -/
abbrev Scope := List (Name × Sort')

abbrev TransM := ReaderT Scope MacroM

/-- The position of the most recent binder named `x` with a sort satisfying `p`. -/
def lookup (s : Scope) (x : Name) (p : Sort' → Bool) : Option (Nat × Sort') :=
  go s 0
where
  go : Scope → Nat → Option (Nat × Sort')
    | [], _ => none
    | (y, b) :: s, n => if y == x && p b then some (n, b) else go s (n + 1)

/-- The typed de Bruijn index `In.there^n In.here`. -/
def mkIn : Nat → MacroM Lean.Term
  | 0 => `(Oxide.In.here)
  | n + 1 => do `(Oxide.In.there $(← mkIn n))

/-- The index of the binder named `x` of sort `b`. -/
def inIdx (x : Ident) (b : Sort') (what : String) : TransM Lean.Term := do
  match lookup (← read) x.getId (· == b) with
  | some (n, _) => mkIn n
  | none => Macro.throwErrorAt x s!"unknown {what} {x.getId}"

/-- A term variable of the top frame: a chain of `TVar.skipVar`/`TVar.skipRgn`
ending in `TVar.here`. -/
def tvarIdx (x : Ident) : TransM Lean.Term := do
  let rec go : Scope → MacroM Lean.Term
    | [] => Macro.throwErrorAt x s!"unknown variable {x.getId}"
    | (y, b) :: s =>
      if y == x.getId && b == .var then `(Oxide.TVar.here)
      else match b with
        | .var => do `(Oxide.TVar.skipVar $(← go s))
        | .rgn => do `(Oxide.TVar.skipRgn $(← go s))
        | _ => Macro.throwErrorAt x
            s!"variable {x.getId} is not a variable of the current frame"
  go (← read)

def rgnName : TSyntax `oxide_rgn → MacroM Name
  | `(oxide_rgn| $n:name) => pure n.getName
  | stx => Macro.throwErrorAt stx "ill-formed region"

/-- A region: the most recent binder of that name, concrete (`letrgn`) or
abstract (signature). -/
def transRgn (r : TSyntax `oxide_rgn) : TransM Lean.Term := do
  let x ← rgnName r
  match lookup (← read) x (fun b => b == .rgn || b == .abs) with
  | some (n, .rgn) => `(Oxide.Region.conc $(← mkIn n))
  | some (n, _) => `(Oxide.Region.abs $(← mkIn n))
  | none => Macro.throwErrorAt r s!"unknown region {x}"

/-- A concrete region (for borrows). -/
def transConcRgn (r : TSyntax `oxide_rgn) : TransM Lean.Term := do
  let x ← rgnName r
  match lookup (← read) x (fun b => b == .rgn || b == .abs) with
  | some (n, .rgn) => mkIn n
  | some _ => Macro.throwErrorAt r s!"borrows need a concrete region, but {x} is abstract"
  | none => Macro.throwErrorAt r s!"unknown region {x}"

def transOwn (o : Ident) : TransM Lean.Term :=
  match o.getId with
  | `uniq => `(Oxide.Own.uniq)
  | `shrd => `(Oxide.Own.shrd)
  | _ => Macro.throwErrorAt o "expected `uniq` or `shrd`"

/-- `![t₁, …, tₙ]`. -/
def mkVec (ts : List Lean.Term) : MacroM Lean.Term := `(![$(ts.toArray),*])

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
def binderScope (frms rgns αs : List Name) : Scope :=
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
      let inner {β : Type} (m : TransM β) : TransM β :=
        withReader (binderScope frms rgns αs ++ ·) m
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
        withReader (fun s => infos ++ (Name.anonymous, .frame) :: s) m
      let shape ← infos.mapM fun (_, b) => match b with
        | .var => `(Oxide.Bnd.var)
        | _ => `(Oxide.Bnd.rgn)
      let mut acc ← `(Oxide.FrameTy.nil)
      for e in es.reverse do
        match e with
        | `(oxide_fentry| $_x:ident : $t:oxide_ty) =>
            acc ← `(Oxide.FrameTy.var $(← inner (transTy t)) $acc)
        | _ => acc ← `(Oxide.FrameTy.rgn [] $acc)
      `(Oxide.FrameExpr.frame [$(shape.toArray),*] $acc)
  | stx => Macro.throwErrorAt stx "ill-formed frame expression"
end

/-- Translate a place expression to its root variable and operations (innermost
first). -/
partial def transPlace : TSyntax `oxide_place → TransM (Ident × List Lean.Term)
  | `(oxide_place| $x:ident) => pure (x, [])
  | `(oxide_place| ( $p:oxide_place )) => transPlace p
  | `(oxide_place| * $p:oxide_place) => do
      let (x, ops) ← transPlace p
      pure (x, ops ++ [← `(Oxide.POp.deref)])
  | `(oxide_place| $p:oxide_place.$i:num) => do
      let (x, ops) ← transPlace p
      pure (x, ops ++ [← `(Oxide.POp.proj $i)])
  | stx => Macro.throwErrorAt stx "ill-formed place expression"

def mkPlace (p : TSyntax `oxide_place) : TransM Lean.Term := do
  let (x, ops) ← transPlace p
  `(({ root := $(← tvarIdx x), ops := [$(ops.toArray),*] } : Oxide.PlaceExpr _))

def withVar {α : Type} (x : Name) (m : TransM α) : TransM α :=
  withReader ((x, .var) :: ·) m

/-- Push parameters `x₁, …, x_k` (`x₁` most recent). -/
def withParams {α : Type} (xs : List Name) (m : TransM α) : TransM α :=
  withReader (xs.map (·, .var) ++ ·) m

def transParam : TSyntax `oxide_param → TransM (Name × Lean.Term)
  | `(oxide_param| $x:ident : $t:oxide_ty) => do pure (x.getId, ← transTy t)
  | stx => Macro.throwErrorAt stx "ill-formed parameter"

/-- Referent steps `.n`, `[n]`, `[n₁..n₂]`. -/
def transRStep : TSyntax `oxide_rstep → MacroM Lean.Term
  | `(oxide_rstep| . $i:num) => `(Oxide.RStep.proj $i)
  | `(oxide_rstep| [ $i:num ]) => `(Oxide.RStep.idx $i)
  | `(oxide_rstep| [ $i:num .. $j:num ]) => `(Oxide.RStep.slice $i $j)
  | stx => Macro.throwErrorAt stx "ill-formed referent step"

/-- Runtime values. -/
partial def transVal : TSyntax `oxide_val → TransM Lean.Term
  | `(oxide_val| $n:num) => `(Oxide.Value.num $n)
  | `(oxide_val| ( )) => `(Oxide.Value.unit)
  | `(oxide_val| $x:ident) => match x.getId with
      | `true => `(Oxide.Value.tt)
      | `false => `(Oxide.Value.ff)
      | f => `(Oxide.Value.fn $(quote f.toString))
  | `(oxide_val| dead!) => `(Oxide.Value.dead)
  | `(oxide_val| ptr!( $x:ident $steps:oxide_rstep* )) => do
      let steps ← steps.toList.mapM fun st => (transRStep st : MacroM Lean.Term)
      `(Oxide.Value.ptr { root := $(← inIdx x .var "variable"), steps := [$(steps.toArray),*] })
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

partial def transExpr : TSyntax `oxide → TransM Lean.Term
  | `(oxide| $n:num) => `(Oxide.Term.val (Oxide.Value.num $n))
  | `(oxide| ( )) => `(Oxide.Term.val Oxide.Value.unit)
  | `(oxide| $p:oxide_place) => do
      match p with
      | `(oxide_place| $x:ident) =>
          if (lookup (← read) x.getId (· == .var)).isSome then `(Oxide.Term.place $(← mkPlace p))
          else match x.getId with
            | `true => `(Oxide.Term.val Oxide.Value.tt)
            | `false => `(Oxide.Term.val Oxide.Value.ff)
            | f => `(Oxide.Term.val (Oxide.Value.fn $(quote f.toString)))
      | _ => `(Oxide.Term.place $(← mkPlace p))
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
      `(Oxide.Term.letrgn $(← withReader ((x, .rgn) :: ·) (transExpr e)))
  | `(oxide| let $x:ident : $t:oxide_ty = $e₁:oxide; $e₂:oxide) => do
      let t ← transTy t
      let e₁ ← transExpr e₁
      let e₂ ← withVar x.getId (transExpr e₂)
      `(Oxide.Term.letE $t $e₁ $e₂)
  | `(oxide| $e₁:oxide; $e₂:oxide) => do
      `(Oxide.Term.seq $(← transExpr e₁) $(← transExpr e₂))
  | `(oxide| | $ps:oxide_param,* | -> $r:oxide_ty { $e:oxide }) => do
      let ps ← ps.getElems.toList.mapM transParam
      let r ← transTy r
      let body ← withParams (ps.map (·.1)) (transExpr e)
      `(Oxide.Term.closure $(quote ps.length) $(← mkVec (ps.map (·.2))) $r $body)
  | `(oxide| || -> $r:oxide_ty { $e:oxide }) => do
      `(Oxide.Term.closure 0 ![] $(← transTy r) $(← transExpr e))
  | `(oxide| $f:oxide($args:oxide,*)) => do
      let args ← args.getElems.toList.mapM transExpr
      `(Oxide.Term.app $(← transExpr f) {} ![] ![] ![] $(quote args.length) $(← mkVec args))
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
          $(← mkVec Φs) $(← mkVec rs) $(← mkVec ts) $(quote args.length) $(← mkVec args))
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

def transFn : TSyntax `oxide_fn → MacroM Lean.Term
  | `(oxide_fn| fn $f:ident $[< $bs:oxide_gbinder,* $[; $αs:ident,*]? >]? ( $ps:oxide_param,* )
        -> $r:oxide_ty $[where $[$b₁:oxide_rgn : $b₂:oxide_rgn],*]? { $e:oxide }) => do
      let (frms, rs) ← match bs with
        | some bs => splitBinders bs.getElems.toList
        | none => pure ([], [])
      let αs : List Name := match αs with
        | some (some αs) => αs.getElems.toList.map (·.getId)
        | _ => []
      let s : Scope := binderScope frms rs αs
      let ps ← (ps.getElems.toList.mapM transParam).run s
      let r ← (transTy r).run s
      let body ← (withParams (ps.map (·.1)) (transExpr e)).run ((Name.anonymous, .frame) :: s)
      `(({ name := $(quote f.getId.toString), binders := $(← mkBinders frms rs αs),
           k := $(quote ps.length), params := $(← mkVec (ps.map (·.2))), ret := $r,
           bounds := $(← mkBounds rs b₁ b₂), body := $body } : Oxide.FnDef))
  | stx => Macro.throwErrorAt stx "ill-formed Oxide function definition"

end Oxide.Notation

/-- `[OXIDE| e ]`: the closed Oxide expression `e` as a scoped term `Oxide.Term []`. -/
macro "[OXIDE| " e:oxide " ]" : term => do
  let t ← (Oxide.Notation.transExpr e).run []
  `(($t : Oxide.Term []))

/-- `[OXIDE_TY| τ ]`: a closed Oxide type `Oxide.Ty []`. -/
macro "[OXIDE_TY| " t:oxide_ty " ]" : term => do
  let t ← (Oxide.Notation.transTy t).run []
  `(($t : Oxide.Ty []))

/-- `[OXIDE_FN| fn f<…>(…) -> τ { e } ]`: a global function definition. -/
macro "[OXIDE_FN| " d:oxide_fn " ]" : term => Oxide.Notation.transFn d

end
