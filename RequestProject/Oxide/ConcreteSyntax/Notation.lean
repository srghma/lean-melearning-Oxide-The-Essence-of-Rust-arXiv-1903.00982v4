module
public meta import Lean.Elab.Term
public import RequestProject.Oxide.Syntax.Runtime

/-!
# Oxide: concrete syntax `[OXIDE| … ]`

A concrete-syntax embedding of Oxide in Lean.  `[OXIDE| e ]` elaborates the
Oxide expression `e` to a closed de Bruijn term `Oxide.Term 0`; named variables
and named regions are resolved to de Bruijn indices at macro-expansion time.
`[OXIDE_FN| fn f<…>(…) -> τ { e } ]` elaborates a global function definition
to an `Oxide.FnDef`.

Since `'a` is lexed by Lean as the start of a character literal, regions are
written as Lean name literals: `` `a `` stands for the region `'a`.

Grammar:
* types: `u32`, `bool`, `unit`, `()`, type variables `T`, `` &`a uniq τ ``,
  `` &`a shrd τ ``, `[τ; n]`, `[τ]`, `(τ,)`, `(τ₁, …, τₙ)`, `Either<τ₁, τ₂>`, dead
  types `τ†`, and function types
  `` fn<@φ, …, `a, …; T, …>(τ₁, …, τₙ)[Φ] -> τ where `a : `b, … `` (the binders,
  the captured environment `[Φ]` and the bounds are optional; without `[Φ]` the
  environment is the empty frame);
* frame expressions `Φ`: frame variables `@φ` and concrete frames
  `` @{ x : τ, `r ↦ {}, … } `` (entries oldest first; region entries have empty
  loan sets, since loans refer to absolute places);
* place expressions: `x`, `*p`, `p.n`, `(p)` (nested projections are written
  `(p.0).1`, since `0.1` is lexed as a decimal literal);
* expressions: `()`, `n`, `true`, `false`, `p`, `` &`a ω p ``, `` &`a ω p[e] ``,
  `` &`a ω p[e₁..e₂] ``, `p[e]`, `p := e`, `` letrgn<`a> { e } ``,
  `let x : τ = e₁; e₂`, `e₁; e₂`, `|x₁ : τ₁, …| -> τ { e }`, `|| -> τ { e }`,
  `f(e₁, …)`, `` f::<Φ, …, `a, …; τ, …>(e₁, …) ``, `if e { e₁ } else { e₂ }`,
  `(e,)`, `(e₁, …, eₙ)`, `[e₁, …]`, `for x in e { e' }`, `while e { e' }`,
  `abort!("msg")`, `Left::<τ₁, τ₂>(e)`, `Right::<τ₁, τ₂>(e)`,
  `match e { Left(x) => e₁, Right(y) => e₂ }` and blocks `{ e }`.
  An identifier that is not a bound variable denotes a global function.
* runtime forms: `framed![x₁, …, xₘ] { e }` (the body only sees the `m` variables of
  its own frame, `xₘ` being the most recent), `shift! x { e }`, `shiftprov! { e }`,
  pointers `ptr!(ℓ steps)` with a root level `ℓ` and steps `.n`, `[n]`, `[n₁..n₂]`,
  `dead!`, and arbitrary runtime values `val!(v)` where `v` is built from
  constants, function names, `dead!`, `ptr!(…)`, tuples `(v,)`/`(v₁, …)`, arrays
  `[v, …]`, slices `|v, …|`, injections `Left::<τ₁, τ₂>(v)`/`Right::<…>(v)` and
  closure values `` closure![a = v, … | `r, …] |x : τ, …| -> τ { e } `` (captured
  values oldest first, then the captured regions, the last one being
  `Region.bound 0` in the body; the body sees only the parameters and the
  captured variables).
* global functions: `` fn f<@φ, …, `a, …; T, …>(x : τ, …) -> τ where `a : `b { e } ``.

Ownership qualifiers `uniq`/`shrd` and the base types are parsed as identifiers
(so that they do not become reserved keywords of Lean).
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
syntax:max oxide_ty "†" : oxide_ty
syntax "&" oxide_rgn ident oxide_ty : oxide_ty
syntax "[" oxide_ty ";" num "]" : oxide_ty
syntax "[" oxide_ty "]" : oxide_ty
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
syntax "ptr!" "(" num oxide_rstep* ")" : oxide_val
syntax "(" oxide_val "," oxide_val,+ ")" : oxide_val
syntax "(" oxide_val "," ")" : oxide_val
syntax "[" oxide_val,* "]" : oxide_val
syntax "|" oxide_val,* "|" : oxide_val
syntax "Left" "::<" oxide_ty "," oxide_ty ">" "(" oxide_val ")" : oxide_val
syntax "Right" "::<" oxide_ty "," oxide_ty ">" "(" oxide_val ")" : oxide_val
syntax "closure!" "[" sepBy(ident " = " oxide_val, ",") ("|" oxide_rgn,*)? "]"
  "|" oxide_param,* "|" " -> " oxide_ty "{" oxide "}" : oxide_val

syntax "dead!" : oxide
syntax "ptr!" "(" num oxide_rstep* ")" : oxide
syntax "val!" "(" oxide_val ")" : oxide
syntax "framed!" "[" ident,* "]" "{" oxide "}" : oxide
syntax "shift!" ident "{" oxide "}" : oxide
syntax "shiftprov!" "{" oxide "}" : oxide

syntax "fn " ident ("<" oxide_gbinder,* (";" ident,*)? ">")? "(" oxide_param,* ")" " -> " oxide_ty
  (" where " sepBy1(oxide_rgn " : " oxide_rgn, ","))? "{" oxide "}" : oxide_fn

end Oxide.Notation

end

public meta section

namespace Oxide.Notation

open Lean

/-- Names in scope during the translation.  All lists are innermost first, except
`absRgns`, `tyVars` and `frmVars`, which list the binders of the enclosing function in
order (index `i` = `i`-th binder). -/
structure Scope where
  vars : List Name := []
  letRgns : List Name := []
  absRgns : List Name := []
  tyVars : List Name := []
  frmVars : List Name := []

abbrev TransM := ReaderT Scope MacroM

def idx? (l : List Name) (x : Name) : Option Nat := l.idxOf? x

def transRgn : TSyntax `oxide_rgn → TransM Lean.Term
  | `(oxide_rgn| $n:name) => do
      let s ← read
      let x := n.getName
      match idx? s.letRgns x with
      | some i => `(Oxide.Region.bound $(quote i))
      | none => match idx? s.absRgns x with
        | some i => `(Oxide.Region.abs $(quote i))
        | none => Macro.throwErrorAt n s!"unknown region {x}"
  | stx => Macro.throwErrorAt stx "ill-formed region"

def transOwn (o : Ident) : TransM Lean.Term :=
  match o.getId with
  | `uniq => `(Oxide.Own.uniq)
  | `shrd => `(Oxide.Own.shrd)
  | _ => Macro.throwErrorAt o "expected `uniq` or `shrd`"

def rgnName : TSyntax `oxide_rgn → MacroM Name
  | `(oxide_rgn| $n:name) => pure n.getName
  | stx => Macro.throwErrorAt stx "ill-formed region"

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

/-- The index of an abstract region among the given binders. -/
def absIdxIn (l : List Name) (r : TSyntax `oxide_rgn) : MacroM Nat := do
  let x ← rgnName r
  match idx? l x with
  | some i => pure i
  | none => Macro.throwErrorAt r s!"unknown abstract region {x}"

/-- Extend the scope with the binders of a polymorphic signature. -/
def extendScope (frms rgns αs : List Name) (s : Scope) : Scope :=
  { s with absRgns := rgns ++ s.absRgns, tyVars := αs ++ s.tyVars, frmVars := frms ++ s.frmVars }

/-- The name of a region entry of a frame. -/
def fentryRgn : TSyntax `oxide_fentry → Option Name
  | `(oxide_fentry| $n:name ↦ { }) => some n.getName
  | _ => none

mutual
partial def transTy : TSyntax `oxide_ty → TransM Lean.Term
  | `(oxide_ty| $x:ident) => do
      match x.getId with
      | `u32 => `(Oxide.Ty.u32)
      | `bool => `(Oxide.Ty.bool)
      | `unit => `(Oxide.Ty.unit)
      | a => match idx? (← read).tyVars a with
        | some i => `(Oxide.Ty.tvar $(quote i))
        | none => Macro.throwErrorAt x s!"unknown type {a}"
  | `(oxide_ty| ( )) => `(Oxide.Ty.unit)
  | `(oxide_ty| ( $t:oxide_ty )) => transTy t
  | `(oxide_ty| ( $t:oxide_ty , )) => do `(Oxide.Ty.tuple [$(← transTy t)])
  | `(oxide_ty| ( $t:oxide_ty, $ts:oxide_ty,* )) => do
      let ts ← (t :: ts.getElems.toList).mapM transTy
      `(Oxide.Ty.tuple [$(ts.toArray),*])
  | `(oxide_ty| $t:oxide_ty †) => do `(Oxide.Ty.dead $(← transTy t))
  | `(oxide_ty| & $r:oxide_rgn $o:ident $t:oxide_ty) => do
      `(Oxide.Ty.ref $(← transRgn r) $(← transOwn o) $(← transTy t))
  | `(oxide_ty| [ $t:oxide_ty ; $n:num ]) => do `(Oxide.Ty.array $(← transTy t) $n)
  | `(oxide_ty| [ $t:oxide_ty ]) => do `(Oxide.Ty.slice $(← transTy t))
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
      let inner {β : Type} (m : TransM β) : TransM β := withReader (extendScope frms rgns αs) m
      let ts ← inner (ts.getElems.toList.mapM transTy)
      let r ← inner (transTy r)
      let Φ ← match Φ with
        | some Φ => inner (transFrm Φ)
        | none => `(Oxide.FrameExpr.frame [])
      let bnds ← match b₁, b₂ with
        | some b₁, some b₂ => (b₁.toList.zip b₂.toList).mapM fun (x, y) => do
            let i ← absIdxIn rgns x
            let j ← absIdxIn rgns y
            `(($(quote i), $(quote j)))
        | _, _ => pure []
      `(Oxide.Ty.fn $(quote frms.length) $(quote rgns.length) $(quote αs.length)
          [$(ts.toArray),*] $r $Φ [$(bnds.toArray),*])
  | stx => Macro.throwErrorAt stx "ill-formed Oxide type"

/-- Frame expressions: a frame variable `@φ`, or a frame `@{ x : τ, `r ↦ {}, … }`
(entries oldest first; inside the frame its own regions are `Region.bound j`, the
`j`-th most recent region entry). -/
partial def transFrm : TSyntax `oxide_frm → TransM Lean.Term
  | `(oxide_frm| @ $x:ident) => do
      match idx? (← read).frmVars x.getId with
      | some i => `(Oxide.FrameExpr.var $(quote i))
      | none => Macro.throwErrorAt x s!"unknown frame variable {x.getId}"
  | `(oxide_frm| @ { $es:oxide_fentry,* }) => do
      let es := es.getElems.toList
      let rgns := (es.filterMap fentryRgn).reverse
      let inner {β : Type} (m : TransM β) : TransM β :=
        withReader (fun s => { s with letRgns := rgns ++ s.letRgns }) m
      let mut ents : Array Lean.Term := #[]
      for e in es do
        match e with
        | `(oxide_fentry| $_x:ident : $t:oxide_ty) =>
            let t ← inner (transTy t)
            ents := ents.push (← `(Oxide.FrameEntry.var $t))
        | `(oxide_fentry| $_r:oxide_rgn ↦ { }) =>
            ents := ents.push (← `(Oxide.FrameEntry.rgn []))
        | _ => Macro.throwErrorAt e "ill-formed frame entry"
      `(Oxide.FrameExpr.frame [$(ents.reverse),*])
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
      let n : Nat := i.getNat
      pure (x, ops ++ [← `(Oxide.POp.proj $(quote n))])
  | stx => Macro.throwErrorAt stx "ill-formed place expression"

def mkPlace (p : TSyntax `oxide_place) : TransM Lean.Term := do
  let (x, ops) ← transPlace p
  match idx? (← read).vars x.getId with
  | some i =>
      `(({ root := ⟨$(quote i), by decide⟩, ops := [$(ops.toArray),*] } : Oxide.PlaceExpr _))
  | none => Macro.throwErrorAt x s!"unknown variable {x.getId}"

def withVar (x : Name) (m : TransM α) : TransM α :=
  withReader (fun s => { s with vars := x :: s.vars }) m

def withVars (xs : List Name) (m : TransM α) : TransM α :=
  withReader (fun s => { s with vars := xs.reverse ++ s.vars }) m

def mkTerms (ts : List Lean.Term) : MacroM Lean.Term := do
  ts.foldrM (fun t acc => `(Oxide.Terms.cons $t $acc)) (← `(Oxide.Terms.nil))

def transParam : TSyntax `oxide_param → TransM (Name × Lean.Term)
  | `(oxide_param| $x:ident : $t:oxide_ty) => do pure (x.getId, ← transTy t)
  | stx => Macro.throwErrorAt stx "ill-formed parameter"

/-- Referent steps `.n`, `[n]`, `[n₁..n₂]`. -/
def transRStep : TSyntax `oxide_rstep → MacroM Lean.Term
  | `(oxide_rstep| . $i:num) => `(Oxide.RStep.proj $i)
  | `(oxide_rstep| [ $i:num ]) => `(Oxide.RStep.idx $i)
  | `(oxide_rstep| [ $i:num .. $j:num ]) => `(Oxide.RStep.slice $i $j)
  | stx => Macro.throwErrorAt stx "ill-formed referent step"

def mkPtr (root : TSyntax `num) (steps : Array (TSyntax `oxide_rstep)) : MacroM Lean.Term := do
  let steps ← steps.toList.mapM transRStep
  `(Oxide.Value.ptr { root := $root, steps := [$(steps.toArray),*] })

mutual
partial def transExpr : TSyntax `oxide → TransM Lean.Term
  | `(oxide| $n:num) => `(Oxide.Term.val (Oxide.Value.num $n))
  | `(oxide| ( )) => `(Oxide.Term.val Oxide.Value.unit)
  | `(oxide| $p:oxide_place) => do
      match p with
      | `(oxide_place| $x:ident) =>
          if (idx? (← read).vars x.getId).isSome then `(Oxide.Term.place $(← mkPlace p))
          else match x.getId with
            | `true => `(Oxide.Term.val Oxide.Value.tt)
            | `false => `(Oxide.Term.val Oxide.Value.ff)
            | f => `(Oxide.Term.val (Oxide.Value.fn $(quote f.toString)))
      | _ => `(Oxide.Term.place $(← mkPlace p))
  | `(oxide| & $r:oxide_rgn $o:ident $p:oxide_place) => do
      `(Oxide.Term.borrow $(← transRgn r) $(← transOwn o) $(← mkPlace p))
  | `(oxide| & $r:oxide_rgn $o:ident $p:oxide_place [ $e:oxide ]) => do
      `(Oxide.Term.borrowIdx $(← transRgn r) $(← transOwn o) $(← mkPlace p) $(← transExpr e))
  | `(oxide| & $r:oxide_rgn $o:ident $p:oxide_place [ $e₁:oxide .. $e₂:oxide ]) => do
      `(Oxide.Term.borrowSlice $(← transRgn r) $(← transOwn o) $(← mkPlace p)
          $(← transExpr e₁) $(← transExpr e₂))
  | `(oxide| $p:oxide_place [ $e:oxide ]) => do
      `(Oxide.Term.index $(← mkPlace p) $(← transExpr e))
  | `(oxide| $p:oxide_place := $e:oxide) => do
      `(Oxide.Term.assign $(← mkPlace p) $(← transExpr e))
  | `(oxide| letrgn < $r:oxide_rgn > { $e:oxide }) => do
      match r with
      | `(oxide_rgn| $n:name) =>
          let e ← withReader (fun s => { s with letRgns := n.getName :: s.letRgns }) (transExpr e)
          `(Oxide.Term.letrgn $e)
      | _ => Macro.throwErrorAt r "ill-formed region"
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
      let body ← withVars (ps.map (·.1)) (transExpr e)
      let tys := ps.map (·.2)
      `(Oxide.Term.closure $(quote ps.length) [$(tys.toArray),*] $r $body)
  | `(oxide| || -> $r:oxide_ty { $e:oxide }) => do
      `(Oxide.Term.closure 0 [] $(← transTy r) $(← transExpr e))
  | `(oxide| $f:oxide($args:oxide,*)) => do
      let args ← args.getElems.toList.mapM transExpr
      `(Oxide.Term.app $(← transExpr f) [] [] [] $(← mkTerms args))
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
      `(Oxide.Term.app $(← transExpr f) [$(Φs.toArray),*] [$(rs.toArray),*] [$(ts.toArray),*]
          $(← mkTerms args))
  | `(oxide| if $c:oxide { $e₁:oxide } else { $e₂:oxide }) => do
      `(Oxide.Term.ite $(← transExpr c) $(← transExpr e₁) $(← transExpr e₂))
  | `(oxide| ( $e:oxide , )) => do
      `(Oxide.Term.tuple $(← mkTerms [← transExpr e]))
  | `(oxide| ( $e:oxide, $es:oxide,* )) => do
      let es ← (e :: es.getElems.toList).mapM transExpr
      `(Oxide.Term.tuple $(← mkTerms es))
  | `(oxide| [ $es:oxide,* ]) => do
      let es ← es.getElems.toList.mapM transExpr
      `(Oxide.Term.array $(← mkTerms es))
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
  | `(oxide| dead!) => `(Oxide.Term.val Oxide.Value.dead)
  | `(oxide| ptr!( $r:num $steps:oxide_rstep* )) => do `(Oxide.Term.val $(← mkPtr r steps))
  | `(oxide| val!( $v:oxide_val )) => do `(Oxide.Term.val $(← transVal v))
  | `(oxide| framed![ $xs:ident,* ] { $e:oxide }) => do
      let xs := xs.getElems.toList.map (·.getId)
      let e ← withReader (fun s => { s with vars := xs.reverse }) (transExpr e)
      `(Oxide.Term.framed $(quote xs.length) $e)
  | `(oxide| shift! $x:ident { $e:oxide }) => do
      `(Oxide.Term.shift $(← withVar x.getId (transExpr e)))
  | `(oxide| shiftprov! { $e:oxide }) => do `(Oxide.Term.shiftRgn $(← transExpr e))
  | stx => Macro.throwErrorAt stx "ill-formed Oxide expression"

/-- Runtime values. -/
partial def transVal : TSyntax `oxide_val → TransM Lean.Term
  | `(oxide_val| $n:num) => `(Oxide.Value.num $n)
  | `(oxide_val| ( )) => `(Oxide.Value.unit)
  | `(oxide_val| $x:ident) => match x.getId with
      | `true => `(Oxide.Value.tt)
      | `false => `(Oxide.Value.ff)
      | f => `(Oxide.Value.fn $(quote f.toString))
  | `(oxide_val| dead!) => `(Oxide.Value.dead)
  | `(oxide_val| ptr!( $r:num $steps:oxide_rstep* )) => mkPtr r steps
  | `(oxide_val| ( $v:oxide_val , )) => do `(Oxide.Value.tuple [$(← transVal v)])
  | `(oxide_val| ( $v:oxide_val, $vs:oxide_val,* )) => do
      let vs ← (v :: vs.getElems.toList).mapM transVal
      `(Oxide.Value.tuple [$(vs.toArray),*])
  | `(oxide_val| [ $vs:oxide_val,* ]) => do
      let vs ← vs.getElems.toList.mapM transVal
      `(Oxide.Value.array [$(vs.toArray),*])
  | `(oxide_val| | $vs:oxide_val,* |) => do
      let vs ← vs.getElems.toList.mapM transVal
      `(Oxide.Value.slice [$(vs.toArray),*])
  | `(oxide_val| Left::<$t₁:oxide_ty, $t₂:oxide_ty>($v:oxide_val)) => do
      `(Oxide.Value.inl $(← transTy t₁) $(← transTy t₂) $(← transVal v))
  | `(oxide_val| Right::<$t₁:oxide_ty, $t₂:oxide_ty>($v:oxide_val)) => do
      `(Oxide.Value.inr $(← transTy t₁) $(← transTy t₂) $(← transVal v))
  | `(oxide_val| closure![ $[$xs:ident = $vs:oxide_val],* $[| $rs:oxide_rgn,*]? ]
        | $ps:oxide_param,* | -> $r:oxide_ty { $e:oxide }) => do
      let xs := xs.toList.map (·.getId)
      let vs ← vs.toList.mapM transVal
      let rs ← match rs with
        | some rs => rs.getElems.toList.mapM (fun r => (rgnName r : MacroM Name))
        | none => pure []
      let inner {β : Type} (m : TransM β) : TransM β :=
        withReader (fun s => { s with letRgns := rs.reverse ++ s.letRgns }) m
      let ps ← ps.getElems.toList.mapM transParam
      let r ← transTy r
      let body ← inner (withReader (fun s => { s with vars := (xs ++ ps.map (·.1)).reverse })
        (transExpr e))
      let tys := ps.map (·.2)
      `(Oxide.Value.closure $(quote xs.length) $(quote ps.length) $(quote rs.length)
          [$(vs.reverse.toArray),*] [$(tys.toArray),*] $r $body)
  | stx => Macro.throwErrorAt stx "ill-formed Oxide value"

end

def absIdx (s : Scope) (r : TSyntax `oxide_rgn) : MacroM Nat := do
  let x ← rgnName r
  match idx? s.absRgns x with
  | some i => pure i
  | none => Macro.throwErrorAt r s!"unknown abstract region {x}"

def transFn : TSyntax `oxide_fn → MacroM Lean.Term
  | `(oxide_fn| fn $f:ident $[< $bs:oxide_gbinder,* $[; $αs:ident,*]? >]? ( $ps:oxide_param,* )
        -> $r:oxide_ty $[where $[$b₁:oxide_rgn : $b₂:oxide_rgn],*]? { $e:oxide }) => do
      let (frms, rs) ← match bs with
        | some bs => splitBinders bs.getElems.toList
        | none => pure ([], [])
      let αs : List Name := match αs with
        | some (some αs) => αs.getElems.toList.map (·.getId)
        | _ => []
      let s : Scope := { absRgns := rs, tyVars := αs, frmVars := frms }
      let ps ← (ps.getElems.toList.mapM transParam).run s
      let r ← (transTy r).run s
      let body ← (withVars (ps.map (·.1)) (transExpr e)).run s
      let bnds ← match b₁, b₂ with
        | some b₁, some b₂ => (b₁.toList.zip b₂.toList).mapM fun (x, y) => do
            let i ← absIdx s x
            let j ← absIdx s y
            `(($(quote i), $(quote j)))
        | _, _ => pure []
      let tys := ps.map (·.2)
      `(({ name := $(quote f.getId.toString), nφ := $(quote frms.length),
           nϱ := $(quote rs.length), nα := $(quote αs.length), params := [$(tys.toArray),*],
           ret := $r, bounds := [$(bnds.toArray),*], body := $body } : Oxide.FnDef))
  | stx => Macro.throwErrorAt stx "ill-formed Oxide function definition"

end Oxide.Notation

/-- `[OXIDE| e ]`: the closed Oxide expression `e` as a de Bruijn term `Oxide.Term 0`. -/
macro "[OXIDE| " e:oxide " ]" : term => do
  let t ← (Oxide.Notation.transExpr e).run {}
  `(($t : Oxide.Term 0))

/-- `[OXIDE_TY| τ ]`: a closed Oxide type. -/
macro "[OXIDE_TY| " t:oxide_ty " ]" : term => do
  let t ← (Oxide.Notation.transTy t).run {}
  `(($t : Oxide.Ty))

/-- `[OXIDE_FN| fn f<…>(…) -> τ { e } ]`: a global function definition. -/
macro "[OXIDE_FN| " d:oxide_fn " ]" : term => Oxide.Notation.transFn d

end
