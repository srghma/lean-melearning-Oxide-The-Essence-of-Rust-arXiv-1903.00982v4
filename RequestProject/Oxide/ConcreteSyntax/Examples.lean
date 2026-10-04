module
public import RequestProject.Oxide.ConcreteSyntax.Notation
public import RequestProject.Oxide.Metatheory.Regressions.MoveCopy
public import RequestProject.Oxide.Metatheory.Regressions.ClosureScopes

/-!
# Oxide: examples of the `[OXIDE| … ]` syntax

All examples elaborate to scope-indexed terms; the equations are checked by
`rfl`.  The scope of each subterm is visible in the indices: `TVar.here`,
`TVar.skipVar`, `TVar.skipRgn` for term variables of the current frame, and
`In.here`/`In.there` for regions, type variables and frame variables.

A bare place without dereference (`x`, `x.1`) is a *move* (`Term.move`, which
takes a `TPlace`, so it cannot contain a dereference); a place through a
dereference (`*r`) is a *copy* (`Term.copy`).  `copy!(p)` and `move!(p)` choose
explicitly.
-/

namespace Oxide.Examples

open Oxide

/-- `let x : u32 = 5; x`: the use of `x` is a move. -/
example : ([OXIDE| let x : u32 = 5; x ] : Program []) =
    Term.letE Ty.u32 (.val (Value.num 5)) (.move ⟨.here, []⟩) := rfl

/-- The innermost binding is `TVar.here`; older variables are reached by skipping.
`copy!(x)` copies. -/
example : ([OXIDE| let x : u32 = 1; let y : u32 = 2; (copy!(x), y) ] : Program []) =
    Term.letE Ty.u32 (.val (Value.num 1)) (.letE Ty.u32 (.val (Value.num 2))
      (.tuple 2 ![.copy (.place ⟨.skipVar .here, []⟩), .move ⟨.here, []⟩])) := rfl

/-- Regions bound by `letrgn` are binders of the scope: a borrow names one by a
typed index `In .rgn _`, and term variables skip region binders with `skipRgn`.
A dereference is structure of the place expression (`PExpr.deref`), not an
element of a list. -/
example : ([OXIDE|
    letrgn<`a> {
      let x : u32 = 5;
      letrgn<`b> {
        let r : &`a uniq u32 = &`a uniq x;
        *r := 6;
        *r
      }
    } ] : Program []) =
    Term.letrgn
      (.letE Ty.u32 (.val (Value.num 5))
        (.letrgn
          (.letE (.ref (.conc (.there (.there .here))) .uniq (.sized Ty.u32))
            (.borrow (.there (.there .here)) .uniq (.place ⟨.skipRgn .here, []⟩))
            (.seq (.assign (.deref (.place ⟨.here, []⟩) []) (.val (Value.num 6)))
              (.copy (.deref (.place ⟨.here, []⟩) [])))))) :=
  rfl

/-- Closures are written in their own scope: the parameters (the first parameter
is `TVar.here`), then the captured frame (here the variable `y`, recorded by the
capture list `Cap.var`), then the frame boundary and the outer binders (none
here). -/
example : ([OXIDE|
    let y : u32 = 1;
    let f : fn(u32, bool) -> u32 = |a : u32, b : bool| -> u32 { if b { a } else { copy!(y) } };
    f(3, true) ] : Program []) =
    Term.letE Ty.u32 (.val (Value.num 1))
      (.letE (.fn {} 2 ![Ty.u32, Ty.bool] Ty.u32 FrameExpr.empty [])
        (.closure [.var] (.var .here .nil) [] .nil 2 ![Ty.u32, Ty.bool] Ty.u32
          (.ite (.move ⟨.skipVar .here, []⟩) (.move ⟨.here, []⟩)
            (.copy (.place ⟨.skipVar (.skipVar .here), []⟩))))
        (.app (.move ⟨.here, []⟩) {} .none 2 ![.val (Value.num 3), .val Value.tt])) := rfl

/-- Sums, `match`, arrays, slices, loops and tuples with projections. -/
example : ([OXIDE|
    letrgn<`a> {
      let s : Either<u32, bool> = Left::<u32, bool>(7);
      let arr : [u32; 3] = [1, 2, 3];
      let p : (u32, (bool, u32)) = (0, (true, 1));
      for z in &`a shrd arr[0..2] { () };
      while false { () };
      (p.1).0 := false;
      match s { Left(n) => n, Right(b) => arr[2] }
    } ] : Program []) =
    Term.letrgn
      (.letE (.sum Ty.u32 Ty.bool) (.inl Ty.u32 Ty.bool (.val (Value.num 7)))
      (.letE (.array Ty.u32 3)
        (.array 3 ![.val (Value.num 1), .val (Value.num 2), .val (Value.num 3)])
      (.letE (.tuple 2 ![Ty.u32, .tuple 2 ![Ty.bool, Ty.u32]])
        (.tuple 2 ![.val (Value.num 0), .tuple 2 ![.val Value.tt, .val (Value.num 1)]])
      (.seq (.forE (.borrowSlice (.there (.there (.there .here))) .shrd
          (.place ⟨.skipVar .here, []⟩) (.val (Value.num 0)) (.val (Value.num 2))) (.val Value.unit))
      (.seq (.whileE (.val Value.ff) (.val Value.unit))
      (.seq (.assign (.place ⟨.here, [1, 0]⟩) (.val Value.ff))
        (.matchE (.move ⟨.skipVar (.skipVar .here), []⟩) (.move ⟨.here, []⟩)
          (.index (.place ⟨.skipVar (.skipVar .here), []⟩) (.val (Value.num 2)))))))))) :=
  rfl

/-- A polymorphic global function.  Its signature lives in the scope of its
binders (type variables most recent, then abstract regions); its body in a new
frame holding the parameters.  It calls no global function, so it is a
definition against any signature. -/
def swapFirst {sig : Sig} : FnDef sig := [OXIDE_FN|
  fn swap_first<`a, `b; T>(x : &`a uniq (T, T), y : &`b shrd u32) -> u32 where `a : `b {
    *x
  } ]

example : (swapFirst (sig := [])).fsig.binders = { nϱ := 2, nα := 1 } ∧ (swapFirst (sig := [])).fsig.k = 2 := ⟨rfl, rfl⟩

example : (swapFirst (sig := [])).fsig.params ⟨0, by decide⟩ =
    .ref (.abs (.there .here)) .uniq (.sized (.tuple 2 ![.tvar .here, .tvar .here])) := rfl

example : (swapFirst (sig := [])).fsig.params ⟨1, by decide⟩ =
    .ref (.abs (.there (.there .here))) .shrd (.sized Ty.u32) := rfl

example : (swapFirst (sig := [])).body = .copy (.deref (.place ⟨.here, []⟩) []) := rfl

/-- A global signature declaring `swap_first`. -/
abbrev sig₁ : Sig := [(swapFirst (sig := [])).fsig]

/-- Calling a global function with explicit region and type arguments.  Global
functions are indices into the signature (`FnIdx`), so a call cannot name an
undeclared function; the type arguments are one bundle `TArgs`. -/
example : ([OXIDE{swap_first}|
    letrgn<`r> {
      let x : (u32, u32) = (1, 2);
      let n : u32 = 0;
      swap_first::<`r, `r; u32>(&`r uniq x, &`r shrd n)
    } ] : Program sig₁) =
    Term.letrgn (.letE (.tuple 2 ![Ty.u32, Ty.u32])
      (.tuple 2 ![.val (Value.num 1), .val (Value.num 2)])
      (.letE Ty.u32 (.val (Value.num 0))
        (.app (.val (.fn .here)) { nϱ := 2, nα := 1 }
          ⟨![], ![.conc (.there (.there .here)), .conc (.there (.there .here))], ![Ty.u32]⟩ 2
          ![.borrow (.there (.there .here)) .uniq (.place ⟨.skipVar .here, []⟩),
            .borrow (.there (.there .here)) .shrd (.place ⟨.here, []⟩)]))) := rfl

/-- A global environment for `sig₁`: the body of `swap_first`. -/
def G₁ : GlobalEnv sig₁ := .cons (swapFirst (sig := sig₁)).body .nil

/-- A function binding a frame variable `@φ`: its parameter is a closure whose
captured environment is the frame variable. -/
def applyF : FnDef [] := [OXIDE_FN|
  fn apply<@φ, `a>(f : fn(u32)[@φ] -> u32, x : &`a shrd u32) -> u32 { f(*x) } ]

example : applyF.fsig.params ⟨0, by decide⟩ =
    .fn {} 1 ![Ty.u32] Ty.u32 (.var (.there .here)) [] := rfl

/-- Calls passing a literal frame `@{…}`, whose types live in the scope of the
frame itself (here `y` points into the frame's own region `s`). -/
example : ([OXIDE{apply, g, z}|
      letrgn<`r> { apply::<@{x : u32, `s ↦ {}, y : &`s shrd u32}, `r; >(g, z) } ] :
      Program [applyF.fsig, (swapFirst (sig := [])).fsig, (swapFirst (sig := [])).fsig]) =
    Term.letrgn (.app (.val (.fn .here)) { nφ := 1, nϱ := 1 }
      ⟨![.frame [.var, .rgn, .var]
        (.var (.ref (.conc (.there .here)) .shrd (.sized Ty.u32)) (.rgn [] (.var Ty.u32 .nil)))],
       ![.conc .here], ![]⟩ 2 ![.val (.fn (.there .here)), .val (.fn (.there (.there .here)))]) :=
  rfl

/-- A polymorphic function type: the binders scope the parameters, the
environment, the result and the bounds. -/
example : [OXIDE_TY| fn<@φ, `a, `b; T>(&`a uniq T, &`b shrd T)[@φ] -> T where `a : `b ] =
    .fn { nφ := 1, nϱ := 2, nα := 1 } 2
      ![.ref (.abs (.there .here)) .uniq (.sized (.tvar .here)),
        .ref (.abs (.there (.there .here))) .shrd (.sized (.tvar .here))]
      (.tvar .here) (.var (.there (.there (.there .here)))) [(0, 1)] := rfl

/-- References to slices; 1-tuples. -/
example : [OXIDE_TY| fn<`a>(&`a shrd [u32]) -> (u32,) ] =
    .fn { nϱ := 1 } 1 ![.ref (.abs .here) .shrd (.slice Ty.u32)] (.tuple 1 ![Ty.u32])
      FrameExpr.empty [] := rfl

/-- Runtime values, including a pointer into the stack. -/
example : ([OXIDE| let a : (u32, u32) = (1, 2);
    val!((ptr!(a .1), [true, false], |2, 3|, Left::<u32, bool>(4), (dead!,))) ] : Program []) =
    Term.letE (.tuple 2 ![Ty.u32, Ty.u32]) (.tuple 2 ![.val (Value.num 1), .val (Value.num 2)])
      (.val (.tuple 5 ![.ptr (.place ⟨.here, [1]⟩), .array 2 ![Value.tt, Value.ff],
        .slice 2 ![Value.num 2, Value.num 3], .inl Ty.u32 Ty.bool (Value.num 4),
        .tuple 1 ![.dead]])) := rfl

/-! ### Running and typing programs written in the concrete syntax -/

/-- The abstract machine runs `let x : u32 = 5; x` to the final configuration
holding `5`: push the `let`, bind `x` (pushing a `popVar` continuation), move
out of `x`, and pop `x` again. -/
example {sig : Sig} (G : GlobalEnv sig) :
    Steps G (Config.init [OXIDE| let x : u32 = 5; x ]) ⟨[], .nil, .val (Value.num 5), .halt⟩ := by
  refine .step _ _ _ (Step.letPush _ _ _ _ _) ?_
  refine .step _ _ _ (Step.letE _ _ _ _ _) ?_
  refine .step _ _ _ (Step.move _ _ ⟨.here, []⟩ _ (Value.num 5) rfl rfl) ?_
  refine .step _ _ _ (Step.popVar _ _ (Value.num 5) _ rfl) ?_
  exact .refl _

example : (⟨[], .nil, .val (Value.num 5), .halt⟩ : Config []).IsFinal := .inl ⟨_, rfl, rfl⟩

/-- The program of the move/copy regression, in concrete syntax. -/
example : (tsProg : Program []) =
    [OXIDE| let x : bool = true; copy!(x); if copy!(x) { () } else { () } ] := rfl

/-- The program of the closure-scope regression, in concrete syntax: the closure
body mentions `r`, so `r` is an outer binder of the closure. -/
example : (tpProg : Program []) =
    [OXIDE| letrgn<`r> { || -> () { Right::<&`r shrd (), ()>(()); () } } ] := rfl

end Oxide.Examples
