module
public import RequestProject.Oxide.ConcreteSyntax.Notation
public import RequestProject.Oxide.Metatheory.Counterexamples.TypeSafety
public import RequestProject.Oxide.Metatheory.Counterexamples.Progress

/-!
# Oxide: examples of the `[OXIDE| … ]` syntax

All examples elaborate to scope-indexed terms; the equations are checked by
`rfl`.  The scope of each subterm is visible in the indices: `TVar.here`,
`TVar.skipVar`, `TVar.skipRgn` for term variables of the current frame, and
`In.here`/`In.there` for regions, type variables and frame variables.
-/

namespace Oxide.Examples

open Oxide

/-- `let x : u32 = 5; x` -/
example : [OXIDE| let x : u32 = 5; x ] =
    Term.letE Ty.u32 (.val (Value.num 5)) (.place ⟨.here, []⟩) := rfl

/-- The innermost binding is `TVar.here`; older variables are reached by skipping. -/
example : [OXIDE| let x : u32 = 1; let y : u32 = 2; (x, y) ] =
    Term.letE Ty.u32 (.val (Value.num 1)) (.letE Ty.u32 (.val (Value.num 2))
      (.tuple 2 ![.place ⟨.skipVar .here, []⟩, .place ⟨.here, []⟩])) := rfl

/-- Regions bound by `letrgn` are binders of the scope: a borrow names one by a
typed index `In .rgn _`, and term variables skip region binders with `skipRgn`. -/
example : [OXIDE|
    letrgn<`a> {
      let x : u32 = 5;
      letrgn<`b> {
        let r : &`a uniq u32 = &`a uniq x;
        *r := 6;
        *r
      }
    } ] =
    Term.letrgn
      (.letE Ty.u32 (.val (Value.num 5))
        (.letrgn
          (.letE (.ref (.conc (.there (.there .here))) .uniq (.sized Ty.u32))
            (.borrow (.there (.there .here)) .uniq ⟨.skipRgn .here, []⟩)
            (.seq (.assign ⟨.here, [.deref]⟩ (.val (Value.num 6))) (.place ⟨.here, [.deref]⟩))))) :=
  rfl

/-- Closures: the parameters are the most recent binders of the body (the first
parameter is `TVar.here`), and the body captures the variables of the current
frame. -/
example : [OXIDE|
    let y : u32 = 1;
    let f : fn(u32, bool) -> u32 = |a : u32, b : bool| -> u32 { if b { a } else { y } };
    f(3, true) ] =
    Term.letE Ty.u32 (.val (Value.num 1))
      (.letE (.fn {} 2 ![Ty.u32, Ty.bool] Ty.u32 FrameExpr.empty [])
        (.closure 2 ![Ty.u32, Ty.bool] Ty.u32
          (.ite (.place ⟨.skipVar .here, []⟩) (.place ⟨.here, []⟩)
            (.place ⟨.skipVar (.skipVar .here), []⟩)))
        (.app (.place ⟨.here, []⟩) {} ![] ![] ![] 2 ![.val (Value.num 3), .val Value.tt])) := rfl

/-- Sums, `match`, arrays, slices, loops and tuples with projections. -/
example : [OXIDE|
    letrgn<`a> {
      let s : Either<u32, bool> = Left::<u32, bool>(7);
      let arr : [u32; 3] = [1, 2, 3];
      let p : (u32, (bool, u32)) = (0, (true, 1));
      for z in &`a shrd arr[0..2] { () };
      while false { () };
      (p.1).0 := false;
      match s { Left(n) => n, Right(b) => arr[2] }
    } ] =
    Term.letrgn
      (.letE (.sum Ty.u32 Ty.bool) (.inl Ty.u32 Ty.bool (.val (Value.num 7)))
      (.letE (.array Ty.u32 3)
        (.array 3 ![.val (Value.num 1), .val (Value.num 2), .val (Value.num 3)])
      (.letE (.tuple 2 ![Ty.u32, .tuple 2 ![Ty.bool, Ty.u32]])
        (.tuple 2 ![.val (Value.num 0), .tuple 2 ![.val Value.tt, .val (Value.num 1)]])
      (.seq (.forE (.borrowSlice (.there (.there (.there .here))) .shrd ⟨.skipVar .here, []⟩
          (.val (Value.num 0)) (.val (Value.num 2))) (.val Value.unit))
      (.seq (.whileE (.val Value.ff) (.val Value.unit))
      (.seq (.assign ⟨.here, [.proj 1, .proj 0]⟩ (.val Value.ff))
        (.matchE (.place ⟨.skipVar (.skipVar .here), []⟩) (.place ⟨.here, []⟩)
          (.index ⟨.skipVar (.skipVar .here), []⟩ (.val (Value.num 2)))))))))) :=
  rfl

/-- A polymorphic global function.  Its signature lives in the scope of its
binders (type variables most recent, then abstract regions); its body in a new
frame holding the parameters. -/
def swapFirst : FnDef := [OXIDE_FN|
  fn swap_first<`a, `b; T>(x : &`a uniq (T, T), y : &`b shrd u32) -> u32 where `a : `b {
    *x
  } ]

example : swapFirst.binders = { nϱ := 2, nα := 1 } ∧ swapFirst.k = 2 := ⟨rfl, rfl⟩

example : swapFirst.params ⟨0, by decide⟩ =
    .ref (.abs (.there .here)) .uniq (.sized (.tuple 2 ![.tvar .here, .tvar .here])) := rfl

example : swapFirst.params ⟨1, by decide⟩ = .ref (.abs (.there (.there .here))) .shrd (.sized Ty.u32) := rfl

example : swapFirst.body = .place ⟨.here, [.deref]⟩ := rfl

/-- Calling a global function with explicit region and type arguments. -/
example : [OXIDE|
    letrgn<`r> {
      let x : (u32, u32) = (1, 2);
      let n : u32 = 0;
      swap_first::<`r, `r; u32>(&`r uniq x, &`r shrd n)
    } ] =
    Term.letrgn (.letE (.tuple 2 ![Ty.u32, Ty.u32])
      (.tuple 2 ![.val (Value.num 1), .val (Value.num 2)])
      (.letE Ty.u32 (.val (Value.num 0))
        (.app (.val (.fn "swap_first")) { nϱ := 2, nα := 1 } ![]
          ![.conc (.there (.there .here)), .conc (.there (.there .here))] ![Ty.u32] 2
          ![.borrow (.there (.there .here)) .uniq ⟨.skipVar .here, []⟩,
            .borrow (.there (.there .here)) .shrd ⟨.here, []⟩]))) := rfl

/-- A function binding a frame variable `@φ`: its parameter is a closure whose
captured environment is the frame variable. -/
def applyF : FnDef := [OXIDE_FN|
  fn apply<@φ, `a>(f : fn(u32)[@φ] -> u32, x : &`a shrd u32) -> u32 { f(*x) } ]

example : applyF.params ⟨0, by decide⟩ = .fn {} 1 ![Ty.u32] Ty.u32 (.var (.there .here)) [] := rfl

/-- Calls passing a literal frame `@{…}`, whose types live in the scope of the
frame itself (here `y` points into the frame's own region `s`). -/
example : [OXIDE| letrgn<`r> { apply::<@{x : u32, `s ↦ {}, y : &`s shrd u32}, `r; >(g, z) } ] =
    Term.letrgn (.app (.val (.fn "apply")) { nφ := 1, nϱ := 1 }
      ![.frame [.var, .rgn, .var]
        (.var (.ref (.conc (.there .here)) .shrd (.sized Ty.u32)) (.rgn [] (.var Ty.u32 .nil)))]
      ![.conc .here] ![] 2 ![.val (.fn "g"), .val (.fn "z")]) := rfl

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
example : [OXIDE| let a : (u32, u32) = (1, 2);
    val!((ptr!(a .1), [true, false], |2, 3|, Left::<u32, bool>(4), (dead!,))) ] =
    Term.letE (.tuple 2 ![Ty.u32, Ty.u32]) (.tuple 2 ![.val (Value.num 1), .val (Value.num 2)])
      (.val (.tuple 5 ![.ptr ⟨.here, [.proj 1]⟩, .array 2 ![Value.tt, Value.ff],
        .slice 2 ![Value.num 2, Value.num 3], .inl Ty.u32 Ty.bool (Value.num 4),
        .tuple 1 ![.dead]])) := rfl

/-! ### Running and typing programs written in the concrete syntax -/

/-- The abstract machine runs `let x : u32 = 5; x` to the final configuration
holding `5`: push the `let`, bind `x` (pushing a `popVar` continuation), copy
`x`, and pop `x` again. -/
example (G : GlobalEnv) :
    Steps G (Config.init [OXIDE| let x : u32 = 5; x ]) ⟨[], .nil, .val (Value.num 5), .halt⟩ := by
  refine .step _ _ _ (Step.letPush _ _ _ _ _) ?_
  refine .step _ _ _ (Step.letE _ _ _ _ _) ?_
  refine .step _ _ _ (Step.copy _ _ _ ⟨.here, []⟩ (Value.num 5) rfl rfl) ?_
  refine .step _ _ _ (Step.popVar _ _ (Value.num 5) _ rfl) ?_
  exact .refl _

example : (⟨[], .nil, .val (Value.num 5), .halt⟩ : Config).IsFinal := .inl ⟨_, rfl, rfl⟩

/-- The program of the type-safety counterexample, in concrete syntax. -/
example : tsProg = [OXIDE| let x : bool = true; x; if x { () } else { () } ] := rfl

/-- The program of the scoping counterexample, in concrete syntax. -/
example : tpProg = [OXIDE| letrgn<`r> { || -> () { Right::<&`r shrd (), ()>(()); () } } ] := rfl

end Oxide.Examples
