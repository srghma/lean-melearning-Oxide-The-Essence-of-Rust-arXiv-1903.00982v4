module
public import RequestProject.Oxide.ConcreteSyntax.Notation
public import RequestProject.Oxide.OperationalSemantics.Dynamics

/-!
# Oxide: examples of the `[OXIDE| … ]` syntax
-/

namespace Oxide.Examples

open Oxide

/-- `let x : u32 = 5; x` -/
example : [OXIDE| let x : u32 = 5; x ] =
    Term.letE Ty.u32 (.val (Value.num 5)) (.place ⟨0, []⟩) := rfl

/-- Variables are de Bruijn indices: the innermost binding has index `0`. -/
example : [OXIDE| let x : u32 = 1; let y : u32 = 2; (x, y) ] =
    Term.letE Ty.u32 (.val (Value.num 1)) (.letE Ty.u32 (.val (Value.num 2))
      (.tuple (.cons (.place ⟨1, []⟩) (.cons (.place ⟨0, []⟩) .nil)))) := rfl

/-- Regions bound by `letrgn` are de Bruijn indices too (`Region.bound`). -/
example : [OXIDE|
    letrgn<`a> {
      letrgn<`b> {
        let x : u32 = 5;
        let r : &`a uniq u32 = &`a uniq x;
        *r := 6;
        *r
      }
    } ] =
    Term.letrgn (.letrgn
      (.letE Ty.u32 (.val (Value.num 5))
        (.letE (.ref (.bound 1) .uniq Ty.u32) (.borrow (.bound 1) .uniq ⟨0, []⟩)
          (.seq (.assign ⟨0, [.deref]⟩ (.val (Value.num 6))) (.place ⟨0, [.deref]⟩))))) := rfl

/-- Closures: the parameters are the innermost bindings of the body. -/
example : [OXIDE|
    let y : u32 = 1;
    let f : fn(u32, bool) -> u32 = |a : u32, b : bool| -> u32 { if b { a } else { y } };
    f(3, true) ] =
    Term.letE Ty.u32 (.val (Value.num 1))
      (.letE (Ty.closure [Ty.u32, Ty.bool] Ty.u32 (.frame []))
        (.closure 2 [Ty.u32, Ty.bool] Ty.u32
          (.ite (.place ⟨0, []⟩) (.place ⟨1, []⟩) (.place ⟨2, []⟩)))
        (.app (.place ⟨0, []⟩) [] [] []
          (.cons (.val (Value.num 3)) (.cons (.val Value.tt) .nil)))) := rfl

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
        (.array (.cons (.val (Value.num 1)) (.cons (.val (Value.num 2))
          (.cons (.val (Value.num 3)) .nil))))
      (.letE (.tuple [Ty.u32, .tuple [Ty.bool, Ty.u32]])
        (.tuple (.cons (.val (Value.num 0)) (.cons (.tuple (.cons (.val Value.tt)
          (.cons (.val (Value.num 1)) .nil))) .nil)))
      (.seq (.forE (.borrowSlice (.bound 0) .shrd ⟨1, []⟩ (.val (Value.num 0))
          (.val (Value.num 2))) (.val Value.unit))
      (.seq (.whileE (.val Value.ff) (.val Value.unit))
      (.seq (.assign ⟨0, [.proj 1, .proj 0]⟩ (.val Value.ff))
        (.matchE (.place ⟨2, []⟩) (.place ⟨0, []⟩) (.index ⟨2, []⟩ (.val (Value.num 2)))))))))) :=
  rfl

/-- A polymorphic global function (the paper's running example shape): abstract
regions and type variables are de Bruijn indices in the order of the binders. -/
def swapFirst : FnDef := [OXIDE_FN|
  fn swap_first<`a, `b; T>(x : &`a uniq (T, T), y : &`b shrd u32) -> u32 where `a : `b {
    *y
  } ]

example : swapFirst.nϱ = 2 ∧ swapFirst.nα = 1 ∧ swapFirst.bounds = [(0, 1)] ∧
    swapFirst.params = [.ref (.abs 0) .uniq (.tuple [.tvar 0, .tvar 0]), .ref (.abs 1) .shrd Ty.u32] :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Calling a global function with explicit region and type arguments. -/
example : [OXIDE|
    letrgn<`r> {
      let x : (u32, u32) = (1, 2);
      let n : u32 = 0;
      swap_first::<`r, `r; u32>(&`r uniq x, &`r shrd n)
    } ] =
    Term.letrgn (.letE (.tuple [Ty.u32, Ty.u32])
      (.tuple (.cons (.val (Value.num 1)) (.cons (.val (Value.num 2)) .nil)))
      (.letE Ty.u32 (.val (Value.num 0))
        (.app (.val (.fn "swap_first")) [] [.bound 0, .bound 0] [Ty.u32]
          (.cons (.borrow (.bound 0) .uniq ⟨1, []⟩)
            (.cons (.borrow (.bound 0) .shrd ⟨0, []⟩) .nil))))) := rfl

/-! ### Frame arguments, polymorphic function types, 1-tuples, dead types and runtime forms -/

/-- A function binding a frame variable `@φ`: its parameter is a closure whose
captured environment is the frame variable. -/
def applyF : FnDef := [OXIDE_FN|
  fn apply<@φ, `a>(f : fn(u32)[@φ] -> u32, x : &`a shrd u32) -> u32 { f(*x) } ]

example : applyF.nφ = 1 ∧ applyF.nϱ = 1 ∧
    applyF.params = [.fn 0 0 0 [Ty.u32] Ty.u32 (.var 0) [], .ref (.abs 0) .shrd Ty.u32] :=
  ⟨rfl, rfl, rfl⟩

/-- Calls passing a frame argument `@{…}` (a concrete frame typing) together with
region and type arguments. -/
example : [OXIDE| letrgn<`r> { apply::<@{x : u32, `s ↦ {}, y : &`s shrd u32}, `r; >(g, z) } ] =
    Term.letrgn (.app (.val (.fn "apply"))
      [.frame [.var (.ref (.bound 0) .shrd Ty.u32), .rgn [], .var Ty.u32]] [.bound 0] []
      (.cons (.val (.fn "g")) (.cons (.val (.fn "z")) .nil))) := rfl

/-- Polymorphic function types with quantifiers, a captured environment and
`where` bounds: binders are de Bruijn indices in the order they are written. -/
example : [OXIDE_TY| fn<@φ, `a, `b; T>(&`a uniq T, &`b shrd T)[@φ] -> T where `a : `b ] =
    .fn 1 2 1 [.ref (.abs 0) .uniq (.tvar 0), .ref (.abs 1) .shrd (.tvar 0)] (.tvar 0) (.var 0)
      [(0, 1)] := rfl

/-- Nested quantifiers shift the outer binders. -/
example : [OXIDE_FN| fn k<`a>(f : fn<`b>(&`b shrd u32, &`a shrd u32) -> u32) -> () { () } ].params =
    [.fn 0 1 0 [.ref (.abs 0) .shrd Ty.u32, .ref (.abs 1) .shrd Ty.u32] Ty.u32 (.frame []) []] := rfl

/-- 1-tuples and dead types. -/
example : [OXIDE_TY| ((u32,)†, (bool, u32†)) ] =
    .tuple [.dead (.tuple [Ty.u32]), .tuple [Ty.bool, .dead Ty.u32]] := rfl

example : [OXIDE| let t : (u32,) = (5,); t.0 ] =
    Term.letE (.tuple [Ty.u32]) (.tuple (.cons (.val (Value.num 5)) .nil)) (.place ⟨0, [.proj 0]⟩) :=
  rfl

/-- Runtime forms: `framed`, `shift`, `shiftprov`, pointers, `dead` and runtime values
(the body of `framed![x, y] { … }` only sees the variables of its own frame). -/
example : [OXIDE|
    let a : u32 = 1;
    framed![x, y] { shift! z { shiftprov! { (x, y, z, ptr!(3 .1 [2] [0..1]), dead!) } } } ] =
    Term.letE Ty.u32 (.val (Value.num 1))
      (.framed 2 (.shift (.shiftRgn (.tuple
        (.cons (.place ⟨2, []⟩) (.cons (.place ⟨1, []⟩) (.cons (.place ⟨0, []⟩)
          (.cons (.val (.ptr ⟨3, [.proj 1, .idx 2, .slice 0 1]⟩)) (.cons (.val .dead) .nil))))))))) :=
  rfl

example : [OXIDE| val!((1, [true, false], |2, 3|, Left::<u32, bool>(4), (dead!,))) ] =
    Term.val (.tuple [Value.num 1, .array [Value.tt, Value.ff], .slice [Value.num 2, Value.num 3],
      .inl Ty.u32 Ty.bool (Value.num 4), .tuple [.dead]]) := rfl

/-- Closure values: captured values (oldest first), captured regions (the last one is
`Region.bound 0` in the body), parameters and body; the body sees the parameters
(innermost) and the captured variables. -/
example : [OXIDE| val!(closure![a = 1, b = true | `s] |x : u32| -> u32 {
      letrgn<`t> { let r : &`s shrd u32 = &`s shrd a; if b { x } else { *r } } }) ] =
    Term.val (.closure 2 1 1 [Value.tt, Value.num 1] [Ty.u32] Ty.u32
      (.letrgn (.letE (.ref (.bound 1) .shrd Ty.u32) (.borrow (.bound 1) .shrd ⟨2, []⟩)
        (.ite (.place ⟨2, []⟩) (.place ⟨1, []⟩) (.place ⟨0, [.deref]⟩))))) := rfl

/-! ### Running a program -/

/-- `let x : u32 = 5; x` steps to `shift x` with `x ↦ 5` pushed on the stack. -/
example : Step [] [[]] [OXIDE| let x : u32 = 5; x ] [[.val (Value.num 5)]]
    (.shift (.place ⟨0, []⟩)) :=
  Step.letE [[]] Ty.u32 (Value.num 5) (.place ⟨0, []⟩)

end Oxide.Examples
