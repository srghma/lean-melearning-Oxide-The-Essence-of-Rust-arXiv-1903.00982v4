module

public import RequestProject.Oxide.Syntax.Environments

/-!
# Oxide syntax, part 4: terms, values and global environments

Paper §3.1 ("The Syntax of Oxide"), Figure "Term Syntax of Oxide", paragraph
"Expressions"; the runtime forms (`framed`, `shift`, values, referents, pointers)
come from §3.6, Figure "Oxide Syntax Extensions for Dynamics"; appendix A.

`Term n` is the type of expressions with at most `n` free variables (de Bruijn
indices), so `Term 0` is the type of closed programs.
-/

@[expose] public section

namespace Oxide

/-- Constants `c ::= () | n | true | false`.  Unsigned integers are modelled by
natural numbers. -/
inductive Prim where
  | unit
  | num (n : Nat)
  | bool (b : Bool)
  deriving DecidableEq, Repr, Inhabited

/-- Steps of a referent: projection `.n`, indexing `[n]` and slicing `[n₁..n₂]`
(we use the half-open interval `[n₁, n₂)`). -/
inductive RStep where
  | proj (i : Nat)
  | idx (i : Nat)
  | slice (i j : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- Referents `𝓡 ::= x | 𝓡.n | 𝓡[n] | 𝓡[n₁..n₂]`: abstract memory addresses whose
root is a stack level.  Steps are listed innermost first. -/
structure Referent where
  root : Nat
  steps : List RStep
  deriving DecidableEq, Repr, Inhabited

mutual
/-- Oxide expressions with `n` free term variables (de Bruijn indices).  The last
two constructors (`framed`, `shift`) only arise at runtime. -/
inductive Term : Nat → Type where
  /-- values (constants, function names and runtime values) -/
  | val {n} (v : Value) : Term n
  /-- use of a place expression (move or copy) -/
  | place {n} (p : PlaceExpr n) : Term n
  /-- borrow `&r ω p` -/
  | borrow {n} (r : Region) (ω : Own) (p : PlaceExpr n) : Term n
  /-- borrow of an index `&r ω p[e]` -/
  | borrowIdx {n} (r : Region) (ω : Own) (p : PlaceExpr n) (e : Term n) : Term n
  /-- borrow of a slice `&r ω p[e₁..e₂]` -/
  | borrowSlice {n} (r : Region) (ω : Own) (p : PlaceExpr n) (e₁ e₂ : Term n) : Term n
  /-- indexing copy `p[e]` -/
  | index {n} (p : PlaceExpr n) (e : Term n) : Term n
  /-- assignment `p := e` -/
  | assign {n} (p : PlaceExpr n) (e : Term n) : Term n
  /-- region introduction `letrgn<r> { e }` (`e` refers to `r` as `Region.bound 0`) -/
  | letrgn {n} (e : Term n) : Term n
  /-- `let x : τ = e₁; e₂` (the body binds index `0`) -/
  | letE {n} (τ : Ty) (e₁ : Term n) (e₂ : Term (n + 1)) : Term n
  /-- sequencing `e₁; e₂` -/
  | seq {n} (e₁ e₂ : Term n) : Term n
  /-- closure `|x₁ : τ₁, …, x_k : τ_k| → τ_r { e }`; in the body, index `i < k`
  denotes parameter `x_{k-i}`.  The number of parameters `k` is recorded
  explicitly (well-formedness requires `params.length = k`). -/
  | closure {n} (k : Nat) (params : List Ty) (ret : Ty) (body : Term (n + k)) : Term n
  /-- application `e_f::<Φ̄, ρ̄, τ̄>(e₁, …, eₙ)` -/
  | app {n} (f : Term n) (envs : List FrameExpr) (rgns : List Region) (tys : List Ty)
      (args : Terms n) : Term n
  /-- `if e₁ { e₂ } else { e₃ }` -/
  | ite {n} (e₁ e₂ e₃ : Term n) : Term n
  /-- tuples `(e₁, …, eₙ)` -/
  | tuple {n} (es : Terms n) : Term n
  /-- arrays `[e₁, …, eₙ]` -/
  | array {n} (es : Terms n) : Term n
  /-- `for x in e₁ { e₂ }` -/
  | forE {n} (e₁ : Term n) (e₂ : Term (n + 1)) : Term n
  /-- `while e₁ { e₂ }` -/
  | whileE {n} (e₁ e₂ : Term n) : Term n
  /-- `abort!(str)` -/
  | abort {n} (msg : String) : Term n
  /-- `Left::<τ₁, τ₂>(e)` -/
  | inl {n} (τ₁ τ₂ : Ty) (e : Term n) : Term n
  /-- `Right::<τ₁, τ₂>(e)` -/
  | inr {n} (τ₁ τ₂ : Ty) (e : Term n) : Term n
  /-- `match e { Left(x₁) => e₁, Right(x₂) => e₂ }` -/
  | matchE {n} (e : Term n) (e₁ e₂ : Term (n + 1)) : Term n
  /-- runtime: `framed e` (the body lives in its own, freshly pushed, stack frame
  which has `m` variables) -/
  | framed {n} (m : Nat) (e : Term m) : Term n
  /-- runtime: `shift e` (pops the most recent binding of the top frame once `e`
  is a value) -/
  | shift {n} (e : Term (n + 1)) : Term n
  /-- runtime: `shiftprov e` (pops the most recent region of the top frame once `e`
  is a value) -/
  | shiftRgn {n} (e : Term n) : Term n
/-- Lists of terms. -/
inductive Terms : Nat → Type where
  | nil {n} : Terms n
  | cons {n} (e : Term n) (es : Terms n) : Terms n
/-- Values (all closed). -/
inductive Value : Type where
  /-- constants -/
  | prim (c : Prim)
  /-- global function names `f` -/
  | fn (f : String)
  /-- the dead value -/
  | dead
  /-- tuples -/
  | tuple (vs : List Value)
  /-- arrays -/
  | array (vs : List Value)
  /-- dynamically sized slices `|v₁, …, vₙ|` -/
  | slice (vs : List Value)
  /-- pointers `ptr 𝓡` -/
  | ptr (R : Referent)
  /-- closure values `⟨ς, |x̄ : τ̄| → τ_r { e }⟩`; the captured frame `frame` has
  `m` values (most recent first) and `q` captured regions (bound in the body as
  `Region.bound 0 … q-1`), there are `k` parameters and the body has scope
  `m + k` (parameters first) -/
  | closure (m k q : Nat) (frame : List Value) (params : List Ty) (ret : Ty)
      (body : Term (m + k))
  /-- left injection -/
  | inl (τ₁ τ₂ : Ty) (v : Value)
  /-- right injection -/
  | inr (τ₁ τ₂ : Ty) (v : Value)
end

instance : Inhabited Value := ⟨.prim .unit⟩
instance {n : Nat} : Inhabited (Term n) := ⟨.val default⟩

namespace Value
def unit : Value := .prim .unit
def num (k : Nat) : Value := .prim (.num k)
def tt : Value := .prim (.bool true)
def ff : Value := .prim (.bool false)
end Value

namespace Terms
/-- Conversion to a list. -/
def toList {n : Nat} : Terms n → List (Term n)
  | .nil => []
  | .cons e es => e :: es.toList
/-- Conversion from a list. -/
def ofList {n : Nat} : List (Term n) → Terms n
  | [] => .nil
  | e :: es => .cons e (ofList es)
@[simp] theorem toList_ofList {n : Nat} (l : List (Term n)) : (ofList l).toList = l := by
  induction l with
  | nil => rfl
  | cons e es ih => simp [ofList, toList, ih]
@[simp] theorem ofList_toList {n : Nat} : (es : Terms n) → ofList es.toList = es
  | .nil => rfl
  | .cons e es => by simp [ofList, toList, ofList_toList es]
end Terms

/-- Global function definitions
`fn f<φ̄, ϱ̄, ᾱ>(x₁ : τ₁, …, x_k : τ_k) → τ_r where ϱ₁ : ϱ₂ { e }`. -/
structure FnDef where
  name : String
  /-- number of frame variables `φ̄` -/
  nφ : Nat
  /-- number of abstract regions `ϱ̄` -/
  nϱ : Nat
  /-- number of type variables `ᾱ` -/
  nα : Nat
  params : List Ty
  ret : Ty
  bounds : List (Nat × Nat)
  body : Term params.length

/-- Global environments `Σ`. -/
abbrev GlobalEnv := List FnDef

/-- Look up a global function. -/
def GlobalEnv.lookup (G : GlobalEnv) (f : String) : Option FnDef := G.find? (·.name == f)

end Oxide
