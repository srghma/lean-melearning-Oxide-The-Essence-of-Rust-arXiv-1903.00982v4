module

public import RequestProject.Oxide.Syntax.Runtime

/-!
# Making the grammar more correct by construction: checked sketches

Companion to `Proposal/CORRECT_BY_CONSTRUCTION.md`.  This file does **not** change
the grammar used by the rest of the development.  It contains

* *witnesses* that the current grammar still admits some ill-formed syntax
  (each is a definition that type checks today), and
* *prototypes* of the replacements, with small theorems showing that the
  ill-formed syntax can no longer be written.
-/

@[expose] public section

namespace Oxide.CBC

variable {sig : Sig}

/-! ## 1. Witnesses: ill-formed syntax the current grammar admits -/

/-- A *source* program containing a raw pointer to a local variable, bypassing
`&r ω p` and the loan machinery.  `ptr` is a runtime-only form in the paper. -/
def srcWithPtr : Program sig :=
  .letE .u32 (.atom (.val (.num 5))) (.val (.ptr (.place ⟨.here, []⟩)))

/-- A source program containing the runtime value `dead`. -/
def srcWithDead : Program sig := .val .dead

/-- A tuple *value* with a slice component: a slice is unsized and may only sit
behind a pointer, yet `Value` lets it occur anywhere (`[τ]` is an `XTy`, not a
`Ty`, but values are not split the same way). -/
def tupleOfSlice : Value sig [] := .tuple 1 fun _ => .slice 0 Fin.elim0

/-- A capture list naming the same variable twice.  `Cap.frameTy` gives both copies
the variable's (possibly non-copyable) type, e.g. two copies of a `&uniq`
reference inside the closure's frame.  `T-Closure` now rejects such lists
(`Cap.Nodup`; see `Metatheory/Regressions/DuplicateCaptures.lean`). -/
def dupCap {Γ : Ctx} : Cap (.var :: Γ) [.var, .var] := .var .here (.var .here .nil)

theorem dupCap_not_nodup {Γ : Ctx} : ¬ (dupCap (Γ := Γ)).vars.Nodup := by
  simp [dupCap, Cap.vars]

/-- Two encodings of the same fully initialized pair: `MTy.Of` relies on the
smart constructor `mkTuple` to keep only the first. -/
def initPair₁ : MTy.Of (Γ := []) (.tuple 2 fun _ => .u32) := .init
def initPair₂ : MTy.Of (Γ := []) (.tuple 2 fun _ => .u32) := .tuple fun _ => .init

theorem initPair_ne : initPair₁ ≠ initPair₂ := by
  intro h; cases h

/-! ## 2. Captures as an order-preserving selection of the current frame -/

/-- `TopSel f Γ`: the captured frame `f` is obtained from the *top frame* of `Γ`
by keeping some of its variables and regions, in order.  There is no constructor
crossing a `.frame` boundary or a type-level binder, so only current-frame
entries can be captured, each at most once. -/
inductive TopSel : Ctx → Ctx → Type where
  | nil {Γ : Ctx} : TopSel [] Γ
  | keepVar {f Γ : Ctx} (c : TopSel f Γ) : TopSel (.var :: f) (.var :: Γ)
  | keepRgn {f Γ : Ctx} (c : TopSel f Γ) : TopSel (.rgn :: f) (.rgn :: Γ)
  | skipVar {f Γ : Ctx} (c : TopSel f Γ) : TopSel f (.var :: Γ)
  | skipRgn {f Γ : Ctx} (c : TopSel f Γ) : TopSel f (.rgn :: Γ)

/-- The capture list described by a selection. -/
def TopSel.toCap : {f Γ : Ctx} → TopSel f Γ → Cap Γ f
  | _, _, .nil => .nil
  | _, _, .keepVar c => .var .here (c.toCap.rename (Ren.wkVar _))
  | _, _, .keepRgn c => .rgn .here (c.toCap.rename (Ren.wkRgn _))
  | _, _, .skipVar c => c.toCap.rename (Ren.wkVar _)
  | _, _, .skipRgn c => c.toCap.rename (Ren.wkRgn _)

theorem Cap.vars_rename {Γ Δ : Ctx} (ρ : Ren Γ Δ) :
    {f : Ctx} → (c : Cap Γ f) → (c.rename ρ).vars = c.vars.map ρ.tvar
  | _, .nil => rfl
  | _, .var x c => by simp [Cap.rename, Cap.vars, Cap.vars_rename ρ c]
  | _, .rgn r c => by simp [Cap.rename, Cap.vars, Cap.vars_rename ρ c]

/-- Captures built from a selection never name a variable twice. -/
theorem TopSel.toCap_vars_nodup : {f Γ : Ctx} → (c : TopSel f Γ) → c.toCap.vars.Nodup
  | _, _, .nil => List.nodup_nil
  | _, _, .keepVar c => by
      simp only [TopSel.toCap, Cap.vars, Cap.vars_rename]
      refine List.nodup_cons.mpr ⟨?_, ?_⟩
      · simp [Ren.wkVar]
      · exact List.Pairwise.map _ (fun _ _ h e => h (TVar.skipVar.inj e)) c.toCap_vars_nodup
  | _, _, .keepRgn c => by
      simp only [TopSel.toCap, Cap.vars, Cap.vars_rename]
      exact List.Pairwise.map _ (fun _ _ h e => h (TVar.skipRgn.inj e)) c.toCap_vars_nodup
  | _, _, .skipVar c => by
      simp only [TopSel.toCap, Cap.vars_rename]
      exact List.Pairwise.map _ (fun _ _ h e => h (TVar.skipVar.inj e)) c.toCap_vars_nodup
  | _, _, .skipRgn c => by
      simp only [TopSel.toCap, Cap.vars_rename]
      exact List.Pairwise.map _ (fun _ _ h e => h (TVar.skipRgn.inj e)) c.toCap_vars_nodup

/-! ## 3. Initialization states with a unique encoding -/

/-- The kind of an initialization state. -/
inductive Kind where
  | init
  | dead
  | mixed
  deriving DecidableEq, Repr

/-- `MSt τ κ`: an initialization state of declared type `τ` and kind `κ`.  A
partially moved tuple records the kinds of its fields and must be genuinely
mixed: some field is not fully initialized and some field is not fully dead.
So "all fields `init`" and "all fields `dead`" have exactly one encoding each. -/
inductive MSt {Γ : Ctx} : Ty Γ → Kind → Type where
  | init {τ : Ty Γ} : MSt τ .init
  | dead {τ : Ty Γ} : MSt τ .dead
  | part {k : Nat} {τs : Fin k → Ty Γ} (ks : Fin k → Kind) (ms : (i : Fin k) → MSt (τs i) (ks i))
      (hinit : ∃ i, ks i ≠ .init) (hdead : ∃ i, ks i ≠ .dead) : MSt (.tuple k τs) .mixed

/-- There is exactly one fully initialized state of each type. -/
instance {Γ : Ctx} {τ : Ty Γ} : Subsingleton (MSt τ .init) :=
  ⟨fun a b => by cases a; cases b; rfl⟩

/-- There is exactly one fully dead state of each type. -/
instance {Γ : Ctx} {τ : Ty Γ} : Subsingleton (MSt τ .dead) :=
  ⟨fun a b => by cases a; cases b; rfl⟩

/-- The smart constructor becomes total and type-directed: it decides the kind
of a tuple from the kinds of its fields. -/
def MSt.tupleKind {k : Nat} (ks : Fin k → Kind) : Kind :=
  if ∀ i, ks i = .init then .init else if ∀ i, ks i = .dead then .dead else .mixed

/-- Building the state of a tuple from the states of its fields. -/
def MSt.mkTuple {Γ : Ctx} {k : Nat} {τs : Fin k → Ty Γ} (ks : Fin k → Kind)
    (ms : (i : Fin k) → MSt (τs i) (ks i)) : MSt (.tuple k τs) (MSt.tupleKind ks) :=
  if h₁ : ∀ i, ks i = .init then by
    rw [MSt.tupleKind, if_pos h₁]; exact .init
  else if h₂ : ∀ i, ks i = .dead then by
    rw [MSt.tupleKind, if_neg h₁, if_pos h₂]; exact .dead
  else by
    rw [MSt.tupleKind, if_neg h₁, if_neg h₂]
    exact .part ks ms (by simpa using h₁) (by simpa using h₂)

/-! ## 4. Values split by sort and phase

The prototype below shows the shape only (closure values, which are mutual with
terms, are omitted).  Each family mirrors a type sort:

* `SVal`  ↔ `Ty`  (sized, initialized): what an expression evaluates to;
* `XVal`  ↔ `XTy` (maybe unsized): what a pointer designates;
* `MVal`  ↔ `MTy` (maybe dead): what a stack slot holds.

Source terms would embed only `SrcVal` (constants and function names). -/

/-- Sized, initialized values (runtime). -/
inductive SVal (sig : Sig) (Γ : Ctx) where
  | prim {b : BaseTy} (c : Prim b)
  | fn (f : FnIdx sig)
  | tuple (k : Nat) (vs : Fin k → SVal sig Γ)
  | array (k : Nat) (vs : Fin k → SVal sig Γ)
  | ptr (R : Referent Γ)
  | inl (τ₁ τ₂ : Ty Γ) (v : SVal sig Γ)
  | inr (τ₁ τ₂ : Ty Γ) (v : SVal sig Γ)

/-- Maybe-unsized values: a slice exists only here. -/
inductive XVal (sig : Sig) (Γ : Ctx) where
  | sized (v : SVal sig Γ)
  | slice (k : Nat) (vs : Fin k → SVal sig Γ)

/-- Maybe-dead values: `dead` exists only here (and in partially moved tuples). -/
inductive MVal (sig : Sig) (Γ : Ctx) where
  | init (v : SVal sig Γ)
  | dead
  | tuple (k : Nat) (vs : Fin k → MVal sig Γ)

/-- The values a programmer can write: constants and global function names. -/
inductive SrcVal (sig : Sig) where
  | prim {b : BaseTy} (c : Prim b)
  | fn (f : FnIdx sig)

/-- Source values embed into runtime values in any scope. -/
def SrcVal.toSVal {Γ : Ctx} : SrcVal sig → SVal sig Γ
  | .prim c => .prim c
  | .fn f => .fn f

/-- A source value is never a pointer (it cannot even mention the scope). -/
theorem SrcVal.toSVal_ne_ptr {Γ : Ctx} (v : SrcVal sig) (R : Referent Γ) :
    v.toSVal ≠ SVal.ptr R := by
  cases v <;> simp [SrcVal.toSVal]

end Oxide.CBC
