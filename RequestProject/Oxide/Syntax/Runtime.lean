module

public import RequestProject.Oxide.Syntax.Terms

/-!
# Oxide syntax, part 5: runtime stacks

Paper §3.6 ("Operational Semantics"), Figure "Oxide Syntax Extensions for
Dynamics": stack frames `ς` and stacks `σ`.
-/

@[expose] public section

namespace Oxide

/-- Entries of runtime stack frames: the value of a variable, or the marker of a
region introduced by `letrgn` (regions have no runtime content; the markers keep
the region levels of the stack and of the stack typing aligned). -/
inductive StackEntry where
  | val (v : Value)
  | rgn
  deriving Inhabited

/-- Stack frames `ς` (most recent entry first). -/
abbrev StackFrame := List StackEntry

/-- Stacks `σ ::= • | σ ‡ ς` (top frame first). -/
abbrev Stack := List StackFrame

end Oxide
