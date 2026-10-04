module

-- scopes and typed de Bruijn indices (the scope-indexed grammar)
public import RequestProject.Oxide.Syntax.Scopes
-- §3.1–3.3 (appendix A): syntax
public import RequestProject.Oxide.Syntax.Places
public import RequestProject.Oxide.Syntax.Types
public import RequestProject.Oxide.Syntax.Terms
public import RequestProject.Oxide.Syntax.Environments
public import RequestProject.Oxide.Syntax.Runtime
-- appendix C: metafunctions
public import RequestProject.Oxide.Metafunctions.Substitution
public import RequestProject.Oxide.Metafunctions.Types
public import RequestProject.Oxide.Metafunctions.Places
public import RequestProject.Oxide.Metafunctions.StackTypings
public import RequestProject.Oxide.Metafunctions.Stacks
-- §3.4: region-based alias management
public import RequestProject.Oxide.AliasManagement.OwnershipSafety
-- §3.5 (appendix B): typechecking
public import RequestProject.Oxide.Typechecking.RegionRewriting
public import RequestProject.Oxide.Typechecking.Typing
public import RequestProject.Oxide.Typechecking.Validity
public import RequestProject.Oxide.Typechecking.Continuations
-- §3.6 (appendix D): operational semantics, as a continuation-based machine
public import RequestProject.Oxide.OperationalSemantics.Machine
-- §3.7 (appendix E): metatheory
public import RequestProject.Oxide.Metatheory.Statements
public import RequestProject.Oxide.Metatheory.Counterexamples.TypeSafety
public import RequestProject.Oxide.Metatheory.Counterexamples.Progress
-- not in the paper: concrete `[OXIDE| … ]` syntax
public import RequestProject.Oxide.ConcreteSyntax.Notation
public import RequestProject.Oxide.ConcreteSyntax.Examples

/-!
# Oxide: The Essence of Rust — entry point

Imports the whole formalization, grouped by the sections of the paper.  Every
syntactic class is indexed by its scope (`Oxide.Ctx`); a closed program is an
`Oxide.Term []`.  See `RequestProject/Oxide/READING_GUIDE.md` for a guided tour.
-/
