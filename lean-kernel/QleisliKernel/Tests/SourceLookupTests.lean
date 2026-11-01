import QleisliKernel.SourceTypes.SourceLookup

/-! Small executable original lookup controls. General lookup agreement is proved
in SourceLookup. Presence preserves category and visibility;
absence is not source validity, primitive fallback or callable authority.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.SourceLookupTests
open QleisliKernel.SourceTypes
open QleisliKernel.SourceTypes QleisliKernel.SourceTypes.SourceLookup

private def view (sources : Sources) (owner name : String) : Option (String × Option Declaration) :=
  (read sources owner name).toOption.map fun checked => (checked.source,checked.binding)

private def failure (sources : Sources) (owner name : String) : Option String :=
  match read sources owner name with | .error error => some error | .ok _ => none

private def moduleRows (source : String) : Sources := #[("main",source)]
private def publicFunction := "pub unitary fn h(q:Q<Bit>)->Q<Bit>{q}"
private def privateFunction := "unitary fn h(q:Q<Bit>)->Q<Bit>{q}"
private def imported := "use other::h;"
private def publicImported := "pub use other::h;"
private def typeNamedH := "pub enum h { A, B }"

private def genuine_absence_retains_original_row : Bool := decide (
    view (moduleRows "// h is only a comment\n") "main" "h" =
      some ("// h is only a comment\n",none))
#guard genuine_absence_retains_original_row
private def other_declaration_is_not_requested_name : Bool := decide (
    view (moduleRows "fn helper()->Unit{()}") "main" "h" =
      some ("fn helper()->Unit{()}",none))
#guard other_declaration_is_not_requested_name
private def public_function_is_present : Bool := decide (
    view (moduleRows publicFunction) "main" "h" =
      some (publicFunction,some ⟨"h",true,"fn",[]⟩))
#guard public_function_is_present
private def private_function_is_still_a_binding : Bool := decide (
    view (moduleRows privateFunction) "main" "h" =
      some (privateFunction,some ⟨"h",false,"fn",[]⟩))
#guard private_function_is_still_a_binding
private def import_is_not_primitive_absence : Bool := decide (
    view (moduleRows imported) "main" "h" =
      some (imported,some ⟨"h",false,"import",["h","other"]⟩))
#guard import_is_not_primitive_absence
private def public_import_keeps_visibility_and_path : Bool := decide (
    view (moduleRows publicImported) "main" "h" =
      some (publicImported,some ⟨"h",true,"import",["h","other"]⟩))
#guard public_import_keeps_visibility_and_path
private def wrong_category_is_not_primitive_absence : Bool := decide (
    view (moduleRows typeNamedH) "main" "h" =
      some (typeNamedH,some ⟨"h",true,"enum",["A",",","B"]⟩))
#guard wrong_category_is_not_primitive_absence
private def meaning_category_is_retained : Bool := decide (
    view (moduleRows "meaning h:Bit=reference(f);") "main" "h" =
      some ("meaning h:Bit=reference(f);",some ⟨"h",false,"meaning",[]⟩))
#guard meaning_category_is_retained

private def missing_module_is_an_error : Bool := decide (
    failure #[("other",publicFunction)] "main" "h" =
      some "missing/ambiguous original source module")
#guard missing_module_is_an_error
private def repeated_identical_module_is_ambiguous : Bool := decide (
    failure #[("main",publicFunction),("main",publicFunction)] "main" "h" =
      some "missing/ambiguous original source module")
#guard repeated_identical_module_is_ambiguous
private def repeated_declaration_is_ambiguous : Bool := decide (
    failure (moduleRows (publicFunction ++ privateFunction)) "main" "h" =
      some "ambiguous original source declaration")
#guard repeated_declaration_is_ambiguous
private def declaration_import_collision_is_ambiguous : Bool := decide (
    failure (moduleRows (publicFunction ++ imported)) "main" "h" =
      some "ambiguous original source declaration")
#guard declaration_import_collision_is_ambiguous
private def incomplete_brace_is_not_absence : Bool := decide (
    (failure (moduleRows "pub enum Broken { A") "main" "h").isSome = true)
#guard incomplete_brace_is_not_absence
private def unterminated_comment_is_not_absence : Bool := decide (
    (failure (moduleRows "/* no closing comment") "main" "h").isSome = true)
#guard unterminated_comment_is_not_absence
private def malformed_import_is_not_absence : Bool := decide (
    (failure (moduleRows "use other::{,};") "main" "h").isSome = true)
#guard malformed_import_is_not_absence

private def resolved (sources : Sources) (caller : String) (tokens : List String) : Bool :=
  ((resolveReference sources caller tokens).run 100000).1.toOption.isSome

-- The same retained binding can subsequently fail visibility or import
-- resolution. Such failures must never be converted to primitive fallback.
private def qualified_public_function_resolves : Bool := decide (
    resolved (moduleRows publicFunction) "other" ["main","::","h"] = true)
#guard qualified_public_function_resolves
private def qualified_private_function_refuses : Bool := decide (
    resolved (moduleRows privateFunction) "other" ["main","::","h"] = false)
#guard qualified_private_function_refuses
private def dangling_import_is_a_binding_but_not_a_resolved_target : Bool := decide (
    resolved (moduleRows imported) "main" ["h"] = false)
#guard dangling_import_is_a_binding_but_not_a_resolved_target
private def cyclic_import_is_not_resolved : Bool := decide (
    resolved #[("main",imported),("other","pub use main::h;")] "main" ["h"] = false)
#guard cyclic_import_is_not_resolved

-- This deliberately exposes the component boundary: cataloguing a function
-- does not validate its full header, body, effects or permission to call it.
private def incomplete_function_header_remains_a_catalogue_binding : Bool := decide (
    view (moduleRows "fn h(") "main" "h" =
      some ("fn h(",some ⟨"h",false,"fn",[]⟩))
#guard incomplete_function_header_remains_a_catalogue_binding

-- An absent requested name does not establish that unrelated declarations
-- form a valid module. The original row must undergo full source checking.
private def incomplete_unrelated_function_does_not_validate_module : Bool := decide (
    view (moduleRows "fn other(") "main" "h" =
      some ("fn other(",none))
#guard incomplete_unrelated_function_does_not_validate_module

#print axioms QleisliKernel.SourceTypes.SourceLookup.read
#print axioms QleisliKernel.SourceTypes.SourceLookup.Checked.absent
#print axioms QleisliKernel.SourceTypes.SourceLookup.Checked.present
#print axioms QleisliKernel.SourceTypes.SourceLookup.Checked.absent_original

end QleisliKernel.Tests.SourceLookupTests
