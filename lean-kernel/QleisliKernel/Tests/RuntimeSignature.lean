import QleisliKernel.SourceTypes.RuntimeSignature

/-! Small complete-interface tests, distinct from body/code-space checking.
No compiled native activation or source-preservation claim follows.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.RuntimeSignature
open Semantics.FiniteCarrier Semantics.RuntimeType SourceTypes

private def emptyOrigin : Origin := ⟨"main","Empty","pub struct Empty {}"⟩

theorem empty_ordinary_is_not_empty_owner : ordinary [.unit] ≠ owner [.unit] := by decide +kernel
theorem ordinary_unit_has_no_owner : ownerBases (ordinary [.unit]) = some [] := by decide +kernel
theorem quantum_unit_is_one_owner : ownerBases (owner [.unit]) = some [[.unit]] := by decide +kernel
theorem quantum_empty_record_is_one_owner :
    ownerBases (owner [.record emptyOrigin []]) = some [[.record emptyOrigin []]] := by decide +kernel
theorem tuple_and_atomic_quantum_product_differ :
    tuple 2 [owner [.unit],owner [.unit]] ≠ owner [.pair,.unit,.unit] := by decide +kernel
theorem outer_ordinary_unit_is_retained :
    tuple 2 [ordinary [.unit],owner [.unit]] ≠ owner [.unit] := by decide +kernel
theorem nested_ordinary_products_are_not_reassociated :
    tuple 2 [owner [.unit],tuple 2 [ordinary [.unit],owner [.bit]]] ≠
      tuple 2 [tuple 2 [owner [.unit],ordinary [.unit]],owner [.bit]] := by decide +kernel
theorem mixed_product_retains_ordered_owner_bases :
    ownerBases (tuple 3 [owner [.unit],ordinary [.bit],owner [.bits 0]]) =
      some [[.unit],[.bits 0]] := by decide +kernel
theorem ownership_cannot_nest : ownerBases (.quantum :: owner [.bit]) = none := by decide +kernel
theorem nominal_record_cannot_hide_owner_field :
    ownerBases (.finite (.record emptyOrigin ["q"]) :: owner [.bit]) = none := by decide +kernel
theorem incomplete_owner_refuses : ownerBases [.quantum] = none := by decide +kernel
theorem extra_type_roots_refuse : ownerBases [.finite .unit,.finite .unit] = none := by decide +kernel

private def sources (text : String) : Sources := #[("main",text)]

private def signature (text : String) :=
  (SourceTypes.RuntimeSignature.read (sources text) "main" "keep").run 10000000

private def observed (text : String) : Option (List Tree × Tree) :=
  match (signature text).1 with
  | .ok read => some (read.parameters.map (·.tree),read.result.tree)
  | .error _ => none

private def mixedSource : String :=
  "pub unitary fn keep(p: (Q<Unit>,(Unit,Q<Bit>)), z: Unit) -> (Q<Unit>,(Unit,Q<Bit>)) { p }"

theorem original_nested_types_keep_full_parameter_and_result_shape :
    observed mixedSource = some (
      [tuple 2 [owner [.unit],tuple 2 [ordinary [.unit],owner [.bit]]],ordinary [.unit]],
      tuple 2 [owner [.unit],tuple 2 [ordinary [.unit],owner [.bit]]]) := by decide +kernel

theorem source_missing_public_quantum_effect_refuses :
    observed "pub fn keep(q: Q<Bit>) -> Q<Bit> { q }" = none := by decide +kernel

theorem private_effect_remains_uninferred_header_metadata :
    observed "fn keep(q: Q<Bit>) -> Q<Bit> { q }" = some ([owner [.bit]],owner [.bit]) := by decide +kernel

theorem classical_header_cannot_claim_quantum_parameters :
    observed "pub classical fn keep(q: Q<Bit>) -> Q<Bit> { q }" = none := by decide +kernel

theorem no_implicit_quantum_read_in_ordinary_signature :
    observed "pub fn keep(q: Bit) -> Bit { q }" = some ([ordinary [.bit]],ordinary [.bit]) := by decide +kernel

theorem nested_quantum_source_type_refuses :
    observed "pub unitary fn keep(q: Q<Q<Bit>>) -> Q<Bit> { q }" = none := by decide +kernel

theorem nominal_quantum_identity_keeps_original_source_and_variant_order :
    let text := "pub enum Tri{A,B,C} pub unitary fn keep(q:Q<Tri>)->Q<Tri>{q}"
    let basis := [.enumeration ⟨"main","Tri",text⟩ ["A","B","C"]]
    observed text = some ([owner basis],owner basis) := by decide +kernel

theorem zero_width_nominal_and_ordinary_unit_are_distinct_parameters :
    let text := "pub struct Empty{} pub unitary fn keep(q:Q<Empty>,z:Unit)->Q<Empty>{q}"
    let basis := [.record ⟨"main","Empty",text⟩ []]
    observed text = some ([owner basis,ordinary [.unit]],owner basis) := by decide +kernel

theorem original_nominal_record_cannot_contain_a_quantum_field :
    observed "pub struct Bad{q:Q<Bit>} pub unitary fn keep(q:Q<Bad>)->Q<Bad>{q}" = none := by decide +kernel

-- Only the declared header is read here. A future execution gate must still
-- check the complete actual body/effect. This read is no verified effect label.
theorem reading_an_annotation_does_not_certify_its_observing_body :
    observed "pub unitary fn keep(q:Q<Bit>)->Unit{discard(q)}" =
      some ([owner [.bit]],ordinary [.unit]) := by decide +kernel

end QleisliKernel.Tests.RuntimeSignature
