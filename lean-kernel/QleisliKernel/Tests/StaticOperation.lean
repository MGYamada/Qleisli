import QleisliKernel.SourceTypes.SourceOperation
import QleisliKernel.SourceTypes.QuantumSignature

/-! Small original static-transfer regressions. These inspect metadata and
generic obligations, separately from actual body/control equations and native
activation. No maximum-width graph or matrix is constructed.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.StaticOperation
open SourceTypes Semantics.FiniteCarrier OperationDescription

private def source :=
  "pub unitary fn keep(q:Q<Bit>)->Q<Bit>{q} " ++
  "pub unitary fn bits(q:Q<Bits<1>>)->Q<Bits<1>>{q} " ++
  "pub observe fn observed(q:Q<Bit>)->Q<Bit>{q} " ++
  "pub unitary fn unused[const U:Op<Bit>](q:Q<Bit>)->Q<Bit>{q} " ++
  "pub unitary fn generic[const U:Op<Bit>](s:Q<Bit>,q:Q<Bit>)->(Q<Bit>,Q<Bit>) requires Controllable(U){qmatch(s,q){0=>U,1=>U}} " ++
  "pub unitary fn no_control[const U:Op<Bit>](s:Q<Bit>,q:Q<Bit>)->(Q<Bit>,Q<Bit>) requires Applicable(U){qmatch(s,q){0=>U,1=>U}}"

private def sources : Sources := #[ ("main",source) ]

private def named (name : String) : Description := provider "main" name [] [] []

private def accepted (description : Description) (context : SourceTypes.StaticOperation.Context := .external) : Bool :=
  ((SourceTypes.StaticOperation.check sources context description).run 10000000).1.isOk

theorem source_provider_has_checked_original_ports :
    ((SourceTypes.StaticOperation.check sources .external (named "keep")).run 10000000).1.map
      (fun checked => (checked.root.input,checked.root.output,checked.root.paths)) =
      .ok ([.bit],[.bit],⟨true,true,true⟩) := by decide +kernel

theorem composed_source_operation_checks_both_children :
    accepted (Description.binary .thenOp (named "keep") (named "keep")) = true := by decide +kernel

theorem equal_width_different_original_type_cannot_compose :
    accepted (Description.binary .thenOp (named "keep") (named "bits")) = false := by decide +kernel

theorem zero_power_keeps_the_external_provider_effect_obligation :
    accepted ((named "observed").unary (fun child => .power child 0)) = false := by decide +kernel

theorem external_observe_cannot_obtain_control_from_a_pure_body :
    accepted (named "observed") = false := by decide +kernel

theorem same_module_observe_retains_an_explicit_internal_body_obligation :
    ((SourceTypes.StaticOperation.check sources (.source "main") (named "observed")).run 10000000).1.map
      (fun checked => checked.providers.map fun provider =>
        (provider.signature.original.parsedHeader.effect,provider.expectedEffect,provider.internalInference)) =
      .ok [(some .observe,.unitary,true)] := by decide +kernel

theorem unrelated_unused_description_node_cannot_hide_a_subject :
    accepted ⟨[.provider "main" "bits" [] [] [],.provider "main" "keep" [] [] []],1⟩ = false := by decide +kernel

theorem forward_and_self_operation_actual_indices_refuse :
    accepted ⟨[.provider "main" "unused" [] [] [("U",0)]],0⟩ = false := by decide +kernel

theorem unused_operation_actual_keeps_exact_original_type :
    accepted (provider "main" "unused" [] [] [("U",named "bits")]) = false := by decide +kernel

theorem unused_operation_actual_keeps_public_effect :
    accepted (provider "main" "unused" [] [] [("U",named "observed")]) = false := by decide +kernel

theorem declared_controllable_formal_keeps_only_its_declared_path :
    ((SourceTypes.StaticOperation.check sources (.source "main")
      (OperationDescription.formal "main" "generic" [] [] [("U",named "keep")] 0)).run 10000000).1.map
      (fun checked => checked.root.paths) = .ok ⟨false,false,true⟩ := by decide +kernel

theorem convenient_actual_does_not_supply_an_undeclared_generic_control_path :
    ((SourceTypes.StaticOperation.check sources (.source "main")
      (OperationDescription.formal "main" "no_control" [] [] [("U",named "keep")] 0)).run 10000000).1.map
      (fun checked => checked.root.paths) = .ok ⟨true,false,false⟩ := by decide +kernel

theorem formal_ordinal_cannot_be_a_natural_or_later_binder :
    accepted (OperationDescription.formal "main" "generic" [] [] [("U",named "keep")] 1) (.source "main") = false :=
  by decide +kernel

end QleisliKernel.Tests.StaticOperation
