import QleisliKernel.SourceTypes.QuantumArms

/-! Small original bare-primitive arm regressions. These inspect the common
source binding only; native whole-arm/control equations remain separate.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.QuantumPrimitiveArms
open SourceTypes Finite Semantics.FiniteCarrier OperationDescription

private def arms (source : String) : Option (List (List Node)) :=
  let action : WorkM (List (List Node)) := do
    let sources : Sources := #[("main",source)]
    let signature ← QuantumSignature.read sources "main" "choose"
    let some keyword := signature.original.occurrence.body.find? (·.text == "qmatch") | throw .request
    let target := signature.inputs[1]?.getD []
    let table ← QuantumArms.readArmsWithSignature signature keyword.span.startByte [.bit] target
    pure (table.arms.map fun arm => arm.operation.description.nodes)
  (action.run 10000000).1.toOption

#guard arms ("#![no_implicit_prelude] pub unitary fn choose(s:Q<Bit>,q:Q<Bit>)->(Q<Bit>,Q<Bit>)" ++
    "{qmatch(s,q){0=>h,1=>global_phase_eighth}}") =
  some [[.primitive .h [.bit]],[.primitive .globalPhaseEighth [.bit]]]

#guard arms ("#![no_implicit_prelude] pub unitary fn choose(s:Q<Bit>,q:Q<Unit>)->(Q<Bit>,Q<Unit>)" ++
    "{qmatch(s,q){0=>global_phase_eighth,1=>global_phase_eighth}}") =
  some [[.primitive .globalPhaseEighth [.unit]],[.primitive .globalPhaseEighth [.unit]]]

-- A lexical/spent binding with this spelling cannot fall back to a primitive.
#guard arms ("#![no_implicit_prelude] pub unitary fn choose(s:Q<Bit>,q:Q<Bit>,h:Q<Unit>)->(Q<Bit>,Q<Bit>)" ++
    "{let _=finish(h);qmatch(s,q){0=>h,1=>global_phase_eighth}}") = none

end QleisliKernel.Tests.QuantumPrimitiveArms
