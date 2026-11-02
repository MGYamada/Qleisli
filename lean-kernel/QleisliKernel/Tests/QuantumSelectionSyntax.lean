import QleisliKernel.SourceTypes.QuantumSequence

/-! Original coherent selection grammar and keyword identity. These small
parser studies grant no arm implementation, control or native equation.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.QuantumSelectionSyntax
open SourceTypes

private def parsed (source : String) : Option QuantumMatch.Parsed := do
  let tokens ← (lexLocated source).toOption
  let (parsed,suffix) ← (QuantumMatch.parse tokens).toOption
  if !suffix.isEmpty then none else some parsed

private def source := "qif(s,q){0=>keep,1=>global_phase_eighth}"

#guard (parsed source).map (fun parsed =>
    (parsed.keyword.text,parsed.arms.map fun arm => arm.label.map (·.text))) =
  some ("qif",[["0"],["1"]])
#guard parsed "qif(s,q){1=>keep,0=>global_phase_eighth}" = none
#guard parsed "qif(s,q){0=>keep,1=>global_phase_eighth,}" = none
#guard parsed "qif(s,q){0=>keep,1=>global_phase_eighth,2=>keep}" = none
#guard (parsed "qmatch(s,q){1=>keep,0=>global_phase_eighth,}").isSome

#guard ((parsed source).map fun parsed =>
    (QuantumMatch.acceptsSelector parsed [.bit],QuantumMatch.acceptsSelector parsed [.bits 1],
      QuantumMatch.acceptsSelector parsed [.unit])) = some (true,false,false)
#guard ((lexLocated (source ++ ";qmatch(s,q){0=>keep,1=>keep}")).toOption.map
    (fun tokens => (QuantumSequence.originalOffsets tokens).length)) = some 2

end QleisliKernel.Tests.QuantumSelectionSyntax
