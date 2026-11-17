import QleisliKernel.SourceTypes.SourceSyntax

/-! Check that coherent arm trees retain the indexed original body tokens.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.SourceQuantum.InlineArm
open SourceTypes

private def calls (source : String) (index : Nat) : Except String (List Nat) := do
  let tokens ← lexLocated source
  let (parsed,remaining) ← QuantumMatch.parse tokens
  if !remaining.isEmpty then throw "remaining source after selection"
  if atArm : index < parsed.arms.length then
    let arm ← SourceSyntax.readInlineArm parsed ⟨index,atArm⟩
    arm.tree.calls
  else throw "arm index outside original selection"

private def expectedCalls (source : String) (names : List String) : List Nat :=
  ((lexLocated source).toOption.getD []).filterMap (fun token =>
    if names.contains token.text then some token.span.startByte else none)

private def originalTarget (source : String) (offset : Nat) : Option String := do
  let site ← ((QuantumMatch.read #[("main",source)] "main" "choose" offset).run 10000000).1.toOption
  if first : 0 < site.parsed.arms.length then
    let arm ← (SourceSyntax.readInlineArm site.parsed ⟨0,first⟩).toOption
    pure arm.targetName
  else none

example :
    let source := "// λ\nqif(c,q){0=>{let r=h(q);global_phase_eighth(r)},1=>h}"
    (calls source 0).toOption = some (expectedCalls source ["h","global_phase_eighth"]).dropLast := by decide

example :
    let source := "qmatch(c,(q)){1=>{global_phase_eighth(q)},0=>{h(q)}}"
    (calls source 1).toOption = some (expectedCalls source ["h"]) := by decide

example : (calls "qif(c,q){0=>h,1=>h}" 0).toOption = none := by decide

example : (calls "qmatch(c,q){0=>{h(q)} h,1=>h}" 0).toOption = none := by decide

example : (calls "qif(c,h(q)){0=>{h(q)},1=>h}" 0).toOption = none := by decide

example :
    let source := "// λ qif in comment\nunitary fn choose(c:Q<Bit>,data:Q<Bit>)->(Q<Bit>,Q<Bit>){qif(c,data){0=>{h(data)},1=>h}}"
    let offset := (expectedCalls source ["qif"]).head?.getD source.utf8ByteSize
    (originalTarget source offset, originalTarget source (offset+1)) = (some "data",none) := by decide +kernel

end QleisliKernel.Tests.SourceQuantum.InlineArm
