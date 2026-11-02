import QleisliKernel.SourceTypes.SourceRuntimeTrace
import QleisliKernel.Tests.SourceTraceOriginals

/-! Active basis obligations bind exact original occurrences and complete
ports; inactive static receipts retain original false-guard proofs. Native body
equations remain separate from these source and finite-function checks.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.SourceRuntimeBasisBindings
open QleisliKernel QleisliKernel.SourceTypes

private def sources (source : String) : Sources := #[("main",source)] ++ SourceTraceOriginals.bundled
private def read (source : String) :=
  ((SourceRuntimeTrace.read (sources source) "main" "route").run 2000000000).1.toOption

private def branches :=
  "pub unitary fn route(c:Bit,q:Q<Bit>)->Q<Bit>{if c{basis q as b{b}}else{basis q as b{not b}}}"
#guard (read branches).map (fun checked =>
  (checked.summary.basis.entries.length,checked.events.flatMap SourceRuntimeContext.Event.basisOffsets |>.length)) = some (2,2)
#guard (read (branches.replace "not b" "0")).isNone
#guard (read ((branches.replace "if c" "if 1").replace "not b" "0")).isNone

private def staticBindings (n : Nat) := do
  let sources := sources "pub unitary fn route[const n:Nat](q:Q<Bit>)->Q<Bit>{if static n==0{q}else{basis q as b{not b}}}"
  let signature ← SourceRuntimeContext.readSignature sources "main" "route" {naturals := [("n",n)]}
  let original ← GenericTypeTrace.readWithInstantiation signature.instantiation
  let bindings ← SourceBasisBindings.prepare signature.instantiation original.basisObligations
  let states := bindings.entries.map fun entry => match entry.2.binding.status with
    | .inactive _ => false | .active _ => true
  return (states,bindings.covered [],bindings.covered (original.basisObligations.map (·.offset)))
#guard ((staticBindings 0).run 2000000000).1.toOption = some ([false],true,false)
#guard ((staticBindings 1).run 2000000000).1.toOption = some ([true],false,true)

private def exactPorts := "pub unitary fn route(q:Q<(Bit,Unit)>)->Q<(Bit,Unit)>{basis q as(b,u){(b,u)}}"
#guard (read exactPorts).map (fun checked => checked.events.all fun event => match event with
  | .basis basis => basis.binding.ports.input == basis.input.basis &&
      basis.binding.ports.output == basis.outputBasis && basis.function.rows == [[0,1]]
  | _ => false) = some true

#print axioms QleisliKernel.SourceTypes.SourceBasisBindings.prepare
#print axioms QleisliKernel.SourceTypes.SourceBasisBindings.ActiveAt.originalMember
#print axioms QleisliKernel.SourceTypes.SourceRuntimeTrace.readBranchSource
end QleisliKernel.Tests.SourceRuntimeBasisBindings
