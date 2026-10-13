import Protocol.ExecutionView.Finite
import QleisliKernel.Qirf.Checked

/-! Complete retained finite graph data, independently read from fresh native
stages. A view is descriptive data; this walker alone authorizes no execution.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Protocol.ExecutionView.FiniteView
open QleisliKernel.Semantics QleisliKernel.Finite

private def graphRecord (tag : String) (fields : List Value) : Value :=
  .array (.text tag :: fields)

private def graphPort (port : Raw.Port) : Value :=
  graphRecord "port" [.natural port.token,
    .array (port.wires.map Value.natural),.natural port.bits]

/-- The root and its metadata come from the same retained native check. Both
the graph table and the actual runtime root are described. Output lookup keeps
the return order, rather than the order of the checker's live store. -/
def graph (artifact : Qirf.Artifact) (root : Qirf.Validity.Root) : WorkM Value := do
  let receipts ← lift (root.receipts.toList.mapM readOption)
  let programs ← lift ((artifact.programs.toList.mapM program).mapError (fun _ => .invalid))
  let evidence ← receipts.mapM functionEvidence
  let actual ← lift ((program root.program).mapError (fun _ => .invalid))
  let state := root.checked.state
  let outputs ← lift (root.program.outputs.mapM fun token =>
    readOption (state.quantum.live.find? fun port => port.token == token))
  let effect := if state.observe then 2 else if state.quantum.iso then 1 else 0
  let interface := match artifact.rootInterface with
    | none => Value.null
    | some (input,output) => graphRecord "root-interface" [basis input,basis output]
  return graphRecord "finite-graph" [.natural artifact.root,interface,
    .array (artifact.sources.toList.map fun source =>
      graphRecord "source" [.text source.1,.text source.2]),
    .array programs,.array evidence,actual,.natural effect,.array (outputs.map graphPort)]

end QleisliKernel.Protocol.ExecutionView.FiniteView
