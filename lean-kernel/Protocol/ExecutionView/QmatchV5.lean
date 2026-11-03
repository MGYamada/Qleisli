import Protocol.QmatchV5
import Protocol.ExecutionView.CheckedCarrier
import Protocol.ExecutionView.CheckedRuntimeRoot
import Protocol.ExecutionView.Graph

/-! Independent typed v5 view preparation. No JSON encoder or original-body
checker supplies the view, and this module grants no native acceptance route.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Protocol.ExecutionView.QmatchV5
open Gate Semantics.FiniteCarrier Protocol.QmatchV5 SourceTypes

private def record (tag : String) (fields : List Value) : Value := .array (.text tag :: fields)
private def basis (value : Basis) : Value := .array (value.map CheckedCarrier.atom)
private def bases (values : List (String × Basis)) : Value := .array (values.map fun (name,value) =>
  record "source-static-basis" [.text name,basis value])
private def naturals (values : List (String × Nat)) : Value := .array (values.map fun (name,value) =>
  record "source-static-natural" [.text name,.natural value])
private def references (values : List (String × Nat)) : Value := .array (values.map fun (name,value) =>
  record "source-operation-reference" [.text name,.natural value])

def node : OperationDescription.Node → Value
  | .provider owner name b n o => record "source-operation-provider" [.text owner,.text name,bases b,naturals n,references o]
  | .formal owner name b n o ordinal => record "source-operation-formal"
      [.text owner,.text name,bases b,naturals n,references o,.natural ordinal]
  | .primitive kind target => record "source-operation-primitive"
      [.text (match kind with | .h => "h" | .globalPhaseEighth => "global_phase_eighth"),basis target]
  | .requested child owner name => record "source-operation-requested" [.natural child,.text owner,.text name]
  | .inverse child => record "source-operation-inverse" [.natural child]
  | .controlled child => record "source-operation-controlled" [.natural child]
  | .thenOp left right => record "source-operation-then" [.natural left,.natural right]
  | .tensor left right => record "source-operation-tensor" [.natural left,.natural right]
  | .power child count => record "source-operation-power" [.natural child,.natural count]
  | .conjugate outer middle => record "source-operation-conjugate" [.natural outer,.natural middle]

def operation (value : OperationDescription.Description) : Value :=
  record "source-operation-description" [.array (value.nodes.map node),.natural value.root]

def source (value : Protocol.QmatchV5.Source) : Value := record "source-function"
  [.text value.moduleName,.text value.functionName,bases value.arguments.bases,naturals value.arguments.naturals,
    .array (value.arguments.operations.map fun (name,value) => record "source-static-operation" [.text name,operation value])]

def position (value : Qirf.SourceSequence.Position) : Value :=
  record "source-interval" [.natural value.offset,.natural value.start,.natural value.count]

def provider : Protocol.QmatchV5.Provider → Value
  | .function evidence => record "qmatch-function-provider" [.natural evidence]
  | .pure program => record "qmatch-pure-provider" [.natural program]

def arm (value : Protocol.QmatchV5.Arm) : Value :=
  record "qmatch-arm" [.natural value.implementation,.natural value.controlled]

def site (value : Protocol.QmatchV5.Site) : Value := record "qmatch-site"
  [CheckedCarrier.typedInterface value.attached,CheckedCarrier.typedInterface value.required,
    position value.position,.array (value.arms.map arm)]

def context : Nat → Protocol.QmatchV5.Context → Finite.WorkM Value :=
  Nat.rec (fun _ => throw .limit) (fun _ readChild (.withReferences positions sites calls branches bodies references) => do
    Finite.exactWork (Exact.charge (16*(positions.length+sites.length+calls.length+branches.length+bodies.length+references.length+1)))
    let calls ← calls.mapM fun (location,body) => do
      return record "source-call" [position location,← readChild body]
    let branches ← branches.mapM fun (location,whenTrue,whenFalse) => do
      return record "source-branch" [position location,← readChild whenTrue,← readChild whenFalse]
    let bodyValue := fun (subject,body) => do return record "source-body" [provider subject,← readChild body]
    let bodies ← bodies.mapM bodyValue
    let references ← references.mapM fun groups => do
      Finite.exactWork (Exact.charge (16*(groups.length+1)))
      let groups ← groups.mapM fun leaves => do
        Finite.exactWork (Exact.charge (16*(leaves.length+1)))
        return Value.array (← leaves.mapM bodyValue)
      return Value.array groups
    return record "source-context" [.array (positions.map position),.array (sites.map site),.array calls,.array branches,.array bodies,.array references])

def runtime (request : Qirf.RuntimeFamily.Request) : Finite.WorkM Value := do
  return record "source-runtime" (← CheckedRuntimeRoot.requestDescription request)

def description (artifact : Qirf.Artifact) (root : Qirf.Validity.Root) (request : Protocol.QmatchV5.Request) :
    Finite.WorkM Value := do
  let graph ← FiniteView.graph artifact root
  return record Protocol.QmatchV5.profile [graph,source request.source,← runtime request.runtime,← context 129 request.context]

end QleisliKernel.Protocol.ExecutionView.QmatchV5
