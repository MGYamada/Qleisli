import QleisliKernel.SourceTypes.SourceComputedSyntax
import QleisliKernel.SourceTypes.SourceSyntax
import QleisliKernel.Raw.Workspace

/-! Original computed scope headers, reference names, binders and body slices.
No syntax result supplies owner typing, exact clean release or logical evidence.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.SourceComputedSyntax
open QleisliKernel.SourceTypes

private def read (source : String) : Except String (Sigma QleisliKernel.SourceTypes.SourceComputedSyntax.Checked) := do
  let tokens ← lexLocated source
  return ⟨tokens,← QleisliKernel.SourceTypes.SourceComputedSyntax.read tokens⟩

#guard (read "with_computed(q,p){|aux|z(aux)}").isOk
#guard (read "with_computed(q,lib::p,logical){|data,aux|(data,z(aux))}").isOk
#guard (read "with_computed(f(q),p){|aux|let b=h(aux);h(b)}").isOk
#guard (read "with_computed(q,p){|aux|z(aux)}").toOption.map
  (fun written => written.2.parts.body.map (·.text)) = some ["z","(","aux",")"]
#guard (read "with_computed(q,p,logical){|data,aux|(data,aux)}").toOption.map
  (fun written => written.2.parts.data.map (·.text)) = some (some "data")
#guard (read "with_computed(q,p[2]){|aux|aux}").toOption.isNone
#guard (read "with_computed(q,p,logical()){|data,aux|(data,aux)}").toOption.isNone
#guard (read "with_computed(q,p){|data,aux|aux}").toOption.isNone
#guard (read "with_computed(q,p,logical){|aux|aux}").toOption.isNone
#guard (read "with_computed(q,p,logical){|same,same|(same,same)}").toOption.isNone
#guard (read "with_computed(q,p,){|aux|aux}").toOption.isNone
#guard (read "with_computed(q,p){|aux|aux} trailing").toOption.isNone

#print axioms QleisliKernel.SourceTypes.SourceComputedSyntax.read

private def workspace (source : String) : Except String (Sigma SourceSyntax.Tree) := do
  let tokens ← lexLocated source
  return ⟨tokens,← SourceSyntax.read (tokens.length+1) 0 false tokens⟩

#guard (workspace "clean(make(q),lib::logical){|data,scratch|(data,h(scratch))}").toOption.any
  fun tree => match tree.2 with
  | .workspace written _ dirty _ => written.parts.logicalName.segments == ["lib","logical"] &&
      dirty.trees.isEmpty && written.parts.scratchBinder.text == "scratch" &&
      (tree.2.calls.toOption.map List.length == some 2)
  | _ => false
#guard (workspace "dirty(q,make(d),logical){|data,scratch|(data,scratch)}").toOption.any
  fun tree => match tree.2 with
  | .workspace written _ dirty _ => written.parts.dirty.isSome && dirty.trees.length == 1
  | _ => false
#guard (workspace "clean(q)").toOption.any fun tree => match tree.2 with
  | .call .. => true
  | _ => false
#guard (workspace "dirty(q,logical){|data,scratch|(data,scratch)}").isOk == false
#guard (workspace "clean(q,logical,){|data,scratch|(data,scratch)}").isOk == false
#guard (workspace "clean(q,logical){|same,same|(same,same)}").isOk == false

#print axioms SourceWorkspaceSyntax.read

open QleisliKernel Finite Semantics.Finite

private def controlledFlip : Step := Raw.unitaryStep (.cnot 0 1)
private def dataX : Step := Raw.gateStep .x 0
private def scratchX : Step := Raw.gateStep .x 1
private def scratchZ : Step := Raw.gateStep .z 1

private def restore (dirty : Bool) (steps logical : List Step) : WorkM Semantics.Exact.Matrix := do
  let expected ← circuitMatrix [] (Raw.circuit 1 logical)
  Raw.Workspace.check [] dirty 1 steps expected

private def restorationFailure (dirty : Bool) (result : Except Error Semantics.Exact.Matrix) : Bool :=
  match result with
  | .error (.workspaceRestoration actual) => actual == dirty
  | _ => false

#guard ((restore false [controlledFlip,controlledFlip] []).run 20000000).1.isOk
#guard restorationFailure false ((restore false [controlledFlip] []).run 20000000).1
#guard restorationFailure false ((restore false [scratchX] []).run 20000000).1
#guard ((restore true [controlledFlip,dataX,controlledFlip,scratchX] [dataX]).run 20000000).1.isOk
#guard restorationFailure true ((restore true [dataX,scratchZ] [dataX]).run 20000000).1

#print axioms Raw.Workspace.check_conditions
end QleisliKernel.Tests.SourceComputedSyntax
