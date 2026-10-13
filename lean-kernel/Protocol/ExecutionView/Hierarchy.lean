import Protocol.ExecutionView.Finite
import Protocol.HierarchicalFinite

/-! Derive the hierarchy runtime plan from typed original data and exact
finite reconstructions. This is descriptive materialization, not a reference
meaning or an acceptance rule. Unsupported execution remains explicit.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Protocol.ExecutionView.HierarchyView
open QleisliKernel.Hierarchical QleisliKernel.Hierarchical.Artifact
open QleisliKernel.Finite

private def record (tag : String) (fields : List Value) : Value :=
  .array (.text tag :: fields)
private def ns (values : List Nat) : Value := .array (values.map .natural)

abbrev Matrices := List (Nat × Semantics.Exact.Matrix)

/-- The returned matrix is the exact required object passed to the original
leaf checker in this computation. No receipt or host matrix is an input. -/
def reconstructLeaf (request : Hierarchical.Finite.Request) :
    WorkM (Nat × Semantics.Exact.Matrix) := do
  let required ← HierarchicalFinite.matrix request.description
  HierarchicalFinite.checkLeaf request.program request.physical.interface required
  return (request.proof.implementation,required)

def reconstructLeaves (requests : Array Hierarchical.Finite.Request) : WorkM Matrices :=
  requests.toList.mapM reconstructLeaf

theorem reconstructLeaf_bound (request : Hierarchical.Finite.Request)
    (result : Nat × Semantics.Exact.Matrix) (work left : Nat)
    (ok : (reconstructLeaf request).run work = (.ok result,left)) :
    result.1 = request.proof.implementation ∧ ∃ middle,
      (HierarchicalFinite.matrix request.description).run work = (.ok result.2,middle) ∧
      (HierarchicalFinite.checkLeaf request.program request.physical.interface result.2).run middle =
        (.ok (),left) := by
  unfold reconstructLeaf at ok
  obtain ⟨required,a,hm,h⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨_,b,hc,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨rfl,rfl⟩ := pure_success _ _ _ _ h
  exact ⟨rfl,a,hm,hc⟩

private def axes (side : Side) : WorkM (List Nat) := do
  exactWork (Exact.charge (1 + side.quantum.size + side.classical.size))
  exactWork (Exact.charge (side.quantum.foldl (fun n p => n+p.axes.size) 0))
  return side.quantum.toList.flatMap (fun p => p.axes.toList)

private def positions (source targets : List Nat) : WorkM (List Nat) := do
  exactWork (Exact.charge (1 + source.length * targets.length))
  targets.mapM fun axis => do
    guard (source.contains axis)
    return source.idxOf axis

private def target (side : Side) (owner : Nat) : WorkM Nat := do
  let all ← axes side
  let port ← lift (readOption (side.quantum.find? (fun p => p.owner == owner)))
  guard (port.axes.size == 1)
  let axis ← lift (readOption port.axes[0]?)
  let found ← positions all [axis]
  lift (readOption found[0]?)

private def node (matrices : Matrices) (index : Nat) (definition : Definition) : WorkM Value := do
  let input ← axes definition.interface.inputs
  let output ← axes definition.interface.outputs
  guard (definition.interface.inputs.classical.isEmpty && definition.interface.outputs.classical.isEmpty &&
    input.length == output.length && definition.effect == .unitary)
  let op ← match definition.body with
    | .leaf _ => do
      exactWork (Exact.charge (matrices.length+1))
      let (_,matrix) ← lift (readOption (matrices.find? (fun p => p.1 == index)))
      pure (record "leaf" [FiniteView.matrix matrix])
    | .sequence children => do
      exactWork (Exact.charge (children.size+1))
      pure (record "sequence" [ns children.toList])
    | .tensor left right => pure (record "tensor" [.natural left,.natural right])
    | .repeatOp count child => pure (record "repeat" [.natural child,.natural count])
    | .inverse child => pure (record "inverse" [.natural child])
    | .control child polarity => pure (record "control" [.natural child,.boolean polarity])
    | .rewire permutation => do
      exactWork (Exact.charge (permutation.axes.size+1))
      pure (record "permutation" [ns permutation.axes.toList])
    | .structural _ => do
      pure (record "permutation" [ns (← positions input output)])
    | .dyadicPhase owner j k => do
      pure (record "phase" [.natural (← target definition.interface.inputs owner),.natural j,.natural k])
    | _ => throw .invalid
  return record "node" [.natural input.length,op]

private def byteSize (value : Value) : WorkM Nat := do
  let bytes ← lift ((encode value).mapError (fun _ => .limit))
  return bytes.size

/-- Every definition participates, including unused and zero-repeat children.
Precharge scans and bound each encoded node before accumulating its value. -/
def program (artifact : Hierarchical.Artifact.Artifact) (matrices : Matrices) : WorkM Value := do
  exactWork (Exact.charge (artifact.definitions.size+1))
  let root ← lift (readOption artifact.definitions[artifact.entry.implementation]?)
  let input ← axes root.interface.inputs
  let output ← axes root.interface.outputs
  let describe := fun nodes => record "hierarchy-program"
    [.array nodes,.natural artifact.entry.implementation,ns input,ns output]
  let initial ← byteSize (describe [])
  let (_,nodes) ← artifact.definitions.toList.zipIdx.foldlM (fun (used,nodes) (definition,index) => do
    let value ← node matrices index definition
    let size ← byteSize value
    guard (used+(size-4) ≤ maxBytes) .limit
    return (used+(size-4),value :: nodes)) (initial,[])
  return describe nodes.reverse

def purePlan (artifact : Hierarchical.Artifact.Artifact) (matrices : Matrices) : WorkM Value := do
  let description := record "hierarchy-plan" [record "pure" [← program artifact matrices]]
  let _ ← byteSize description
  return description

/-- Derive preparation and readout positions from actual definitions, not the
request's names or claimed result. It describes the runtime's explicit pack. -/
def instrumentPlan (packet : Instrument.Packet) (matrices : Matrices) : WorkM Value := do
  let circuit ← program packet.artifact matrices
  let root ← lift (readOption packet.artifact.definitions[packet.artifact.entry.implementation]?)
  let before ← axes root.interface.inputs
  let after ← axes root.interface.outputs
  let inputSide := match packet.preparation.initializations[0]? with
    | some first => first.interface.inputs
    | none => packet.preparation.outputs
  guard inputSide.classical.isEmpty
  let input ← axes inputSide
  let inputPositions ← positions before input
  exactWork (Exact.charge (packet.preparation.initializations.size + packet.readout.measurements.size+1))
  let fresh ← packet.preparation.initializations.toList.mapM fun definition => do
    let .init0 owner := definition.body | throw .invalid
    let all ← axes definition.interface.outputs
    let position ← target definition.interface.outputs owner
    lift (readOption all[position]?)
  let measured ← packet.readout.measurements.toList.mapM fun definition => do
    let .observeZ owner value := definition.body | throw .invalid
    let all ← axes definition.interface.inputs
    let position ← target definition.interface.inputs owner
    let axis ← lift (readOption all[position]?)
    return (value,axis)
  let pack := packet.readout.pack.toList
  exactWork (Exact.charge (pack.length * measured.length+1))
  let measuredAxes ← pack.mapM fun value => do
    let (_,axis) ← lift (readOption (measured.find? (fun p => p.1 == value)))
    pure axis
  let outcomePositions ← positions after measuredAxes
  let residual ← axes packet.readout.outputs
  let residualPositions ← positions after residual
  let description := record "hierarchy-plan" [record "instrument" [circuit,
    ns input,ns fresh,ns inputPositions,
    .array (measured.map (fun (value,axis) => record "measurement" [.natural value,.natural axis])),
    ns pack,ns outcomePositions,ns residual,ns residualPositions]]
  let _ ← byteSize description
  return description

end QleisliKernel.Protocol.ExecutionView.HierarchyView
