import QleisliKernel.Hierarchical.NodeTyping
import QleisliKernel.Qirf.ControlAccess
import QleisliKernel.Raw.Finite

/-! Sector checks over the actual ordered hierarchy body.
The enclosing hierarchy check still validates the complete artifact and binds
the selected source occurrence to this root. The leaf reader must reconstruct
the original leaf bytes on the supplied interface.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Hierarchical.ControlAccess

open Artifact
open QleisliKernel.Finite
open QleisliKernel.Semantics.Exact
open QleisliKernel.Semantics.Finite (gather)

abbrev LeafReader := ByteArray → Interface → WorkM Matrix

private def read {α : Type} (value : Option α) : WorkM α :=
  lift (readOption value)

private def identity (bits : Nat) : WorkM Matrix := do
  let dimension := 2^bits
  exactWork (Exact.charge (dimension^2))
  lift (arithmetic (Exact.Matrix.identity dimension))

private def route (bits : Nat) (axes : List Nat) : WorkM Matrix := do
  guard (axes.length == bits && axesValid bits axes) .request
  exactWork (Exact.charge (2^bits * (1 + bits)))
  Raw.mapping bits bits ((List.range (2^bits)).map (gather · axes))

private def controlled (child : Matrix) (polarity : Bool) : WorkM Matrix := do
  let dimension := 2 * child.rows
  guard (child.rows == child.cols && Exact.matrixValid dimension dimension) .request
  exactWork (Exact.charge (2 * dimension^2))
  let entries := child.entries.toArray
  lift (arithmetic (Exact.Matrix.make dimension dimension ((List.range (dimension^2)).map fun i =>
    let row := i / dimension
    let col := i % dimension
    if row % 2 != col % 2 then Scalar.zero
    else if (row % 2 == 1) == polarity then
      entries[row / 2 * child.cols + col / 2]?.getD Scalar.zero
    else if row == col then Scalar.one
    else Scalar.zero)))

private def phase (interface : Interface) (target j k bits : Nat) : WorkM Matrix := do
  -- The existing exact scalar ring represents eighth roots of unity.
  guard (angleValid j k) .request
  let denominator := 2^k
  guard (j * 8 % denominator == 0) .limit
  let owner ← read (interface.inputs.quantum.find? (·.owner == target))
  let axis ← read owner.axes[0]?
  let position := (wires interface.inputs).toList.idxOf axis
  guard (position < bits) .request
  let step : Semantics.Finite.Step :=
    ⟨[], .monomial [position] [0,1] [0,j * 8 / denominator]⟩
  circuitMatrix [] (Raw.circuit bits [step])

private def bodyAction (leaf : LeafReader) (definition : Definition)
    (child : Nat → WorkM Matrix) (bits : Nat) : WorkM Matrix :=
  match definition.body with
  | .leaf bytes => leaf bytes definition.interface
  | .rewire map => route bits map.axes.toList
  | .structural _ => route bits (Structural.axisMap definition.interface)
  | .sequence children => do
    children.foldlM (fun actual index => do
      exactWork (Exact.Matrix.composeWork (← child index) actual)) (← identity bits)
  | .tensor left right => do exactWork (Exact.Matrix.tensorWork (← child left) (← child right))
  | .call index input output => do
    let entered ← exactWork (Exact.Matrix.composeWork (← child index) (← route bits input.axes.toList))
    exactWork (Exact.Matrix.composeWork (← route bits output.axes.toList) entered)
  | .repeatOp count index => do
    let value ← child index
    exactWork (Exact.charge (count+1))
    (List.range count).foldlM (fun actual _ =>
      exactWork (Exact.Matrix.composeWork value actual)) (← identity bits)
  | .inverse index => do exactWork (Exact.Matrix.adjointWork (← child index))
  | .control index polarity => do controlled (← child index) polarity
  | .dyadicPhase target j k => phase definition.interface target j k bits
  | .computed .. | .observeZ .. | .init0 .. => throw .request

/-- Read the root from the original table, recursively through actual edges.
Charge before reading endpoint fields and materializing children. Recursion
spends fuel as well as shared work, including under a zero repetition. -/
def action (leaf : LeafReader) (artifact : Artifact) : Nat → Nat → WorkM Matrix
  | 0, _ => throw .limit
  | fuel+1, index => do
    let definition ← read artifact.definitions[index]?
    let interface := definition.interface
    exactWork (Exact.charge (16 * (1 + interface.scan + definition.body.charge)))
    let bits := Ports.wireCount interface.inputs
    let outputBits := Ports.wireCount interface.outputs
    exactWork (Exact.charge (16 * (1 + interface.charge + bits^2 + outputBits^2)))
    guard (bits ≤ 6 && outputBits ≤ 6) .limit
    guard (definition.effect == .unitary && bits == outputBits &&
      NodeTyping.quantumOnly interface) .request
    let actual ← bodyAction leaf definition (action leaf artifact fuel) bits
    guard (actual.rows == 2^bits && actual.cols == 2^bits) .request
    return actual

/-- The original source supplies the ordered port types and role at each
argument. A zero-width owner still occupies one position in both lists. -/
structure Request where
  root : Nat
  ports : Array Basis
  controls : Array Bool
  deriving Repr

def Request.matches (request : Request) (interface : Interface) : Bool :=
  request.ports.size == request.controls.size && request.controls.any id &&
    request.ports == Structural.types interface.inputs &&
    request.ports == Structural.types interface.outputs

def controlledAxes (roles : Array Bool) (side : Side) : List Nat :=
  let (_,axes) := (roles.toList.zip side.quantum.toList).foldl (fun (offset,axes) (control,port) =>
    (offset + port.axes.size,
      if control then axes ++ (List.range port.axes.size).map (offset + ·) else axes)) (0,[])
  axes

/-- Check the original call's ordered owner forest and the selected
computational coordinates of its reconstructed action. -/
def check (leaf : LeafReader) (artifact : Artifact) (request : Request) :
    WorkM Matrix := do
  let root ← read artifact.definitions[request.root]?
  exactWork (Exact.charge (16 * (1 + root.interface.scan + request.ports.size + request.controls.size)))
  guard (request.ports.size ≤ 64) .request
  exactWork (Exact.charge (16 * (1 + root.interface.charge +
    request.ports.foldl (fun total basis => total + basis.size) 0)))
  guard (request.matches root.interface) .request
  let actual ← action leaf artifact Limits.maxDepth request.root
  QleisliKernel.Qirf.ControlAccess.checkMatrix
    (Ports.wireCount root.interface.inputs) actual (controlledAxes request.controls root.interface.inputs)
  return actual

theorem check_bound (leaf : LeafReader) (artifact : Artifact) (request : Request)
    (actual : Matrix) (work left : Nat)
    (ok : (check leaf artifact request).run work = (.ok actual,left)) :
    ∃ root start middle, artifact.definitions[request.root]? = some root ∧
      request.matches root.interface = true ∧
      (action leaf artifact Limits.maxDepth request.root).run start = (.ok actual,middle) ∧
      (QleisliKernel.Qirf.ControlAccess.checkMatrix (Ports.wireCount root.interface.inputs)
        actual (controlledAxes request.controls root.interface.inputs)).run middle = (.ok (),left) ∧
      Semantics.ControlAccess.PreservesSectors actual
        (controlledAxes request.controls root.interface.inputs) := by
  obtain ⟨root,_,found,tail⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨_,_,_,tail⟩ := bind_success _ _ _ _ _ tail
  obtain ⟨_,_,_,tail⟩ := bind_success _ _ _ _ _ tail
  obtain ⟨_,_,_,tail⟩ := bind_success _ _ _ _ _ tail
  obtain ⟨_,start,interface,tail⟩ := bind_success _ _ _ _ _ tail
  obtain ⟨matrix,middle,reconstructed,tail⟩ := bind_success _ _ _ _ _ tail
  obtain ⟨_,finish,sector,result⟩ := bind_success _ _ _ _ _ tail
  obtain ⟨same,remaining⟩ := pure_success _ _ _ _ result
  subst actual
  subst finish
  have present : artifact.definitions[request.root]? = some root := by
    have bound := (lift_success _ _ _ _ found).1
    cases h : artifact.definitions[request.root]? <;> simp_all [read,readOption]
  exact ⟨root,start,middle,present,(guard_success _ _ _ _ interface).1,reconstructed,sector,
    QleisliKernel.Qirf.ControlAccess.checkMatrix_sectors _ _ _ _ _ sector⟩

end QleisliKernel.Hierarchical.ControlAccess
