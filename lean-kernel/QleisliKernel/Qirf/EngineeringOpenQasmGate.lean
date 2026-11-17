import QleisliKernel.Target.CanonicalOpenQasmResources
import QleisliKernel.Target.CanonicalOpenQasm
import QleisliKernel.Qirf.OperationIRMeaning
import QleisliKernel.Qirf.EngineeringPure

/-! Exact reconstruction and engineering comparison for literal OpenQASM gate
definitions. Subroutine ports are open and ordered. A terminal instrument has
different observations and cannot supply this phase-sensitive bound.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.EngineeringOpenQasmGate
open QleisliKernel.Finite QleisliKernel.Semantics.Exact QleisliKernel.Semantics.Finite
open QleisliKernel.Engineering
open Target.CanonicalOpenQasmRouting (ascii header)
open Target.CanonicalOpenQasmResources (Gate Instruction lines)
open Target.CanonicalOpenQasm (GateCounts maxGates)
open SourceTypes.NaturalAffine (witness)
open RuntimeInterval (Computed)

inductive Ports where
  | one | two
  deriving BEq, DecidableEq, Repr

def Ports.basis : Ports → Basis
  | .one => [.bit]
  | .two => [.pair,.bit,.bit]

structure Block where
  ports : Ports
  instructions : List Instruction
  deriving BEq, DecidableEq, Repr

def maxBytes : Nat := 1024

private def formals : List UInt8 → Option (List Nat)
  | [97,59] => some [0]
  | [98,59] => some [1]
  | [97,44,32,98,59] => some [0,1]
  | [98,44,32,97,59] => some [1,0]
  | _ => none

private def instruction (ports : Ports) (line : List UInt8) : Option Instruction := do
  let name := line.takeWhile (· != 32)
  let 32 :: args := line.drop name.length | none
  let gate ← Gate.read name
  let wires ← formals args
  if wires.length == gate.arity && wires.all (· < width ports.basis) then
    some ⟨gate,wires⟩
  else
    none

def decode (bytes : ByteArray) : Option Block := do
  if bytes.size > maxBytes || (bytes.extract 0 header.length).data.toList != header then none else
  let declaration :: body ← lines (bytes.extract header.length bytes.size).data.toList | none
  let ports ←
    if declaration == ascii "gate implementation a {" then some Ports.one
    else if declaration == ascii "gate implementation a, b {" then some Ports.two
    else none
  let closing :: reversed ← body.reverse | none
  if closing == ascii "}" && reversed.length ≤ maxGates then
    return ⟨ports, ← reversed.reverse.mapM (instruction ports)⟩
  else none

def Block.counts (block : Block) : GateCounts :=
  ⟨block.instructions.length,
    (block.instructions.filter fun step => step.gate == .t || step.gate == .tdg).length⟩

structure CheckedBlock (bytes : ByteArray) (limits : GateCounts) where
  block : Block
  read : decode bytes = some block
  within : block.counts.within limits = true

def checkBlock (bytes : ByteArray) (limits : GateCounts) : WorkM (CheckedBlock bytes limits) := do
  guard (bytes.size ≤ maxBytes && limits.gates ≤ maxGates && limits.tGates ≤ maxGates) .limit
  exactWork (Exact.charge (64 * (bytes.size + 1)))
  match read : decode bytes with
  | none => throw .request
  | some block =>
    if within : block.counts.within limits = true then return ⟨block,read,within⟩
    else throw .request

def circuit (ports : Ports) (instructions : List Instruction) : Circuit :=
  ⟨ports.basis,instructions.map Instruction.step⟩

structure CheckedAction (circuit : Circuit) where
  matrix : Matrix
  read : Computed (circuitMatrix [] circuit) matrix
  isometry : ∃ before after, Exact.Matrix.isometry matrix before = (.ok true,after)

def checkAction (circuit : Circuit) : WorkM (CheckedAction circuit) := do
  let actual ← witness (circuitMatrix [] circuit)
  let isometry ← witness (exactWork (Exact.Matrix.isometryWork actual.val))
  if checked : isometry.val = true then
    have gram : ∃ before after, Exact.Matrix.isometry actual.val before = (.ok true,after) := by
      obtain ⟨before,after,ran⟩ := isometry.property
      exact ⟨before,after,checked ▸ exactWork_success _ _ _ _ ran⟩
    return ⟨actual.val,actual.property,gram⟩
  else throw .equation

def readIdeal (ports : Ports) (ideal : EngineeringPure.LeafRequest) : WorkM PureLeaf.Checked :=
  PureLeaf.check ideal.artifact ideal.order ports.basis ports.basis ideal.input ideal.output ideal.required

structure CheckedSlice (ports : Ports) (instructions : List Instruction)
    (ideal : EngineeringPure.LeafRequest) (epsilon : Coefficient) where
  actual : CheckedAction (circuit ports instructions)
  intended : PureLeaf.Checked
  idealRead : Computed (readIdeal ports ideal) intended
  bound : Pure.Checked
  boundRead : Computed (Pure.checkMatrices actual.matrix intended.actual epsilon) bound

def checkSlice (ports : Ports) (instructions : List Instruction)
    (ideal : EngineeringPure.LeafRequest) (epsilon : Coefficient) :
    WorkM (CheckedSlice ports instructions ideal epsilon) := do
  let actual ← checkAction (circuit ports instructions)
  let intended ← witness (readIdeal ports ideal)
  let bound ← witness (Pure.checkMatrices actual.matrix intended.val.actual epsilon)
  return ⟨actual,intended.val,intended.property,bound.val,bound.property⟩

/-- Both comparisons use the same ordered open ports and partition the one
decoded artifact. Component budgets must sum to the explicit total. -/
structure SequentialRequest where
  bytes : ByteArray
  limits : GateCounts
  split : Nat
  first : EngineeringPure.LeafRequest
  second : EngineeringPure.LeafRequest
  firstBudget : Coefficient
  secondBudget : Coefficient
  totalBudget : Coefficient

structure CheckedSequential (request : SequentialRequest) where
  target : CheckedBlock request.bytes request.limits
  split : request.split ≤ target.block.instructions.length
  first : CheckedSlice target.block.ports (target.block.instructions.take request.split)
    request.first request.firstBudget
  second : CheckedSlice target.block.ports (target.block.instructions.drop request.split)
    request.second request.secondBudget
  sum : Exact.Coefficient.add request.firstBudget request.secondBudget = .ok request.totalBudget

def checkSequential (request : SequentialRequest) : WorkM (CheckedSequential request) := do
  let target ← checkBlock request.bytes request.limits
  if split : request.split ≤ target.block.instructions.length then
    let first ← checkSlice target.block.ports (target.block.instructions.take request.split)
      request.first request.firstBudget
    let second ← checkSlice target.block.ports (target.block.instructions.drop request.split)
      request.second request.secondBudget
    let total ← witness (lift (arithmetic (Exact.Coefficient.add request.firstBudget request.secondBudget)))
    if budget : total.val = request.totalBudget then
      have sum : Exact.Coefficient.add request.firstBudget request.secondBudget = .ok request.totalBudget := by
        obtain ⟨before,after,ran⟩ := total.property
        exact budget ▸ arithmetic_success _ _ (lift_success _ _ before after ran).1
      return ⟨target,split,first,second,sum⟩
    else throw .equation
  else throw .request

/-- Axis a is the low control bit and b is the data bit. The exact desired
operator is the controlled lift of the original checked ideal. This comparison
makes no source access claim. -/
structure ControlledRequest where
  bytes : ByteArray
  limits : GateCounts
  ideal : EngineeringPure.LeafRequest
  epsilon : Coefficient

structure CheckedControlled (request : ControlledRequest) where
  target : CheckedBlock request.bytes request.limits
  ports : target.block.ports = .two
  actual : CheckedAction (circuit target.block.ports target.block.instructions)
  ideal : PureLeaf.Checked
  idealRead : Computed (readIdeal .one request.ideal) ideal
  controlled : Matrix
  controlledRead : Computed (OperationIRMeaning.controlled ideal.actual) controlled
  bound : Pure.Checked
  boundRead : Computed (Pure.checkMatrices actual.matrix controlled request.epsilon) bound

def checkControlled (request : ControlledRequest) : WorkM (CheckedControlled request) := do
  let target ← checkBlock request.bytes request.limits
  if ports : target.block.ports = .two then
    let actual ← checkAction (circuit target.block.ports target.block.instructions)
    let ideal ← witness (readIdeal .one request.ideal)
    let controlled ← witness (OperationIRMeaning.controlled ideal.val.actual)
    let bound ← witness (Pure.checkMatrices actual.matrix controlled.val request.epsilon)
    return ⟨target,ports,actual,ideal.val,ideal.property,controlled.val,controlled.property,bound.val,bound.property⟩
  else throw .request

private def sample : ByteArray :=
  "OPENQASM 3.0;\ninclude \"stdgates.inc\";\ngate implementation a, b {\nsdg b;\ncx a, b;\ns b;\n}\n".toUTF8

#guard (decode sample).map (·.instructions) ==
  some [⟨.sdg,[1]⟩,⟨.cx,[0,1]⟩,⟨.s,[1]⟩]
#guard ((checkBlock sample ⟨2,0⟩).run 100000).1.isOk == false
#guard ((checkBlock sample ⟨3,0⟩).run 0).1.isOk == false
#guard (decode (sample ++ "reset a;\n".toUTF8)).isNone

end QleisliKernel.Qirf.EngineeringOpenQasmGate
