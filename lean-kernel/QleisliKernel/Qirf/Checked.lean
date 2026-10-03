import QleisliKernel.Qirf

/-! Typed stages of actual QIRF acceptance, retaining the original root and equation.
No host result or producer success flag is an input.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.Validity
open Semantics.Exact Semantics.Finite Semantics.Observation Finite

/-- Root type transport keeps the twelve-bit structural domain. Finite
equations separately retain their existing six-bit capacity. -/
def rootBasis (basis : Basis) : Bool :=
  basis.length ≤ 4096 && width basis ≤ 12 &&
  basis.foldl (fun (pending : Option (List Nat)) atom => do
    let depth :: rest ← pending | none
    if depth > 64 then none else
    match atom with
    | .unit | .bit => some rest
    | .pair => some ((depth+1) :: (depth+1) :: rest)
    | .tuple n =>
      if n < 3 || n > 4096 then none else some (List.replicate n (depth+1) ++ rest))
      (some [1]) == some []

def interfaceValid (artifact : Qirf.Artifact) (program : Program) : Bool :=
  match artifact.rootInterface with
  | none => true
  | some (input,output) =>
    rootBasis input && rootBasis output && program.effect == .unitary &&
    program.classicalInputs.isEmpty && program.classicalOutputs.isEmpty &&
    program.inputs.length == 1 && program.outputs.length == 1 &&
    ((program.inputs[0]?).map fun port =>
      port.bits == width input && port.bits == width output).getD false

structure Request where
  signature : Basis
  target : Target
  sources : Option (Array (String × String))

/-- A result is data produced by checking, not a supplied certificate. Its
correctness is established separately from the executable acceptance path. -/
structure Root where
  dependencies : List Dependency
  program : Program
  checked : Raw.Observation.Checked

structure Equation where
  target : Program
  actual : Matrix

structure Checked where
  root : Root
  equation : Option Equation

def sourcesUsed (artifact : Qirf.Artifact) : Bool :=
  let used := artifact.entries.foldl (fun used entry =>
    entry.sources.foldl (fun used index => used.set! index true) used)
    (Array.replicate artifact.sources.size false)
  used.all id

/-- Preserve the complete original graph, root and independent event reader.
The optional mathematical request is a separate stage with the same budget. -/
def checkRoot (artifact : Qirf.Artifact) (order : Array Nat) : WorkM Root := do
  let dependencies ← checkGraph artifact order
  guard (sourcesUsed artifact)
  let program ← lift (readOption artifact.programs[artifact.root]?)
  let checked ← Raw.Observation.verify dependencies program
  guard (interfaceValid artifact program) .request
  return ⟨dependencies,program,checked⟩

/-- Retain both original requested semantics and the reconstructed operator.
Equality checking and whole-space unitarity still execute before returning. -/
def checkRequested (artifact : Qirf.Artifact) (dependencies : List Dependency)
    (program : Program) (request : Request) : WorkM Equation := do
  guard (artifact.rootInterface == some (request.signature,request.signature)) .request
  guard (request.sources.isNone || request.sources == some artifact.sources) .request
  guard (Raw.BranchFunction.preflight request.signature program) .limit
  let target ← meaningProgram request.signature request.target
  let actual ← Raw.BranchFunction.reconstruct dependencies program
  let required ← Raw.BranchFunction.reconstruct [] target
  exactWork (Exact.charge actual.entries.length)
  guard (actual == required) .equation
  wholeSpace actual
  return ⟨target,actual⟩

/-- The single production acceptance path; callers cannot inject stage results. -/
def check (artifact : Qirf.Artifact) (order : Array Nat)
    (request : Option Request) : WorkM Checked := do
  let root ← checkRoot artifact order
  let equation ← match request with
    | none => pure none
    | some request => do
      let equation ← checkRequested artifact root.dependencies root.program request
      pure (some equation)
  return ⟨root,equation⟩

end QleisliKernel.Qirf.Validity
