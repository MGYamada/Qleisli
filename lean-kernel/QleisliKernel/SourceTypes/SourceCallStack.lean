import QleisliKernel.SourceTypes.StaticTypes

/-! Closed runtime call-stack checks after original generic typing/decrease
checking. Smaller chosen Nat values alone never establish the original guarded
decrease obligation. These checks grant no recursion or provider authority.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes.SourceCallStack
open Finite

structure Frame where
  moduleName : String
  functionName : String
  naturals : StaticNatural.Bindings
  ordinary : Bool
  deriving BEq, DecidableEq, Repr

def Frame.id (frame : Frame) : String × String := (frame.moduleName,frame.functionName)

def decreases (previous current : StaticNatural.Bindings) : Bool :=
  previous.length == current.length && previous.all (fun (name,bound) =>
    match current.find? (fun binding => binding.1 == name) with
    | some (_,actual) => actual ≤ bound
    | none => false) && previous.any (fun (name,bound) =>
    match current.find? (fun binding => binding.1 == name) with
    | some (_,actual) => actual < bound
    | none => false)

def valid (frame : Frame) : Bool :=
  decide ((frame.naturals.map (·.1)).Nodup) && frame.naturals.all (fun binding => binding.2 ≤ 4294967295)

def permits (active : List Frame) (current : Frame) : Bool :=
  valid current && match active with
    | [] => true
    | previous :: _ =>
      if previous.id == current.id then
        previous.ordinary && current.ordinary && valid previous && decreases previous.naturals current.naturals
      else !(active.any (fun previous => previous.id == current.id))

private def fields (frame : Frame) : Nat :=
  frame.moduleName.utf8ByteSize+frame.functionName.utf8ByteSize+
    (frame.naturals.map fun binding => binding.1.utf8ByteSize+2).sum+2

structure Checked (active : List Frame) (current : Frame) where
  permitted : permits active current = true

def read (active : List Frame) (current : Frame) : WorkM (Checked active current) := do
  exactWork (Exact.charge (16*((active.map fields).sum+fields current+1)*(current.naturals.length+1)))
  if permitted : permits active current = true then return ⟨permitted⟩ else throw .request

end QleisliKernel.SourceTypes.SourceCallStack
