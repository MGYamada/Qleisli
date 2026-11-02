import QleisliKernel.SourceTypes.SourceRuntimeTransformSyntax
import QleisliKernel.SourceTypes.SourceRuntimeValues

/-! Complete direct-transform runtime group ports. Internal packing is not a
source type: every original Q leaf, nested tuple and zero-width owner remains.
Native forward-body and transformed-operator equations remain mandatory.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes.SourceRuntimeTransformPorts
open QleisliKernel QleisliKernel.SourceTypes SourceRuntimeValues
open SourceRuntimeTransformSyntax

structure Ports where
  input : Semantics.RuntimeType.Tree
  output : Semantics.RuntimeType.Tree
  deriving BEq, DecidableEq, Repr

def group (parameters : List Semantics.RuntimeType.Tree) : Except String Semantics.RuntimeType.Tree :=
  match parameters with
  | [] => .error "direct runtime transform arity zero"
  | [single] => .ok single
  | _ => .ok (Semantics.RuntimeType.tuple parameters.length parameters)

def quantumValue (tree : Semantics.RuntimeType.Tree) : Except String Value := do
  let (values,_,_) ← seedValues [(⟨tree,[]⟩ : RuntimeSignature.Part #[])]
  let [value] := values | throw "runtime group type multiplicity"
  if (valueOwners value).isEmpty || value.any (fun atom => match atom with | .ordinary .. => true | _ => false) then
    throw "runtime group must contain only nonempty quantum owner leaves"
  return value

def read (parameters : List Semantics.RuntimeType.Tree) (result : Semantics.RuntimeType.Tree)
    (access : Access) (repeated : Bool := false) : Except String Ports := do
  let input ← group parameters
  let _ ← quantumValue input
  let _ ← quantumValue result
  if access == .adjoint && parameters.length == 1 && !repeated then
    match input,result with
    | .quantum :: _,.quantum :: _ => return ⟨result,input⟩
    | _,_ => pure ()
  if input != result then throw "runtime group complete result type differs from original target"
  return ⟨input,result⟩

def product (counts : List Nat) : Except String Nat :=
  counts.foldlM (fun accumulated count => do
    let result := accumulated*count
    if result > 4294967295 then throw "runtime transparent power intermediate overflow"
    return result) 1

def apply (ports : Ports) (access : Access) (arguments : List Value) (nextOrdinal : Nat) : Except String
    (Value × List Semantics.SourceOwners.Owner × List Semantics.SourceOwners.Owner × Nat) := do
  let (control,target) ← if access == .controlled then do
      let [[.owner control],target] := arguments | throw "runtime controlled group arguments"
      if control.basis != [.bit] then throw "runtime group control exact Bit type"
      return (some control,target)
    else do
      let [target] := arguments | throw "runtime transform requires one complete target expression"
      return (none,target)
  if typeOf target != ports.input then throw "runtime transform target exact group shape"
  let template ← quantumValue ports.output
  let (value,fresh) := template.foldl (fun (value,fresh) atom => match atom with
    | .tuple arity => (value ++ [.tuple arity],fresh)
    | .owner owner =>
      let actual : Semantics.SourceOwners.Owner := ⟨nextOrdinal+fresh.length,owner.basis⟩
      (value ++ [.owner actual],fresh ++ [actual])
    | .ordinary .. => (value,fresh)) ([],[])
  let consumed := valueOwners target
  if let some control := control then
    if consumed.any (·.ordinal == control.ordinal) then throw "runtime control aliases target owner"
    return (.tuple 2 :: .owner control :: value,fresh,consumed,nextOrdinal+fresh.length)
  return (value,fresh,consumed,nextOrdinal+fresh.length)

end QleisliKernel.SourceTypes.SourceRuntimeTransformPorts
