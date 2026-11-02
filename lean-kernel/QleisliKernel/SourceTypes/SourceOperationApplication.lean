import QleisliKernel.SourceTypes.SourceRuntimeValues
import QleisliKernel.SourceTypes.SourceOperation
import QleisliKernel.SourceTypes.PhaseApplication
import QleisliKernel.SourceTypes.SourceOperationSyntax

/-! Original operation-expression application, including genuine Op formals.
The typed operation graph and exact runtime owner ports are retained together.
Provider bodies and constructed native equations remain separate obligations.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes.SourceOperationApplication
open QleisliKernel QleisliKernel.SourceTypes SourceRuntimeValues

abbrev controlled := SourceOperationSyntax.controlled

abbrev selected := SourceOperationSyntax.selected

def targetBasis (tokens : List LocatedToken) (arguments : List Value) :
    Except String Semantics.FiniteCarrier.Basis :=
  if controlled tokens then match arguments with
    | [[.owner _],[.owner target]] => .ok target.basis
    | _ => .error "controlled operation runtime arguments"
  else match arguments with
    | [[.owner owner]] => .ok owner.basis
    | _ => .error "unary operation runtime arguments"

def ofQuantum (value : Semantics.SourceOwners.Value) : Value := value.map fun atom => match atom with
  | .owner owner => .owner owner
  | .tuple arity => .tuple arity

def toQuantum (value : Value) : Except String Semantics.SourceOwners.Value := value.mapM fun atom =>
  match atom with
  | .owner owner => pure (.owner owner)
  | .tuple arity => pure (.tuple arity)
  | .ordinary .. => throw "ordinary value in quantum operation result"

def apply (input output : Semantics.FiniteCarrier.Basis) (controlled : Bool)
    (arguments : List Value) (nextOrdinal : Nat) : Except String
      (Value × List Semantics.SourceOwners.Owner × List Semantics.SourceOwners.Owner × Nat) := do
  if controlled then
    let [[.owner control],[.owner target]] := arguments | throw "controlled operation argument shape"
    if control.basis != [.bit] || control.ordinal == target.ordinal then
      throw "controlled operation control/owner type"
    if input != .pair :: control.basis ++ target.basis || output != input then
      throw "controlled operation exact ports"
    return ([.tuple 2,.owner control,.owner target],[],[],nextOrdinal)
  let [[.owner owner]] := arguments | throw "operation application requires one quantum owner"
  if owner.basis != input then throw "operation application exact input type"
  if input == output then return ([.owner owner],[],[],nextOrdinal)
  let result : Semantics.SourceOwners.Owner := ⟨nextOrdinal,output⟩
  return ([.owner result],[result],[owner],nextOrdinal+1)

structure Event (sources : Sources) (caller : String) where
  tokens : List LocatedToken
  call : CallSyntax.Checked tokens
  callerName : String
  original : OrdinarySignature.Original sources caller callerName
  instantiation : StaticInstantiation.Checked original
  naturals : PhaseApplication.Naturals sources
  scope : List String
  operation : SourceOperation.CheckedWithInstantiation instantiation naturals.helpers.val
    naturals.environment scope call.call.callee
  applicable : operation.graph.root.paths.applicable = true
  arguments : List Value
  nextOrdinal : Nat
  value : Value
  allocated : List Semantics.SourceOwners.Owner
  consumed : List Semantics.SourceOwners.Owner
  afterOrdinal : Nat
  applied : apply operation.graph.root.input operation.graph.root.output (controlled call.call.callee)
    arguments nextOrdinal = .ok (value,allocated,consumed,afterOrdinal)
  held : List Semantics.SourceOwners.Owner
  remaining : List Semantics.SourceOwners.Owner

def Event.inputOwners {sources caller} (event : Event sources caller) : List Semantics.SourceOwners.Owner :=
  event.arguments.flatMap valueOwners

def Event.outputOwners {sources caller} (event : Event sources caller) : List Semantics.SourceOwners.Owner :=
  valueOwners event.value

def Event.frameOwners {sources caller} (event : Event sources caller) : List Semantics.SourceOwners.Owner :=
  event.inputOwners ++ event.held ++ event.remaining

def Event.effect {sources caller} (event : Event sources caller) : Semantics.Raw.Effect :=
  event.operation.graph.root.effect

end QleisliKernel.SourceTypes.SourceOperationApplication
