import QleisliKernel.Qirf.RuntimePrimitiveAction
import QleisliKernel.Qirf.RuntimeOwnerTransition
import QleisliKernel.Qirf.RuntimeStructuralAction

/-! Original event binding for one checked native primitive. The event keeps
its complete source callee, tokens, lexical scope and offset. Actual source
owners, current frame, owner transition, port lookups and checker invocation
remain indexed by the same native action. This receipt issues no handle.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimePrimitiveSource
open QleisliKernel Finite SourceTypes
open RuntimeOwnerMap (Owner Map)

/-- The existing ordered logical-owner lookup, shared without a second read. -/
def rolePorts (roles : List Owner) (bindings : Map) : WorkM (List Semantics.Raw.Port) := do
  let ordered ← RuntimeOwnerMap.order roles bindings
  return ordered.map (·.port)

structure PortAt (role : Owner) (bindings : Map) where
  port : Semantics.Raw.Port
  original : RuntimeInterval.Computed (rolePorts [role] bindings) [port]

/-- Retain the actual singleton lookup already needed by the native action. -/
def readPort (role : Owner) (bindings : Map) : WorkM (PortAt role bindings) := do
  let ports ← NaturalAffine.witness (rolePorts [role] bindings)
  match selected : ports.val with
  | [port] =>
    return ⟨port,by rw [← selected]; with_reducible exact ports.property⟩
  | _ => throw .request

inductive PrimitiveKind : CallName.Primitive → RuntimePrimitiveAction.Kind → Prop where
  | h : PrimitiveKind .h .h
  | globalPhaseEighth : PrimitiveKind .globalPhaseEighth .globalPhaseEighth

/-- The original native dispatch, with its successful source-kind equality. -/
def readKind : (kind : CallName.Primitive) →
    WorkM {required : RuntimePrimitiveAction.Kind // PrimitiveKind kind required}
  | .h => pure ⟨.h,.h⟩
  | .globalPhaseEighth => pure ⟨.globalPhaseEighth,.globalPhaseEighth⟩
  | _ => throw .request

/-- Kind and operand are taken from the true original event. A phase cannot
borrow an exponent inferred from a matrix or a different source occurrence. -/
inductive Selected {sources caller} :
    SourceRuntimeContext.Event sources caller → Nat → Owner → RuntimePrimitiveAction.Kind → Type where
  | primitive (event : SourceRuntimeContext.PrimitiveEvent sources caller) (nextOrdinal : Nat)
      (role : Owner) (kind : RuntimePrimitiveAction.Kind)
      (preserving : (event.allocated.isEmpty && event.consumed.isEmpty && event.nextOrdinal == nextOrdinal) = true)
      (argument : event.arguments = [[.owner role]]) (selected : PrimitiveKind event.kind kind) :
      Selected (.primitive event) nextOrdinal role kind
  | phase (event : SourceRuntimeContext.PhaseEvent sources caller) (nextOrdinal : Nat) :
      Selected (.phase event) nextOrdinal event.operand (.phase event.application.coefficient.exponent)

/-- The action's original source and its existing native computation are both
retained. The separate interval and action interval have the SAME literal
block/start/count indices; neither is replaced by a caller-supplied frame. -/
structure Checked {dependencies program block start count input output role kind}
    (action : @RuntimePrimitiveAction.Checked dependencies program block start count input output role kind) where
  sources : Sources
  caller : String
  event : SourceRuntimeContext.Event sources caller
  history : RuntimeStructuralAction.SourceState
  interval : RuntimeInterval.Checked block start count
  frame : RuntimeOwnerMap.Checked (history.bindings.map (·.owner)) interval.before
  selected : Selected event history.nextOrdinal role kind
  owners : RuntimeOwnerTransition.Checked interval frame.bindings
  ownerRead : RuntimeInterval.Computed (RuntimeOwnerTransition.read interval frame.bindings) owners
  inputPort : PortAt role frame.bindings
  inputToken : inputPort.port.token = input
  outputPort : PortAt role owners.after.bindings
  outputToken : outputPort.port.token = output
  actionRead : RuntimeInterval.Computed (RuntimePrimitiveAction.check block start count input output role kind) action

def Checked.after {dependencies program block start count input output role kind action}
    (checked : @Checked dependencies program block start count input output role kind action) :
    RuntimeStructuralAction.SourceState :=
  {checked.history with bindings := checked.owners.after.bindings}

end QleisliKernel.Qirf.RuntimePrimitiveSource
