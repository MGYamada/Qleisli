import QleisliKernel.Qirf.StructuralXorPredicate
import QleisliKernel.Qirf.RuntimePrimitiveSource

/-! Bind a predicate to the actual Raw applyUnitary interval in its local
data-then-auxiliary order. Whole computed scopes additionally bind their use,
inverse and clean return. Copyright 2026 Qleisli Project Contributors.
SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.StructuralXorInterval
open QleisliKernel Finite Semantics.Finite SourceTypes
open RuntimePrimitiveSource (PortAt readPort)

structure Checked {sources caller dependencies program block start count}
    {event : SourceRuntimeContext.ComputedEvent sources caller}
    (original : StructuralXorPredicate.Original event)
    (interval : @RuntimeInterval.Checked dependencies program block start count)
    (entry : RuntimeOwnerMap.Map) (combined : Semantics.SourceOwners.Owner) where
  basis : combined.basis = .pair :: event.input.basis ++ [.bit]
  frame : RuntimeOwnerMap.Checked (entry.map (·.owner)) interval.before
  sameFrame : frame.bindings = entry
  input : PortAt combined entry
  output : Semantics.Raw.Port
  steps : List Step
  literal : (block.operations.drop start).take count =
    [.pure (.applyUnitary input.port.token output.token steps)]
  outputRead : PureInterval.ports interval.after [output.token] = some [output]
  width : input.port.bits = original.width+1
  wires : output.wires = input.port.wires
  after : RuntimeOwnerMap.Checked (entry.map (·.owner)) interval.after
  sameAfter : after.bindings = entry.map (fun binding =>
    if binding.owner == combined then ⟨combined,output⟩ else binding)
  xorAction : StructuralXor.Checked original.width original.compiled.clauses steps

/-- Independently check the actual local circuit and preserve every live
owner. The enclosing scope must establish that the joined owner came from the
original data and auxiliary and bind the rest of compute–use–uncompute. -/
def read {sources caller dependencies program block start count}
    {event : SourceRuntimeContext.ComputedEvent sources caller}
    (original : StructuralXorPredicate.Original event)
    (interval : @RuntimeInterval.Checked dependencies program block start count)
    (entry : RuntimeOwnerMap.Map) (combined : Semantics.SourceOwners.Owner) :
    WorkM (Checked original interval entry combined) := do
  exactWork (Exact.charge (32*(block.operations.length + combined.basis.length + event.input.basis.length + 1)))
  if basis : combined.basis = .pair :: event.input.basis ++ [.bit] then
    let frame ← RuntimeOwnerMap.checkBindings (entry.map (·.owner)) interval.before entry
    let input ← readPort combined entry
    match literal : (block.operations.drop start).take count with
    | [.pure (.applyUnitary consumed returned steps)] =>
      match outputRead : PureInterval.ports interval.after [returned] with
      | some [output] =>
        if ports : consumed = input.port.token ∧ returned = output.token then
          if width : input.port.bits = original.width+1 then
            if wires : output.wires = input.port.wires then
              let xorAction ← StructuralXorPredicate.check original steps
              let updated := entry.map (fun binding => if binding.owner == combined then ⟨combined,output⟩ else binding)
              let after ← RuntimeOwnerMap.checkBindings (entry.map (·.owner)) interval.after updated
              return ⟨basis,frame.val,frame.property,input,output,steps,
                by simpa only [ports.1,ports.2] using literal,
                by simpa only [ports.2] using outputRead,
                width,wires,after.val,after.property,xorAction⟩
            else throw .request
          else throw .request
        else throw .request
      | _ => throw .request
    | _ => throw .request
  else throw .request

#print axioms read

end QleisliKernel.Qirf.StructuralXorInterval
