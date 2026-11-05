import Qleisli.RuntimeNamedPrimitiveOutputs
import Qleisli.RuntimeNamedInputAction

/-! Factor the complete actual caller output encoding through its native
primitive code while retaining arbitrary correlated spectators/references.
Actual output-coefficient transport remains a separate obligation.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeNamedOutputEncoding
open QleisliKernel QleisliKernel.Qirf QleisliKernel.Finite

/-- The complete authentic caller output encoding factors through this same
native output code and every spectator/reference coefficient. This is a code
identity, not yet a whole-function output-coefficient transformation theorem. -/
theorem complete_output_encoding {Reference : Type}
    {dependencies program block start count inputs ordinary effect sources caller before child retired value}
    {event : SourceTypes.SourceRuntimeContext.NamedEvent sources caller}
    (scope : @RuntimeCallScope.Checked dependencies program block start count inputs ordinary effect)
    (boundary : RuntimeNamedBoundary.Checked scope.interval inputs event before child retired value)
    (target : RuntimeOwnerMap.Binding) (member : target ∈ boundary.afterFrame.bindings)
    (frame : RuntimeForestCode.Frame boundary.afterFrame)
    (actual : RuntimeForestCode.OwnerCode target) (native : Semantics.Exact.Matrix)
    (read : RuntimeInterval.Computed (Carrier.ownerCode [⟨target.port,target.owner.basis⟩]) native)
    (joint : Nat → Reference → Complex) (physical : Nat) (reference : Reference) :
    RuntimeForestProduct.referenceAction frame joint physical reference =
      RuntimeNamedPrimitiveSourceLift.encodedParent
        (target.port.wires.map scope.interval.after.quantum.frame.idxOf) native
        (fun digit environment ref => RuntimeFiniteTargetFibre.targetFibre frame target environment joint digit ref)
        physical reference := by
  obtain ⟨work,left,checked⟩ := scope.interval.intervalRead
  have valid := (Raw.Observation.checkOps_invariants _ _ _ _ _ work left checked).1
  rw [RuntimeNamedInputAction.singleton_encoding actual native read]
  exact RuntimeNamedInputAction.complete_encoding frame valid target member actual joint physical reference

/-- The complete frame belongs to the original call's actual output state.
The target and native code are derived from its retained child, not supplied
as encoding equations by the caller of this proposition. -/
def OccurrenceEncoding {Reference : Type} {dependencies program block step}
    (held : @RuntimeNamedPrimitiveOccurrence.Occurrence dependencies program block step) : Prop :=
  match held with
  | .named (scope := scope) (boundary := boundary) (action := action) _ _ =>
    ∀ frame : RuntimeForestCode.Frame boundary.afterFrame,
      ∃ target : RuntimeOwnerMap.Binding, boundary.mapped = [target] ∧
        ∀ (joint : Nat → Reference → Complex) physical reference,
          RuntimeForestProduct.referenceAction frame joint physical reference =
            RuntimeNamedPrimitiveSourceLift.encodedParent
              (target.port.wires.map scope.interval.after.quantum.frame.idxOf) action.outputCode
              (fun digit environment ref =>
                RuntimeFiniteTargetFibre.targetFibre frame target environment joint digit ref)
              physical reference

theorem actual_occurrence_encoding {Reference : Type}
    {artifact root execution fuel program block step}
    (held : @RuntimeNamedPrimitiveOccurrence.Occurrence root.dependencies program block step)
    (call : RuntimeNamedChildRuns.ChildRun artifact root execution
      (RuntimePureBody.runBlockCore artifact root execution (fuel+1)) step) :
    OccurrenceEncoding (Reference := Reference) held := by
  have codes := RuntimeNamedPrimitiveOutputs.actual_occurrence_output_code held call
  cases held with
  | @named start count inputs sources caller before childHistory childRetired ordinary first size inputToken outputToken role kind
      event scope body read boundary finalOrdinary action original bound =>
    intro frame
    obtain ⟨target,same,member,nativeRead⟩ := codes
    obtain ⟨actual,_lookup⟩ := RuntimeOwnerCodeReindex.lookup_exists frame.owners target member
    refine ⟨target,same,?_⟩
    intro joint physical reference
    exact complete_output_encoding scope boundary target member frame actual action.outputCode
      nativeRead joint physical reference

/-- The actual original pre/post computations supply both output-encoding
laws. The transformed logical coefficients still need their separate join. -/
theorem original_pre_post_output_encodings {Reference : Type}
    {artifact owner name arguments request prepared order runtime}
    (body : @RuntimeBodyOperations.Checked artifact owner name arguments request prepared order runtime)
    (view : RuntimeNamedThreeOccurrence.Three body.checked.result.steps) :
    OccurrenceEncoding (Reference := Reference) view.prePrimitive ∧
      OccurrenceEncoding (Reference := Reference) view.postPrimitive := by
  obtain ⟨pre,_center,post⟩ := RuntimeNamedSourceFlow.original_child_runs body view
  exact ⟨actual_occurrence_encoding view.prePrimitive pre,actual_occurrence_encoding view.postPrimitive post⟩

#print axioms complete_output_encoding
#print axioms original_pre_post_output_encodings
end Qleisli.RuntimeNamedOutputEncoding
