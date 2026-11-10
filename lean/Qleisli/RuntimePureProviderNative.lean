import Qleisli.PureNamedScopeView
import Qleisli.RawBranchFunction
import Qleisli.ExactMatrix
import QleisliKernel.Qirf.RuntimeProviderAction

/-! The real pure-body guard and matrix receipts provide independent native
shape, literal IR meaning, and exact transport through both carrier codes.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimePureProviderNative
open QleisliKernel QleisliKernel.Qirf QleisliKernel.Finite QleisliKernel.SourceTypes
open RuntimePureBody (BlockRunner BlockResult Context ExecutionMode OutputBoundary runBlockCore runBlockStep)
open Qleisli.RuntimePureNamedScope (PureBlock)
open Qleisli.Semantics.Exact (action)
open Qleisli.Semantics.ObservingFunction (BodyMeaning)

private theorem pure_guard_shape (artifact : Artifact) (root : Validity.Root)
    (execution : ExecutionMode artifact root) (next : BlockRunner artifact root execution)
    (boundary : OutputBoundary)
    {rootOwner rootName owner name : String}
    (source : SourceRuntimeScope.Subject artifact.sources owner name)
    (path : RuntimeOrdinaryBody.CallPath artifact.sources rootOwner rootName owner name)
    (program : Semantics.Observation.Program) (request : Context)
    (plan : execution.queries.BodyData source request)
    (history : RuntimeStructuralAction.SourceState) (ordinary : RuntimeOrdinaryBody.State)
    (block : RuntimeInterval.Block root.dependencies program)
    (result : BlockResult root.dependencies program block × List execution.Receipt)
    (checked : RuntimeInterval.Computed
      (runBlockStep artifact root execution next .pureBody boundary source path program request
        plan history ordinary block) result) :
    program.classicalInputs = [] ∧
      ∃ operations : List Semantics.Raw.Op, block.operations = operations.map Semantics.Observation.Op.pure := by
  obtain ⟨work,left,ran⟩ := checked
  simp (config := {zeta := false}) only [runBlockStep] at ran
  obtain ⟨_,afterSignature,_,rest⟩ := bind_success _ _ _ _ _ ran
  extract_lets -underBinder +onlyGivenNames afterMode at rest
  let singleton (value : SourceRuntimeValues.Value) :=
    (SourceRuntimeValues.ordinary value).all fun (basis,_) =>
      Semantics.FiniteCarrier.dimension basis == some 1
  let guardPure : WorkM Unit := do
    guard (source.effect == .unitary && singleton source.value &&
      source.parameterValues.all singleton &&
      program.classicalInputs.isEmpty && program.classicalOutputs.isEmpty) .request
    let _ ← lift (readOption (Sector.pureOps block.operations))
    pure ()
  have modeRead : (guardPure >>= afterMode).run afterSignature = (.ok result,left) := by
    simpa only [guardPure,bind_assoc] using rest
  obtain ⟨_,_,checkedMode,_⟩ := bind_success _ _ _ _ _ modeRead
  obtain ⟨_,_,checkedShape,parsed⟩ := bind_success _ _ _ _ _ checkedMode
  have shape := (guard_success _ _ _ _ checkedShape).1
  simp only [Bool.and_eq_true,List.isEmpty_iff] at shape
  obtain ⟨operations,_,read,_⟩ := bind_success _ _ _ _ _ parsed
  have found := (lift_success _ _ _ _ read).1
  have actual : Sector.pureOps block.operations = some operations := by
    cases literal : Sector.pureOps block.operations with
    | none => simp only [literal,readOption] at found; cases found
    | some values =>
      simp only [literal,readOption,Except.ok.injEq] at found
      exact congrArg some found
  exact ⟨shape.1.2,operations,Sector.pureOps_bound _ _ actual⟩

private theorem root_entry_empty {dependencies program}
    (prepared : RuntimeInterval.Prepared dependencies program) (empty : program.classicalInputs = []) :
    prepared.block.entry.classical = [] := by
  obtain ⟨work,left,checked⟩ := prepared.inputRead
  unfold PureInterval.initial at checked
  obtain ⟨quantum,_,_,returned⟩ := bind_success _ _ _ _ _ checked
  rw [empty] at returned
  change (pure ({quantum} : Raw.Observation.State) : WorkM Raw.Observation.State).run _ =
    (.ok prepared.entry,left) at returned
  change prepared.entry.classical = []
  rw [(pure_success _ _ _ _ returned).1]

/-- Pure mode supplies the literal instruction shape and empty ordinary
entry on the actual provider block, from its own successful preparation. -/
theorem checked_pure_shape {artifact root owner name signature program request bindings}
    {body : @SourceRuntimeTrace.Body artifact.sources owner name signature}
    (checked : @RuntimePureBody.Checked artifact root owner name signature body program request bindings) :
    PureBlock checked.result.prepared.block := by
  obtain ⟨native,result,work,left,read⟩ := checked
  unfold RuntimePureBody.run at read
  obtain ⟨walk,afterBlock,blockRead,returned⟩ := bind_success _ _ _ _ _ read
  have resultData := (pure_success _ _ _ _ returned).1
  subst result
  unfold RuntimePureBody.runBlock RuntimePureBody.runBlockUsing at blockRead
  obtain ⟨actual,afterCore,coreRead,blockReturned⟩ := bind_success _ _ _ _ _ blockRead
  let history : RuntimeStructuralAction.SourceState :=
    ⟨bindings,body.checked.summary.parameterValues.flatMap SourceRuntimeValues.valueOwners,
      body.checked.summary.nextOwner⟩
  have original : RuntimeInterval.Computed
      (runBlockStep artifact root (.fresh .strict) (runBlockCore artifact root (.fresh .strict) 127)
        .pureBody .rootOrder (.whole body) (.root body) program request () history {} native.block) actual :=
    ⟨work,afterCore,coreRead⟩
  obtain ⟨empty,literal⟩ := pure_guard_shape artifact root (.fresh .strict)
    (runBlockCore artifact root (.fresh .strict) 127)
    .rootOrder (.whole body) (.root body) program request () history {} native.block actual original
  exact ⟨root_entry_empty native empty,literal⟩

/-- The exact no-leak receipt intertwines physical and logical actions on
all joint input/reference coefficients, including rectangular port codes. -/
theorem code_action {effect inputCode outputCode physical}
    (equations : PureProviderSubject.Equations effect inputCode outputCode physical)
    {Reference : Type} (joint : Nat → Reference → ℂ) (row : Nat) (reference : Reference)
    (bounded : row < physical.rows) :
    action physical (fun i r => action inputCode joint i r) row reference =
      action outputCode (fun i r => action equations.action joint i r) row reference := by
  obtain ⟨before,after,actual⟩ := equations.actualRead
  obtain ⟨first,last,specified⟩ := equations.specifiedRead
  have left := Qleisli.Exact.compose_action physical inputCode equations.actual before after
    (exactWork_success _ _ _ _ actual) joint row reference bounded
  have right := Qleisli.Exact.compose_action outputCode equations.action equations.specified first last
    (exactWork_success _ _ _ _ specified) joint row reference (equations.physicalShape.2 ▸ bounded)
  exact left.symm.trans ((congrArg (fun matrix => action matrix joint row reference) equations.noLeak).trans right)

/-- Both equations refer to the original program and to the provider's own
logical matrix. The first binds the actual IR denotation; the second gives
the exact encoded action without discarding phase or reference columns. -/
theorem checked_native_action {artifact context description graph index request header root demand}
    (checked : @RuntimeProviderAction.Checked artifact context description graph index request header root demand) :
    let native := checked.paths.ir.original
    BodyMeaning root.dependencies native.program native.prepared.physical ∧
      ∀ {Reference : Type} (joint : Nat → Reference → ℂ) (row : Nat) (reference : Reference),
        row < native.prepared.physical.rows →
        action native.prepared.physical (fun i r => action native.prepared.inputCode joint i r) row reference =
          action native.prepared.outputCode (fun i r => action checked.action joint i r) row reference := by
  intro native
  obtain ⟨work,left,reconstructed⟩ := native.prepared.physicalRead
  exact ⟨Qleisli.Raw.BranchFunction.reconstruct_denotes root.dependencies native.program
      native.prepared.ports.noClassical.1 native.prepared.physical work left reconstructed,
    fun joint row reference bounded => code_action native.prepared.equations joint row reference bounded⟩

#print axioms checked_pure_shape
#print axioms checked_native_action
end Qleisli.RuntimePureProviderNative
