import QleisliKernel.Qirf.RuntimeNamedBoundary
import QleisliKernel.Qirf.RuntimeForestCode
import QleisliKernel.Qirf.RuntimePureBody

/-! Preserve the exact child return encoding through the original named-call
owner transport. Owner identities remain distinct; the checked original map
preserves each complete basis and port, so its sparse code and caller-coordinate
axes agree. No bounded code-reader availability or source action is assumed.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeNamedCodeTransport
open QleisliKernel QleisliKernel.Qirf QleisliKernel.SourceTypes
open RuntimeOwnerMap (Binding Map)
open RuntimeForestCode (carrierOwners forestBasis forestAxes sparseLayout embed)

private theorem mapped_basis {actuals original actual}
    (read : SourceRuntimeValues.mappedOwner actuals original = .ok actual) :
    actual.basis = original.basis := by
  cases found : actuals[original.ordinal]? with
  | none => simp [SourceRuntimeValues.mappedOwner,found] at read
  | some selected =>
    by_cases same : selected.basis = original.basis
    · have returned : selected = actual := by
        simpa [SourceRuntimeValues.mappedOwner,found,same,pure,Except.pure,bind,Except.bind] using read
      rw [← returned]
      exact same
    · simp [SourceRuntimeValues.mappedOwner,found,same,bind,Except.bind] at read

private def mappedBinding (actuals : List Semantics.SourceOwners.Owner) (binding : Binding) :
    Except String Binding := do
  let owner ← SourceRuntimeValues.mappedOwner actuals binding.owner
  pure ⟨owner,binding.port⟩

private theorem mappedBinding_carrier {actuals binding returned}
    (read : mappedBinding actuals binding = .ok returned) :
    (⟨returned.port,returned.owner.basis⟩ : Semantics.CarrierInterface.Owner) =
      ⟨binding.port,binding.owner.basis⟩ := by
  unfold mappedBinding at read
  cases ownerRead : SourceRuntimeValues.mappedOwner actuals binding.owner with
  | error error =>
    simp only [ownerRead,bind,Except.bind] at read
    cases read
  | ok owner =>
    have same : returned = (⟨owner,binding.port⟩ : Binding) := by
      simpa only [ownerRead,bind,Except.bind,pure,Except.pure,Except.ok.injEq] using read.symm
    rw [same]
    exact congrArg (fun basis => (⟨binding.port,basis⟩ : Semantics.CarrierInterface.Owner)) (mapped_basis ownerRead)

private theorem mapped_carriers (actuals : List Semantics.SourceOwners.Owner) (bindings : Map) :
    ∀ mapped, bindings.mapM (mappedBinding actuals) = .ok mapped →
      carrierOwners mapped = carrierOwners bindings := by
  induction bindings with
  | nil =>
    intro mapped read
    have same : mapped = [] := (Except.ok.inj read).symm
    subst mapped
    rfl
  | cons binding rest ih =>
    intro mapped read
    cases head : mappedBinding actuals binding with
    | error error =>
      simp only [List.mapM_cons,head,bind,Except.bind] at read
      cases read
    | ok returned =>
      cases tail : rest.mapM (mappedBinding actuals) with
      | error error =>
        simp only [List.mapM_cons,head,bind,Except.bind,tail] at read
        cases read
      | ok remaining =>
        have same : mapped = returned :: remaining := by
          simpa only [List.mapM_cons,head,bind,Except.bind,pure,Except.pure,tail,Except.ok.injEq] using read.symm
        subst mapped
        have carrier := mappedBinding_carrier head
        simpa only [carrierOwners,List.map_cons,carrier] using
          congrArg (List.cons (⟨binding.port,binding.owner.basis⟩ : Semantics.CarrierInterface.Owner))
            (ih remaining tail)

section
variable {dependencies program sources caller block start count interval inputs event before child retired value}
    (boundary : @RuntimeNamedBoundary.Checked dependencies program sources caller block start count interval
      inputs event before child retired value)

/-- These are the actual returned child bindings and the actual original
caller mapping, including complete nominal basis trees and zero-width ports. -/
theorem returned_carriers : carrierOwners boundary.mapped = carrierOwners child.bindings :=
  mapped_carriers event.ownerMap child.bindings boundary.mapped boundary.mappedRead

theorem returned_basis : forestBasis boundary.mapped = forestBasis child.bindings :=
  congrArg Semantics.CarrierInterface.forest (returned_carriers boundary)

theorem returned_ports : boundary.mapped.map (·.port) = child.bindings.map (·.port) := by
  have ports := congrArg (List.map Semantics.CarrierInterface.Owner.port) (returned_carriers boundary)
  simpa only [carrierOwners,List.map_map,Function.comp_def] using ports

/-- Project both copies into the SAME actual caller frame. Wire identifiers
need not equal frame indices; no physical-width shortcut fixes the axes. -/
theorem returned_axes (callerFrame : List Nat) :
    forestAxes callerFrame boundary.mapped = forestAxes callerFrame child.bindings := by
  have wires := congrArg (List.flatMap Semantics.Raw.Port.wires) (returned_ports boundary)
  simpa only [forestAxes,List.flatMap_map,Function.comp_def] using
    congrArg (List.map callerFrame.idxOf) wires

/-- The original child forest determines the same sparse code after mapping.
This is an equality of the independent sparse interpreter, not a claimed new
bounded invocation or a supplied equality of two unrelated code matrices. -/
theorem returned_sparse :
    sparseLayout (forestBasis boundary.mapped) = sparseLayout (forestBasis child.bindings) :=
  congrArg sparseLayout (returned_basis boundary)

theorem returned_embedding (callerFrame : List Nat) (code : RuntimeForestCode.Sparse)
    (physical logical : Nat) :
    embed callerFrame boundary.mapped code physical logical =
      embed callerFrame child.bindings code physical logical := by
  unfold embed
  rw [returned_axes boundary]
end

/-- Only actual named steps carry a child return. Their retained original
boundary determines its complete carrier, sparse interpreter and caller axes.
Other step kinds acquire no source-action or code-preservation assertion. -/
def StepReturnCodes {dependencies program block}
    (step : @RuntimePureBody.Step dependencies program block) : Prop :=
  match step with
  | .named (childHistory := child) _ _ _ _ boundary _ _ =>
    carrierOwners boundary.mapped = carrierOwners child.bindings ∧
    sparseLayout (forestBasis boundary.mapped) = sparseLayout (forestBasis child.bindings) ∧
    ∀ callerFrame, forestAxes callerFrame boundary.mapped = forestAxes callerFrame child.bindings
  | .pure .. | .gap .. | .observation .. | .conditional .. => True

theorem step_return_codes {dependencies program block}
    (step : @RuntimePureBody.Step dependencies program block) : StepReturnCodes step :=
  match step with
  | .named _ _ _ _ boundary _ _ =>
    ⟨returned_carriers boundary,returned_sparse boundary,returned_axes boundary⟩
  | .pure .. | .gap .. | .observation .. | .conditional .. => True.intro

#print axioms returned_carriers
#print axioms returned_axes
#print axioms returned_sparse
#print axioms returned_embedding
#print axioms step_return_codes
end Qleisli.RuntimeNamedCodeTransport
