import Qleisli.RuntimeNamedOutputEncoding

/-! Actual caller output geometry for a retained original primitive call.
Full source owners, nominal bases, ordered wires, zero-width owners and all
spectators follow the original boundary and the same parent native events.
These laws do not grant an accepted handle or compose whole source actions.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeNamedCallerGeometry
open QleisliKernel QleisliKernel.Qirf QleisliKernel.Finite
open RuntimeOwnerMap (Binding Map)
open RuntimeForestCode

private theorem bindings_unique {roles state} (checked : RuntimeOwnerMap.Checked roles state) :
    checked.bindings.Nodup :=
  List.Pairwise.of_map (fun binding : Binding => binding.port.token)
    (fun _ _ different same => different (congrArg (fun binding : Binding => binding.port.token) same))
    checked.tokensDistinct

/-- Logical identity removes exactly the actual binding, even at zero width. -/
theorem owner_complement {roles state} (checked : RuntimeOwnerMap.Checked roles state)
    (target : Binding) (member : target ∈ checked.bindings) :
    checked.bindings.filter (fun binding => !([target.owner]).contains binding.owner) =
      checked.bindings.erase target := by
  rw [List.Nodup.erase_eq_filter (bindings_unique checked) target]
  have ordinals : (checked.bindings.map (fun binding => binding.owner.ordinal)).Nodup := by
    simpa only [← checked.ordered,List.map_map,Function.comp_def] using checked.ownersDistinct
  apply List.filter_congr
  intro binding present
  by_cases same : binding = target
  · subst binding
    simp
  · have different : binding.owner ≠ target.owner := by
      intro equal
      exact same (RuntimeOwnerTransitionAction.map_unique (fun b : Binding => b.owner.ordinal) _ ordinals
        binding present target member (congrArg (·.ordinal) equal))
    simp [different,same]

theorem erase_appended (others : Map) (target : Binding) (unique : (others++[target]).Nodup) :
    (others++[target]).erase target = others := by
  have disjoint := (List.nodup_append.mp unique).2.2
  have missing : target ∉ others := by
    intro present
    exact disjoint target present target List.mem_cons_self rfl
  rw [List.erase_append_right [target] missing]
  simp

/-- Completeness and distinct actual tokens identify the whole native port. -/
theorem full_port_unique {roles state} (checked : RuntimeOwnerMap.Checked roles state)
    (first second : Semantics.Raw.Port) (left : first ∈ state.quantum.live)
    (right : second ∈ state.quantum.live) (tokens : first.token = second.token) : first = second := by
  have unique : (state.quantum.live.map (·.token)).Nodup := by
    apply (checked.complete.map (·.token)).nodup_iff.mp
    simpa only [List.map_map,Function.comp_def] using checked.tokensDistinct
  exact RuntimeOwnerTransitionAction.map_unique (fun port : Semantics.Raw.Port => port.token) _ unique
    first left second right tokens

def Geometry {dependencies program block step}
    (held : @RuntimeNamedPrimitiveOccurrence.Occurrence dependencies program block step) : Prop :=
  match held with
  | .named (before := before) (scope := scope) (boundary := boundary) _ bound =>
    ∀ {roles} (input : RuntimeOwnerMap.Checked roles scope.interval.before),
      input.bindings = before.bindings →
      ∃ returned : Binding, boundary.mapped = [returned] ∧
        returned.owner.basis = bound.binding.owner.basis ∧
        returned.port.wires = bound.binding.port.wires ∧
        scope.interval.after.quantum.frame = scope.interval.before.quantum.frame ∧
        boundary.afterFrame.bindings.erase returned = input.bindings.erase bound.binding

/-- The actual original child and the same parent event interpretation supply
its precise output carrier, unchanged caller frame and complete spectator map.
No width equality, supplied code equation or separability premise is used. -/
theorem actual_geometry {artifact root execution fuel program block step}
    (held : @RuntimeNamedPrimitiveOccurrence.Occurrence root.dependencies program block step)
    (call : RuntimeNamedChildRuns.ChildRun artifact root execution
      (RuntimePureBody.runBlockCore artifact root execution (fuel+1)) step)
    (events : List Semantics.Raw.Event) (on : RuntimeNamedOccurrenceAction.On held events) : Geometry held := by
  have inputs := RuntimeNamedPrimitiveInputs.actual_occurrence_input held call
  have outputs := RuntimeNamedPrimitiveOutputs.actual_occurrence_output held call
  have codes := RuntimeNamedPrimitiveOutputs.actual_occurrence_output_code held call
  cases held with
  | @named start count tokens sources caller before childHistory childRetired ordinary first size inputToken output role kind
      event scope body read boundary finalOrdinary primitive original bound =>
    intro roles input same
    obtain ⟨returned,mapped,member,_nativeRead⟩ := codes
    obtain ⟨_childEvents,facts,_meaning,_law⟩ := on
    have inputCarrier : ([⟨bound.binding.port,role.basis⟩] : List Semantics.CarrierInterface.Owner) =
        [⟨bound.binding.port,bound.binding.owner.basis⟩] := by
      simpa only [RuntimeNamedPrimitiveInputs.OccurrenceInput,bound.entry,bound.singleton,carrierOwners,List.map_singleton] using inputs
    have roleBasis := congrArg Semantics.CarrierInterface.Owner.basis (List.cons.inj inputCarrier).1
    have outputCarrier : ([⟨returned.port,returned.owner.basis⟩] : List Semantics.CarrierInterface.Owner) =
        [⟨original.outputPort.port,role.basis⟩] := by
      calc
        _ = carrierOwners boundary.mapped := by rw [mapped]; rfl
        _ = primitive.interval.returned.map (fun port => (⟨port,role.basis⟩ : Semantics.CarrierInterface.Owner)) := outputs
        _ = _ := by rw [RuntimeNamedPrimitiveOutputs.primitive_output_port original]; rfl
    have portSame := congrArg Semantics.CarrierInterface.Owner.port (List.cons.inj outputCarrier).1
    have typeSame := (congrArg Semantics.CarrierInterface.Owner.basis (List.cons.inj outputCarrier).1).trans roleBasis
    have outputToken := (congrArg Semantics.Raw.Port.token portSame).trans original.outputToken
    have frameSame := congrArg Semantics.RawTrace.Interface.frame facts.parentInterface
    change scope.interval.after.quantum.frame = scope.interval.before.quantum.frame at frameSame
    let nativePort : Semantics.Raw.Port := ⟨output,bound.binding.port.wires,bound.binding.port.wires.length⟩
    have interface := congrArg Semantics.RawTrace.Interface.live facts.parentInterface
    change scope.interval.after.quantum.live =
      scope.interval.before.quantum.live.filter (fun port => port.token != bound.binding.port.token) ++ [nativePort] at interface
    have nativeMember : nativePort ∈ scope.interval.after.quantum.live := by
      rw [interface]
      exact List.mem_append_right _ List.mem_cons_self
    have returnedMember : returned.port ∈ scope.interval.after.quantum.live :=
      boundary.afterFrame.complete.mem_iff.mp (List.mem_map.mpr ⟨returned,member,rfl⟩)
    have actualPort : returned.port = nativePort := full_port_unique boundary.afterFrame _ _ returnedMember nativeMember outputToken
    have wiresSame := congrArg Semantics.Raw.Port.wires actualPort
    have selected := RuntimeSelectionPartition.order_values _ _ _ boundary.input.orderRead
    have inputMember : bound.binding ∈ input.bindings := by
      rw [same]
      exact selected.1 ((congrArg (fun bs => bound.binding ∈ bs) bound.singleton).mpr (List.mem_singleton_self _))
    have inputOwners : event.inputOwners = [bound.binding.owner] := by
      exact selected.2.symm.trans (by
        simpa only [List.map_singleton] using congrArg (List.map RuntimeOwnerMap.Binding.owner) bound.singleton)
    have complement : before.bindings.filter (fun binding => !event.inputOwners.contains binding.owner) =
        input.bindings.erase bound.binding := by
      rw [← same,inputOwners]
      exact owner_complement input bound.binding inputMember
    have after : boundary.afterFrame.bindings = input.bindings.erase bound.binding ++ [returned] := by
      calc
        _ = boundary.after.bindings := boundary.sameAfter
        _ = _ := boundary.afterBindings
        _ = _ := by rw [complement,mapped]
    have afterUnique := bindings_unique boundary.afterFrame
    rw [after] at afterUnique
    refine ⟨returned,mapped,typeSame,wiresSame,frameSame,?_⟩
    rw [after]
    exact erase_appended _ _ afterUnique

#print axioms actual_geometry

/-- The same complete source bindings have the same retained logical layouts,
regardless of the successful native-reader budgets or receipt objects. -/
theorem codes_same {leftBindings rightBindings : Map} (same : leftBindings = rightBindings)
    (left : OwnerCodes leftBindings) (right : OwnerCodes rightBindings)
    (leftFrame rightFrame : List Nat) (frames : rightFrame = leftFrame) :
    (RuntimeForestOrderedProduct.sparseProduct left).dimension =
        (RuntimeForestOrderedProduct.sparseProduct right).dimension ∧
      ∀ physical logical,
        RuntimeForestOrderedProduct.coefficients leftFrame left physical logical =
          RuntimeForestOrderedProduct.coefficients rightFrame right physical logical := by
  subst rightBindings
  subst rightFrame
  induction left with
  | nil => cases right; exact ⟨rfl,by intro physical logical; rfl⟩
  | cons first rest ih =>
    cases right with
    | cons other tail =>
      obtain ⟨sizes,coefficients⟩ := ih tail
      have layout := RuntimeOwnerCodeReindex.layout_unique first other
      refine ⟨?_,?_⟩
      · change first.layout.labels.length * (RuntimeForestOrderedProduct.sparseProduct rest).dimension =
          other.layout.labels.length * (RuntimeForestOrderedProduct.sparseProduct tail).dimension
        rw [layout,sizes]
      · intro physical logical
        change Qleisli.Semantics.Exact.entry (Semantics.FiniteCarrier.encoding first.layout)
            (Semantics.Finite.gather physical _) (logical%first.layout.labels.length) *
            RuntimeForestOrderedProduct.coefficients leftFrame rest physical (logical/first.layout.labels.length) =
          Qleisli.Semantics.Exact.entry (Semantics.FiniteCarrier.encoding other.layout)
            (Semantics.Finite.gather physical _) (logical%other.layout.labels.length) *
            RuntimeForestOrderedProduct.coefficients leftFrame tail physical (logical/other.layout.labels.length)
        rw [layout,coefficients]

/-- Full source basis equality identifies the retained layout; wire geometry
is a separate original-source fact, never inferred from a matrix dimension. -/
theorem layouts_same {input output : Binding} (left : OwnerCode input) (right : OwnerCode output)
    (basis : output.owner.basis = input.owner.basis) : right.layout = left.layout := by
  have original := right.reference.1
  rw [basis] at original
  exact Option.some.inj (original.symm.trans left.reference.1)

#print axioms codes_same
#print axioms layouts_same

end Qleisli.RuntimeNamedCallerGeometry
