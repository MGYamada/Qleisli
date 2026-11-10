import Protocol.ExecutionView.QmatchV5
import Protocol.ExecutionView.Packet
import QleisliKernel.Qirf.RuntimeBodyOperations

/-! Check the complete original v5 body before comparing its execution view.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Protocol.ExecutionView.CheckedQmatchV5
open Gate
open QleisliKernel.Qirf QleisliKernel.SourceTypes

structure Original (bytes : ByteArray) where
  body : ByteArray
  requestBytes : ByteArray
  packet : Protocol.Validity.packet bytes = .ok (body,some requestBytes)
  artifact : Artifact
  order : Array Nat
  artifactRead : RuntimeInterval.Computed (Protocol.Qirf.readAll body) (artifact,order)
  request : Protocol.QmatchV5.Request
  requestRead : RuntimeInterval.Computed (Protocol.QmatchV5.readRequest requestBytes) request
  compatible : request.compatible = true
  prepared : RuntimeBodyOperations.Prepared artifact request.source.moduleName request.source.functionName
    request.source.arguments request.context
  preparedRead : RuntimeInterval.Computed (RuntimeBodyOperations.prepare artifact request.source.moduleName
    request.source.functionName request.source.arguments request.context) prepared
  checked : RuntimeBodyOperations.Checked prepared order request.combinedRuntime
  bodyRead : RuntimeInterval.Computed (RuntimeBodyOperations.read prepared order request.combinedRuntime) checked
  selection : 0 < checked.selections.count
  complete : checked.coverage.residual = []

def readOriginal (bytes : ByteArray) : Finite.WorkM (Original bytes) := do
  match packet : Protocol.Validity.packet bytes with
  | .error _ => throw .invalid
  | .ok (_,none) => throw .request
  | .ok (body,some requestBytes) =>
    let artifact ← NaturalAffine.witness (Protocol.Qirf.readAll body)
    let request ← NaturalAffine.witness (Protocol.QmatchV5.readRequest requestBytes)
    if compatible : request.val.compatible = true then
      let prepared ← NaturalAffine.witness (RuntimeBodyOperations.prepare artifact.val.1
        request.val.source.moduleName request.val.source.functionName request.val.source.arguments request.val.context)
      let checked ← NaturalAffine.witness (RuntimeBodyOperations.read prepared.val artifact.val.2 request.val.combinedRuntime)
      if selection : 0 < checked.val.selections.count then
        if complete : checked.val.coverage.residual = [] then
          return ⟨body,requestBytes,packet,artifact.val.1,artifact.val.2,
            by with_reducible exact artifact.property,
            request.val,by with_reducible exact request.property,compatible,
            prepared.val,by with_reducible exact prepared.property,
            checked.val,by with_reducible exact checked.property,selection,complete⟩
        else throw .request
      else throw .request
    else throw .request

def description {bytes : ByteArray} (original : Original bytes) : Finite.WorkM Value :=
  ExecutionView.QmatchV5.description original.artifact original.checked.root original.request

def check (bytes supplied : ByteArray) : CheckM (Original bytes) := do
  guard (framed supplied) .invalidView
  let checked ← native (readOriginal bytes)
  let view ← native (description checked)
  let expected ← lift ((encode view).mapError fun _ => .encoding)
  guard (supplied.data == expected.data) .decodedView
  return checked

structure Binding (bytes supplied : ByteArray) (checked : Original bytes) (work left : Nat) where
  afterCore : Nat
  view : Value
  framed : framed supplied = true
  core : (readOriginal bytes).run work = (.ok checked,afterCore)
  described : (description checked).run afterCore = (.ok view,left)
  compared : encode view = .ok supplied

theorem check_binding (bytes supplied : ByteArray) (checked : Original bytes) (work left : Nat)
    (ok : (check bytes supplied).run work = (.ok checked,left)) :
    Nonempty (Binding bytes supplied checked work left) := by
  unfold check at ok
  obtain ⟨_,a,hf,h⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨result,b,hc,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨view,c,hv,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨expected,d,he,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,e,hs,h⟩ := bind_success _ _ _ _ _ h
  have final : checked = result ∧ left = e := by cases h; exact ⟨rfl,rfl⟩
  rcases final with ⟨rfl,rfl⟩
  have frame := guard_success _ _ _ _ hf
  have encoded := lift_success _ _ _ _ he
  have same := guard_success _ _ _ _ hs
  have equalData : supplied.data = expected.data := beq_iff_eq.mp same.1
  have equal : supplied = expected := by cases supplied; cases expected; cases equalData; rfl
  have encoding : encode view = .ok supplied := by
    cases value : encode view <;> simp_all [Except.mapError]
  have start := frame.2
  have encodedWork := encoded.2
  have comparedWork := same.2
  subst a; subst d; subst c
  exact ⟨⟨b,view,frame.1,native_success _ _ _ _ hc,native_success _ _ _ _ hv,encoding⟩⟩

/-- Every pending position of the original source queue has its own
unambiguous discharge in the checked report. -/
theorem Original.covers {bytes : ByteArray} (original : Original bytes)
    (position : RuntimeArmDutyCoverage.Position original.prepared)
    (pending : original.prepared.source.pending.entries[position.val].unconsumed = true) :
    ∃ discharge : RuntimeArmDutyCoverage.Discharge original.checked.coverage.candidates position,
      ⟨position,discharge⟩ ∈ original.checked.coverage.consumed := by
  let coverage := original.checked.coverage
  have all : position ∈ List.finRange original.prepared.source.pending.entries.length := List.mem_finRange _
  have covered : RuntimeArmDutyCoverage.covered coverage.candidates position = true := by
    cases found : RuntimeArmDutyCoverage.covered coverage.candidates position with
    | true => rfl
    | false =>
      have residual : position ∈ coverage.residual := by
        change position ∈ coverage.result.residual
        rw [coverage.result.exactResidual]
        exact List.mem_filter.mpr ⟨all,by simp [RuntimeArmDutyCoverage.remaining,pending,found]⟩
      have empty : coverage.residual = [] := original.complete
      rw [empty] at residual
      exact False.elim (List.not_mem_nil residual)
  have mapped : position ∈ coverage.result.consumed.map (·.1) := by
    rw [coverage.result.exactConsumed]
    exact List.mem_filter.mpr ⟨all,by simp [pending,covered]⟩
  obtain ⟨⟨index,witness⟩,present,same⟩ := List.mem_map.mp mapped
  change index = position at same
  subst index
  exact ⟨witness,present⟩

theorem Original.root_safe {bytes : ByteArray} (original : Original bytes) :
    original.artifact.programs[original.artifact.root]? = some original.checked.root.program ∧
      Semantics.Ownership.OwnershipSafe original.checked.root.program ∧
      Semantics.ClassicalScope.ScopeSafe original.checked.root.program := by
  obtain ⟨_,_,read⟩ := original.checked.fresh
  have root := QleisliKernel.Qirf.Validity.checkRootFromRoots_postcondition _ _ _ _ _ _ _ read
  obtain ⟨_,_,verified⟩ := root.verification
  exact ⟨root.original,Raw.Observation.verify_ownershipSafe _ _ _ _ _ verified,
    Raw.Observation.verify_scopeSafe _ _ _ _ _ verified⟩

def input (value : Packet.Input) : CheckM (Original value.original) :=
  match value.scope with
  | .execution => check value.original value.graph
  | .inspection | .caller => throw .packet

def run (bytes : ByteArray) : CheckM (Σ value : Packet.Input, Original value.original) := do
  let value ← lift (Packet.read bytes)
  return ⟨value,← input value⟩

theorem run_binding (bytes : ByteArray) (checked : Σ value : Packet.Input, Original value.original)
    (work left : Nat) (ok : (run bytes).run work = (.ok checked,left)) :
    Packet.read bytes = .ok checked.1 ∧ checked.1.scope = .execution ∧
      Nonempty (Binding checked.1.original checked.1.graph checked.2 work left) := by
  unfold run at ok
  obtain ⟨value,middle,packet,rest⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨original,budget,consumed,returned⟩ := bind_success _ _ _ _ _ rest
  have parsed := lift_success _ _ _ _ packet
  have start := parsed.2
  subst middle
  have final : checked = ⟨value,original⟩ ∧ left = budget := by cases returned; exact ⟨rfl,rfl⟩
  rcases final with ⟨rfl,rfl⟩
  cases scope : value.scope with
  | inspection => simp only [input,scope] at consumed; cases consumed
  | caller => simp only [input,scope] at consumed; cases consumed
  | execution =>
    simp only [input,scope] at consumed
    exact ⟨parsed.1,rfl,check_binding _ _ _ _ _ consumed⟩

#print axioms check_binding
#print axioms Original.covers
#print axioms Original.root_safe
#print axioms run_binding
end QleisliKernel.Protocol.ExecutionView.CheckedQmatchV5
