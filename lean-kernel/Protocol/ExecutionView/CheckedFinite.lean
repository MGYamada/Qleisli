import Protocol.ExecutionView.Frame
import Protocol.ExecutionView.Graph
import Protocol.Validity
import QleisliKernel.Raw.ObservationScope

/-! Pure finite execution-view gate. It reuses the actual QIRF checker once and
compares the same fresh result inside Lean. CLI/protocol integration is separate.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Protocol.ExecutionView.CheckedFinite

inductive Error where
  | packet | invalidView | native (error : Finite.Error) | encoding | decodedView
  deriving BEq, DecidableEq, Repr

abbrev CheckM := ExceptT Error (StateM Nat)

private def lift {α : Type} (result : Except Error α) : CheckM α :=
  match result with | .ok value => pure value | .error error => throw error

private def native {α : Type} (action : Finite.WorkM α) : CheckM α := fun work =>
  let (result,left) := action.run work
  (result.mapError Error.native,left)

private def guard (condition : Bool) (error : Error) : CheckM Unit :=
  if condition then pure () else throw error

structure Checked where
  body : ByteArray
  requestBytes : Option ByteArray
  artifact : Qirf.Artifact
  order : Array Nat
  requirement : Option Qirf.Validity.Request
  result : Qirf.Validity.Checked

/-- No stage result or success flag is accepted from the caller. The supplied
view is mandatory data, compared against the freshly checked original root. -/
def check (bytes supplied : ByteArray) : CheckM Checked := do
  guard (framed supplied) .invalidView
  let (body,requestBytes) ← lift ((Validity.packet bytes).mapError fun _ => .packet)
  let (artifact,order) ← native (Protocol.Qirf.read body)
  let requirement ← native (Validity.readRequest requestBytes)
  let result ← native (Qirf.Validity.check artifact order requirement)
  let description ← native (FiniteView.graph artifact result.root)
  let expected ← lift ((encode description).mapError fun _ => .encoding)
  guard (supplied.data == expected.data) .decodedView
  return ⟨body,requestBytes,artifact,order,requirement,result⟩

private theorem bind_run {α β : Type} (first : CheckM α) (next : α → CheckM β) (work : Nat) :
    (first >>= next).run work =
      match first.run work with
      | (.error error,left) => (.error error,left)
      | (.ok value,left) => (next value).run left := by
  simp only [ExceptT.run,bind,ExceptT.bind,ExceptT.mk,StateT.bind]
  cases first work with
  | mk result middle => cases result <;> rfl

private theorem bind_success {α β : Type} (first : CheckM α) (next : α → CheckM β)
    (work left : Nat) (value : β) (ok : (first >>= next).run work = (.ok value,left)) :
    ∃ intermediate middle, first.run work = (.ok intermediate,middle) ∧
      (next intermediate).run middle = (.ok value,left) := by
  rw [bind_run] at ok
  cases h : first.run work with
  | mk result middle =>
    rw [h] at ok
    cases result with
    | error error => cases ok
    | ok intermediate => exact ⟨intermediate,middle,rfl,ok⟩

private theorem native_success {α : Type} (action : Finite.WorkM α) (result : α)
    (work left : Nat) (ok : (native action).run work = (.ok result,left)) :
    action.run work = (.ok result,left) := by
  change ((action.run work).1.mapError Error.native,(action.run work).2) = (.ok result,left) at ok
  cases h : action.run work with
  | mk value middle =>
    rw [h] at ok
    cases value <;> simp_all [Except.mapError]

private theorem lift_success {α : Type} (input : Except Error α) (result : α)
    (work left : Nat) (ok : (lift input).run work = (.ok result,left)) :
    input = .ok result ∧ left = work := by
  cases input with
  | error error => cases ok
  | ok value => cases ok; exact ⟨rfl,rfl⟩

private theorem guard_success (condition : Bool) (error : Error) (work left : Nat)
    (ok : (guard condition error).run work = (.ok (),left)) :
    condition = true ∧ left = work := by
  unfold guard at ok
  cases condition with
  | false => cases ok
  | true => cases ok; exact ⟨rfl,rfl⟩

/-- Success retains the original bytes, each actual decoder/checker computation
and the exact bytes compared after the common check. View derivation has its
own remaining-work value; it does not pretend to preserve the core's budget. -/
structure Binding (bytes supplied : ByteArray) (checked : Checked) (work left : Nat) where
  afterArtifact : Nat
  afterRequest : Nat
  afterCore : Nat
  description : Value
  framedView : framed supplied = true
  packetBound : Validity.packet bytes = .ok (checked.body,checked.requestBytes)
  artifactBound : (Protocol.Qirf.read checked.body).run work =
    (.ok (checked.artifact,checked.order),afterArtifact)
  requestBound : (Validity.readRequest checked.requestBytes).run afterArtifact =
    (.ok checked.requirement,afterRequest)
  checkedBound : (Qirf.Validity.check checked.artifact checked.order checked.requirement).run afterRequest =
    (.ok checked.result,afterCore)
  viewBound : (FiniteView.graph checked.artifact checked.result.root).run afterCore =
    (.ok description,left)
  compared : encode description = .ok supplied

theorem check_binding (bytes supplied : ByteArray) (checked : Checked) (work left : Nat)
    (ok : (check bytes supplied).run work = (.ok checked,left)) :
    Nonempty (Binding bytes supplied checked work left) := by
  unfold check at ok
  obtain ⟨_,w₀,hf,h⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨input,a,hp,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨decoded,b,ha,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨requirement,c,hr,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨result,d,hc,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨description,e,hv,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨expected,f,he,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,g,hs,h⟩ := bind_success _ _ _ _ _ h
  have resultEq : checked = ⟨input.1,input.2,decoded.1,decoded.2,requirement,result⟩ ∧ left = g := by
    cases h
    exact ⟨rfl,rfl⟩
  rcases resultEq with ⟨rfl,rfl⟩
  have frame := guard_success _ _ _ _ hf
  have packet := lift_success _ _ _ _ hp
  have bound : Validity.packet bytes = .ok input := by
    cases h : Validity.packet bytes <;> simp_all [Except.mapError]
  have encoded := lift_success _ _ _ _ he
  have same := guard_success _ _ _ _ hs
  have equalData : supplied.data = expected.data := beq_iff_eq.mp same.1
  have equal : supplied = expected := by
    cases supplied
    cases expected
    cases equalData
    rfl
  have encoding : encode description = .ok supplied := by
    cases h : encode description <;> simp_all [Except.mapError]
  have start := frame.2
  have packetWork := packet.2
  have compareWork := same.2
  have encodingWork := encoded.2
  subst w₀
  subst a
  subst f
  subst e
  exact ⟨⟨b,c,d,description,frame.1,bound,
    native_success _ _ _ _ ha,native_success _ _ _ _ hr,
    native_success _ _ _ _ hc,native_success _ _ _ _ hv,encoding⟩⟩

/-- Checked transport to the original ordinary packet guarantee. The core
finishes before view derivation, and the original root identity is unchanged. -/
def Binding.original {bytes supplied : ByteArray} {checked : Checked} {work left : Nat}
    (binding : Binding bytes supplied checked work left) :
    Validity.Acceptance bytes checked.requirement.isSome work binding.afterCore where
  body := checked.body
  requestBytes := checked.requestBytes
  artifact := checked.artifact
  order := checked.order
  requirement := checked.requirement
  afterArtifact := binding.afterArtifact
  afterRequest := binding.afterRequest
  packetBound := binding.packetBound
  artifactBound := binding.artifactBound
  requestBound := binding.requestBound
  accepted := by
    simp only [Qirf.Validity.inspect,Finite.bind_run,binding.checkedBound]
    rfl
  requested := rfl

theorem check_ownershipSafe (bytes supplied : ByteArray) (checked : Checked) (work left : Nat)
    (ok : (check bytes supplied).run work = (.ok checked,left)) :
    ∃ _binding : Binding bytes supplied checked work left,
      checked.artifact.programs[checked.artifact.root]? = some checked.result.root.program ∧
      Semantics.Ownership.OwnershipSafe checked.result.root.program := by
  obtain ⟨binding⟩ := check_binding _ _ _ _ _ ok
  exact ⟨binding,Qirf.Validity.check_ownershipSafe _ _ _ _ _ _ binding.checkedBound⟩

theorem check_scopeSafe (bytes supplied : ByteArray) (checked : Checked) (work left : Nat)
    (ok : (check bytes supplied).run work = (.ok checked,left)) :
    ∃ _binding : Binding bytes supplied checked work left,
      checked.artifact.programs[checked.artifact.root]? = some checked.result.root.program ∧
      Semantics.ClassicalScope.ScopeSafe checked.result.root.program := by
  obtain ⟨binding⟩ := check_binding _ _ _ _ _ ok
  have facts := (Qirf.Validity.check_postcondition _ _ _ _ _ _ binding.checkedBound).root
  obtain ⟨a,b,verified⟩ := facts.verification
  exact ⟨binding,facts.original,Raw.Observation.verify_scopeSafe _ _ _ _ _ verified⟩

end QleisliKernel.Protocol.ExecutionView.CheckedFinite
