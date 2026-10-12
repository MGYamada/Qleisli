import Protocol.ExecutionView.Caller
import Protocol.ExecutionView.CheckedFinite
import Protocol.ExecutionView.CheckedContract

/-! Attach caller-origin comparison to the same finite/native-contract result.
These pure staging gates issue no handle; production protocol cutover is pending.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Protocol.ExecutionView.CheckedCaller
open Gate

private def compare (artifact : Qirf.Artifact) (root : Qirf.Validity.Root)
    (limit : Nat) (supplied : ByteArray) (indices : List Nat) : CheckM Unit := do
  guard (framed supplied) .invalidView
  let description ← native (Caller.origin artifact root indices limit)
  let expected ← lift ((encode description).mapError fun _ => .encoding)
  guard (supplied.data == expected.data) .decodedView

structure Comparison (artifact : Qirf.Artifact) (root : Qirf.Validity.Root)
    (limit : Nat) (supplied : ByteArray) (indices : List Nat) (work left : Nat) where
  description : Value
  framedView : framed supplied = true
  viewBound : (Caller.origin artifact root indices limit).run work = (.ok description,left)
  compared : encode description = .ok supplied

private theorem compare_binding (artifact : Qirf.Artifact) (root : Qirf.Validity.Root)
    (limit : Nat) (supplied : ByteArray) (indices : List Nat) (work left : Nat)
    (ok : (compare artifact root limit supplied indices).run work = (.ok (),left)) :
    Nonempty (Comparison artifact root limit supplied indices work left) := by
  unfold compare at ok
  obtain ⟨_,a,hf,h⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨description,b,hv,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨expected,c,he,hs⟩ := bind_success _ _ _ _ _ h
  have frame := guard_success _ _ _ _ hf
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
  have encodedWork := encoded.2
  have comparedWork := same.2
  subst a
  subst c
  subst b
  exact ⟨⟨description,frame.1,native_success _ _ _ _ hv,encoding⟩⟩

private def attach {α : Type} (base : CheckM α) (artifact : α → Qirf.Artifact)
    (root : α → Qirf.Validity.Root) (graph supplied : ByteArray) (indices : List Nat) : CheckM α := do
  guard (graph.size + supplied.size ≤ maxBytes) .invalidView
  let checked ← base
  compare (artifact checked) (root checked) (maxBytes-graph.size) supplied indices
  return checked

structure Binding {α : Type} (base : CheckM α) (artifact : α → Qirf.Artifact)
    (root : α → Qirf.Validity.Root) (graph supplied : ByteArray) (indices : List Nat)
    (checked : α) (work left : Nat) where
  afterBase : Nat
  sizedView : decide (graph.size + supplied.size ≤ maxBytes) = true
  baseBound : base.run work = (.ok checked,afterBase)
  comparison : Comparison (artifact checked) (root checked) (maxBytes-graph.size)
    supplied indices afterBase left

private theorem attach_binding {α : Type} (base : CheckM α) (artifact : α → Qirf.Artifact)
    (root : α → Qirf.Validity.Root) (graph supplied : ByteArray) (indices : List Nat)
    (checked : α) (work left : Nat)
    (ok : (attach base artifact root graph supplied indices).run work = (.ok checked,left)) :
    Nonempty (Binding base artifact root graph supplied indices checked work left) := by
  unfold attach at ok
  obtain ⟨_,a,hs,h⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨result,b,hb,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,c,hc,h⟩ := bind_success _ _ _ _ _ h
  have final : checked = result ∧ left = c := by cases h; exact ⟨rfl,rfl⟩
  rcases final with ⟨rfl,rfl⟩
  have sized := guard_success _ _ _ _ hs
  have sameWork := sized.2
  subst a
  obtain ⟨comparison⟩ := compare_binding _ _ _ _ _ _ _ hc
  exact ⟨⟨b,sized.1,hb,comparison⟩⟩

def finite (bytes graph supplied : ByteArray) (indices : List Nat) : CheckM CheckedFinite.Checked :=
  attach (CheckedFinite.check bytes graph) (·.artifact) (·.result.root) graph supplied indices

def contract (bytes graph supplied : ByteArray) (indices : List Nat) : CheckM NativeContract.Retained :=
  attach (CheckedContract.check bytes graph) (·.artifact)
    (fun checked => FiniteView.nativeRoot checked.request) graph supplied indices

abbrev FiniteBinding (bytes graph supplied : ByteArray) (indices : List Nat)
    (checked : CheckedFinite.Checked) (work left : Nat) :=
  Binding (CheckedFinite.check bytes graph) (·.artifact) (·.result.root)
    graph supplied indices checked work left

abbrev ContractBinding (bytes graph supplied : ByteArray) (indices : List Nat)
    (checked : NativeContract.Retained) (work left : Nat) :=
  Binding (CheckedContract.check bytes graph) (·.artifact)
    (fun checked => FiniteView.nativeRoot checked.request) graph supplied indices checked work left

theorem finite_binding (bytes graph supplied : ByteArray) (indices : List Nat)
    (checked : CheckedFinite.Checked) (work left : Nat)
    (ok : (finite bytes graph supplied indices).run work = (.ok checked,left)) :
    Nonempty (FiniteBinding bytes graph supplied indices checked work left) :=
  attach_binding _ _ _ _ _ _ _ _ _ ok

theorem contract_binding (bytes graph supplied : ByteArray) (indices : List Nat)
    (checked : NativeContract.Retained) (work left : Nat)
    (ok : (contract bytes graph supplied indices).run work = (.ok checked,left)) :
    Nonempty (ContractBinding bytes graph supplied indices checked work left) :=
  attach_binding _ _ _ _ _ _ _ _ _ ok

theorem FiniteBinding.original {bytes graph supplied : ByteArray} {indices : List Nat}
    {checked : CheckedFinite.Checked} {work left : Nat}
    (binding : FiniteBinding bytes graph supplied indices checked work left) :
    ∃ original : CheckedFinite.Binding bytes graph checked work binding.afterBase,
      Nonempty (Validity.Acceptance bytes checked.requirement.isSome work original.afterCore) := by
  obtain ⟨original⟩ := CheckedFinite.check_binding _ _ _ _ _ binding.baseBound
  exact ⟨original,⟨original.original⟩⟩

theorem ContractBinding.original {bytes graph supplied : ByteArray} {indices : List Nat}
    {checked : NativeContract.Retained} {work left : Nat}
    (binding : ContractBinding bytes graph supplied indices checked work left) :
    ∃ original : CheckedContract.Binding bytes graph checked work binding.afterBase,
      Nonempty (NativeContract.RetainedBinding bytes checked work original.afterCore) := by
  obtain ⟨original⟩ := CheckedContract.check_binding _ _ _ _ _ binding.baseBound
  exact ⟨original,original.original⟩

theorem finite_ownershipSafe (bytes graph supplied : ByteArray) (indices : List Nat)
    (checked : CheckedFinite.Checked) (work left : Nat)
    (ok : (finite bytes graph supplied indices).run work = (.ok checked,left)) :
    ∃ _binding : FiniteBinding bytes graph supplied indices checked work left,
      checked.artifact.programs[checked.artifact.root]? = some checked.result.root.program ∧
      Semantics.Ownership.OwnershipSafe checked.result.root.program := by
  obtain ⟨binding⟩ := finite_binding _ _ _ _ _ _ _ ok
  obtain ⟨_,facts⟩ := CheckedFinite.check_ownershipSafe _ _ _ _ _ binding.baseBound
  exact ⟨binding,facts⟩

theorem finite_scopeSafe (bytes graph supplied : ByteArray) (indices : List Nat)
    (checked : CheckedFinite.Checked) (work left : Nat)
    (ok : (finite bytes graph supplied indices).run work = (.ok checked,left)) :
    ∃ _binding : FiniteBinding bytes graph supplied indices checked work left,
      checked.artifact.programs[checked.artifact.root]? = some checked.result.root.program ∧
      Semantics.ClassicalScope.ScopeSafe checked.result.root.program := by
  obtain ⟨binding⟩ := finite_binding _ _ _ _ _ _ _ ok
  obtain ⟨_,facts⟩ := CheckedFinite.check_scopeSafe _ _ _ _ _ binding.baseBound
  exact ⟨binding,facts⟩

end QleisliKernel.Protocol.ExecutionView.CheckedCaller
