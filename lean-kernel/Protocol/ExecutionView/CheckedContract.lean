import Protocol.ExecutionView.Gate
import Protocol.ExecutionView.Contracts

/-! Pure contract execution-view comparison over one retained core result.
Native dispatch and CheckedCaller connect this gate to QLV2 and caller cache binding.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Protocol.ExecutionView.CheckedContract
open Gate
abbrev Checked := NativeContract.Retained

/-- The candidate supplies only a description. Both roots and all retained
request data come from this fresh original native-contract execution. -/
def check (bytes supplied : ByteArray) : CheckM Checked := do
  guard (framed supplied) .invalidView
  let checked ← native (NativeContract.checkRetained bytes)
  let description ← native (FiniteView.nativeContract checked)
  let expected ← lift ((encode description).mapError fun _ => .encoding)
  guard (supplied.data == expected.data) .decodedView
  return checked

structure Binding (bytes supplied : ByteArray) (checked : Checked) (work left : Nat) where
  afterCore : Nat
  description : Value
  framedView : framed supplied = true
  checkedBound : (NativeContract.checkRetained bytes).run work = (.ok checked,afterCore)
  viewBound : (FiniteView.nativeContract checked).run afterCore = (.ok description,left)
  compared : encode description = .ok supplied

/-- The compared data is derived from the exact returned record, with continuous
work states. The original core finishes before view derivation. -/
theorem check_binding (bytes supplied : ByteArray) (checked : Checked) (work left : Nat)
    (ok : (check bytes supplied).run work = (.ok checked,left)) :
    Nonempty (Binding bytes supplied checked work left) := by
  unfold check at ok
  obtain ⟨_,a,hf,h⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨result,b,hc,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨description,c,hv,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨expected,d,he,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,e,hs,h⟩ := bind_success _ _ _ _ _ h
  have final : checked = result ∧ left = e := by
    cases h
    exact ⟨rfl,rfl⟩
  rcases final with ⟨rfl,rfl⟩
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
  subst d
  subst c
  exact ⟨⟨b,description,frame.1,native_success _ _ _ _ hc,
    native_success _ _ _ _ hv,encoding⟩⟩

/-- Exact returned-field binding to the original packet is inherited from the
same core execution, not from a separately selected existential root. -/
theorem Binding.original {bytes supplied : ByteArray} {checked : Checked} {work left : Nat}
    (binding : Binding bytes supplied checked work left) :
    Nonempty (NativeContract.RetainedBinding bytes checked work binding.afterCore) :=
  NativeContract.checkRetained_bound _ _ _ _ binding.checkedBound

end QleisliKernel.Protocol.ExecutionView.CheckedContract
