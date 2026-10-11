import Qleisli.QirfValidity
import Protocol.Validity

/-! The actual native QLV1 entry point reaches the composed QIRF theorem.
The packet reader and ordinary root's OwnershipSafe/ScopeSafe are explicitly bound;
parser/compiler, full EffectSound and hierarchical coverage remain separate.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.NativeValidity
open QleisliKernel.Protocol.Validity

/-- No Rust decision or supplied semantic witness is a premise. All stage
results and original-body semantics follow from this packet's native success. -/
theorem check_sound (bytes : ByteArray) (hasRequest : Bool) (work left : Nat)
    (ok : (check bytes).run work = (.ok hasRequest,left)) :
    ∃ binding : Acceptance bytes hasRequest work left,
      ∃ checked,
        (QleisliKernel.Qirf.Validity.check binding.artifact binding.order binding.requirement).run
          binding.afterRequest = (.ok checked,left) ∧
        Qleisli.Qirf.Validity.VerifiedMeaning binding.artifact binding.order binding.requirement checked := by
  obtain ⟨binding⟩ := check_acceptance _ _ _ _ ok
  obtain ⟨checked,accepted,meaning⟩ := Qleisli.Qirf.Validity.inspect_sound _ _ _ _ _ binding.accepted
  exact ⟨binding,checked,accepted,meaning⟩

/-- All classical uses, fresh definitions, both branch arms and simultaneous
phi inputs are covered on the original decoded root. No finite request or host
verification result is a premise. -/
theorem check_scopeSafe (bytes : ByteArray) (hasRequest : Bool) (work left : Nat)
    (ok : (check bytes).run work = (.ok hasRequest,left)) :
    ∃ binding : Acceptance bytes hasRequest work left,
      ∃ program, binding.artifact.programs[binding.artifact.root]? = some program ∧
        QleisliKernel.Semantics.ClassicalScope.ScopeSafe program := by
  obtain ⟨binding,checked,_,meaning⟩ := check_sound _ _ _ _ ok
  exact ⟨binding,checked.root.program,meaning.root.original,meaning.root.scopes⟩

end Qleisli.NativeValidity
