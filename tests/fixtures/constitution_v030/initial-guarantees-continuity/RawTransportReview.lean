import Qleisli.RawRepresentationTransport
import Qleisli.NativeValidity

/-! Fixed typed review of old-operation transport and actual original-byte
acceptance endpoints. This preserves existing scopes, not a new admission.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/
set_option autoImplicit false
open Qleisli.RawRepresentationTransport
open QleisliKernel.Semantics

example : Function.Injective encodeRawOp := encodeRawOp_injective
example : Function.Injective encodeProgram := encodeProgram_injective
example (program : Qleisli.Semantics.RawLegacy.Raw.Program) :
    RawTrace.run (encodeRawProgram program) =
      Qleisli.Semantics.RawLegacy.RawTrace.run program := rawWholeTrace_preserved program
example (program : Qleisli.Semantics.RawLegacy.Observation.Program) :
    Observation.read (encodeProgram program) =
      Qleisli.Semantics.RawLegacy.Observation.read program := wholeTrace_preserved program
example (program : Qleisli.Semantics.RawLegacy.Observation.Program) :
    Ownership.OwnershipSafe (encodeProgram program) ↔
      Qleisli.Semantics.RawLegacy.Ownership.OwnershipSafe program := ownership_preserved program
example (program : Qleisli.Semantics.RawLegacy.Observation.Program) :
    ClassicalScope.ScopeSafe (encodeProgram program) ↔
      Qleisli.Semantics.RawLegacy.ClassicalScope.ScopeSafe program := scope_preserved program
example (artifact : LegacyArtifact) :
    (encodeArtifact artifact).programs[(encodeArtifact artifact).root]? =
      artifact.programs[artifact.root]?.map encodeProgram := originalRoot_preserved artifact
example (artifact : LegacyArtifact) (program : Qleisli.Semantics.RawLegacy.Observation.Program) :
    ((encodeArtifact artifact).programs[(encodeArtifact artifact).root]? = some (encodeProgram program) ∧
      Ownership.OwnershipSafe (encodeProgram program)) ↔
    (artifact.programs[artifact.root]? = some program ∧
      Qleisli.Semantics.RawLegacy.Ownership.OwnershipSafe program) := originalRoot_ownership artifact program
example (artifact : LegacyArtifact) (program : Qleisli.Semantics.RawLegacy.Observation.Program) :
    ((encodeArtifact artifact).programs[(encodeArtifact artifact).root]? = some (encodeProgram program) ∧
      ClassicalScope.ScopeSafe (encodeProgram program)) ↔
    (artifact.programs[artifact.root]? = some program ∧
      Qleisli.Semantics.RawLegacy.ClassicalScope.ScopeSafe program) := originalRoot_scope artifact program

example (bytes : ByteArray) (hasRequest : Bool) (work left : Nat)
    (ok : (QleisliKernel.Protocol.Validity.check bytes).run work = (.ok hasRequest, left)) :
    ∃ binding : QleisliKernel.Protocol.Validity.Acceptance bytes hasRequest work left,
      ∃ program, binding.artifact.programs[binding.artifact.root]? = some program ∧
        Ownership.OwnershipSafe program :=
  QleisliKernel.Protocol.Validity.check_ownershipSafe bytes hasRequest work left ok
example (bytes : ByteArray) (hasRequest : Bool) (work left : Nat)
    (ok : (QleisliKernel.Protocol.Validity.check bytes).run work = (.ok hasRequest, left)) :
    ∃ binding : QleisliKernel.Protocol.Validity.Acceptance bytes hasRequest work left,
      ∃ program, binding.artifact.programs[binding.artifact.root]? = some program ∧
        ClassicalScope.ScopeSafe program :=
  Qleisli.NativeValidity.check_scopeSafe bytes hasRequest work left ok

#print axioms Qleisli.RawRepresentationTransport.encodeProgram_injective
#print axioms Qleisli.RawRepresentationTransport.wholeTrace_preserved
#print axioms Qleisli.RawRepresentationTransport.originalRoot_ownership
#print axioms Qleisli.RawRepresentationTransport.originalRoot_scope
#print axioms QleisliKernel.Protocol.Validity.check_ownershipSafe
#print axioms Qleisli.NativeValidity.check_scopeSafe
