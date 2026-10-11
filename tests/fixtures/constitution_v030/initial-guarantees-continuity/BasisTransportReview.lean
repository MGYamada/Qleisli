import Qleisli.FiniteBasisTransport
import Qleisli.NativeValidity

/-! Fixed type review for representation transport of existing ordinary-root
ownership and classical scope guarantees; no new guarantee is admitted.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/
set_option autoImplicit false
open Qleisli.FiniteBasisTransport QleisliKernel.Semantics.Finite

example : Function.Injective encodeBasis := encodeBasis_injective
example (basis : List LegacyAtom) : width (encodeBasis basis) = legacyWidth basis :=
  width_preserved basis
example (basis : List LegacyAtom) :
    QleisliKernel.Finite.basisValid (encodeBasis basis) = legacyValid basis :=
  basisValid_preserved basis
example (basis : List LegacyAtom) :
    QleisliKernel.Qirf.Validity.rootBasis (encodeBasis basis) = legacyRootValid basis :=
  rootBasis_preserved basis
example (basis : List LegacyAtom) (target : QleisliKernel.Qirf.Target) :
    QleisliKernel.Semantics.Qirf.targetProgram (encodeBasis basis) target =
      legacyTargetProgram basis target := targetProgram_preserved basis target
example (artifact : LegacyArtifact) :
    (encodeArtifact artifact).programs[(encodeArtifact artifact).root]? =
      artifact.programs[artifact.root]? := originalRoot_preserved artifact
example (artifact : LegacyArtifact) (program : QleisliKernel.Semantics.Observation.Program) :
    ((encodeArtifact artifact).programs[(encodeArtifact artifact).root]? = some program ∧
      QleisliKernel.Semantics.Ownership.OwnershipSafe program) ↔
    (artifact.programs[artifact.root]? = some program ∧
      QleisliKernel.Semantics.Ownership.OwnershipSafe program) :=
  ownership_preserved artifact program
example (artifact : LegacyArtifact) (program : QleisliKernel.Semantics.Observation.Program) :
    ((encodeArtifact artifact).programs[(encodeArtifact artifact).root]? = some program ∧
      QleisliKernel.Semantics.ClassicalScope.ScopeSafe program) ↔
    (artifact.programs[artifact.root]? = some program ∧
      QleisliKernel.Semantics.ClassicalScope.ScopeSafe program) :=
  scope_preserved artifact program
example (artifact : LegacyArtifact) (program : QleisliKernel.Semantics.Observation.Program) :
    QleisliKernel.Qirf.Validity.interfaceValid (encodeArtifact artifact) program =
      legacyInterfaceValid artifact program := interfaceValid_preserved artifact program

example (bytes : ByteArray) (hasRequest : Bool) (work left : Nat)
    (ok : (QleisliKernel.Protocol.Validity.check bytes).run work = (.ok hasRequest, left)) :
    ∃ binding : QleisliKernel.Protocol.Validity.Acceptance bytes hasRequest work left,
      ∃ program, binding.artifact.programs[binding.artifact.root]? = some program ∧
        QleisliKernel.Semantics.Ownership.OwnershipSafe program :=
  QleisliKernel.Protocol.Validity.check_ownershipSafe bytes hasRequest work left ok
example (bytes : ByteArray) (hasRequest : Bool) (work left : Nat)
    (ok : (QleisliKernel.Protocol.Validity.check bytes).run work = (.ok hasRequest, left)) :
    ∃ binding : QleisliKernel.Protocol.Validity.Acceptance bytes hasRequest work left,
      ∃ program, binding.artifact.programs[binding.artifact.root]? = some program ∧
        QleisliKernel.Semantics.ClassicalScope.ScopeSafe program :=
  Qleisli.NativeValidity.check_scopeSafe bytes hasRequest work left ok

#print axioms Qleisli.FiniteBasisTransport.ownership_preserved
#print axioms Qleisli.FiniteBasisTransport.scope_preserved
#print axioms Qleisli.FiniteBasisTransport.targetProgram_preserved
#print axioms QleisliKernel.Protocol.Validity.check_ownershipSafe
#print axioms Qleisli.NativeValidity.check_scopeSafe
