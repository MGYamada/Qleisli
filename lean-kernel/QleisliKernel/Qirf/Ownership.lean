import QleisliKernel.Qirf.Validity
import QleisliKernel.Raw.ObservationOwnership

/-! Ordinary QIRF roots satisfy independent linear ownership, whether or not
the caller additionally requests a finite algorithm contract.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.Validity

theorem check_resourceSafe (artifact : Qirf.Artifact) (order : Array Nat)
    (request : Option Request) (checked : Checked) (work left : Nat)
    (ok : (check artifact order request).run work = (.ok checked,left)) :
    artifact.programs[artifact.root]? = some checked.root.program ∧
      Semantics.Ownership.ResourceSafe checked.root.program := by
  have facts := (check_postcondition _ _ _ _ _ _ ok).root
  obtain ⟨a,b,verified⟩ := facts.verification
  exact ⟨facts.original,Raw.Observation.verify_resourceSafe _ _ _ _ _ verified⟩

theorem inspect_resourceSafe (artifact : Qirf.Artifact) (order : Array Nat)
    (request : Option Request) (work left : Nat)
    (ok : (inspect artifact order request).run work = (.ok (),left)) :
    ∃ program, artifact.programs[artifact.root]? = some program ∧
      Semantics.Ownership.ResourceSafe program := by
  obtain ⟨checked,accepted,_⟩ := inspect_result _ _ _ _ _ ok
  exact ⟨checked.root.program,check_resourceSafe _ _ _ _ _ _ accepted⟩

end QleisliKernel.Qirf.Validity
