import Qleisli.RuntimeForestFrameEvidence
import Qleisli.RuntimeBoundaryOwnerEvidence

/-! Mathematical sparse Frames for the actual complete source boundaries.
The evidence comes from their own checked storage and exact binding lists.
These erased existence proofs neither observe readFrame invocations nor supply
intermediate-body availability or the public caller's remaining work budget.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/

namespace Qleisli.RuntimeBoundaryFrameEvidence
open QleisliKernel QleisliKernel.Qirf

/-- Complete original input storage supplies a mathematical sparse Frame for
the exact map computed by this same input boundary. -/
theorem inputs_frame {sources owner name signature dependencies program}
    {body : @SourceTypes.SourceRuntimeTrace.Body sources owner name signature}
    {root : RuntimeInterval.Prepared dependencies program}
    {stores : List Semantics.RuntimeStorage.Value}
    (inputs : RuntimeSourceBoundary.Inputs body root stores) :
    Nonempty (RuntimeForestCode.Frame inputs.owners) :=
  RuntimeForestFrameEvidence.of_ownerCodes inputs.owners
    (RuntimeBoundaryOwnerEvidence.inputs_ownerCodes inputs)

/-- Complete original result storage supplies a mathematical sparse Frame for
the exact returned map, preserving its full owner order and zero-width ports. -/
theorem outputs_frame {value state owners stored tokens}
    (outputs : RuntimeSourceBoundary.Outputs value state owners stored tokens) :
    Nonempty (RuntimeForestCode.Frame owners) :=
  RuntimeForestFrameEvidence.of_ownerCodes owners
    (RuntimeBoundaryOwnerEvidence.outputs_ownerCodes outputs)

#print axioms inputs_frame
#print axioms outputs_frame

end Qleisli.RuntimeBoundaryFrameEvidence
