import QleisliKernel.Tests.SequenceSector
import QleisliKernel.Tests.SequenceSectorLegacy
import QleisliKernel.Tests.OriginalSelectionContinuity
import QleisliKernel.Tests.ContextIntervalContinuity

/-! Bounded before/after observations for shared selection extraction.
The complete public reader and interval refinements are proved separately.
SequenceSector deliberately reuses the original caller and funds shared port
checks, so these observations do not assert identical work consumption.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.SequenceSectorSharingTests
open QleisliKernel QleisliKernel.Qirf
open QleisliKernel.Tests.SequenceSector

private def legacyRequest (request : Qirf.SequenceSector.Request) : SequenceSectorLegacy.Request :=
  ⟨request.attached,request.required,request.position,request.programs⟩

private def view (result : Except Finite.Error (List Nat)) : Option (List Nat) × Option Finite.Error :=
  match result with | .ok value => (some value,none) | .error error => (none,some error)

def agrees (data : Artifact := artifact) (asked : List Qirf.SequenceSector.Request := requests) : Bool :=
  let previous := ((SequenceSectorLegacy.check data order "main" "route"
    (asked.map legacyRequest)).run 10000000).1.map fun checked => checked.locals.map (·.logical.length)
  view (result data asked) == view previous

#guard agrees
#guard agrees {artifact with programs := artifact.programs.set! 0 (main 2 4)}
#guard agrees {artifact with programs := artifact.programs.set! 0 (main 4 2)}
#guard agrees {artifact with programs := artifact.programs.set! 0 (main 0 0)}
#guard agrees {artifact with programs := artifact.programs.set! 3 (arm 2)}
#guard agrees {artifact with programs := artifact.programs.set! 4 (controlled 2)}
#guard agrees artifact (requests.take 1)
#guard agrees artifact requests.reverse
#guard agrees artifact [firstRequest,firstRequest]
#guard agrees artifact [{firstRequest with programs := [⟨0,2⟩,⟨0,2⟩]},secondRequest]
#guard agrees artifact [{firstRequest with programs := [⟨1,0⟩,⟨0,2⟩]},secondRequest]
#guard agrees {artifact with programs := artifact.programs.set! 0 {main with outputs := [9,10]}}
#guard agrees {artifact with programs := artifact.programs.set! 0 {main with outputs := [9,2,10]}}
#guard agrees {artifact with programs := artifact.programs.set! 0 {main with effect := .observe}}
#guard agrees {artifact with sources := artifact.sources.push ("unrelated","fn unused()->Unit{()}")}

#print axioms Qirf.PureInterval.Many.two_owner_legacy_refinement
#print axioms OriginalSelectionContinuity.siteWrapper
#print axioms OriginalSelectionContinuity.armsWrapper
end QleisliKernel.Tests.SequenceSectorSharingTests
