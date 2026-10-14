import QleisliKernel.Qirf.EngineeringOpenQasm
import Qleisli.NativeEngineeringInstrument

/-! Actual target-byte decoder/checker refinement for the closed engineering
profile. Standard target gate meanings are an explicit specification assumption.
No source/export preservation, target hardware, exact cross-body correspondence,
control, inverse, cleanup, resource or constitutional PR/RS evidence follows.
The complete-adjoint metric retains every finite reference, also at epsilon0.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.NativeEngineeringOpenQasm
open QleisliKernel
open QleisliKernel.Qirf.EngineeringOpenQasm

structure Meaning (request : Request) (checked : Checked) : Prop where
  decoded : QleisliKernel.Target.CanonicalOpenQasm.decode request.target = .ok checked.target
  originalTarget : checked.target.original = request.target
  actualSignature : request.actualSignature = Semantics.CanonicalTerminalQasm.signature
  expectedSignature : request.expectedSignature = Semantics.CanonicalTerminalQasm.signature
  instrument : ∃ projection, Qleisli.NativeEngineeringInstrument.Meaning
    (request.instrument checked.target) checked.instrument projection

/-- The actual side is the independently decoded target's generated original
body. The ideal, signatures, dependencies and complete Kraus semantics belong
to the same fresh execution; neither probabilities nor receipts are premises. -/
theorem check_meaning (request : Request) (checked : Checked) (work left : Nat)
    (ok : (QleisliKernel.Qirf.EngineeringOpenQasm.check request).run work = (.ok checked,left)) :
    Meaning request checked := by
  have facts := check_postcondition _ _ _ _ ok
  obtain ⟨afterCharge,_,accepted⟩ := facts.execution
  obtain ⟨projection,meaning⟩ :=
    Qleisli.NativeEngineeringInstrument.check_meaning _ _ afterCharge left accepted
  exact ⟨facts.decoded,QleisliKernel.Target.CanonicalOpenQasm.decode_original _ _ facts.decoded,
    facts.signature,meaning.signaturesEqual.symm.trans facts.signature,⟨projection,meaning⟩⟩

end Qleisli.NativeEngineeringOpenQasm
