import QleisliKernel.Engineering.Instrument
import QleisliKernel.Qirf.InstrumentContract

/-! Original-graph binding for engineering observing-instrument inequalities.
Both exact original roots, dependencies, complete Kraus reconstructions and
ordered public projections are checked afresh. This does not change the exact
InstrumentContract gate, establish source/type lowering, create coherent control
or cleanup access, certify resources or discharge constitutional PR/RS. Its
engineering-only result has the same limits at epsilon zero. No native byte
schema, CLI mode, public handle or compiler consumption is introduced here.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.EngineeringInstrument
open Semantics.Exact Semantics.InstrumentContract Finite

structure Request where
  actual : Artifact
  actualOrder : Array Nat
  expected : Artifact
  expectedOrder : Array Nat
  actualSignature : Signature
  expectedSignature : Signature
  identity : Semantics.Function.Identity
  epsilon : Coefficient
  majorants : List Coefficient

structure Checked where
  actual : Validity.Root
  expected : Validity.Root
  actualInstrument : Raw.Instrument.Checked
  expectedInstrument : Raw.Instrument.Checked
  actualHistories : List Raw.InstrumentEquality.History
  expectedHistories : List Raw.InstrumentEquality.History
  bounds : Engineering.Instrument.Checked

/-- Reuse the ordinary original-graph/interface/reconstruction checks, then
check engineering inequalities instead of invoking exact pair equality. Full
signature trees remain request data; source-to-IR preservation is separate. -/
def check (request : Request) : WorkM Checked := do
  exactWork (Exact.charge (InstrumentContract.identityCost request.identity))
  guard (Raw.Function.identityValid request.identity &&
    request.identity.sources.all Qirf.sourceValid) .limit
  exactWork (Exact.charge (InstrumentContract.signatureCost request.actualSignature +
    InstrumentContract.signatureCost request.expectedSignature))
  guard (request.actualSignature == request.expectedSignature) .request
  let projection ← InstrumentContract.project request.expectedSignature.result
  let actualRoot ← Validity.checkRoot request.actual request.actualOrder
  let expectedRoot ← Validity.checkRoot request.expected request.expectedOrder
  InstrumentContract.interface request.actualSignature projection actualRoot
  InstrumentContract.interface request.expectedSignature projection expectedRoot
  let actualInstrument ← Raw.Instrument.reconstruct actualRoot.dependencies actualRoot.program []
  let expectedInstrument ← Raw.Instrument.reconstruct expectedRoot.dependencies expectedRoot.program []
  let actualHistories ← Raw.InstrumentEquality.prepare actualRoot.program.classicalOutputs actualInstrument.histories
  let expectedHistories ← Raw.InstrumentEquality.prepare expectedRoot.program.classicalOutputs expectedInstrument.histories
  let rows := 2^actualInstrument.structureCheck.state.quantum.frame.length
  let cols := 2^actualInstrument.structureCheck.prepared.inputBits
  let bounds ← Engineering.Instrument.checkHistories rows cols projection.classicalBits
    actualHistories expectedHistories request.epsilon request.majorants
  return ⟨actualRoot,expectedRoot,actualInstrument,expectedInstrument,actualHistories,expectedHistories,bounds⟩

/-- All facts refer to this continuous checking execution; producer flags,
probability tables, reconstructed matrices and cached receipts are not inputs. -/
structure Acceptance (request : Request) (checked : Checked) (work left : Nat) where
  projection : Projection
  afterIdentity : Nat
  afterSignatures : Nat
  afterProjection : Nat
  afterActualRoot : Nat
  afterExpectedRoot : Nat
  afterActualInterface : Nat
  afterExpectedInterface : Nat
  afterActualReconstruction : Nat
  afterExpectedReconstruction : Nat
  afterActualHistories : Nat
  afterExpectedHistories : Nat
  identityCharge : (Exact.charge (InstrumentContract.identityCost request.identity)).run work =
    (.ok (),afterIdentity)
  identityValid : Raw.Function.identityValid request.identity = true
  sourcesValid : request.identity.sources.all Qirf.sourceValid = true
  signatureCharge : (Exact.charge (InstrumentContract.signatureCost request.actualSignature +
    InstrumentContract.signatureCost request.expectedSignature)).run afterIdentity = (.ok (),afterSignatures)
  signaturesEqual : request.actualSignature = request.expectedSignature
  projected : (InstrumentContract.project request.expectedSignature.result).run afterSignatures =
    (.ok projection,afterProjection)
  actualRoot : (Validity.checkRoot request.actual request.actualOrder).run afterProjection =
    (.ok checked.actual,afterActualRoot)
  expectedRoot : (Validity.checkRoot request.expected request.expectedOrder).run afterActualRoot =
    (.ok checked.expected,afterExpectedRoot)
  actualInterface : (InstrumentContract.interface request.actualSignature projection checked.actual).run
    afterExpectedRoot = (.ok (),afterActualInterface)
  expectedInterface : (InstrumentContract.interface request.expectedSignature projection checked.expected).run
    afterActualInterface = (.ok (),afterExpectedInterface)
  actualReconstructed : (Raw.Instrument.reconstruct checked.actual.dependencies checked.actual.program []).run
    afterExpectedInterface = (.ok checked.actualInstrument,afterActualReconstruction)
  expectedReconstructed : (Raw.Instrument.reconstruct checked.expected.dependencies checked.expected.program []).run
    afterActualReconstruction = (.ok checked.expectedInstrument,afterExpectedReconstruction)
  actualPrepared : (Raw.InstrumentEquality.prepare checked.actual.program.classicalOutputs
    checked.actualInstrument.histories).run afterExpectedReconstruction = (.ok checked.actualHistories,afterActualHistories)
  expectedPrepared : (Raw.InstrumentEquality.prepare checked.expected.program.classicalOutputs
    checked.expectedInstrument.histories).run afterActualHistories = (.ok checked.expectedHistories,afterExpectedHistories)
  bounded : (Engineering.Instrument.checkHistories
    (2^checked.actualInstrument.structureCheck.state.quantum.frame.length)
    (2^checked.actualInstrument.structureCheck.prepared.inputBits) projection.classicalBits
    checked.actualHistories checked.expectedHistories request.epsilon request.majorants).run
    afterExpectedHistories = (.ok checked.bounds,left)

theorem check_acceptance (request : Request) (checked : Checked) (work left : Nat)
    (ok : (check request).run work = (.ok checked,left)) :
    Nonempty (Acceptance request checked work left) := by
  obtain ⟨_,w₁,hc,h⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨_,w₁',hv,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨valid,same₁⟩ := guard_success _ _ _ _ hv
  subst w₁'
  obtain ⟨_,w₂,hsc,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₂',hse,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨equal,same₂⟩ := guard_success _ _ _ _ hse
  subst w₂'
  obtain ⟨projection,w₃,hp,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨actualRoot,w₄,har,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨expectedRoot,w₅,her,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₆,hai,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₇,hei,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨actualInstrument,w₈,ha,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨expectedInstrument,w₉,he,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨actualHistories,w₁₀,hah,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨expectedHistories,w₁₁,heh,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨bounds,w₁₂,hbound,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨rfl,rfl⟩ := pure_success _ _ _ _ h
  have identities : Raw.Function.identityValid request.identity = true ∧
      request.identity.sources.all Qirf.sourceValid = true := by
    simpa only [Bool.and_eq_true] using valid
  exact ⟨⟨projection,w₁,w₂,w₃,w₄,w₅,w₆,w₇,w₈,w₉,w₁₀,w₁₁,
    exactWork_success _ _ _ _ hc,identities.1,identities.2,exactWork_success _ _ _ _ hsc,
    beq_iff_eq.mp equal,hp,har,her,hai,hei,ha,he,hah,heh,hbound⟩⟩

end QleisliKernel.Qirf.EngineeringInstrument
