import QleisliKernel.Semantics.InstrumentContract
import QleisliKernel.Qirf.Validity
import QleisliKernel.Raw.InstrumentEquality

/-! Original QIRF graph and exact observing-instrument comparison stages.
Complete signatures are requested type data, not inferred from equal widths.
Source preservation and the public byte decoder/accepted handle remain separate.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.InstrumentContract
open Semantics.Exact Semantics.Finite Semantics.InstrumentContract Finite

def signatureCost (signature : Signature) : Nat :=
  signature.result.foldl (fun cost atom => cost + 1 + match atom with
    | .quantum basis => basis.length | _ => 0) signature.input.length

def identityCost (identity : Semantics.Function.Identity) : Nat :=
  identity.sources.length + Raw.Function.identityBytes identity

/-- Check a complete prefix result tree before using its ordered projections.
Product and basis bounds reuse the current structural root type domain. -/
def project (atoms : List ResultAtom) : WorkM Projection := do
  guard (atoms.length ≤ 4096) .limit
  exactWork (Exact.charge atoms.length)
  let (_,_,pending,projection) ← atoms.foldlM (fun (remaining,slots,pending,projection) atom => do
    let depth :: rest := pending | throw .invalid
    guard (depth ≤ 64) .limit
    let arity ← match atom with
      | .pair => pure 2
      | .tuple n => guard (3 ≤ n && n ≤ 4096) .limit; pure n
      | _ => pure 0
    let remaining := remaining - 1
    let slots := slots - 1 + arity
    -- Each pending child needs at least one remaining atom. Refuse malformed
    -- prefixes before allocating children; pending storage stays ≤4096 cells.
    guard (slots ≤ remaining)
    match atom with
    | .unit => return (remaining,slots,rest,projection)
    | .bit => return (remaining,slots,rest,{projection with classicalBits := projection.classicalBits + 1})
    | .bits n => return (remaining,slots,rest,{projection with classicalBits := projection.classicalBits + n})
    | .quantum basis =>
      exactWork (Exact.charge (basis.length + projection.quantum.length + 1))
      guard (Validity.rootBasis basis) .request
      return (remaining,slots,rest,{projection with quantum := projection.quantum ++ [basis]})
    | .pair => return (remaining,slots,(depth+1) :: (depth+1) :: rest,projection)
    | .tuple n =>
      exactWork (Exact.charge n)
      return (remaining,slots,List.replicate n (depth+1) ++ rest,projection))
    (atoms.length,1,[1],⟨[],0⟩)
  guard pending.isEmpty
  return projection

/-- Principal Observe is checked from the actual body, not its effect label.
Ordered live-owner lookup retains zero-width owners and each exact basis slot. -/
def interface (signature : Signature) (projection : Projection) (root : Validity.Root) : WorkM Unit := do
  exactWork (Exact.charge (signature.input.length + root.program.inputs.length +
    root.program.outputs.length * (1 + root.checked.state.quantum.live.length) +
    root.program.classicalInputs.length + root.program.classicalOutputs.length))
  guard (Validity.rootBasis signature.input) .request
  guard (root.program.effect == .observe && root.checked.state.observe) .request
  guard root.program.classicalInputs.isEmpty .request
  let [input] := root.program.inputs | throw .request
  guard (input.bits == width signature.input) .request
  guard (root.program.outputs.length == projection.quantum.length &&
    root.program.classicalOutputs.length == projection.classicalBits) .request
  (root.program.outputs.zip projection.quantum).forM fun (token,basis) => do
    let port ← lift (readOption (root.checked.state.quantum.live.find? (fun port => port.token == token)))
    guard (port.bits == width basis) .request

structure Checked where
  actual : Validity.Root
  expected : Validity.Root
  actualInstrument : Raw.Instrument.Checked
  expectedInstrument : Raw.Instrument.Checked
  actualHistories : List Raw.InstrumentEquality.History
  expectedHistories : List Raw.InstrumentEquality.History

/-- Both complete original graphs are freshly checked before reconstruction.
There is no matrix, receipt or success flag input. The two selected source
names/snapshots are validated identity data; no source-lowering proof is claimed. -/
def check (actual : Artifact) (actualOrder : Array Nat)
    (expected : Artifact) (expectedOrder : Array Nat)
    (actualSignature expectedSignature : Signature)
    (identity : Semantics.Function.Identity) : WorkM Checked := do
  exactWork (Exact.charge (identityCost identity))
  guard (Raw.Function.identityValid identity && identity.sources.all Qirf.sourceValid) .limit
  exactWork (Exact.charge (signatureCost actualSignature + signatureCost expectedSignature))
  guard (actualSignature == expectedSignature) .request
  let projection ← project expectedSignature.result
  let actualRoot ← Validity.checkRoot actual actualOrder
  let expectedRoot ← Validity.checkRoot expected expectedOrder
  interface actualSignature projection actualRoot
  interface expectedSignature projection expectedRoot
  let actualInstrument ← Raw.Instrument.reconstruct actualRoot.dependencies actualRoot.program []
  let expectedInstrument ← Raw.Instrument.reconstruct expectedRoot.dependencies expectedRoot.program []
  let actualHistories ← Raw.InstrumentEquality.prepare actualRoot.program.classicalOutputs actualInstrument.histories
  let expectedHistories ← Raw.InstrumentEquality.prepare expectedRoot.program.classicalOutputs expectedInstrument.histories
  let rows := 2^actualInstrument.structureCheck.state.quantum.frame.length
  let cols := 2^actualInstrument.structureCheck.prepared.inputBits
  Raw.InstrumentEquality.compare rows cols projection.classicalBits actualHistories expectedHistories
  return ⟨actualRoot,expectedRoot,actualInstrument,expectedInstrument,actualHistories,expectedHistories⟩

/-- Success facts from this checking execution, never producer certificates.
The complete original roots, fresh dependencies, type equality, projections
and coefficient equation retain a continuous sequence of shared work states. -/
structure Acceptance (actual : Artifact) (actualOrder : Array Nat)
    (expected : Artifact) (expectedOrder : Array Nat)
    (actualSignature expectedSignature : Signature) (identity : Semantics.Function.Identity)
    (checked : Checked) (work left : Nat) where
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
  identityCharge : (Exact.charge (identityCost identity)).run work = (.ok (),afterIdentity)
  identityValid : Raw.Function.identityValid identity = true
  sourcesValid : identity.sources.all Qirf.sourceValid = true
  signatureCharge : (Exact.charge (signatureCost actualSignature + signatureCost expectedSignature)).run
    afterIdentity = (.ok (),afterSignatures)
  signaturesEqual : actualSignature = expectedSignature
  projected : (project expectedSignature.result).run afterSignatures = (.ok projection,afterProjection)
  actualRoot : (Validity.checkRoot actual actualOrder).run afterProjection = (.ok checked.actual,afterActualRoot)
  expectedRoot : (Validity.checkRoot expected expectedOrder).run afterActualRoot = (.ok checked.expected,afterExpectedRoot)
  actualInterface : (interface actualSignature projection checked.actual).run afterExpectedRoot =
    (.ok (),afterActualInterface)
  expectedInterface : (interface expectedSignature projection checked.expected).run afterActualInterface =
    (.ok (),afterExpectedInterface)
  actualReconstructed : (Raw.Instrument.reconstruct checked.actual.dependencies checked.actual.program []).run
    afterExpectedInterface = (.ok checked.actualInstrument,afterActualReconstruction)
  expectedReconstructed : (Raw.Instrument.reconstruct checked.expected.dependencies checked.expected.program []).run
    afterActualReconstruction = (.ok checked.expectedInstrument,afterExpectedReconstruction)
  actualPrepared : (Raw.InstrumentEquality.prepare checked.actual.program.classicalOutputs
    checked.actualInstrument.histories).run afterExpectedReconstruction = (.ok checked.actualHistories,afterActualHistories)
  expectedPrepared : (Raw.InstrumentEquality.prepare checked.expected.program.classicalOutputs
    checked.expectedInstrument.histories).run afterActualHistories = (.ok checked.expectedHistories,afterExpectedHistories)
  compared : (Raw.InstrumentEquality.compare
    (2^checked.actualInstrument.structureCheck.state.quantum.frame.length)
    (2^checked.actualInstrument.structureCheck.prepared.inputBits) projection.classicalBits
    checked.actualHistories checked.expectedHistories).run afterExpectedHistories = (.ok (),left)

theorem check_acceptance (actual : Artifact) (actualOrder : Array Nat)
    (expected : Artifact) (expectedOrder : Array Nat)
    (actualSignature expectedSignature : Signature) (identity : Semantics.Function.Identity)
    (checked : Checked) (work left : Nat)
    (ok : (check actual actualOrder expected expectedOrder actualSignature expectedSignature identity).run work =
      (.ok checked,left)) :
    Nonempty (Acceptance actual actualOrder expected expectedOrder actualSignature expectedSignature identity checked work left) := by
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
  obtain ⟨_,w₁₂,hcompare,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨rfl,rfl⟩ := pure_success _ _ _ _ h
  have identities : Raw.Function.identityValid identity = true ∧ identity.sources.all Qirf.sourceValid = true := by
    simpa only [Bool.and_eq_true] using valid
  exact ⟨⟨projection,w₁,w₂,w₃,w₄,w₅,w₆,w₇,w₈,w₉,w₁₀,w₁₁,
    exactWork_success _ _ _ _ hc,identities.1,identities.2,exactWork_success _ _ _ _ hsc,
    beq_iff_eq.mp equal,hp,har,her,hai,hei,ha,he,hah,heh,hcompare⟩⟩

end QleisliKernel.Qirf.InstrumentContract
