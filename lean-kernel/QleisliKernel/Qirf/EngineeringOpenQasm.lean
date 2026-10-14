import QleisliKernel.Target.CanonicalOpenQasm
import QleisliKernel.Qirf.EngineeringInstrument

/-! Target-byte binding for a separate engineering-only instrument comparison.
The literal canonical target is decoded independently, its actual graph is
constructed from that word, and the original ideal/dependencies and both full
instruments pass the unchanged exact body/Kraus gates before the inequality.
No source/export preservation, exact cross-meaning, hardware, coherent-control,
cleanup, resource or constitutional PR/RS claim follows, including at epsilon0.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.EngineeringOpenQasm
open Semantics.Exact Semantics.InstrumentContract Finite

structure Request where
  target : ByteArray
  expected : Artifact
  expectedOrder : Array Nat
  actualSignature : Signature
  expectedSignature : Signature
  identity : Semantics.Function.Identity
  epsilon : Coefficient
  majorants : List Coefficient

/-- The actual graph is never supplied by the caller. The closed target's
zero-width owner, order, terminal readout and effect are explicit Raw data. -/
def actualArtifact (target : QleisliKernel.Target.CanonicalOpenQasm.Decoded) : Artifact :=
  ⟨#[Semantics.CanonicalTerminalQasm.program target.gates],#[],#[],0,none⟩

def Request.instrument (request : Request) (target : QleisliKernel.Target.CanonicalOpenQasm.Decoded) :
    EngineeringInstrument.Request :=
  ⟨actualArtifact target,#[0],request.expected,request.expectedOrder,
    request.actualSignature,request.expectedSignature,request.identity,request.epsilon,request.majorants⟩

structure Checked where
  target : QleisliKernel.Target.CanonicalOpenQasm.Decoded
  instrument : EngineeringInstrument.Checked

private def adapt {α : Type} (value : Except String α) : WorkM α :=
  lift (value.mapError fun _ => .invalid)

/-- Precharge precedes byte traversal. The request, independent target decode,
ideal graph, exact complete instruments and metric share the same work state. -/
def check (request : Request) : WorkM Checked := do
  guard (request.target.size ≤ QleisliKernel.Target.CanonicalOpenQasm.maxBytes) .limit
  exactWork (Exact.charge (1 + request.target.size))
  let target ← adapt (QleisliKernel.Target.CanonicalOpenQasm.decode request.target)
  guard (request.actualSignature == Semantics.CanonicalTerminalQasm.signature) .request
  let checked ← EngineeringInstrument.check (request.instrument target)
  return ⟨target,checked⟩

structure Postcondition (request : Request) (checked : Checked) (work left : Nat) : Prop where
  byteLimit : request.target.size ≤ QleisliKernel.Target.CanonicalOpenQasm.maxBytes
  decoded : QleisliKernel.Target.CanonicalOpenQasm.decode request.target = .ok checked.target
  signature : request.actualSignature = Semantics.CanonicalTerminalQasm.signature
  execution : ∃ afterCharge,
    (Exact.charge (1 + request.target.size)).run work = (.ok (),afterCharge) ∧
    (EngineeringInstrument.check (request.instrument checked.target)).run afterCharge =
      (.ok checked.instrument,left)

/-- The generated actual graph and ideal checking are subjects of this actual
executed decision, not a later selected matrix, summary or cached receipt. -/
theorem check_postcondition (request : Request) (checked : Checked) (work left : Nat)
    (ok : (check request).run work = (.ok checked,left)) : Postcondition request checked work left := by
  obtain ⟨_,a,hlimit,h⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨_,b,hcharge,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨target,c,hdecoded,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,d,hsignature,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨instrument,e,hchecked,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨rfl,rfl⟩ := pure_success _ _ _ _ h
  have limit := guard_success _ _ _ _ hlimit
  have decoded := lift_success _ _ _ _ hdecoded
  have signature := guard_success _ _ _ _ hsignature
  have read : QleisliKernel.Target.CanonicalOpenQasm.decode request.target = .ok target := by
    cases value : QleisliKernel.Target.CanonicalOpenQasm.decode request.target <;> simp_all [adapt,Except.mapError]
  have first := limit.2
  have second := decoded.2
  have third := signature.2
  subst a
  subst c
  subst d
  exact ⟨by simpa using limit.1,read,beq_iff_eq.mp signature.1,
    ⟨b,exactWork_success _ _ _ _ hcharge,hchecked⟩⟩

end QleisliKernel.Qirf.EngineeringOpenQasm
