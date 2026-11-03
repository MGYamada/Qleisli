import QleisliKernel.Qirf.RuntimePreparedOperation

/-! Additional shared-source and explicit reference-context controls.
The consolidated caller/provider/Meaning action equations are covered by the
end-to-end fixture. These controls retain the complete non-accepting source
assessment, strict guard/error order, and missing/excess reference refusals.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.RuntimePreparedSource
open QleisliKernel Finite SourceTypes Qirf

def source : String := "#![no_implicit_prelude]\nunitary fn sign(q: Q<Bit>) -> Q<Bit> { phase[1,1](q) }\nunitary fn keep(q: Q<Bit>) -> Q<Bit> { q }\nmeaning Sign: Bit = reference(sign);\npub unitary fn route(q: Q<Bit>) -> Q<Bit> { checked_op(sign, Sign)(q) }\nfn main() -> Unit { () }\n"

private def falseSource := source.replace "reference(sign)" "reference(keep)"
private def noAssertion := source.replace "checked_op(sign, Sign)(q)" "sign(q)"
private def z : Semantics.Observation.Program := ⟨[⟨0,[0],1⟩],[],[.pure (.gate .z 0 1)],[1],[],.unitary⟩
private def artifact (text : String) : Artifact := ⟨#[z,z,z],#[],#[("main",text)],0,none⟩

private def inspectSource (text : String) : WorkM Bool := do
  let prepared ← RuntimeBodyDiscovery.prepareSource (artifact text) "main" "route" {}
  let [.operation event] := prepared.body.checked.events | throw .request
  return prepared.pending.queue.complete &&
    prepared.pending.entries.map (·.index.val) == List.range prepared.pending.queue.items.length &&
    prepared.pending.entries.any (·.unconsumed) &&
    prepared.signature.original.source == text && prepared.body.checked.signature.original.source == text &&
    event.operation.graph.hasMeaningRequirements && event.operation.graph.requirements.length == 1

#guard (inspectSource source).run 13000000 |>.1.toOption == some true
#guard (inspectSource falseSource).run 13000000 |>.1.toOption == some true

private def strict (text name : String) : WorkM Unit := do
  let _ ← RuntimeBodyDiscovery.readSource (artifact text) "main" name {}
  pure ()
#guard (match (strict source "route").run 13000000 with | (.error .request,_) => true | _ => false)
#guard (match (strict falseSource "route").run 13000000 with | (.error .request,_) => true | _ => false)
-- Pending-M withholding precedes the selected signature lookup in both cases.
#guard ((strict source "route").run 13000000).2 == ((strict source "missing").run 13000000).2

private def sharedStrict : WorkM Bool := do
  let checked ← RuntimeBodyDiscovery.readSource (artifact noAssertion) "main" "route" {}
  let prepared := checked.preparation
  return prepared.pending.entries.all (fun entry => !entry.unconsumed) &&
    prepared.signature.original.source == checked.signature.original.source &&
    prepared.body.checked.signature.original.source == checked.body.checked.signature.original.source
#guard sharedStrict.run 13000000 |>.1.toOption == some true

private def prepareOnly (missing extra wrongContext : Bool := false) : WorkM (List Nat) := do
  let artifact := artifact source
  let source ← RuntimeBodyDiscovery.prepareSource artifact "main" "route" {}
  let [.operation event] := source.body.checked.events | throw .request
  let some definition := source.catalogue.records.find? (fun body => body.name == "sign") | throw .request
  let some token := definition.definition.original.envelope.occurrence.body.head? | throw .request
  let phase : RuntimeContextRequest.Context := .mk [⟨token.span.startByte,0,1⟩] [] [] [] []
  let position : SourceSequence.Position := ⟨event.call.calleeOffset,0,1⟩
  let child : RuntimeContextRequest.Context := .mk [] [] [] [] [(.pure 1,phase)]
  let context : RuntimeContextRequest.Context := .mk [position] [] [(position,child)] [] []
  let reference : RuntimeProviderHeader.Request :=
    (.pure 2,if wrongContext then .mk [] [] [] [] [] else phase)
  let references := if missing then [] else if extra then [[reference],[]] else [[reference]]
  let prepared ← RuntimePreparedOperation.prepare artifact source context references
  return prepared.roots

-- The real provider and reference use separate requests/subjects while sharing
-- the original source; this remains preparation and checks no graph root.
#guard (prepareOnly false).run 13000000 |>.1.toOption == some [0,1,2]
#guard (match (prepareOnly true).run 13000000 with | (.error .request,_) => true | _ => false)
#guard (match (prepareOnly false true).run 13000000 with | (.error .request,_) => true | _ => false)
#guard (match (prepareOnly false false true).run 13000000 with | (.error .request,_) => true | _ => false)

end QleisliKernel.Tests.RuntimePreparedSource
