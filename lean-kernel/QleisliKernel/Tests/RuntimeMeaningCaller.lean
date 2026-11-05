import QleisliKernel.Qirf.RuntimeMeaningCaller
import QleisliKernel.Tests.RuntimePreparedSource

/-! Original direct checked operation with independently replaceable caller,
provider and reference programs. Each run uses one work budget and one graph.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.RuntimeMeaningCaller
open QleisliKernel Finite SourceTypes Qirf

private abbrev source := RuntimePreparedSource.source
private def port (token : Nat) : Semantics.Raw.Port := ⟨token,[0],1⟩
private def program (op : Option Semantics.Raw.Op) : Semantics.Observation.Program :=
  ⟨[port 0],[],op.toList.map .pure,[if op.isSome then 1 else 0],[],.unitary⟩

private inductive Fault where
  | none | falseMeaning | omittedCallerPhase | staleProviderOffset | missingReference | extraReference | staleReturn
  deriving BEq

private def inspect (fault : Fault) (throughCaller : Bool) : WorkM (List Nat) := do
  let z := program (some (.gate .z 0 1))
  let caller := if fault == .omittedCallerPhase then program (some (.applyUnitary 0 1 [])) else z
  let text := if fault == .falseMeaning then source.replace "reference(sign)" "reference(keep)" else source
  let reference := if fault == .falseMeaning then program none else z
  let artifact : Artifact := ⟨#[caller,z,reference],#[],#[("main",text)],0,none⟩
  let original ← RuntimeBodyDiscovery.prepareSource artifact "main" "route" {}
  -- Byte offsets in the preserved original text, separately checked by both
  -- source readers. A provider cannot borrow the caller's position.
  let pos : SourceSequence.Position := ⟨203,0,1⟩
  let empty : RuntimeContextRequest.Context := .mk [] [] [] [] []
  let phase (offset : Nat) : RuntimeContextRequest.Context := .mk [⟨offset,0,1⟩] [] [] [] []
  let provider := phase (if fault == .staleProviderOffset then 203 else 63)
  let child : RuntimeContextRequest.Context := .mk [] [] [] [] [(.pure 1,provider)]
  let calls : RuntimeContextRequest.Context := .mk [pos] [] [(pos,child)] [] []
  let ref : RuntimeProviderHeader.Request := (.pure 2,if fault == .falseMeaning then empty else phase 63)
  let references := if fault == .missingReference then [] else if fault == .extraReference then [ref,ref] else [ref]
  let op ← RuntimePreparedOperation.prepare artifact original calls [references]
  let fresh ← RuntimePreparedOperation.prepareRoot op #[0,1,2]
  if !throughCaller then
    let checked ← RuntimePreparedOperation.read op fresh.root
    return [checked.subject.action.rows,checked.specification.action.cols]
  let owner := Semantics.RuntimeType.owner [.bit]
  let returned := port (if fault == .staleReturn then 0 else 1)
  let runtime : RuntimeFamily.Request := ⟨.exported,"main","route",[owner],[[.quantum ⟨port 0,[.bit]⟩]],
    [[]],owner,[.quantum ⟨returned,[.bit]⟩],.unitary,{}⟩
  let checked ← RuntimeMeaningCaller.read op fresh runtime
  return [checked.operation.subject.action.rows,checked.operation.specification.action.cols] ++
    checked.moved.after.bindings.map (·.port.token)

private def run (fault : Fault) (throughCaller := true) := ((inspect fault throughCaller).run 10000000).1

#guard (run .none).toOption == some [2,2,1]
#guard (run .omittedCallerPhase false).toOption == some [2,2]
#guard [Fault.falseMeaning,.omittedCallerPhase].all fun fault =>
  match run fault with | .error .equation => true | _ => false
#guard [Fault.staleProviderOffset,.missingReference,.extraReference,.staleReturn].all fun fault =>
  match run fault with | .error .request => true | _ => false

end QleisliKernel.Tests.RuntimeMeaningCaller
