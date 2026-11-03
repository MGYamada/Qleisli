import QleisliKernel.Qirf.SourceDutyProviderFresh

/-! Fresh-source preparation controls. These retain actual source readers and
typed owner boundaries; no quantum IR, native equation, path or accepted handle
is constructed. Refusals describe this preparatory subset, not language bans.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.SourceDutyProviderFresh
open QleisliKernel Finite SourceTypes

private def prepareItem {sources catalogue} (queue : @GenericDutyQueue.Checked sources catalogue)
    (expected : Semantics.FiniteCarrier.Basis) (item : GenericDutyQueue.Item catalogue) :
    Qirf.SourceDutySlots.ItemExpectation queue item → WorkM (List Bool) :=
  match item with
  | .demand _ _ => fun plan => plan.providers.mapM fun provider => do
    let prepared ← Qirf.SourceDutyProviderFresh.read provider.2
    let native := prepared.original.supplied.provider
    let body := prepared.original.body.checked
    return native.signature.inputs == [expected] && native.signature.outputs == [expected] &&
      decide (body.signature.parameters.map (·.tree) = [Semantics.RuntimeType.owner expected]) &&
      decide (body.signature.result.tree = Semantics.RuntimeType.owner expected) &&
      body.summary.inferredEffect == .unitary && body.summary.generic.inferredEffect == .unitary &&
      prepared.original.supplied.arguments.actuals.isEmpty && body.events.length == 1
  | .header .. | .call .. | .pendingRecursion .. => fun _ => pure []

private def prepare (source : String) (expected : Semantics.FiniteCarrier.Basis) : WorkM (List Bool) := do
  let catalogue ← GenericCatalogue.read #[("main",source)]
  let queue ← GenericDutyQueue.read catalogue
  let plan ← Qirf.SourceDutySlots.read queue
  let rows ← plan.entries.mapM fun entry => prepareItem queue expected entry.subject entry.subjectExpectation
  return rows.flatten

private def bitSource := "#![no_implicit_prelude]\n" ++
  "pub enum Tag{A,B}\n" ++
  "unitary fn leaf(q:Q<Bit>)->Q<Bit>{phase[1,1](q)}\n" ++
  "unitary fn route(s:Q<Tag>,q:Q<Bit>)->(Q<Tag>,Q<Bit>){" ++
  "qmatch(s,q){Tag::A=>leaf,Tag::B=>leaf}}\n"

-- Both written arm occurrences produce their own real provider instance and
-- exact original leaf body. No equal-name or equal-matrix slot is shared.
#guard (prepare bitSource [.bit]).run 10000000 |>.1.toOption == some [true,true]

private def unitSource := "#![no_implicit_prelude]\n" ++
  "pub enum Tag{A,B}\n" ++
  "unitary fn leaf(q:Q<Unit>)->Q<Unit>{global_phase_eighth(q)}\n" ++
  "unitary fn route(s:Q<Tag>,q:Q<Unit>)->(Q<Tag>,Q<Unit>){" ++
  "qmatch(s,q){Tag::A=>leaf,Tag::B=>leaf}}\n"

-- Zero physical width preserves the Q<Unit> input/result owner and its scalar
-- phase source event. This control performs source preparation only.
#guard (prepare unitSource [.unit]).run 10000000 |>.1.toOption == some [true,true]

private def genericSource := bitSource.replace "unitary fn route(" "unitary fn route[const n:Nat]("

-- An unrelated unused Nat is not silently assigned a value. Such enclosing
-- originals need the separate general supplier/instance continuation.
#guard (match (prepare genericSource [.bit]).run 10000000 with | (.error .request,_) => true | _ => false)

private def forwardedSource := "#![no_implicit_prelude]\n" ++
  "unitary fn leaf(q:Q<Bit>)->Q<Bit>{phase[1,1](q)}\n" ++
  "unitary fn invoke[const U:Op<Bit>](q:Q<Bit>)->Q<Bit> requires Applicable(U){U(q)}\n" ++
  "unitary fn route(q:Q<Bit>)->Q<Bit>{invoke[leaf](q)}\n"

-- The closed leaf at an expanded callee header still has a real call chain.
-- A copied provider name cannot turn that forwarding into a fresh occurrence.
#guard (match (prepare forwardedSource [.bit]).run 10000000 with | (.error .request,_) => true | _ => false)

private def groupSource := "#![no_implicit_prelude]\n" ++
  "unitary fn leaf(q:Q<Bit>)->Q<Bit>{phase[1,1](q)}\n" ++
  "unitary fn route(q:Q<Bit>)->Q<Bit>{adjoint(leaf)(q)}\n"

-- Even this unary example retains its original runtime-group application.
-- The preparatory Op leaf route does not reinterpret it as a packed group.
#guard (match (prepare groupSource [.bit]).run 10000000 with | (.error .request,_) => true | _ => false)

end QleisliKernel.Tests.SourceDutyProviderFresh
