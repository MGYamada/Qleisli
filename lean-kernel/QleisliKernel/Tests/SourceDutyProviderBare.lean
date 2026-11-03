import QleisliKernel.Qirf.SourceDutyProviderHeader

/-! Bare original supplier controls. The first direct/transitive strings are
the frozen sources used by the external before-observer. These are source and
artifact-header preparation tests; body/IR/path/Meaning equations are not
discharged. Refusals describe the explicit preparatory subset, not the language.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.SourceDutyProviderBare
open QleisliKernel Finite SourceTypes

private def directA : String := "#![no_implicit_prelude]\npub enum Tag { A, B }\nunitary fn sign(q: Q<Bit>) -> Q<Bit> { phase[1,1](q) }\npub unitary fn direct[const unused: Nat](s: Q<Tag>, q: Q<Bit>) -> (Q<Tag>, Q<Bit>) {\n    b::choose[sign](s, q)\n}\nfn main() -> Unit { () }\n"
private def transitiveA : String := "#![no_implicit_prelude]\npub enum Tag { A, B }\nunitary fn sign(q: Q<Bit>) -> Q<Bit> { phase[1,1](q) }\npub unitary fn transitive[const unused: Nat](s: Q<Tag>, q: Q<Bit>) -> (Q<Tag>, Q<Bit>) {\n    b::forward[sign](s, q)\n}\nfn main() -> Unit { () }\n"
private def sourceB : String := "#![no_implicit_prelude]\npub unitary fn choose[const U: Op<Bit>](s: Q<a::Tag>, q: Q<Bit>) -> (Q<a::Tag>, Q<Bit>)\n    requires Applicable(U), Controllable(U) {\n    qmatch(s, q) { a::Tag::A => U, a::Tag::B => U }\n}\npub unitary fn forward[const V: Op<Bit>](s: Q<a::Tag>, q: Q<Bit>) -> (Q<a::Tag>, Q<Bit>)\n    requires Applicable(V), Controllable(V) {\n    choose[V](s, q)\n}\n"

private def spare := "#![no_implicit_prelude]\nunitary fn unused(q:Q<Bit>)->Q<Bit>{q}\n"

private def artifact (sourceA sourceB : String) (unit : Bool) : Qirf.Artifact :=
  let bits := if unit then 0 else 1
  let circuit := if unit then Semantics.Observation.Op.pure (.applyUnitary 0 1 [⟨[],.monomial [] [0] [1]⟩])
    else .pure (.gate .z 0 1)
  let program : Semantics.Observation.Program :=
    ⟨[⟨0,List.range bits,bits⟩],[],[circuit],[1],[],.unitary⟩
  ⟨#[program],#[],#[("a",sourceA),("b",sourceB),("spare",spare)],0,none⟩

private def item (artifact : Qirf.Artifact) {catalogue : GenericCatalogue.Checked artifact.sources}
    (queue : GenericDutyQueue.Checked catalogue) (wanted : String) (strict : Bool)
    (expected : Semantics.FiniteCarrier.Basis) (original : GenericDutyQueue.Item catalogue) :
    Qirf.SourceDutySlots.ItemExpectation queue original → WorkM (List (Nat × Bool)) :=
  match original with
  | .demand invocation _ => fun plan => do
    let some root := catalogue.records[invocation.id.root]? | throw .request
    if root.name != wanted then return []
    plan.providers.mapM fun provider => do
      let prepared ← if strict then Qirf.SourceDutyProviderFresh.read provider.2
        else Qirf.SourceDutyProviderFresh.readBare provider.2
      let bound ← Qirf.SourceDutyProviderHeader.read artifact prepared (.pure 0,.mk [] [] [] [] [])
      let native := prepared.original.supplied.provider
      let body := prepared.original.body.checked
      let authenticated := match prepared.provenance with
        | .fresh _ => false
        | .bare source =>
          source.supplier.original.entry.body.owner == "a" &&
          source.supplier.original.entry.body.name == wanted &&
          !source.supplier.original.entry.body.definition.original.header.formals.isEmpty &&
          source.duty.entry.body.owner == "b" && source.calls.rows.any (fun row => row.1 == "b")
      return (invocation.depth,authenticated && !native.signature.original.declaration.isPublic &&
        decide (prepared.original.supplied.context = .source "a") &&
        native.signature.inputs == [expected] && native.signature.outputs == [expected] &&
        decide (body.signature.parameters.map (·.tree) = [Semantics.RuntimeType.owner expected]) &&
        decide (body.signature.result.tree = Semantics.RuntimeType.owner expected) &&
        native.signature.staticArguments.bases.isEmpty && native.signature.staticArguments.naturals.isEmpty &&
        prepared.original.supplied.arguments.actuals.isEmpty && body.events.length == 1 &&
        bound.rows.any (fun row => row.1 == "a") && bound.rows.any (fun row => row.1 == "b") &&
        !bound.rows.any (fun row => row.1 == "spare"))
  | .header .. | .call .. | .pendingRecursion .. => fun _ => pure []

private def prepare (sourceA sourceB wanted : String) (strict : Bool := false) (unit : Bool := false) :
    WorkM (List (Nat × Bool)) := do
  let artifact := artifact sourceA sourceB unit
  let catalogue ← GenericCatalogue.read artifact.sources
  let queue ← GenericDutyQueue.read catalogue
  let plan ← Qirf.SourceDutySlots.read queue
  let expected := if unit then [.unit] else [.bit]
  let rows ← plan.entries.mapM fun entry =>
    item artifact queue wanted strict expected entry.subject entry.subjectExpectation
  return rows.flatten

-- Private a::sign is forwarded through the actual b::choose header, then
-- appears at both written arm occurrences. Every occurrence remains separate.
#guard (prepare directA sourceB "direct").run 10000000 |>.1.toOption ==
  some [(1,true),(1,true),(1,true)]

-- The original a::transitive supplier survives both actual call edges. No
-- lookup of private a::sign under b's later body context is attempted.
#guard (prepare transitiveA sourceB "transitive").run 10000000 |>.1.toOption ==
  some [(1,true),(2,true),(2,true),(2,true)]

-- The old strict reader is still independently refusing the frozen cases.
#guard (match (prepare directA sourceB "direct" true).run 10000000 with
  | (.error .request,_) => true | _ => false)
#guard (match (prepare transitiveA sourceB "transitive" true).run 10000000 with
  | (.error .request,_) => true | _ => false)

-- Q<Unit> retains its real logical owner and original scalar phase event.
private def unitA := directA.replace "Bit" "Unit" |>.replace "phase[1,1](q)" "global_phase_eighth(q)"
private def unitB := sourceB.replace "Bit" "Unit"
#guard (prepare unitA unitB "direct" false true).run 10000000 |>.1.toOption ==
  some [(1,true),(1,true),(1,true)]

private def bareSyntaxItem {sources catalogue} (queue : @GenericDutyQueue.Checked sources catalogue)
    (wanted : String) (original : GenericDutyQueue.Item catalogue) :
    Qirf.SourceDutySlots.ItemExpectation queue original → WorkM (List Bool) :=
  match original with
  | .demand invocation _ => fun plan => do
    let some root := catalogue.records[invocation.id.root]? | throw .request
    if root.name != wanted then return []
    return plan.providers.map fun provider => match provider.2.written with | .name _ => true | .application _ => false
  | .header .. | .call .. | .pendingRecursion .. => fun _ => pure []

private def bareSyntax (source : String) : WorkM (List Bool) := do
  let catalogue ← GenericCatalogue.read #[("a",source),("b",sourceB)]
  let queue ← GenericDutyQueue.read catalogue
  let plan ← Qirf.SourceDutySlots.read queue
  let rows ← plan.entries.mapM fun entry => bareSyntaxItem queue "direct" entry.subject entry.subjectExpectation
  return rows.flatten

private def bracketed := directA.replace "choose[sign]" "choose[sign[]]"
-- The shared original type/queue/slot readers still admit this written form;
-- explicit empty brackets do not become a bare name in this preparation.
#guard (bareSyntax bracketed).run 10000000 |>.1.toOption == some [false,false,false]
#guard (match (prepare bracketed sourceB "direct").run 10000000 with
  | (.error .request,_) => true | _ => false)

private def specialized := directA.replace "fn sign(" "fn sign[const n:Nat](" |>.replace "choose[sign]" "choose[sign[0]]"
#guard (bareSyntax specialized).run 10000000 |>.1.toOption == some [false,false,false]
#guard (match (prepare specialized sourceB "direct").run 10000000 with
  | (.error .request,_) => true | _ => false)

-- An introduced ordinary local is supported by the source language, but this
-- initial-scope-only bridge does not invent a receipt for its captured scope.
private def localScope := directA.replace "    b::choose" "    let token = (); b::choose"
#guard (match (prepare localScope sourceB "direct").run 10000000 with
  | (.error .request,_) => true | _ => false)

end QleisliKernel.Tests.SourceDutyProviderBare
