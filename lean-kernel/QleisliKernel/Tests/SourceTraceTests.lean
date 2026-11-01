import QleisliKernel.SourceTypes.SourceTrace
import QleisliKernel.Tests.SourceTraceOriginals

/-! Small source-only observations with original programs and fault controls.
All quantum tests use at most four physical bits; no Raw acceptance is invoked.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.SourceTraceTests
open QleisliKernel.SourceTypes
open QleisliKernel QleisliKernel.SourceTypes QleisliKernel.Semantics.SourceOwners
open QleisliKernel.SourceTypes.SourceTrace QleisliKernel.Tests.SourceTraceOriginals

private structure EventView where
  operation : String
  selected : List Nat
  held : List Nat
  frame : List Nat
  deriving BEq, DecidableEq, Repr

private def ordinals (owners : List Owner) : List Nat := owners.map (·.ordinal)
private def sorted (owners : List Owner) : List Nat := (ordinals owners).mergeSort (· ≤ ·)

private def eventView {sources caller} : Event sources caller → EventView
  | .selection event held _ _ =>
    ⟨"qmatch",[event.selector.ordinal,event.target.ordinal],ordinals held,sorted (held ++ owners event.before)⟩
  | .primitive event =>
    ⟨event.kind.name,[event.operand.ordinal],ordinals event.held,sorted (event.held ++ owners event.before)⟩

private def sources (source : String) : Sources := #[ ("main",source) ] ++ bundled
private def result (source : String) :=
  ((read (sources source) "main" "route").run 2000000000).1.toOption
private def view (source : String) : Option (List EventView × List Nat) :=
  (result source).map fun checked =>
    (checked.result.events.map eventView,ordinals (valueOwners checked.result.value))
private def rejected (source : String) : Bool := (result source).isNone

-- The five currently supported original programs are consumed byte-for-byte.
#guard view structural_control = some ([⟨"qmatch",[0,1],[],[0,1]⟩],[0,1])
#guard view multiple_selections = some
  ([⟨"qmatch",[0,1],[],[0,1]⟩,⟨"qmatch",[0,1],[],[0,1]⟩],[0,1])
#guard view prefix_target = some ([⟨"h",[1],[],[0,1]⟩,⟨"qmatch",[0,1],[],[0,1]⟩],[0,1])
#guard view prefix_spectator = some
  ([⟨"h",[0],[],[0,1,2]⟩,⟨"qmatch",[1,2],[],[0,1,2]⟩],[1,2,0])
#guard view suffix_target = some ([⟨"qmatch",[0,1],[],[0,1]⟩,⟨"h",[1],[0],[0,1]⟩],[0,1])
#guard rejected ordinary_spectator -- requires actual ordinary-value signature/storage support
#guard rejected hidden_observe_negative -- refusal is not a general public-effect preservation proof

private def single (body : String) : String :=
  "pub unitary fn route(q:Q<Bit>)->Q<Bit>{" ++ body ++ "}"
private def pair (body : String) : String :=
  "pub unitary fn route(a:Q<Bit>,b:Q<Bit>)->(Q<Bit>,Q<Bit>){" ++ body ++ "}"
private def zeroSpectator (body : String) : String :=
  "pub unitary fn route(u:Q<Unit>,q:Q<Bit>)->(Q<Unit>,Q<Bit>){" ++ body ++ "}"

#guard view (single "h(h(q))") = some ([⟨"h",[0],[],[0]⟩,⟨"h",[0],[],[0]⟩],[0])
#guard ((result (single "h(h(q))")).map fun checked =>
  match checked.callOffsets with | [inner,outer] => inner > outer | _ => false) = some true
#guard view (pair "(h(a),h(b))") = some
  ([⟨"h",[0],[],[0,1]⟩,⟨"h",[1],[0],[0,1]⟩],[0,1])
#guard view (zeroSpectator "(u,h(q))") = some ([⟨"h",[1],[0],[0,1]⟩],[0,1])
#guard view "pub unitary fn route(u:Q<Unit>)->Q<Unit>{global_phase_eighth(u)}" =
  some ([⟨"global_phase_eighth",[0],[],[0]⟩],[0])
#guard view (zeroSpectator "(global_phase_eighth(u),h(q))") = some
  ([⟨"global_phase_eighth",[0],[],[0,1]⟩,⟨"h",[1],[0],[0,1]⟩],[0,1])
#guard view (single "((h(q)))") = some ([⟨"h",[0],[],[0]⟩],[0])
#guard view (single "let (q,)=(h(q),);q") = some ([⟨"h",[0],[],[0]⟩],[0])
#guard rejected (single "(h(q),)") -- singleton tuple is not a quantum owner
#guard rejected (pair "(h(a),h(a))")
#guard rejected (zeroSpectator "h(q)")
#guard rejected (zeroSpectator "let _=u;(u,h(q))")
#guard rejected "pub unitary fn route(u:Q<Unit>)->Q<Unit>{h(u)}"
#guard rejected "pub enum Tag{A,B} pub unitary fn route(q:Q<Tag>)->Q<Tag>{h(q)}"
#guard rejected (pair "h((a,b))")
#guard rejected (pair "global_phase_eighth(a,b)")

-- Lexical scope outlives owner consumption and takes precedence over primitives.
#guard rejected "pub unitary fn route(h:Q<Unit>,q:Q<Bit>)->(Q<Unit>,Q<Bit>){let u=h;(u,h(q))}"
#guard rejected (single "let h=q;h(h)")
#guard rejected ("unitary fn h(q:Q<Bit>)->Q<Bit>{q}" ++ single "h(q)")
#guard rejected ("unitary fn f(q:Q<Bit>)->Q<Bit>{q}" ++ single "f(q)")
#guard rejected (single "power(h,2)(q)")
#guard rejected (single "phase[1,1](q)")
#guard rejected (single "h(q);q")
#guard rejected (single "h(q);f(q)")
#guard rejected (single "measure_z(q)")
#guard rejected (single "h(q,q)")
#guard rejected (single "h()")
#guard rejected (single "h(_)" )
#guard ((result "pub observe fn route(q:Q<Bit>)->Q<Bit>{h(q)}").map fun checked =>
  checked.signature.original.parsedHeader.effect) = some (some .observe)
#guard rejected "pub fn route(q:Q<Bit>)->Q<Bit>{h(q)}"

-- Tuple segmentation must not split the commas in an existing qmatch arm table.
private def nestedQmatch :=
  "pub enum Tag{A,B} unitary fn keep(q:Q<Bit>)->Q<Bit>{q}" ++
  "pub unitary fn route(u:Q<Unit>,s:Q<Tag>,q:Q<Bit>)->(Q<Unit>,Q<Tag>,Q<Bit>){" ++
  "let (u,(s,q))=(u,qmatch(s,q){Tag::B=>keep,Tag::A=>keep});(u,s,q)}"
#guard view nestedQmatch = some ([⟨"qmatch",[1,2],[0],[0,1,2]⟩],[0,1,2])
#guard rejected
  "pub enum Tag{A,B} unitary fn keep(q:Q<Bit>)->Q<Bit>{q} pub unitary fn route(s:Q<Tag>,q:Q<Bit>)->(Q<Tag>,Q<Bit>){qmatch(s,h(q)){Tag::A=>keep,Tag::B=>keep}}"

-- Arm bodies are not validated here. Persistent lexical names do prevent
-- a consumed local from being resolved as a global function in an arm.
private def shadowedArm :=
  "pub enum Tag{A,B} unitary fn turn(q:Q<Bit>)->Q<Bit>{q}" ++
  "pub unitary fn route(turn:Q<Unit>,s:Q<Tag>,q:Q<Bit>)->(Q<Unit>,Q<Tag>,Q<Bit>){" ++
  "let u=turn;let(s,q)=qmatch(s,q){Tag::A=>turn,Tag::B=>turn};(u,s,q)}"
#guard rejected shadowedArm
#guard ((result (shadowedArm.replace "=>turn" "=>main::turn")).map fun checked =>
  checked.result.events.all fun event => match event with
  | .selection original _ scope _ => scope.contains "turn" && original.scope == scope
  | .primitive _ => false) = some true

-- One-qubit sequential call count is deliberately beyond 128. The historical
-- qmatch-site limit must not become a total-expression or total-call limit.
private def manyCalls := single (String.join (List.replicate 129 "let q=h(q);") ++ "q")
#guard ((result manyCalls).map fun checked =>
  (checked.result.events.length,checked.result.events.filterMap Event.qmatchOffset)) = some (129,[])

-- Opt-out disables only derived-prelude lookup, never bare language primitives.
-- The former reader limitation is retained in module-header-first.json and Git.
#guard view ("#![no_implicit_prelude]\n" ++ single "h(q)") =
  some ([⟨"h",[0],[],[0]⟩],[0])
#guard rejected ("#![no_implicit_prelude]\n#![no_implicit_prelude]\n" ++ single "h(q)")
#guard rejected (single "h(q)" ++ "#![no_implicit_prelude]\n")
#guard rejected ("#![no_implicit_prelude]\nunitary fn h(q:Q<Bit>)->Q<Bit>{q}" ++ single "h(q)")

#print axioms QleisliKernel.SourceTypes.SourceSyntax.read
#print axioms QleisliKernel.SourceTypes.SourceTrace.read
#print axioms QleisliKernel.SourceTypes.SourceTrace.Checked.allOriginalQmatches
#print axioms QleisliKernel.SourceTypes.SourceTrace.Checked.allOriginalCalls
#print axioms QleisliKernel.SourceTypes.SourceTrace.Checked.completeOwnerReturn
#print axioms QleisliKernel.SourceTypes.SourceTrace.PrimitiveEvent.originalTokens
#print axioms QleisliKernel.SourceTypes.SourceTrace.PrimitiveEvent.hRequiresBit

end QleisliKernel.Tests.SourceTraceTests
