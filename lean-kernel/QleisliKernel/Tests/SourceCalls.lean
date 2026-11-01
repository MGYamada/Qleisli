import QleisliKernel.Tests.SourceTraceOriginals
import QleisliKernel.SourceTypes.SourceTrace

/-! Original named calls, body-derived owner return, exact static actuals and
public effects. These are small component checks, not source-preservation proofs.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.SourceCalls
open QleisliKernel QleisliKernel.SourceTypes QleisliKernel.Semantics.SourceOwners

private def sources (source : String) : Sources :=
  #[("main",source)] ++ SourceTraceOriginals.bundled

private def read (source : String) :=
  ((SourceTrace.read (sources source) "main" "route").run 2000000000).1.toOption

private def order (source : String) : Option (List Nat) :=
  (read source).map fun checked => (valueOwners checked.result.value).map (·.ordinal)

private def single (body : String) : String :=
  "pub unitary fn route(q:Q<Bit>)->Q<Bit>{" ++ body ++ "}"

private def exchange :=
  "unitary fn exchange(a:Q<Bit>,b:Q<Bit>)->(Q<Bit>,Q<Bit>){(b,h(a))}" ++
  "pub unitary fn route(a:Q<Bit>,b:Q<Bit>)->(Q<Bit>,Q<Bit>){exchange(a,b)}"

#guard order exchange = some [1,0]
#guard ((read exchange).map fun checked => checked.result.events.all fun event => match event with
  | .named named => named.functionName == "exchange" &&
    named.inputOwners.map (·.ordinal) == [0,1] && named.outputOwners.map (·.ordinal) == [1,0]
  | _ => false) = some true

private def zero :=
  "unitary fn exchange(a:Q<Unit>,b:Q<Unit>)->(Q<Unit>,Q<Unit>){(b,global_phase_eighth(a))}" ++
  "pub unitary fn route(a:Q<Unit>,b:Q<Unit>)->(Q<Unit>,Q<Unit>){exchange(a,b)}"
#guard order zero = some [1,0]

private def nested :=
  "unitary fn exchange(a:Q<Bit>,b:Q<Bit>)->(Q<Bit>,Q<Bit>){(b,a)}" ++
  "pub unitary fn route(u:Q<Unit>,a:Q<Bit>,b:Q<Bit>)->(Q<Unit>,(Q<Bit>,Q<Bit>)){" ++
  "(u,exchange(h(a),phase[1,1](b)))}"
#guard order nested = some [0,2,1]
#guard ((read nested).map fun checked => checked.result.events.map fun event => match event with
  | .primitive primitive => (primitive.kind.name,primitive.held.map (·.ordinal))
  | .phase phase => ("phase",phase.held.map (·.ordinal))
  | .named named => (named.functionName,named.held.map (·.ordinal))
  | .operation operation => ("operation",operation.held.map (·.ordinal))
  | .selection .. => ("qmatch",[])) = some [("h",[0]),("phase",[0,1]),("exchange",[0])]

-- Caller expression depth cannot cap the complete original callee body.
private def longBody := "unitary fn long(q:Q<Bit>)->Q<Bit>{" ++
  String.join (List.replicate 129 "let q=h(q);") ++ "q}" ++ single "long(q)"
#guard order longBody = some [0]

private def cycle := "unitary fn first(q:Q<Bit>)->Q<Bit>{second(q)}" ++
  "unitary fn second(q:Q<Bit>)->Q<Bit>{first(q)}" ++ single "first(q)"
#guard match ((SourceTrace.read (sources cycle) "main" "route").run 2000000000).1 with
  | .error .request => true | _ => false

-- Same-original-module inference is precise, even for public conservative APIs.
#guard order ("pub observe fn conservative(q:Q<Bit>)->Q<Bit>{h(q)}" ++
  single "conservative(q)") = some [0]

private def external (effect : String) (body : String) :=
  #[ ("main","use lib::conservative;pub " ++ effect ++
      " fn route(q:Q<Bit>)->Q<Bit>{conservative(q)}"),
     ("lib","pub observe fn conservative(q:Q<Bit>)->Q<Bit>{" ++ body ++ "}") ] ++
    SourceTraceOriginals.bundled
#guard ((SourceTrace.read (external "unitary" "h(q)") "main" "route").run 2000000000).1.toOption.isNone
#guard ((SourceTrace.read (external "observe" "h(q)") "main" "route").run 2000000000).1.isOk

-- Neither missing returns nor nominally foreign equal-width owners transport.
#guard (read ("unitary fn lose(a:Q<Bit>,b:Q<Bit>)->Q<Bit>{a}" ++
  "pub unitary fn route(a:Q<Bit>,b:Q<Bit>)->Q<Bit>{lose(a,b)}")).isNone
#guard (read ("pub enum E{A,B}unitary fn f(q:Q<E>)->Q<E>{q}" ++ single "f(q)")).isNone
#guard (read ("unitary fn f(q:Q<Bit>)->Q<Bit>{q}" ++ single "f(q,q)")).isNone
#guard (read ("unitary fn f(q:Q<Bit>)->Q<Bit>{q}" ++ single "let f=q;f(f)")).isNone

-- Unused actuals still appear in the complete original static application.
private def generic := "unitary fn id[const A:Basis,const n:Nat](q:Q<A>)->Q<A>{q}" ++
  single "id[type(Bit),3](q)"
#guard order generic = some [0]
#guard (read (generic.replace "type(Bit),3" "type(Bit)")).isNone

private def formal := "unitary fn keep(q:Q<Bit>)->Q<Bit>{q}" ++
  "unitary fn apply[const U:Op<Bit>](q:Q<Bit>)->Q<Bit> requires Applicable(U){U(q)}" ++
  single "apply[keep](q)"
#guard order formal = some [0]
#guard (read (formal.replace " requires Applicable(U)" "")).isNone
#guard order (single "adjoint(h)(q)") = some [0]
#guard order ("pub unitary fn route(c:Q<Bit>,q:Q<Bit>)->(Q<Bit>,Q<Bit>){controlled(h)(c,q)}") = some [0,1]
#guard order "pub unitary fn route(u:Q<Unit>)->Q<Unit>{adjoint(global_phase_eighth)(u)}" = some [0]
#guard (read "pub unitary fn route(u:Q<Unit>)->Q<Unit>{adjoint(h)(u)}").isNone
#guard (read (single "power(h,2)(q)")).isNone

private def formalArms := "unitary fn keep(q:Q<Bit>)->Q<Bit>{q}" ++
  "unitary fn choose[const U:Op<Bit>](s:Q<Bit>,q:Q<Bit>)->(Q<Bit>,Q<Bit>)" ++
  " requires Controllable(U){qmatch(s,q){0=>U,1=>U}}" ++
  "pub unitary fn route(s:Q<Bit>,q:Q<Bit>)->(Q<Bit>,Q<Bit>){choose[keep](s,q)}"
#guard order formalArms = some [0,1]
#guard (read ((formalArms.replace "choose[const U:Op<Bit>](s:" "choose[const U:Op<Bit>](U:").replace
  "{qmatch(s,q)" "{qmatch(U,q)")).isNone

#print axioms QleisliKernel.SourceTypes.SourceTrace.readNamedSource
#print axioms QleisliKernel.SourceTypes.SourceCalls.transport
#print axioms QleisliKernel.SourceTypes.SourceEffect.unitary_permits
end QleisliKernel.Tests.SourceCalls
