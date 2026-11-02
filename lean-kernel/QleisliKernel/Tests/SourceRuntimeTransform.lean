import QleisliKernel.SourceTypes.SourceRuntimeTrace
import QleisliKernel.Tests.SourceTraceOriginals

/-! Small direct-transform runtime groups. Original provider returns and nested
owner trees remain distinct from static unary operation descriptions. These
source checks do not replace native transformed-operator equations.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.SourceRuntimeTransform
open QleisliKernel QleisliKernel.SourceTypes
open SourceRuntimeValues SourceRuntimeContext

private def sources (source : String) : Sources :=
  #[("main",source)] ++ SourceTraceOriginals.bundled

private def read (source : String) :=
  ((SourceTypes.SourceRuntimeTrace.read (sources source) "main" "route").run 2000000000).1.toOption

private def view (source : String) := (read source).map fun checked =>
  ((valueOwners checked.summary.value).map (·.ordinal),
    checked.summary.consumed.map (·.ordinal),checked.summary.inferredEffect)

private def permutation :=
  "unitary fn f(a:Q<Bit>,b:Q<Bit>)->(Q<Bit>,Q<Bit>){(b,h(a))}" ++
  "pub unitary fn route(a:Q<Bit>,b:Q<Bit>)->(Q<Bit>,Q<Bit>){adjoint(f)((a,b))}"

#guard view permutation = some ([2,3],[0,1],.unitary)
#guard ((read permutation).map fun checked => checked.events.all fun event => match event with
  | .transform event =>
    (valueOwners event.forward.value).map (·.ordinal) == [1,0] &&
      event.written.access == .adjoint && event.arguments.length == 1 && event.copies == 1
  | _ => false) = some true

private def controlled :=
  "unitary fn f(a:Q<Bit>,b:Q<Unit>)->(Q<Bit>,Q<Unit>){(h(a),b)}" ++
  "pub unitary fn route(c:Q<Bit>,a:Q<Bit>,b:Q<Unit>)->(Q<Bit>,(Q<Bit>,Q<Unit>)){controlled(f)(c,(a,b))}"
#guard view controlled = some ([0,3,4],[1,2],.unitary)
#guard (read (controlled.replace "controlled(f)(c,(a,b))" "controlled(f)(c,(b,a))")).isNone
#guard (read (controlled.replace "controlled(f)(c,(a,b))" "controlled(f)(c,(c,b))")).isNone

private def zeroPower :=
  "unitary fn f(a:Q<Bit>,b:Q<Unit>)->(Q<Bit>,Q<Unit>){(h(a),b)}" ++
  "pub unitary fn route(a:Q<Bit>,b:Q<Unit>)->(Q<Bit>,Q<Unit>){power(power(f,2),0)((a,b))}"
#guard view zeroPower = some ([2,3],[0,1],.unitary)
#guard ((read zeroPower).map fun checked => checked.events.all fun event => match event with
  | .transform event => event.copies == 0 && event.counts.map (·.checked.value) == [2,0]
  | _ => false) = some true
#guard (read ("use std::state::reset;" ++
  (zeroPower.replace "unitary fn f" "observe fn f").replace "(h(a),b)" "(reset(a),b)")).isNone

-- A same-original-module public prefix remains conservative; external use
-- keeps that public effect even when the original forward body is pure.
#guard view (permutation.replace "unitary fn f" "pub observe fn f") = some ([2,3],[0,1],.unitary)
private def external :=
  #[("main","use lib::f;pub unitary fn route(a:Q<Bit>,b:Q<Bit>)->(Q<Bit>,Q<Bit>){adjoint(f)((a,b))}"),
    ("lib","pub observe fn f(a:Q<Bit>,b:Q<Bit>)->(Q<Bit>,Q<Bit>){(b,h(a))}")] ++
    SourceTraceOriginals.bundled
#guard ((SourceTypes.SourceRuntimeTrace.read external "main" "route").run 2000000000).1.toOption.isNone

private def arrows :=
  "unitary fn f(q:Q<(Bit,Unit)>)->Q<(Unit,Bit)>{let(a,b)=split(q);join(b,a)}" ++
  "pub unitary fn route(q:Q<(Unit,Bit)>)->Q<(Bit,Unit)>{adjoint(f)(q)}"
#guard view arrows = some ([1],[0],.unitary)
#guard (read (arrows.replace "adjoint(f)(q)" "adjoint(power(f,0))(q)")).isNone

#guard (read "unitary fn f()->Unit{()}pub unitary fn route(q:Q<Unit>)->Q<Unit>{power(f,0)(q)}").isNone
#guard (read "unitary fn f(c:Bit,q:Q<Bit>)->(Bit,Q<Bit>){(c,q)}pub unitary fn route(c:Bit,q:Q<Bit>)->(Bit,Q<Bit>){power(f,0)((c,q))}").isNone
#guard view "unitary fn f(q:Q<Bits<0>>)->Q<Bits<0>>{global_phase_eighth(q)}pub unitary fn route(q:Q<Bits<0>>)->Q<Bits<0>>{power(f,0)(q)}" =
  some ([1],[0],.unitary)
#guard (SourceRuntimeTransformPorts.product [4294967295,2,0]).isError
#guard SourceRuntimeTransformPorts.product [4294967295,0] = .ok 0

-- A genuine primitive keeps its contextual unary rule.
#guard view "pub unitary fn route(q:Q<Bit>)->Q<Bit>{adjoint(h)(q)}" = some ([0],[],.unitary)

#print axioms QleisliKernel.SourceTypes.SourceRuntimeTransformPorts.read
#print axioms QleisliKernel.SourceTypes.SourceRuntimeTransformPorts.apply
#print axioms QleisliKernel.SourceTypes.SourceRuntimeTrace.readTransformSource
end QleisliKernel.Tests.SourceRuntimeTransform
