import QleisliKernel.Tests.RawTraceTests

/-! Existing exact phases through the common source and literal Raw readers.
All controls use one physical qubit. No native execution handle is supplied.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.PhaseSourceContext
open QleisliKernel QleisliKernel.Semantics QleisliKernel.Tests.RawTraceTests

def phase (exponent input output : Nat) : Observation.Op :=
  .pure (.applyUnitary input output [⟨[],.monomial [0] [0,1] [0,exponent]⟩])

def one (exponent : Nat) : Observation.Program :=
  ⟨[⟨10,[7],1⟩],[],[phase exponent 10 13],[13],[],.unitary⟩

def nested (exponent : Nat) : Observation.Program :=
  {one exponent with operations := [.pure (.gate .h 10 13),phase exponent 13 14],outputs := [14]}

def controls : List (String × Bool) := [
  ("phase retains its exact literal action",checks (single "phase[1,3](q)") (one 1) [1]),
  ("wrong relative phase refuses",!checks (single "phase[1,3](q)") (one 7) [1]),
  ("relative phase cannot become a global scalar",!checks (single "phase[1,3](q)")
    {one 1 with operations := [.pure (.applyUnitary 10 13 [⟨[],.monomial [] [0] [1]⟩])]} [1]),
  ("static alias parameters retain exact values",checks
    (single "static let j=2;static let k=4;phase[j,k](q)") (one 1) [1]),
  ("aliases may follow an ordinary owner binding",checks
    (single "static let j=1;let q=h(q);static let n=j+1;phase[n,3](q)") (nested 2) [1,1]),
  ("runtime arguments precede the outer phase interval",checks (single "phase[1,3](h(q))") (nested 1) [1,1]),
  ("phase cancellation cannot erase the original calls",!checks
    (single "phase[7,3](phase[1,3](q))") {one 1 with operations := [],outputs := [10]} []),
  ("unused overflowing initializer refuses",!checks
    (single "static let unused=(4294967295+1)-4294967295;phase[1,3](q)") (one 1) [1]),
  ("zero multiplication cannot hide overflow",!checks
    (single "phase[0*((3000000000+3000000000)-3000000000),3](q)") (one 0) [1]),
  ("noncanonical numerator refuses",!checks (single "phase[8,3](q)") (one 0) [1]),
  ("unsupported exact coefficient does not round",!checks (single "phase[1,4](q)") (one 1) [1]),
  ("static alias cannot reuse a consumed runtime name",!checks
    (single "let j=();let ()=j;static let j=1;phase[j,3](q)") (one 1) [1]),
  ("a runtime value cannot supply a static natural",!checks
    (single "let j=();phase[j,3](q)") (one 1) [1]),
  ("runtime owner cannot shadow an earlier static alias",!checks
    (single "static let j=1;let j=q;phase[j,3](j)") (one 1) [1]),
  ("unused static alias still blocks runtime shadowing",!checks
    (single "static let j=1;let j=q;phase[1,3](j)") (one 1) [1]),
  ("runtime tuple pattern cannot shadow a static alias",!checks
    (single "static let j=1;let(j,)=(q,);phase[j,3](j)") (one 1) [1]),
  ("ordinary Unit binder cannot shadow a static alias",!checks
    (single "static let j=1;let j=();phase[j,3](q)") (one 1) [1]),
  ("an event-free body cannot hide runtime shadowing",!checks
    (single "static let j=1;let j=q;j") {one 1 with operations := [],outputs := [10]} []),
  ("runtime owner rebinding preserves unrelated static aliases",checks
    (single "static let j=1;let q=h(q);phase[j,3](q)") (nested 1) [1,1]),
  ("lexical phase shadow cannot fall back to a primitive",!checks
    (single "static let phase=1;phase[1,3](q)") (one 1) [1]),
  ("a named phase function is not a primitive",!checks
    ("unitary fn phase(q:Q<Bit>)->Q<Bit>{q}" ++ single "phase[1,3](q)") (one 1) [1]),
  ("public Observe remains the outer contract",checks
    (single "phase[1,3](q)" "observe") {one 1 with effect := .observe} [1]),
  ("public Observe cannot sharpen to Unitary",!checks
    (single "phase[1,3](q)" "observe") (one 1) [1]),
  ("unsupported generic source cannot fabricate caller bindings",!checks
    "pub unitary fn route[const j:Nat](q:Q<Bit>)->Q<Bit>{phase[j,3](q)}" (one 1) [1])
]

#guard controls.all (·.2)

end QleisliKernel.Tests.PhaseSourceContext
