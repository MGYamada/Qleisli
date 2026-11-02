import QleisliKernel.SourceTypes.GenericTypeTrace
import QleisliKernel.SourceTypes.StaticRuntimeSignature

/-! Small whole-original-body type/effect studies. These retain exact expected
original effects, opaque types and pending finite obligations. They construct no
maximum quantum instance and grant no selected body/native capability.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.GenericTypeTrace
open SourceTypes Finite

private def summary (sources : Sources) (arguments : StaticTypes.Arguments := {}) :
    Option (Semantics.Raw.Effect × Bool × Nat × Nat) :=
  let action : WorkM (Semantics.Raw.Effect × Bool × Nat × Nat) := do
    let signature ← StaticRuntimeSignature.prepareWithArguments sources "main" "root" arguments
    let instantiation : StaticInstantiation.Checked signature.original := .static arguments signature.environment rfl
    let checked ← SourceTypes.GenericTypeTrace.readWithInstantiation instantiation
    pure (checked.inferredEffect,checked.quantumUse,checked.basisObligations.length,checked.recursiveCalls.length)
  (action.run 10000000).1.toOption

private def program (source : String) : Sources := #[("main","#![no_implicit_prelude] " ++ source)]

private def chosenBit : StaticTypes.Arguments := {bases := [("A",[.bit])]}

-- FiniteCarrier.children returns none for scalar LEAVES, not an invalid
-- prefix. Original ordinary values must retain those exact scalar codes.
#guard (GenericValues.ordinaryValue [.fixed .bit]).toOption = some [.ordinary [.fixed .bit]]
#guard (GenericValues.ordinaryValue [.fixed .unit]).toOption = some [.ordinary [.fixed .unit]]
#guard (GenericValues.ordinaryValue [.fixed .pair,.fixed .unit,.fixed .bit]).toOption =
    some [.tuple 2,.ordinary [.fixed .unit],.ordinary [.fixed .bit]]

#guard summary (program "pub unitary fn root[const A:Basis](q:Q<A>)->Q<A>{q}") chosenBit = some (.unitary,true,0,0)
#guard summary (program "pub unitary fn root[const A:Basis](q:Q<A>)->Q<A>{h(q)}") chosenBit = none
#guard summary (program "pub unitary fn root[const A:Basis](q:Q<A>)->(Q<Bit>,Q<Bit>){split(q)}")
    {bases := [("A",[.pair,.bit,.bit])]} = none

-- Both original static branches are checked under their own original guards.
#guard summary (program "pub unitary fn root[const n:Nat](q:Q<Bit>)->Q<Bit>{if static n>0 {phase[n-1,3](q)} else {q}}")
    {naturals := [("n",0)]} = some (.unitary,true,0,0)
#guard summary (program "pub unitary fn root[const A:Basis,const n:Nat](q:Q<A>)->Q<A>{if static n>0 {h(q)} else {q}}")
    {bases := [("A",[.bit])],naturals := [("n",0)]} = none

-- A selected inactive arm cannot erase real observation from the original effect.
#guard summary (program ("pub unitary fn root[const n:Nat](q:Q<Bit>)->Q<Bit>{if static n>0 {" ++
    "let m=measure_z(q);let u=unit(());basis u as _ {m}} else {q}}")) {naturals := [("n",0)]} = none

-- Opaque basis lifts retain a pending finite injection obligation and the
-- ORIGINAL conservative effect, including when a selected type is Unit.
#guard summary (program "pub isometry fn root[const A:Basis](q:Q<A>)->Q<Bit>{basis q as a {0}}")
    {bases := [("A",[.unit])]} = some (.iso,true,1,0)
#guard summary (program "pub unitary fn root[const A:Basis](q:Q<A>)->Q<Bit>{basis q as a {0}}") chosenBit = none
#guard summary (program "pub unitary fn root[const A:Basis](q:Q<A>)->Q<A>{basis q as a {a}}") chosenBit =
    some (.unitary,true,1,0)

-- Same-original-module inference is precise; external public effects remain.
#guard summary (program ("pub observe fn keep(q:Q<Bit>)->Q<Bit>{q} " ++
    "pub unitary fn root(q:Q<Bit>)->Q<Bit>{keep(q)}")) = some (.unitary,true,0,0)
#guard summary #[
    ("main","#![no_implicit_prelude] use library::keep;pub unitary fn root(q:Q<Bit>)->Q<Bit>{keep(q)}"),
    ("library","#![no_implicit_prelude] pub observe fn keep(q:Q<Bit>)->Q<Bit>{q}") ] = none

-- Original guarded self recursion retains its checked all-Nat decrease.
#guard summary (program "pub unitary fn root[const n:Nat](q:Q<Bit>)->Q<Bit>{if static n>0 {root[n-1](q)} else {q}}")
    {naturals := [("n",1)]} = some (.unitary,true,0,1)
#guard summary (program "pub unitary fn root[const n:Nat](q:Q<Bit>)->Q<Bit>{if static n>0 {root[n](q)} else {q}}")
    {naturals := [("n",1)]} = none
#guard summary (program ("pub unitary fn root[const n:Nat,const m:Nat](q:Q<Bit>)->Q<Bit>{" ++
    "if static n>0 {root[n-1,m+1](q)} else {q}}")) {naturals := [("n",1),("m",0)]} = none

-- Binding identity prevents an inner owner shadow from resurrecting a moved
-- outer owner when the original branch ends.
#guard summary (program ("pub unitary fn root[const n:Nat](q:Q<Bit>)->Q<Bit>{" ++
    "if static n>0 {let q=h(q);()} else {()};q}")) {naturals := [("n",0)]} = none

#guard summary (program "pub enum E{A,B} pub fn root()->E{E::A}") = some (.unitary,false,0,0)
#guard summary (program "pub enum E{A,B} pub fn root()->Bit{match E::A {E::A=>0,E::B=>1}}") =
    some (.unitary,false,0,0)
#guard summary (program ("pub enum E{A,B} pub unitary fn root[const A:Basis](q:Q<A>)->Q<A>{" ++
    "match E::A {E::A=>q,E::B=>h(q)}}")) chosenBit = none
#guard summary (program "pub enum E{A,B} pub fn root()->Bit{match E::A {E::A=>0,E::A=>1}}") = none
#guard summary (program "pub struct R{pub a:Bit,pub z:Unit} pub fn root(x:Bit)->R{R{z:(),a:x}}") =
    some (.unitary,false,0,0)
#guard summary (program "pub struct R{pub a:Bit,pub z:Unit} pub fn root(r:R)->Bit{r.a}") =
    some (.unitary,false,0,0)

end QleisliKernel.Tests.GenericTypeTrace
