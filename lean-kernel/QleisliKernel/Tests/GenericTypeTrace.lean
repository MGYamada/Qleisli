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

private def registerFold (last take yieldValue : String) : Sources :=
  program ("pub unitary fn root[const n:Nat](q:Q<Bits<n>>)->Q<Bits<n>>{" ++
    "qfor static i in 0.." ++ last ++ " carry q=q {let (x,r)=take_bit[n," ++ take ++ "](q);yield " ++
    yieldValue ++ "}}")

-- The index is a symbolic coordinate under the written half-open bound. A
-- selected zero width cannot remove original obligations from the body.
#guard summary (registerFold "n" "i" "put_bit[n,i](x,r);") {naturals := [("n",2)]} = some (.unitary,true,0,0)
#guard summary (registerFold "n" "i" "put_bit[n,i](x,r)") {naturals := [("n",0)]} = some (.unitary,true,0,0)
#guard summary (registerFold "n" "n" "put_bit[n,i](x,r);") {naturals := [("n",2)]} = none
#guard summary (program ("pub unitary fn root[const n:Nat](q:Q<Bits<n>>)->Q<Bits<n>>{" ++
    "qfor static i in 0..n carry q=q {static let j=i;let (j,r)=take_bit[n,j](q);yield put_bit[n,j](j,r);}}"))
    {naturals := [("n",0)]} = none
#guard summary (registerFold "n" "i" "r;") {naturals := [("n",0)]} = none
#guard summary (registerFold "n" "i" "put_bit[n,i](x,outside);") {naturals := [("n",0)]} = none
#guard summary (program "pub unitary fn root(q:Q<Bit>)->Q<Bit>{qfor static i in 1..0 carry q=q {yield q;}}") = none
#guard summary (program "pub unitary fn root(q:Q<Bit>,r:Q<Bit>)->(Q<Bit>,Q<Bit>){(qfor static i in 0..0 carry q=q {yield h(r);},r)}") = none
#guard summary (program "pub unitary fn root(q:Q<Unit>)->Q<Unit>{qfor static i in 0..0 carry q=q {yield q}}") = some (.unitary,true,0,0)
#guard summary (program "pub fn root()->Unit{for static i in 0..0 carry ()=() {yield}}") = some (.unitary,false,0,0)
#guard summary (program "pub unitary fn root(q:Q<Bit>)->Q<Bit>{for static i in 0..0 carry q=q {yield q;}}") = none

private def coherentBody (form block : String) : Sources :=
  program ("pub observe fn root(c:Q<Bit>,q:Q<Bit>)->(Q<Bit>,Q<Bit>){" ++
    form ++ "(c,q){0=>h,1=>{" ++ block ++ "}}}")

#guard summary (coherentBody "qif" "let r=h(q);global_phase_eighth(r)") = some (.unitary,true,0,0)
#guard summary (coherentBody "qmatch" "let r=h(q);global_phase_eighth(r)") = some (.unitary,true,0,0)
#guard summary (coherentBody "qif" "let m=measure_z(q);basis unit(()) as _ {m}") = none
#guard summary (coherentBody "qmatch" "h(c)") = none
#guard summary (coherentBody "qmatch" "(h(q),())") = none

private def inlineAccess (requires : String) : Option Bool :=
  let sources := program ("pub unitary fn root[const U:Op<Bit>](c:Q<Bit>,q:Q<Bit>)->(Q<Bit>,Q<Bit>) requires " ++
    requires ++ " {qmatch(c,q){0=>h,1=>{U(q)}}}")
  let action := do
    let definition ← SourceTypes.GenericTypeTrace.readDefinition sources "main" "root"
    let tokens := definition.original.envelope.occurrence.body
    let tree ← lift ((SourceSyntax.read (tokens.length+1) 0 true tokens).mapError fun _ => Error.request)
    let body ← SourceTypes.GenericTypeTrace.checkTree definition tree
    pure (body.duties.any fun duty => match duty.kind,duty.requirement with
      | .application,.access paths => paths.applicable && paths.controllable
      | _,_ => false)
  (action.run 10000000).1.toOption

#guard inlineAccess "Applicable(U)" = none
#guard inlineAccess "Applicable(U),Controllable(U)" = some true

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
#guard summary (program "pub classical fn root[const n:Nat](x:Bit)->Bit{if static n>0 {root[n-1](x)} else {x}}")
    {naturals := [("n",1)]} = none

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

private def predicate : String := "classical fn predicate(b:Bit)->Bit{b} "

#guard summary (program (predicate ++
    "pub unitary fn root(q:Q<Bit>)->Q<Bit>{with_computed(q,predicate){|a|global_phase_eighth(a)}}")) =
    some (.unitary,true,0,0)
#guard summary (program (predicate ++
    "pub unitary fn root(q:Q<Bit>)->Q<Bit>{with_computed(q,predicate,h){|data,a|(h(data),a)}}")) =
    some (.unitary,true,0,0)
#guard summary (program (predicate ++
    "pub unitary fn root(q:Q<Bit>,x:Bit)->Q<Bit>{with_computed(q,predicate){|a|if x {h(a)} else {a}}}")) =
    some (.unitary,true,0,0)
#guard summary (program (predicate ++
    "pub unitary fn root(q:Q<Bit>,x:Bit)->Q<Bit>{with_computed(q,predicate,h){|data,a|(if x {h(data)} else {data},a)}}")) = none
#guard summary (program (predicate ++
    "pub unitary fn root[const A:Basis](q:Q<A>)->Q<A>{with_computed(q,predicate){|a|a}}")) chosenBit = none
#guard summary (program (predicate ++
    "pub unitary fn root(q:Q<Bit>,r:Q<Bit>)->(Q<Bit>,Q<Bit>){let q=with_computed(q,predicate){|a|let r=h(r);a};(q,r)}")) = none
#guard summary (program (predicate ++
    "pub observe fn root(q:Q<Bit>)->Q<Bit>{with_computed(q,predicate){|a|let m=measure_z(a);let u=unit(());basis u as _ {m}}}")) = none

private def widthPredicate :=
  "classical fn mark[const width:Nat](b:Bits<width>)->Bit requires width>=3{b[0] and not b[1] and b[2]} "

private def genericPredicate :=
  widthPredicate ++ "pub unitary fn root[const n:Nat](q:Q<Bits<n>>)->Q<Bits<n>> requires n>=3" ++
    "{with_computed(q,mark[n]){|a|phase[1,1](a)}}"

#guard summary (program genericPredicate) {naturals := [("n",3)]} = some (.unitary,true,0,0)
#guard summary (program genericPredicate) {naturals := [("n",4)]} = some (.unitary,true,0,0)
#guard summary (program (genericPredicate.replace "mark[n]" "mark[n+1]"))
    {naturals := [("n",3)]} = none
#guard summary (program (genericPredicate.replace " requires n>=3" ""))
    {naturals := [("n",3)]} = none
#guard summary (program (genericPredicate.replace "mark[n]" "mark"))
    {naturals := [("n",3)]} = none

private def computedCount : Option Nat :=
  let sources := program (predicate ++
    "pub unitary fn root(q:Q<Bit>)->Q<Bit>{with_computed(q,predicate){|a|a}}")
  let action : WorkM Nat := do
    let signature ← StaticRuntimeSignature.prepareWithArguments sources "main" "root" {}
    let instantiation : StaticInstantiation.Checked signature.original := .static {} signature.environment rfl
    pure (← SourceTypes.GenericTypeTrace.readWithInstantiation instantiation).computedObligations.length
  (action.run 10000000).1.toOption

#guard computedCount = some 1

#guard summary (program "pub fn root()->Bits<0>{empty_bits()}") = some (.unitary,false,0,0)
#guard summary (program "pub fn root[const n:Nat](b:Bit,x:Bits<n>)->Bits<n+1>{prepend_bit[n](b,x)}")
    {naturals := [("n",0)]} = some (.unitary,false,0,0)
#guard summary (program ("pub unitary fn root[const n:Nat,const k:Nat](q:Q<Bits<n>>)->(Q<Bit>,Q<Bits<n-1>>) " ++
    "requires n>0,k<n {take_bit[n,k](q)}")) {naturals := [("n",1),("k",0)]} = some (.unitary,true,0,0)
#guard summary (program ("pub unitary fn root[const n:Nat,const k:Nat](a:Q<Bit>,q:Q<Bits<n-1>>)->Q<Bits<n>> " ++
    "requires n>0,k<n {put_bit[n,k](a,q)}")) {naturals := [("n",1),("k",0)]} = some (.unitary,true,0,0)
#guard summary (program ("pub unitary fn root[const n:Nat,const k:Nat](q:Q<Bits<n>>)->(Q<Bit>,Q<Bits<n-1>>) " ++
    "requires n>0 {take_bit[n,k](q)}")) {naturals := [("n",1),("k",0)]} = none
#guard summary (program ("pub unitary fn root[const A:Basis](q:Q<A>)->(Q<Bit>,Q<Bits<0>>){take_bit[1,0](q)}"))
    {bases := [("A",[.bits 1])]} = none

-- Cardinality-one ports may infer Unit while retaining their distinct full
-- types and pending injection. Neither rectangular child gains Controlled.
#guard summary (program "pub unitary fn root(q:Q<Unit>)->Q<Bits<0>>{basis q as _ {empty_bits()}}") =
    some (.unitary,true,1,0)
#guard summary (program ("unitary fn expand(q:Q<Unit>)->Q<Bits<0>>{basis q as _ {empty_bits()}} " ++
    "pub unitary fn root(q:Q<Unit>)->Q<Bits<0>>{expand(q)}")) = some (.unitary,true,0,0)
#guard summary (program ("unitary fn expand(q:Q<Unit>)->Q<Bits<0>>{basis q as _ {empty_bits()}} " ++
    "pub unitary fn root(q:Q<Bits<0>>)->Q<Unit>{adjoint(expand)(q)}")) = some (.unitary,true,0,0)
#guard summary (program ("unitary fn expand(q:Q<Unit>)->Q<Bits<0>>{basis q as _ {empty_bits()}} " ++
    "unitary fn shrink(q:Q<Bits<0>>)->Q<Unit>{basis q as _ {()}} " ++
    "pub unitary fn root(s:Q<Bit>,q:Q<Unit>)->(Q<Bit>,Q<Unit>){qmatch(s,q){0=>then_op(expand,shrink),1=>then_op(expand,shrink)}}")) = none

#guard summary (program "pub classical fn root(x:Bit)->Bit{not x}") = some (.unitary,false,0,0)
#guard summary (program "pub classical fn root()->Bits<0>{empty_bits()}") = some (.unitary,false,0,0)
#guard summary (program "pub classical fn root()->Bits<1>{prepend_bit[0](0,empty_bits())}") = none
#guard summary (program "pub classical fn root()->Bit{let x=0;x}") = none
#guard summary (program "pub classical fn root()->Unit{}") = none
#guard summary (program "fn ordinary(x:Bit)->Bit{x} pub classical fn root(x:Bit)->Bit{ordinary(x)}") = none
#guard summary (program "classical fn ordinary(x:Bit)->Bit{x} pub classical fn root(x:Bit)->Bit{ordinary(x)}") =
    some (.unitary,false,0,0)
#guard summary (program ("fn ordinary()->Bit{0} " ++
    "pub isometry fn root(q:Q<Unit>)->Q<Bit>{basis q as _ {ordinary()}}")) = none
#guard summary (program ("pub isometry fn root(q:Q<Unit>)->Q<Bit>{basis q as _ {let x=0;x}}")) = none
#guard summary (program ("pub enum E{A,B} pub classical fn root(e:E)->Bit{" ++
    "match e {E::A=>{0},E::B=>1}}")) = none

#guard summary (program "pub classical fn root(():Unit)->Unit{()}") = some (.unitary,false,0,0)
#guard summary (program "pub unitary fn root(q:Q<Unit>)->Q<Unit>{let ()=();q}") = some (.unitary,true,0,0)
#guard summary (program "pub unitary fn root(q:Q<Unit>)->Unit{let ()=q;()}") = none
#guard summary (program "pub fn root[const A:Basis](x:A)->Unit{let ()=x;()}")
    {bases := [("A",[.unit])]} = none
#guard summary (program "pub fn root(x:Bits<0>)->Unit{let ()=x;()}") = none
#guard summary (program "pub struct R{} pub fn root(x:R)->Unit{let ()=x;()}") = none
#guard summary (program "pub fn root()->Unit{let (x)=();x}") = none

#guard summary (program ("pub unitary fn root[const Q:Nat,const Op:Nat,const Unit:Nat,const Bit:Nat,const CBit:Nat]" ++
    "(q:Q<Bit>)->Q<Bit>{phase[Q+Op+Unit+Bit+CBit,3](q)}"))
    {naturals := [("Q",1),("Op",0),("Unit",0),("Bit",0),("CBit",0)]} = some (.unitary,true,0,0)
#guard summary (program "pub unitary fn root[const Bit:Basis](q:Q<Bit>)->Q<Bit>{q}")
    {bases := [("Bit",[.bit])]} = none

end QleisliKernel.Tests.GenericTypeTrace
