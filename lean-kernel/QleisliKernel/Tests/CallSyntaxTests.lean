import QleisliKernel.SourceTypes.CallSyntax
import QleisliKernel.SourceTypes.AccessSyntax
import QleisliKernel.Qirf.RuntimeAccessInterval
import QleisliKernel.Qirf.RuntimeAccessSource
import QleisliKernel.Qirf.RuntimeAccessPartition

/-! Bounded original-token controls; no name/owner/effect or body acceptance.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.CallSyntaxTests
open QleisliKernel.SourceTypes
open QleisliKernel.SourceTypes CallSyntax

def parsed (source : String) : Option Call := do
  let tokens ← (lexLocated source).toOption
  let checked ← (read tokens).toOption
  return checked.call

def shape (source : String) : Option (List String × List (List String) × List Bool) :=
  (parsed source).map fun call =>
    (call.callee.map (·.text),call.arguments.map fun arg => arg.tokens.map (·.text),
      call.arguments.map (·.followingComma.isSome))

example : shape "h(q)" = some (["h"],[["q"]],[false]) := by decide +kernel
example : shape "f()" = some (["f"],[],[]) := by decide +kernel
example : shape "f(q,)" = some (["f"],[["q"]],[true]) := by decide +kernel
example : shape "defs::swap(q,r)" =
    some (["defs","::","swap"],[["q"],["r"]],[true,false]) := by decide +kernel
example : shape "f[Q<Bit>,2](x)" =
    some (["f","[","Q","<","Bit",">",",","2","]"],[["x"]],[false]) := by decide +kernel
example : shape "h(sign(q))" =
    some (["h"],[["sign","(","q",")"]],[false]) := by decide +kernel
example : shape "power(f,2)(q)" =
    some (["power","(","f",",","2",")"],[["q"]],[false]) := by decide +kernel
example : shape "f((q,r),s)" =
    some (["f"],[["(","q",",","r",")"],["s"]],[true,false]) := by decide +kernel
example : shape "h(qmatch(s,q){0=>idle,1=>sign})" =
    some (["h"],[["qmatch","(","s",",","q",")","{","0","=",">","idle",",",
      "1","=",">","sign","}"]],[false]) := by decide +kernel

-- Opaque callee tokens are never silently replaced by a convenient final name.
-- This splitter alone does not establish that the callee is a valid expression.
example : (shape "h(q);f(r)").map (·.1) =
    some ["h","(","q",")",";","f"] := by decide +kernel

example : (parsed "h").isNone = true := by decide +kernel
example : (parsed "(q)").isNone = true := by decide +kernel
example : (parsed "h(q) trailing").isNone = true := by decide +kernel
example : (parsed "h(q]").isNone = true := by decide +kernel
example : (parsed "h([q))").isNone = true := by decide +kernel
example : (parsed "h(q,,r)").isNone = true := by decide +kernel
example : (parsed "h(,q)").isNone = true := by decide +kernel
example : (parsed "h(q").isNone = true := by decide +kernel

example : ((parsed "/*λ*/h(q)").map fun call =>
    (call.callee.head?.map (·.span.startByte),call.opening.span.startByte,
      call.arguments.head?.map (fun arg => arg.tokens.head?.map (·.span.startByte)),
      call.closing.span.endByte)) = some (some 6,7,some (some 8),10) := by decide +kernel

open AccessSyntax in
private def places (source : String) : Option (List Place × List Place) := do
  let tokens ← (lexLocated source).toOption
  let both ← (readAdjacent tokens).toOption
  let owners name := if name == "q" then some (⟨⟨name,⟨0,1⟩⟩,[.bits 3],[7,2,5]⟩ : Owner)
    else if name == "empty" then some ⟨⟨name,⟨2,7⟩⟩,[.bits 0],[]⟩ else none
  let naturals path := if path == ["i"] then some 1 else none
  return (← both.before.places owners naturals (fun _ _ => none),
    ← both.after.places owners naturals (fun _ _ => none))

example : (places "cnot(ctrl q[i],excl q[0]); cnot(ctrl q[i],excl q[2]); q").map
    (fun (left,right) => (left.map (·.axes),right.map (·.axes),AccessSyntax.compatible left right)) =
    some ([[2],[7]],[[2],[5]],true) := by decide +kernel

example : (places "cnot(ctrl q[1],excl q[0]); z(excl q[0]); q").map
    (fun (left,right) => AccessSyntax.compatible left right) = some false := by decide +kernel

example : (places "f(excl empty); g(ctrl empty); empty").map
    (fun (left,right) => AccessSyntax.compatible left right) = some false := by decide +kernel

example : (places "f(excl q[1..3]); g(ctrl q[i-i..1]); q").map
    (fun (left,right) => (left.map (·.axes),right.map (·.axes),AccessSyntax.compatible left right)) =
    some ([[2,5]],[[7]],true) := by decide +kernel

example : (places "f(excl q[3]); g(ctrl q[1]); q").isNone = true := by decide +kernel
example : (places "f(excl q[1. .3]); g(ctrl q[1]); q").isNone = true := by decide +kernel
example : (places "f(excl q[1],q); g(ctrl q[1]); q").isNone = true := by decide +kernel
example : (places "f(excl q[1],); g(ctrl q[1]); q").isNone = true := by decide +kernel
example : (places "f(excl q[1]); (); g(ctrl q[1]); q").isNone = true := by decide +kernel
example : (places "f(excl q[1]) g(ctrl q[2]); h(ctrl q[1]); q").isNone = true := by decide +kernel
example : (places "defs::f[1](excl q[1]); g(ctrl q[2]); q").map
    (fun (left,right) => AccessSyntax.compatible left right) = some true := by decide +kernel

open QleisliKernel.Finite QleisliKernel.Qirf in
private def checkAccessInterval (text : String) (inputs outputs : List Nat) (checkControl : Bool) :
    Except String (Except Error (List Nat)) := do
  let call ← AccessSyntax.readCall (← lexLocated text)
  let lookup name : Option AccessSyntax.Owner :=
    if name == "q" then some ⟨⟨name,⟨0,1⟩⟩,[.bits 3],[7,2,5]⟩ else none
  let raw : Semantics.Raw.Program :=
    ⟨[⟨0,[7],1⟩,⟨1,[2],1⟩,⟨2,[5],1⟩],[.cnot 1 0 3 4],[4,3,2],.unitary⟩
  let program := Semantics.Ownership.pureProgram raw
  let action : WorkM (List Nat) := do
    let root ← RuntimeInterval.prepare [] program
    let checked ← RuntimeAccessInterval.read call lookup (fun _ => none) (fun _ _ => none)
      root.block 0 1 inputs outputs
    if checkControl then
      let _ ← RuntimeAccessInterval.checkSectors checked
    return RuntimeAccessInterval.controlAxes checked.places
  return (action.run 2000000).1

private def outcome : Except String (Except Finite.Error (List Nat)) → String
  | .ok (.ok [0]) => "ordered control"
  | .ok (.error .request) => "request"
  | .ok (.error .equation) => "equation"
  | _ => "unexpected"

example : outcome (checkAccessInterval "cnot(ctrl q[1],excl q[0])" [1,0] [3,4] true) =
    "ordered control" := by decide +kernel
example : outcome (checkAccessInterval "cnot(ctrl q[1],excl q[0])" [0,1] [4,3] false) =
    "request" := by decide +kernel
example : outcome (checkAccessInterval "cnot(ctrl q[1],excl q[0])" [1,0] [4,3] false) =
    "request" := by decide +kernel
example : outcome (checkAccessInterval "cnot(ctrl q[1],excl q[2])" [1,0] [3,4] false) =
    "request" := by decide +kernel
example : outcome (checkAccessInterval "cnot(excl q[1],ctrl q[0])" [1,0] [3,4] true) =
    "equation" := by decide +kernel

open QleisliKernel.Finite QleisliKernel.Qirf in
private def emptyOwnerReturn (outputs : List Nat) : Bool :=
  let attempt : Except String Bool := do
    let tokens ← lexLocated "f(ctrl a,excl b)"
    let call ← AccessSyntax.readCall tokens
    let lookup name : Option AccessSyntax.Owner :=
      if name == "a" then some ⟨⟨name,⟨0,1⟩⟩,[.unit],[]⟩
      else if name == "b" then some ⟨⟨name,⟨3,4⟩⟩,[.bits 0],[]⟩ else none
    let raw : Semantics.Raw.Program := ⟨[⟨0,[],0⟩,⟨1,[],0⟩],[],[0,1],.unitary⟩
    let program := Semantics.Ownership.pureProgram raw
    let action : WorkM Unit := do
      let root ← RuntimeInterval.prepare [] program
      let _ ← RuntimeAccessInterval.read call lookup (fun _ => none) (fun _ _ => none)
        root.block 0 0 [0,1] outputs
    return (action.run 2000000).1.isOk
  attempt.toOption.getD false

example : emptyOwnerReturn [0,1] = true := by decide +kernel
example : emptyOwnerReturn [1,0] = false := by decide +kernel

open QleisliKernel.Finite QleisliKernel.Qirf in
private def originalFirst (header body : String) (raw : Semantics.Raw.Program)
    (count : Nat) (inputs outputs : List Nat) : Except Error (List String × List Nat) :=
  let source := s!"pub unitary fn route({header}) -> {body}"
  let attempt : WorkM (List String × List Nat) := do
    let signature ← QuantumSignatureCore.read #[("main",source)] "main" "route"
    let root ← RuntimeInterval.prepare [] (Semantics.Ownership.pureProgram raw)
    let checked ← RuntimeAccessSource.read signature root
    let first ← RuntimeAccessSource.readFirst checked 0 count inputs outputs
    let _ ← RuntimeAccessInterval.checkSectors first.interval
    return (checked.entry.map (·.original.binder.text), RuntimeAccessInterval.controlAxes first.interval.places)
  (attempt.run 2000000).1

private def cnotFirst : Semantics.Raw.Program :=
  ⟨[⟨0,[7],1⟩,⟨1,[2],1⟩],[.cnot 0 1 2 3],[2,3],.unitary⟩

example : (originalFirst "c: Q<Bit>, t: Q<Bit>"
    "(Q<Bit>,Q<Bit>){cnot(ctrl c,excl t); cnot(ctrl c,excl t); (c,t)}"
    cnotFirst 1 [0,1] [2,3]).toOption = some (["c","t"],[0]) := by decide +kernel

private def emptyFirst (header : String) (ports : List Nat) : Except Finite.Error (List String × List Nat) :=
  originalFirst header "(Q<Unit>,Q<Bits<0>>){f(ctrl a,excl b); g(ctrl a,excl b); (a,b)}"
    ⟨[⟨0,[],0⟩,⟨1,[],0⟩],[],[0,1],.unitary⟩ 0 ports ports

example : (emptyFirst "a: Q<Unit>, b: Q<Bits<0>>" [0,1]).toOption =
    some (["a","b"],[]) := by decide +kernel
example : (emptyFirst "a: Q<Unit>, b: Q<Bits<0>>" [1,0]).isOk = false := by decide +kernel
example : (emptyFirst "a: Q<Unit>, a: Q<Bits<0>>" [0,1]).isOk = false := by decide +kernel
example : (emptyFirst "a: Q<Unit>, b: Q<Bit>" [0,1]).isOk = false := by decide +kernel

open QleisliKernel.Finite QleisliKernel.Qirf in
private def partitionFirst (source : String) (raw : Semantics.Raw.Program)
    (start count : Nat) (inputs outputs : List Nat) : Bool × Option (List Semantics.Raw.Port) :=
  let prepare := RuntimeInterval.prepare [] (Semantics.Ownership.pureProgram raw)
  let attempt : WorkM (List Semantics.Raw.Port) := do
    let root ← prepare
    let signature ← QuantumSignatureCore.read #[("main",source)] "main" "route"
    let checked ← RuntimeAccessSource.read signature root
    let partition ← RuntimeAccessPartition.read checked start count inputs outputs
    let _ ← RuntimeAccessInterval.checkSectors partition.call.interval
    return partition.owners.restored
  ((prepare.run 2000000).1.isOk,(attempt.run 2000000).1.toOption)

private def partitionCnotSource : String :=
  "pub unitary fn route(q: Q<Bits<3>>) -> Q<Bits<3>> {\
    cnot(ctrl q[1],excl q[0]); cnot(ctrl q[1],excl q[2]); q}"

private def partitionCnot (restorePosition : Nat) : Semantics.Raw.Program :=
  ⟨[⟨0,[7,2,5],3⟩],
    [.split 0 1 2 1,.split 2 3 4 1,.join 1 4 5,
      .split 5 6 7 0,.split 7 8 9 1,.join 6 9 10,
      .cnot 3 8 11 12,
      .split 10 13 14 0,.join 13 12 15,.join 15 14 16,
      .split 16 17 18 restorePosition,.join 17 11 19,.join 19 18 20],
    [20],.unitary⟩

example : partitionFirst partitionCnotSource (partitionCnot 1) 6 1 [3,8] [11,12] =
    (true,some [⟨20,[7,2,5],3⟩]) := by decide +kernel
example : partitionFirst partitionCnotSource (partitionCnot 2) 6 1 [3,8] [11,12] =
    (true,none) := by decide +kernel

private def partitionEmpty (start : Nat) : Bool × Option (List Semantics.Raw.Port) :=
  let source := s!"pub unitary fn route(q: Q<Bits<2>>) -> Q<Bits<2>> " ++
    "{f(excl q[" ++ toString start ++ ".." ++ toString start ++ "]); g(excl q[0]); q}"
  partitionFirst source
    ⟨[⟨0,[5,7],2⟩],[.split 0 1 2 1,.split 2 3 4 0,.join 1 4 5,
      .split 5 6 7 1,.join 6 3 8,.join 8 7 9],[9],.unitary⟩ 3 0 [3] [3]

example : partitionEmpty 1 = (true,some [⟨9,[5,7],2⟩]) := by decide +kernel
example : partitionEmpty 0 = (true,none) := by decide +kernel

open QleisliKernel.Finite QleisliKernel.Qirf in
private def partitionPair (source : String) (gap : List Semantics.Raw.Op) (parent : Nat) :
    Bool × Option (List Semantics.Raw.Port) :=
  let firstRaw := partitionCnot 1
  let raw : Semantics.Raw.Program := {firstRaw with operations := firstRaw.operations ++ gap ++
    [.split parent 21 22 1,.split 22 23 24 1,.join 21 24 25,
      .split 25 26 27 1,.split 27 28 29 1,.join 26 29 30,
      .cnot 23 28 31 32,
      .split 30 33 34 1,.join 33 32 35,.join 35 34 36,
      .split 36 37 38 1,.join 37 31 39,.join 39 38 40], outputs := [40]}
  let prepare := RuntimeInterval.prepare [] (Semantics.Ownership.pureProgram raw)
  let attempt : WorkM (List Semantics.Raw.Port) := do
    let root ← prepare
    let signature ← QuantumSignatureCore.read #[("main",source)] "main" "route"
    let checked ← RuntimeAccessSource.read signature root
    let first ← RuntimeAccessPartition.read checked 6 1 [3,8] [11,12]
    let second ← RuntimeAccessPartition.readSecond first (19+gap.length) 1 [23,28] [31,32]
    let _ ← RuntimeAccessInterval.checkSectors second.call
    return second.owners.restored
  ((prepare.run 2000000).1.isOk,(attempt.run 2000000).1.toOption)

example : partitionPair partitionCnotSource [] 20 = (true,some [⟨40,[7,2,5],3⟩]) := by decide +kernel
example : partitionPair partitionCnotSource [.applyUnitary 20 41 []] 41 = (true,none) := by decide +kernel

end QleisliKernel.Tests.CallSyntaxTests
