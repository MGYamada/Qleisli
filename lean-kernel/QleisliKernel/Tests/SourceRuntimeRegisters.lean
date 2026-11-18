import QleisliKernel.SourceTypes.SourceRuntimeTrace
import QleisliKernel.SourceTypes.SourceRuntimeOrdinary
import QleisliKernel.Tests.SourceTraceOriginals

/-! Existing register primitives with exact tags, zero-width owners, original
Nat guards and head-first ordinary values. Native repartition maps still need
their actual ordered Split/Join equations with coefficient +1.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.SourceRuntimeRegisters
open QleisliKernel QleisliKernel.SourceTypes SourceRuntimeValues

private def sources (source : String) : Sources := #[("main",source)] ++ SourceTraceOriginals.bundled
private def read (source : String) (arguments : StaticTypes.Arguments := {}) :=
  ((SourceRuntimeTrace.read (sources source) "main" "route" arguments).run 2000000000).1.toOption

private def roundtrip :=
  "pub unitary fn route(q:Q<Bits<1>>)->Q<Bits<1>>{let(bit,rest)=take_bit[1,0](q);put_bit[1,0](bit,rest)}"
#guard (read roundtrip).map (fun checked => ((valueOwners checked.summary.value).map (·.ordinal),
  checked.summary.allocated.map (·.basis),checked.summary.consumed.map (·.ordinal))) =
  some ([3],[[.bit],[.bits 0],[.bits 1]],[0,1,2])
#guard (read "pub unitary fn route(q:Q<Bits<1>>)->Q<Bit>{let(bit,rest)=take_bit[1,0](q);bit}").isNone
#guard (read "pub unitary fn route(q:Q<Bit>)->(Q<Bit>,Q<Bits<0>>){take_bit[1,0](q)}").isNone
#guard (read "pub unitary fn route(bit:Q<Bit>,rest:Q<Unit>)->Q<Bits<1>>{put_bit[1,0](bit,rest)}").isNone
#guard (read (roundtrip.replace "take_bit[1,0]" "take_bit[1,1]")).isNone
#guard (read (roundtrip.replace "take_bit[1,0]" "take_bit")).isNone

private def prepend := "pub fn route(bit:Bit)->Bits<1>{prepend_bit[0](bit,empty_bits())}"
#guard (read prepend).map (fun checked =>
  (checked.summary.quantumUse,checked.summary.generic.quantumUse)) = some (false,false)
-- The original classical bracket form is a retained first parse refusal;
-- normal runtime fn is a separate explicit translation, not a grammar rescue.
#guard (read (prepend.replace "pub fn" "pub classical fn")).isNone

private def packed := "pub fn route(bit:Bit,tail:Bits<1>)->Bits<2>{prepend_bit[1](bit,tail)}"
private def values (head tail : Nat) : Semantics.SourceOrdinary.Valuation :=
  ⟨fun ordinal => [head,tail][ordinal]?,fun _ => none,fun _ _ _ => none⟩
#guard (read packed).map (fun checked =>
  (QleisliKernel.SourceTypes.SourceRuntimeOrdinary.extract (values 0 1) checked.summary.value).toOption) =
  some (some [.ordinary [.bits 2] 2])

private def generic :=
  "pub unitary fn route[const n:Nat,const k:Nat](q:Q<Bits<n>>)->(Q<Bit>,Q<Bits<n-1>>)" ++
  "requires n>0,k<n{take_bit[n,k](q)}"
#guard (read generic {naturals := [("n",2),("k",1)]}).isSome
#guard (read (generic.replace "n>0,k<n" "n>0") {naturals := [("n",2),("k",1)]}).isNone
#guard (read generic {naturals := [("n",2),("k",2)]}).isNone

private def registerFold :=
  "pub unitary fn route[const n:Nat,const first:Nat](u:Q<Unit>,q:Q<Bits<n>>)->(Q<Unit>,Q<Bits<n>>)" ++
  "requires first<=n{let r=qfor static i in first..n carry r=q{" ++
  "let(bit,tail)=take_bit[n,i](r);yield put_bit[n,i](bit,tail);};(u,r)}"

private def readFold (source : String) (n first : Nat) :=
  read source {naturals := [("n",n),("first",first)]}

private structure RegisterIteration where
  coordinate : Nat
  takeArguments : List Nat
  putArguments : List Nat
  carryIn : List Nat
  carryOut : List Nat
  consumed : List Nat
  spectators : List Nat
  deriving DecidableEq

private def registerFoldTrace (n first : Nat) :
    Option (List RegisterIteration × List (Nat × Semantics.FiniteCarrier.Basis)) := do
  let checked ← readFold registerFold n first
  let [.staticFold fold children] := checked.events | none
  let true := fold.iterations.length == children.length | none
  let iterations ← (fold.iterations.zip children).mapM fun (iteration,events) => do
    let [.registerPrimitive take,.registerPrimitive put] := events | none
    let true := take.kind == .takeBit && put.kind == .putBit && take.held == put.held | none
    pure ⟨iteration.coordinate,take.application.arguments.map (·.value),
      put.application.arguments.map (·.value),(valueOwners iteration.carry).map (·.ordinal),
      (valueOwners iteration.seeded.value).map (·.ordinal),iteration.seeded.consumed.map (·.ordinal),
      take.held.map (·.ordinal)⟩
  return (iterations,(valueOwners checked.summary.value).map fun owner => (owner.ordinal,owner.basis))

-- Both primitive calls read the current written coordinate. Each iteration
-- owns the preceding carry, with the zero-width spectator held outside it.
#guard registerFoldTrace 3 1 = some
  ([⟨1,[3,1],[3,1],[1],[4],[1,2,3],[0]⟩,⟨2,[3,2],[3,2],[4],[7],[4,5,6],[0]⟩],[(0,[.unit]),(7,[.bits 3])])
#guard registerFoldTrace 0 0 = some ([],[(0,[.unit]),(1,[.bits 0])])

-- Empty ranges still submit their original bodies to the common source check.
#guard (readFold (registerFold.replace "take_bit[n,i]" "take_bit[n,n]") 0 0).isNone
#guard (readFold (registerFold.replace "yield put_bit" "finish(u);yield put_bit") 0 0).isNone

#print axioms QleisliKernel.SourceTypes.SourceRegisterApplication.read
#print axioms QleisliKernel.SourceTypes.SourceRegisterApplication.apply
end QleisliKernel.Tests.SourceRuntimeRegisters
