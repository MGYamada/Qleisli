import QleisliKernel.SourceTypes.StaticOperation

/-! Small original ordered-kind regressions. A later formal's spelling cannot
replace a preceding global type/helper binding, and a convenient closed value
cannot create an unavailable forward binder. No body/operator claim follows.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.StaticKinds
open SourceTypes OperationDescription Semantics.FiniteCarrier

private def leaf : String := "pub enum E{Only} pub unitary fn keep(q:Q<E>)->Q<E>{q}"
private def middle : String := "pub use leaf::E;"
private def main : String :=
  "use middle::E; pub unitary fn choose[const U:Op<E>,const E:Basis](q:Q<Bit>)->Q<Bit>{q}"

private def chosen : Description := provider "main" "choose" [("E",[.bit])] [] [("U",provider "leaf" "keep" [] [] [])]

#guard (((SourceTypes.StaticOperation.check #[ ("main",main),("middle",middle),("leaf",leaf) ] .external chosen).run 10000000).1.toOption).map
    (fun checked => (checked.root.input,checked.root.output,checked.sourceRows.map (·.1) |>.contains "middle")) =
    some ([.bit],[.bit],true)

private def helper : String := "pub static fn width()->Nat{0}"
private def kindHelper : String :=
  "pub unitary fn empty(q:Q<Bits<0>>)->Q<Bits<0>>{q} " ++
  "pub unitary fn choose[const U:Op<Bits<helper::width()>>,const width:Nat](q:Q<Bit>)->Q<Bit>{q}"

private def withHelper : Description := provider "main" "choose" [] [("width",5)] [("U",provider "main" "empty" [] [] [])]

#guard (((SourceTypes.StaticOperation.check #[ ("main",kindHelper),("helper",helper) ] .external withHelper).run 10000000).1.toOption).map
    (fun checked => (checked.root.input,checked.root.output,checked.sourceRows.map (·.1) |>.contains "helper")) =
    some ([.bit],[.bit],true)

private def forward : String :=
  "pub unitary fn empty(q:Q<Bits<0>>)->Q<Bits<0>>{q} " ++
  "pub unitary fn choose[const U:Op<Bits<n>>,const n:Nat](q:Q<Bit>)->Q<Bit>{q}"

#guard ((SourceTypes.StaticOperation.check #[ ("main",forward) ] .external
  (provider "main" "choose" [] [("n",0)] [("U",provider "main" "empty" [] [] [])])).run 10000000).1.isOk = false

end QleisliKernel.Tests.StaticKinds
