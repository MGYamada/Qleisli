import QleisliKernel.Qirf.RuntimeFamily

/-! Bounded integration controls over original source headers and fresh Raw
roots, at most three physical bits. #guard evaluates the actual checker;
these observations are not source-body or numerical-runtime proofs.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.RuntimeFamily
open Semantics.FiniteCarrier Semantics.RuntimeType Semantics.Observation
open Qirf Qirf.RuntimeFamily

def text : String := "pub enum Tri{A,B,C} pub unitary fn keep(flag:Bit,q:Q<Tri>)->(Bit,Q<Tri>){(flag,q)}"
def tri (source : String := text) : Basis := [.enumeration ⟨"main","Tri",source⟩ ["A","B","C"]]
def q (source : String := text) : Semantics.CarrierInterface.Owner := ⟨⟨0,[0,1],2⟩,tri source⟩
def program : Program := ⟨[(q).port],[0],[],[0],[0],.unitary⟩
def artifact (body : Program := program) (source : String := text) : Artifact :=
  ⟨#[body],#[],#[("main",source)],0,none⟩
def request (source : String := text) : Request := {
  selection := .exported, moduleName := "main", declarationName := "keep",
  parameters := [ordinary [.bit],owner (tri source)],
  inputStorage := [[.ordinary [.bit] (.bit 0)],[.quantum (q source)]],
  inputRows := [[false],[true]], result := tuple 2 [ordinary [.bit],owner (tri source)],
  storage := [.tuple 2,.ordinary [.bit] (.bit 0),.quantum (q source)], publicEffect := .unitary }

private def counts {root request inputCode outputCode} : Nat →
    ({assignments : List (List Bool)} → Rows root request inputCode outputCode assignments → List Nat) :=
  Nat.rec (fun {_} _ => []) (fun _ next {_} rows => match rows with
    | .nil => [] | .cons head tail => head.instrument.histories.length :: next tail)

def observe (actual : Artifact) (requested : Request) : Option (List Nat) :=
  match ((RuntimeFamily.check actual #[0] requested).run 10000000).1 with
  | .ok checked => some ([checked.entry.parameters.length,checked.inputCode.cols,
      checked.outputCode.cols,checked.domain.code.labels.length] ++
      counts (checked.domain.code.labels.length+1) checked.rows)
  | _ => none

def observingText : String :=
  "pub enum Tri{A,B,C} pub observe fn keep(q:Q<Tri>)->Q<Tri>{let hidden=measure_z(init0());q}"
def observingProgram : Program :=
  ⟨[(q observingText).port],[],[.pure (.init0 1 2),.measure 1 0],[0],[],.observe⟩
def observingRequest : Request := {request observingText with
  parameters := [owner (tri observingText)],
  inputStorage := [[.quantum (q observingText)]], inputRows := [[]],
  result := owner (tri observingText), storage := [.quantum (q observingText)], publicEffect := .observe }

def zeroText : String :=
  "pub enum One{Only} pub unitary fn keep(empty:Unit,q:Q<One>)->(Q<One>,Unit){(q,empty)}"
def one : Basis := [.enumeration ⟨"main","One",zeroText⟩ ["Only"]]
def zeroOwner : Semantics.CarrierInterface.Owner := ⟨⟨0,[],0⟩,one⟩
def zeroProgram : Program := ⟨[zeroOwner.port],[],[],[0],[],.unitary⟩
def zeroRequest : Request := {request zeroText with
  parameters := [ordinary [.unit],owner one],
  inputStorage := [[.ordinary [.unit] .unit],[.quantum zeroOwner]], inputRows := [[]],
  result := tuple 2 [owner one,ordinary [.unit]],
  storage := [.tuple 2,.quantum zeroOwner,.ordinary [.unit] .unit] }

def hiddenResultText : String :=
  "pub enum Tri{A,B,C} pub observe fn keep(q:Q<Tri>)->(Q<Tri>,Tri){let b=measure_z(init0());(q,if b{Tri::B}else{Tri::A})}"
def hiddenResultProgram (invalid : Bool) : Program :=
  ⟨[(q hiddenResultText).port],[],[.pure (.init0 1 2),.measure 1 0,.constant false 1],[0],
    if invalid then [0,0] else [0,1],.observe⟩
def hiddenResultRequest (invalid : Bool) : Request := {request hiddenResultText with
  parameters := [owner (tri hiddenResultText)], inputStorage := [[.quantum (q hiddenResultText)]],
  inputRows := [[]], result := tuple 2 [owner (tri hiddenResultText),ordinary (tri hiddenResultText)],
  storage := [.tuple 2,.quantum (q hiddenResultText),
    .ordinary (tri hiddenResultText) (.enumeration ⟨"main","Tri",hiddenResultText⟩ (if invalid then [0,0] else [0,1]))],
  publicEffect := .observe }

def jointText : String :=
  "pub unitary fn keep(q:Q<Bit>,r:Q<Bit>)->(Q<Bit>,Q<Bit>){cnot(q,r)}"
def jointProgram : Program :=
  ⟨[⟨0,[0],1⟩,⟨1,[1],1⟩],[],[.pure (.cnot 0 1 2 3)],[2,3],[],.unitary⟩
def jointRequest : Request := {request jointText with
  parameters := [owner [.bit],owner [.bit]],
  inputStorage := [[.quantum ⟨⟨0,[0],1⟩,[.bit]⟩],[.quantum ⟨⟨1,[1],1⟩,[.bit]⟩]],
  inputRows := [[]], result := tuple 2 [owner [.bit],owner [.bit]],
  storage := [.tuple 2,.quantum ⟨⟨2,[0],1⟩,[.bit]⟩,.quantum ⟨⟨3,[1],1⟩,[.bit]⟩] }

def leakingProgram : Program := {program with
  operations := [.pure (.applyUnitary 0 1 [⟨[],.monomial [0,1] [0,1,3,2] [0,0,0,0]⟩])],outputs := [1] }

def controls : List (String × Bool) := [
  ("mixed identity checks all ordinary inputs and a three-state quantum code",
    observe (artifact) (request) == some [2,3,3,2,1,1]),
  ("producer input subset refuses",(observe (artifact) {request with inputRows := [[false]]}).isNone),
  ("producer input order refuses",(observe (artifact) {request with inputRows := [[true],[false]]}).isNone),
  ("full parameter tree is exact",(observe (artifact)
    {request with parameters := [owner (tri),ordinary [.bit]]}).isNone),
  ("full result tuple tree is exact",(observe (artifact)
    {request with result := tuple 2 [owner (tri),ordinary [.bit]]}).isNone),
  ("same-width quantum Basis substitution refuses",(observe (artifact)
    {request with inputStorage := [[.ordinary [.bit] (.bit 0)],[.quantum ⟨(q).port,[.bits 2]⟩]]}).isNone),
  ("ordered quantum axes remain exact",(observe (artifact)
    {request with storage := [.tuple 2,.ordinary [.bit] (.bit 0),.quantum ⟨⟨0,[1,0],2⟩,tri⟩]}).isNone),
  ("zero-width ordinary parameter and quantum owner survive",
    observe (artifact zeroProgram zeroText) zeroRequest == some [2,1,1,1,1]),
  ("zero-width ordinary parameter cannot disappear",(observe (artifact zeroProgram zeroText)
    {zeroRequest with inputStorage := [[.quantum zeroOwner]]}).isNone),
  ("zero-width quantum owner cannot disappear",(observe (artifact zeroProgram zeroText)
    {zeroRequest with storage := [.ordinary [.unit] .unit]}).isNone),
  ("all hidden histories include the zero-probability outcome",
    observe (artifact observingProgram observingText) observingRequest == some [1,3,3,1,2]),
  ("public Observe cannot be sharpened from its actual identity channel",
    (observe (artifact observingProgram observingText) {observingRequest with publicEffect := .unitary}).isNone),
  ("actual hidden observation cannot borrow a Unitary header",
    (observe (artifact {program with operations := [.pure (.init0 1 2),.measure 1 1],effect := .observe})
      (request)).isNone),
  ("fresh Raw validation rejects lost quantum owner",(observe (artifact {program with outputs := []}) (request)).isNone),
  ("unrelated original source is not justified by a header",
    (observe {artifact with sources := #[("main",text),("unrelated","fn unused()->Unit{()}")]} (request)).isNone),
  ("typed quantum and classical results cover all hidden histories",
    observe (artifact (hiddenResultProgram false) hiddenResultText) (hiddenResultRequest false) == some [1,3,3,1,2]),
  ("invalid classical result on zero-probability quantum history refuses",
    (observe (artifact (hiddenResultProgram true) hiddenResultText) (hiddenResultRequest true)).isNone),
  ("a joint CNOT uses one full two-owner operator",
    observe (artifact jointProgram jointText) jointRequest == some [2,4,4,1,1]),
  ("same-typed quantum owners cannot exchange actual return roles",
    (observe (artifact jointProgram jointText) {jointRequest with
      storage := [.tuple 2,.quantum ⟨⟨3,[1],1⟩,[.bit]⟩,.quantum ⟨⟨2,[0],1⟩,[.bit]⟩]}).isNone),
  ("valid physical permutation cannot leak the three-state code into padding",
    (observe (artifact leakingProgram) {request with
      storage := [.tuple 2,.ordinary [.bit] (.bit 0),.quantum ⟨⟨1,[0,1],2⟩,tri⟩]}).isNone),
  ("no work budget refuses",((RuntimeFamily.check (artifact) #[0] (request)).run 0).1.isOk == false)]

example : controls.length = 21 := by decide +kernel
#guard controls.all (·.2)

end QleisliKernel.Tests.RuntimeFamily
