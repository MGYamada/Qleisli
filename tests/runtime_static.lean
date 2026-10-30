import QleisliKernel.SourceTypes.StaticRuntimeSignature

/-! Executable comparisons against independent expected static results.
These are tests of the actual checked functions, not kernel reduction proofs,
source/body preservation or native compilation proofs. Generic correctness
remains in SourceTypes.StaticNatural; no quantum maximum is generated.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
open QleisliKernel QleisliKernel.SourceTypes

private def run (source expression : String) (bindings : StaticNatural.Bindings) :
    Option Nat := do
  let tokens ← (lex expression).toOption
  let prepared ← ((StaticNatural.prepare #[("main",source)] "main" "keep" tokens).run 10000000).1.toOption
  let closed ← ((StaticNatural.close prepared bindings).run 10000000).1.toOption
  return closed.value

private def source (parameters premises : String) : String :=
  "pub unitary fn keep[" ++ parameters ++ "](q:Q<Bits<n>>)->Q<Bits<n>> " ++ premises ++ "{q}"

private def guarded := source "const n:Nat" "requires n>=1,n-1<=3"
private def unguarded := source "const n:Nat" ""
private def mixed :=
  "pub unitary fn keep[const z:Nat,const A:Basis,const a:Nat,const U:Op<A -> A>]" ++
    "(q:Q<A>)->Q<A> requires z>=a,Applicable(U),z-a<=3{q}"

-- The independent expected outcomes do not supply native acceptance.
private def cases : List (String × String × String × StaticNatural.Bindings × Option Nat) := [
    ("guarded subtraction", guarded, "n-1", [("n",3)], some 2),
    ("false earlier premise", guarded, "n-1", [("n",0)], none),
    ("false later premise", guarded, "n-1", [("n",5)], none),
    ("unguarded despite favorable actual", unguarded, "n-1", [("n",3)], none),
    ("nonlinear despite small actual", unguarded, "n*n", [("n",2)], none),
    ("ordered premise cannot be repaired", source "const n:Nat" "requires n-1<=3,n>=1",
      "n", [("n",2)], none),
    ("missing Nat actual", guarded, "n", [], none),
    ("extra Nat actual", guarded, "n", [("n",2),("extra",0)], none),
    ("duplicate Nat actual", source "const n:Nat,const m:Nat" "", "n",
      [("n",2),("n",3)], none),
    ("wrong Nat formal", guarded, "n", [("A",2)], none),
    ("u32 binding overflow", unguarded, "n", [("n",4294967296)], none),
    ("mixed original ordinals", mixed, "z-a", [("a",1),("z",3)], some 2),
    ("mixed bindings may be reordered", mixed, "z-a", [("z",3),("a",1)], some 2),
    ("Basis formal is not a Nat", mixed, "A", [("z",3),("a",1)], none),
    ("Basis binding cannot enter Nat map", mixed, "z-a", [("z",3),("a",1),("A",1)], none),
    ("duplicate access", source "const n:Nat,const U:Op<Bit>" "requires Applicable(U),Applicable(U)",
      "n", [("n",1)], none),
    ("access on Nat", source "const n:Nat" "requires Applicable(n)", "n", [("n",1)], none),
    ("duplicate static formal", source "const n:Nat,const n:Basis" "", "n", [("n",1)], none),
    ("empty static clause", "pub fn keep[]()->Unit{()}", "0", [], none),
    ("original helper with premise", "static fn previous[const x:Nat]()->Nat requires x>=1{x-1} " ++ guarded,
      "previous[n]()", [("n",3)], some 2),
    ("unused invalid helper still refuses", "static fn bad[const x:Nat]()->Nat{x-1} " ++ guarded,
      "n", [("n",2)], none),
    ("formal shadows a helper call", "static fn n()->Nat{2} " ++ unguarded, "n()", [("n",1)], none),
    ("zero coefficient is constant", unguarded, "(n-n)*n+2", [("n",3)], some 2),
    ("closed result u32 overflow", unguarded, "n+4294967295", [("n",1)], none)
  ]


private def naturalComparisons : IO Unit := do
  unless cases.length == 24 do throw (IO.userError "static comparison inventory changed")
  for (name,program,expression,bindings,expected) in cases do
    let actual := run program expression bindings
    unless actual == expected do
      throw (IO.userError s!"static result mismatch: {name}; expected {expected}, got {actual}")
  IO.println "passed 24 original static header/Nat binding comparisons; no execution authority"

private def typeResult (source expression : String) (arguments : StaticTypes.Arguments) :
    Option Semantics.FiniteCarrier.Basis := do
  let tokens ← (lex expression).toOption
  let environment ← ((StaticTypes.prepare #[("main",source)] "main" "keep" arguments).run 10000000).1.toOption
  let result ← ((StaticTypes.readType environment tokens).run 10000000).1.toOption
  return result.basis

private def typeComparisons : IO Unit := do
  let generic := "pub unitary fn keep[const A:Basis,const n:Nat](q:Q<A>)->Q<A> requires n>=1{q}"
  let source := "pub enum Tri{First,Middle,Last} " ++ generic
  let origin : Semantics.FiniteCarrier.Origin := ⟨"main","Tri",source⟩
  let tri : Semantics.FiniteCarrier.Basis := [.enumeration origin ["First","Middle","Last"]]
  let arguments : StaticTypes.Arguments := ⟨[("A",tri)],[("n",2)]⟩
  let cases : List (String × String × String × StaticTypes.Arguments × Option Semantics.FiniteCarrier.Basis) := [
    ("nominal Basis retains the original type",source,"A",arguments,some tri),
    ("type tree and Nat substitution compose",source,"(A,Bits<n-1>)",arguments,
      some ([.pair] ++ tri ++ [.bits 1])),
    ("type axes retain source order",source,"(Bits<n-1>,A)",arguments,
      some ([.pair,.bits 1] ++ tri)),
    ("closed type fallback keeps original declaration",source,"Tri",arguments,some tri),
    ("missing Basis actual",source,"A",{arguments with bases := []},none),
    ("extra Basis actual",source,"A",{arguments with bases := [("A",tri),("B",[.bit])]},none),
    ("duplicate Basis actual",source,"A",{arguments with bases := [("A",tri),("A",tri)]},none),
    ("wrong Basis formal",source,"A",{arguments with bases := [("n",tri)]},none),
    ("Nat formal is not a type",source,"n",arguments,none),
    ("Basis formal is not a size",source,"Bits<A>",arguments,none),
    ("unused stale Basis actual refuses",source,"Bit",
      {arguments with bases := [("A",[.enumeration origin ["Middle","First","Last"]])]},none),
    ("unused changed original bytes refuse",source,"Bit",
      {arguments with bases := [("A",[.enumeration {origin with source := source ++ " "}
        ["First","Middle","Last"]])]},none),
    ("empty finite prefix refuses",source,"A",{arguments with bases := [("A",[])]},none),
    ("Unit actual remains Unit",source,"A",{arguments with bases := [("A",[.unit])]},some [.unit]),
    ("zero Bits actual remains Bits",source,"A",{arguments with bases := [("A",[.bits 0])]},some [.bits 0]),
    ("false original premise refuses",source,"A",{arguments with naturals := [("n",0)]},none),
    ("caller Nat cannot capture nominal fields", "pub struct Packet{field:Bits<n>} " ++ generic,
      "Packet",⟨[("A",[.unit])],[("n",2)]⟩,none),
    ("operation closure remains outside this component",
      "pub unitary fn keep[const U:Op<Bit>](q:Q<Bit>)->Q<Bit> requires Applicable(U){U(q)}",
      "Bit",{},none)
  ]
  unless cases.length == 18 do throw (IO.userError "static type inventory changed")
  for (name,program,expression,bindings,expected) in cases do
    let actual := typeResult program expression bindings
    unless actual == expected do throw (IO.userError ("static type mismatch: " ++ name))
  IO.println "passed 18 original Basis/Nat type substitution comparisons; no runtime activation"

private def runtimeLabels := "pub enum Tri{First,Middle,Last}"

private def runtimeResult (program : String) (arguments : StaticTypes.Arguments) :
    Option (List Semantics.RuntimeType.Tree × Semantics.RuntimeType.Tree) := do
  let result ← ((StaticRuntimeSignature.read
    #[("labels",runtimeLabels),("main",program)] "main" "keep" arguments).run 10000000).1.toOption
  return (result.parameters.map (·.tree),result.result.tree)

private def runtimeComparisons : IO Unit := do
  let tri : Semantics.FiniteCarrier.Basis :=
    [.enumeration ⟨"labels","Tri",runtimeLabels⟩ ["First","Middle","Last"]]
  let arguments : StaticTypes.Arguments := ⟨[("A",tri)],[("n",2)]⟩
  let ordinary := Semantics.RuntimeType.ordinary
  let owner := Semantics.RuntimeType.owner
  let tuple := Semantics.RuntimeType.tuple
  let cases : List (String × String × StaticTypes.Arguments ×
      Option (List Semantics.RuntimeType.Tree × Semantics.RuntimeType.Tree)) := [
    ("original ordinary generic signature",
      "pub fn keep[const A:Basis,const n:Nat](x:A)->A{x}",arguments,
      some ([ordinary tri],ordinary tri)),
    ("mixed owner and ordinary generic signature",
      "pub unitary fn keep[const A:Basis,const n:Nat](q:Q<A>,x:A)->(Q<A>,A){(q,x)}",arguments,
      some ([owner tri,ordinary tri],tuple 2 [owner tri,ordinary tri])),
    ("generic finite product under one owner",
      "pub unitary fn keep[const A:Basis,const n:Nat](q:Q<(A,Bits<n-1>)>)->Q<(A,Bits<n-1>)> requires n>=1{q}",arguments,
      some ([owner ([.pair] ++ tri ++ [.bits 1])],owner ([.pair] ++ tri ++ [.bits 1]))),
    ("generic ordinary tuple retains runtime shape",
      "pub fn keep[const A:Basis,const n:Nat](x:(A,Bits<n>))->(A,Bits<n>){x}",arguments,
      some ([tuple 2 [ordinary tri,ordinary [.bits 2]]],tuple 2 [ordinary tri,ordinary [.bits 2]])),
    ("zero-width owner remains an owner",
      "pub unitary fn keep[const A:Basis](q:Q<A>)->(Q<A>,Unit){(q,())}",⟨[("A",[.unit])],[]⟩,
      some ([owner [.unit]],tuple 2 [owner [.unit],ordinary [.unit]])),
    ("public quantum header needs an explicit effect",
      "pub fn keep[const A:Basis,const n:Nat](q:Q<A>)->Q<A>{q}",arguments,none),
    ("nested quantum ownership refuses",
      "pub unitary fn keep[const A:Basis,const n:Nat](q:Q<Q<A>>)->Q<A>{q}",arguments,none),
    ("closed values cannot repair unguarded signature arithmetic",
      "pub unitary fn keep[const A:Basis,const n:Nat](q:Q<Bits<n-1>>)->Q<Bits<n-1>>{q}",arguments,none),
    ("classical header cannot carry quantum ports",
      "pub classical fn keep(q:Q<Bit>)->Q<Bit>{q}",{},none),
    ("unused original Nat actual is still required",
      "pub fn keep[const A:Basis,const n:Nat](x:A)->A{x}",{arguments with naturals := []},none)
  ]
  unless cases.length == 10 do throw (IO.userError "runtime static signature inventory changed")
  for (name,program,bindings,expected) in cases do
    unless runtimeResult program bindings == expected do
      throw (IO.userError ("runtime static signature mismatch: " ++ name))
  IO.println "passed 10 original runtime signature comparisons; body/native integration remains separate"

def main : IO Unit := do
  naturalComparisons
  typeComparisons
  runtimeComparisons
