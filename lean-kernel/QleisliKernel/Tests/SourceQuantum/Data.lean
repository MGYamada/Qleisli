import QleisliKernel.SourceTypes.QuantumArms

/-! Small original-source quantum-header/site/arm regressions. These test
metadata and source binding only, separately from actual QIRF body equations.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.SourceQuantum
open SourceTypes Semantics.FiniteCarrier Semantics.Raw

def source (table : String := "Tri::C=>keep,Tri::A=>keep,Tri::B=>keep")
    (arm : String := "unitary fn keep(q:Q<Bit>)->Q<Bit>{q}") :=
  "// λ original qmatch in comment is not a site\npub enum Tri { A,B,C } " ++ arm ++
    " pub unitary fn choose(s:Q<Tri>,q:Q<Bit>)->(Q<Tri>,Q<Bit>){qmatch(s,q){" ++ table ++ "}}"

def selector (text : String) : Basis := [.enumeration ⟨"main","Tri",text⟩ ["A","B","C"]]

def offset (text : String) : Nat :=
  ((((lexLocated text).toOption.getD []).find? (·.text == "qmatch")).map
    (·.span.startByte)).getD text.utf8ByteSize

def error {α : Type} (value : Except Finite.Error α) : Option Finite.Error :=
  match value with | .ok _ => none | .error error => some error

def tableView (text : String) (basis : Basis) (target : Basis := [.bit]) :=
  ((QuantumArms.read #[("main",text)] "main" "choose" (offset text) basis target).run 10000000).1.map
    fun table => table.arms.map (·.label.ordinal)

def signatureView (text : String) :=
  ((QuantumSignature.read #[("main",text)] "main" "keep").run 10000000).1.map
    fun checked => (checked.inputs,checked.outputs,checked.original.parsedHeader.effect)

def siteError (text : String) (name : String := "choose") (delta : Nat := 0) :=
  error ((QuantumMatch.read #[("main",text)] "main" name (offset text+delta)).run 10000000).1

end QleisliKernel.Tests.SourceQuantum
