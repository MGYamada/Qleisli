import QleisliKernel.SourceTypes.PhaseApplication

/-! Small closed generic Nat/phase regressions, separately from source-body,
Raw interval, control and native acceptance. Normal #guard evaluation retains
no large closed reduction proof terms and constructs no maximum-size system.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.GenericPhase
open SourceTypes Finite

private def adapt {α : Type} (value : Except String α) : WorkM α :=
  lift (value.mapError fun _ => .request)

private def source (body : String) (requirements : String := "") : String :=
  "#![no_implicit_prelude] pub unitary fn phase_arm[const n:Nat](q:Q<Bit>)->Q<Bit> " ++
    requirements ++ "{" ++ body ++ "}"

private def phase (sources : Sources) (arguments : StaticTypes.Arguments) : Option (Nat × Nat × List String) :=
  let action : WorkM (Nat × Nat × List String) := do
    let signature ← QuantumSignature.readWithArguments sources "main" "phase_arm" arguments
    let initial ← PhaseApplication.prepareWithSignature signature
    let preamble ← adapt (StaticBindings.readPrefix signature.original.occurrence.body)
    let (naturals,scope) ← PhaseApplication.extend sources "main" preamble initial (signature.staticNames ++ ["q"])
    let call ← adapt (CallSyntax.read preamble.suffix)
    let checked ← PhaseApplication.read sources "main" naturals scope call
    pure (checked.j.result.value,checked.k.result.value,naturals.sourceRows.map (·.1))
  (action.run 10000000).1.toOption

private def plain (body : String) (n : Nat) (requirements : String := "") : Option (Nat × Nat) :=
  (phase #[ ("main",source body requirements) ] {naturals := [("n",n)]}).map fun (j,k,_) => (j,k)

-- Closed substitution cannot repair unsupported symbolic multiplication.
#guard plain "phase[n*n,3](q)" 0 = none

-- A convenient zero result cannot supply the missing original subtraction premise.
#guard plain "phase[n-1,3](q)" 1 = none

#guard plain "phase[n-1,3](q)" 2 "requires n>=1" = some (1,3)

#guard plain "static let alias=n-1;phase[alias,3](q)" 2 "requires n>=1" = some (1,3)

-- Unused initializers still undergo original symbolic checking.
#guard plain "static let unused=n*n;phase[0,3](q)" 0 = none

-- Closed caller actuals and every intermediate remain u32.
#guard plain "static let unused=n+1;phase[0,3](q)" 4294967295 = none

private def helper : String := "pub static fn next[const n:Nat]()->Nat{n+1}"
private def unused : String := "pub static fn spare[const n:Nat]()->Nat{n}"

private def helperPhase (body : String) (requirements : String := "") : Sources :=
  #[ ("main","#![no_implicit_prelude] use helpers::next; pub unitary fn phase_arm[const n:Nat](q:Q<Bit>)->Q<Bit> " ++
      requirements ++ "{" ++ body ++ "}"),("helpers",helper),("unused",unused) ]

-- An unused helper initializer retains its actual import route, without covering a global unused helper.
#guard (phase (helperPhase "static let ignored=next[n]();phase[0,3](q)") {naturals := [("n",1)]}).map
    (fun (j,k,rows) => (j,k,rows.contains "helpers",rows.contains "unused")) = some (0,3,true,false)

-- Header premises preserve their actual helper route even without a body call.
#guard (phase (helperPhase "phase[0,3](q)" "requires n>=next[0]()") {naturals := [("n",1)]}).map
    (fun (j,k,rows) => (j,k,rows.contains "helpers",rows.contains "unused")) = some (0,3,true,false)

#guard phase (helperPhase "phase[0,3](q)" "requires n>=next[0]()") {naturals := [("n",0)]} = none

private def unusedActual : String :=
  "#![no_implicit_prelude] pub unitary fn phase_arm[const n:Nat,const unused:Nat](q:Q<Bit>)->Q<Bit> requires unused>=1{phase[0,3](q)}"

-- Named actual completeness, original predicates and u32 checks include unused bindings.
#guard phase #[ ("main",unusedActual) ] {naturals := [("n",1),("unused",0)]} = none
#guard phase #[ ("main",unusedActual) ] {naturals := [("n",1)]} = none
#guard phase #[ ("main",unusedActual) ] {naturals := [("n",1),("unused",4294967296)]} = none
#guard phase #[ ("main",unusedActual) ] {naturals := [("n",1),("unused",1),("unexpected",0)]} = none

end QleisliKernel.Tests.GenericPhase
