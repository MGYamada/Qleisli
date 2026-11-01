import QleisliKernel.SourceTypes.SymbolicTypes

/-! Small opaque Basis and exact affine-type regressions. No symbolic type
comparison grants native body preservation or an operation implementation.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.SymbolicTypes
open SourceTypes Finite Semantics.SymbolicBasis

private def source (requirements : String) :=
  "#![no_implicit_prelude] struct Cell{value:Bit} " ++
  "pub unitary fn generic[const A:Basis,const n:Nat,const m:Nat](q:Q<A>)->Q<A> " ++ requirements ++ "{q}"

private def signature (requirements : String := "") :
    WorkM (QuantumSignatureCore.Checked #[("main",source requirements)] "main" "generic") :=
  QuantumSignatureCore.prepareWithArguments #[("main",source requirements)] "main" "generic"
    {bases := [("A",[.bit])],naturals := [("n",1),("m",1)]}

-- The selected Bit remains the original opaque Basis parameter in source types.
#guard
  (((do
    let signature ← signature
    let symbolic ← SourceTypes.SymbolicTypes.readSignature signature
    pure (symbolic.inputs.map (·.code),symbolic.outputs.map (·.code))) : WorkM _).run 10000000).1.toOption =
      some ([[.parameter ⟨"main","generic",0⟩]],[[.parameter ⟨"main","generic",0⟩]])

private def equalTypes (left right : List String) (requirements : String := "") : Bool :=
  let action : WorkM Unit := do
    let signature ← signature requirements
    let symbolic ← SourceTypes.SymbolicTypes.readSignature signature
    let left ← SourceTypes.SymbolicTypes.read symbolic.state signature.staticNames signature.staticNames.length left
    let right ← SourceTypes.SymbolicTypes.read symbolic.state signature.staticNames signature.staticNames.length right
    let _ ← SourceTypes.SymbolicTypes.equate symbolic.state left.result.code right.result.code
    pure ()
  (action.run 10000000).1.isOk

#guard equalTypes ["A"] ["Bit"] = false
#guard equalTypes ["A"] ["(","Bit",",","Unit",")"] = false
#guard equalTypes ["Cell"] ["Bit"] = false
#guard equalTypes ["Bits","<","0",">"] ["Unit"] = false

-- Equal selected widths do not prove equality of unrelated original Nat names.
#guard equalTypes ["Bits","<","n",">"] ["Bits","<","m",">"] = false
#guard equalTypes ["Bits","<","n",">"] ["Bits","<","m",">"] "requires n==m" = true
#guard equalTypes ["Bits","<","n","+","n",">"] ["Bits","<","2","*","n",">"] = true

-- Substitution is simultaneous even for an original recursive call identity.
#guard
  ((SourceTypes.SymbolicTypes.substitute 0 [(⟨"main","generic",0⟩,[.parameter ⟨"main","generic",0⟩])]
    [] [.parameter ⟨"main","generic",0⟩]).run 10000000).1.toOption.map (·.code) =
      some [.parameter ⟨"main","generic",0⟩]

end QleisliKernel.Tests.SymbolicTypes
