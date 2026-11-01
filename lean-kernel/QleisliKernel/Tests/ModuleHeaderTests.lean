import QleisliKernel.SourceTypes.QuantumSignature
import QleisliKernel.SourceTypes.RuntimeSignature
import QleisliKernel.SourceTypes.Members
import QleisliKernel.SourceTypes.CallName

/-! Original module/directive conformance. Success here reads declarations;
it supplies no body-lowering or execution-preservation theorem.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.ModuleHeaderTests
open QleisliKernel.SourceTypes

private def directive := "#![no_implicit_prelude]\n"
private def sign := "pub unitary fn sign(q:Q<Bit>)->Q<Bit>{phase[1,1](q)}"
private def ordinary (source : String) (name : String := "sign") : Bool :=
  ((OrdinarySignature.readOriginalEnvelope #[("main",source)] "main" name).run 10000000).1.isOk

#guard ordinary sign
#guard ordinary (directive ++ sign)
#guard ordinary ("// λ before the original header\n" ++ directive ++ sign)
#guard ordinary (directive ++ sign ++ " unitary fn next(q:Q<Bit>)->Q<Bit>{q}") "next"
#guard ordinary (directive ++ "use leaf::keep; " ++ sign)
#guard ordinary (directive ++ "enum E{A,B} " ++ sign)
#guard ordinary (directive ++ "pub unitary fn generic[const n:Nat](q:Q<Bit>)->Q<Bit>{q}") "generic"

-- These remain complete original tokens, including the authenticated directive.
#guard (((OrdinarySignature.readOriginalEnvelope #[("main",directive ++ sign)] "main" "sign").run
    10000000).1.toOption.map fun original =>
      (original.source,original.occurrence.header.take 5 |>.map (·.text))) =
    some (directive ++ sign,["#","!","[","no_implicit_prelude","]"])
#guard ((QuantumSignature.read #[("main",directive ++ sign)] "main" "sign").run 10000000).1.isOk
#guard ((RuntimeSignature.read #[("main",directive ++
    "pub observe fn mixed(q:Q<Bit>,b:Bit)->(Q<Bit>,Bit){(q,b)}")] "main" "mixed").run 10000000).1.isOk

-- Attribute projection confers no static substitution or quantum capability.
#guard !((OrdinarySignature.readOriginal #[("main",directive ++
    "pub unitary fn generic[const n:Nat](q:Q<Bit>)->Q<Bit>{q}")] "main" "generic").run 10000000).1.isOk

private def nominal (source : String) : Bool :=
  ((Members.readOriginal #[("main",source)] "main" "E").run 10000000).1.isOk
#guard nominal (directive ++ "pub enum E{A,B}")
#guard nominal ("// λ\n" ++ directive ++ "pub struct E{pub b:Bit}")

private def malformed : List String := [
  directive ++ directive ++ sign,
  "use leaf::keep; " ++ directive ++ sign,
  "enum E{A,B} " ++ directive ++ sign,
  sign ++ directive,
  "#![unknown]\n" ++ sign,
  "#![no_implicit_prelude\n" ++ sign,
  "#[no_implicit_prelude]\n" ++ sign]
#guard malformed.all fun source => !ordinary source
#guard !nominal (directive ++ directive ++ "pub enum E{A,B}")
#guard !nominal ("use leaf::keep; " ++ directive ++ "pub enum E{A,B}")

-- A copied directive with foreign source positions cannot become a prefix.
private def foreignPrefixRefused : Bool :=
  match lexLocated (directive ++ sign), sourceCatalogue ("// λ\n" ++ directive ++ sign) with
  | .ok foreign, .ok catalogue =>
    match catalogue.bodies with
    | [body] => !(ModuleHeader.project ("// λ\n" ++ directive ++ sign)
        (foreign.take 5 ++ body.header.drop 5)).isOk
    | _ => false
  | _,_ => false
#guard foreignPrefixRefused

#guard (CallName.policyTokens ["#","!","[","no_implicit_prelude","]","fn"]).toOption = some true
#guard (CallName.policyTokens ["fn"]).toOption = some false
#guard (CallName.policyTokens ["fn","#","!","[","no_implicit_prelude","]"]).isOk = false

end QleisliKernel.Tests.ModuleHeaderTests
