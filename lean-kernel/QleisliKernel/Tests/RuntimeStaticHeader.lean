import QleisliKernel.SourceTypes.OrdinarySignature

/-! Original static header retention only. These checks deliberately do not
activate generic execution, instantiate an operation or accept its constraints.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.RuntimeStaticHeader
open SourceTypes

private def header (text : String) : Option
    (Option (List String) × List (List String) × List String × Option (List String)) :=
  match (OrdinarySignature.readOriginalEnvelope #[("main",text)] "main" "keep").run 10000000 |>.1 with
  | .error _ => none
  | .ok value => some (value.parsedHeader.staticTokens.map (List.map (·.text)),
      value.parsedHeader.parameterTypes,value.parsedHeader.resultTokens.map (·.text),
      value.parsedHeader.requiresTokens.map (List.map (·.text)))

private def closed (text : String) : Bool :=
  match (OrdinarySignature.readOriginal #[("main",text)] "main" "keep").run 10000000 |>.1 with
  | .error _ => false
  | .ok _ => true

theorem closed_header_retains_its_original_shape :
    header "pub fn keep(x:Bit)->Bit{x}" = some (none,[["Bit"]],["Bit"],none) := by decide +kernel

theorem basis_binder_is_not_erased :
    header "pub fn keep[const A:Basis](x:A)->A{x}" =
      some (some ["const","A",":","Basis"],[["A"]],["A"],none) := by decide +kernel

theorem nat_premises_keep_original_order :
    header "pub unitary fn keep[const n:Nat](q:Q<Bits<n>>)->Q<Bits<n>> requires n>=1,n<=3{q}" =
      some (some ["const","n",":","Nat"],[["Q","<","Bits","<","n",">",">"]],
        ["Q","<","Bits","<","n",">",">"],
        some ["n",">","=","1",",","n","<","=","3"]) := by decide +kernel

theorem operation_arrow_and_access_are_original_tokens :
    header "pub isometry fn keep[const A:Basis,const B:Basis,const U:Op<A -> B>](q:Q<A>)->Q<B> requires Applicable(U){U(q)}" =
      some (some ["const","A",":","Basis",",","const","B",":","Basis",",",
        "const","U",":","Op","<","A","-",">","B",">"],
        [["Q","<","A",">"]],["Q","<","B",">"],
        some ["Applicable","(","U",")"]) := by decide +kernel

theorem explicit_empty_binders_are_distinct_from_no_binders :
    header "pub fn keep[](x:Bit)->Bit{x}" = some (some [],[["Bit"]],["Bit"],none) := by decide +kernel

theorem empty_premises_refuse :
    header "pub fn keep(x:Bit)->Bit requires {x}" = none := by decide +kernel

theorem unmatched_static_bracket_refuses :
    header "pub fn keep[const A:Basis(x:A)->A{x}" = none := by decide +kernel

theorem ordinary_gate_still_refuses_generic_binders :
    closed "pub fn keep[const A:Basis](x:A)->A{x}" = false := by decide +kernel

theorem ordinary_gate_still_refuses_unchecked_premises :
    closed "pub fn keep(x:Bit)->Bit requires 1==0{x}" = false := by decide +kernel

theorem ordinary_gate_still_accepts_closed_header :
    closed "pub fn keep(x:Bit)->Bit{x}" = true := by decide +kernel

end QleisliKernel.Tests.RuntimeStaticHeader
