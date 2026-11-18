import QleisliKernel.SourceTypes.AccessSyntax
import QleisliKernel.SourceTypes.RuntimeSignature
import QleisliKernel.SourceTypes.StaticRuntimeSignature

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

private structure AccessSample where
  role : String
  owner : String
  ownerStart : Nat
  markerStart : Nat
  markerEnd : Nat
  types : List String
  deriving DecidableEq

private def declaredAccess (text : String) : Option (List (Option AccessSample)) := do
  let original ← ((OrdinarySignature.readOriginalEnvelope #[("main",text)] "main" "keep").run 10000000).1.toOption
  let declared ← (AccessSyntax.readDeclaredParameters original).toOption
  return declared.parameters.map fun parameter =>
    match parameter.2 with
    | .ordinary _ => none
    | .access written =>
      let role := match written.role with | .ctrl => "ctrl" | .excl => "excl"
      some ⟨role,written.owner.text,written.owner.span.startByte,written.marker.span.startByte,
        written.marker.span.endByte,written.typeTokens.map (·.text)⟩

theorem declared_access_retains_roles_order_and_locations :
    declaredAccess
      "pub unitary fn keep(q:ctrl Q<(Bit,Bits<2>)>, note:excl, r:excl Q<Unit>, ctrl:Q<Bit>)->Unit{()}" =
      some [some ⟨"ctrl","q",20,22,26,["Q","<","(","Bit",",","Bits","<","2",">",")",">"]⟩,
        none,some ⟨"excl","r",56,58,62,["Q","<","Unit",">"]⟩,none] := by decide +kernel

theorem declared_access_requires_one_named_owner_and_one_complete_type :
    declaredAccess "pub unitary fn keep(_:ctrl Q<Bit>)->Unit{()}" = none ∧
    declaredAccess "pub unitary fn keep((x,y):excl Q<(Bit,Bit)>)->Unit{()}" = none ∧
    declaredAccess "pub unitary fn keep(q:ctrl Q<Bit><Unit>)->Unit{()}" = none ∧
    declaredAccess "pub unitary fn keep(q:ctrl Q<>)->Unit{()}" = none := by decide +kernel

theorem declared_access_is_runtime_syntax :
    declaredAccess "pub classical fn keep(q:ctrl Q<Bit>)->Unit{()}" = none ∧
    declaredAccess "pub static fn keep(q:excl Q<Bit>)->Unit{()}" = none := by decide +kernel

private def runtimeHeader (text : String) : Bool :=
  ((RuntimeSignature.read #[("main",text)] "main" "keep").run 10000000).1.isOk

theorem declared_access_does_not_project_an_unmarked_runtime_type :
    header "pub unitary fn keep(q:ctrl Q<Bit>)->Unit{()}" =
      some (none,[["ctrl","Q","<","Bit",">"]],["Unit"],none) ∧
    runtimeHeader "pub unitary fn keep(q:ctrl Q<Bit>)->Unit{()}" = false ∧
    runtimeHeader "pub unitary fn keep(q:Q<Bit>)->Q<Bit>{q}" = true := by decide +kernel

private structure DeclaredResultSample where
  slots : List (Nat × String × String)
  source : Semantics.RuntimeType.Tree
  hidden : Semantics.RuntimeType.Tree
  deriving DecidableEq

private def declaredResult (text : String) : Option DeclaredResultSample := do
  let original ← ((OrdinarySignature.readOriginalEnvelope #[("main",text)] "main" "keep").run 10000000).1.toOption
  let prepared ← ((RuntimeSignature.readDeclaredAccess original).run 10000000).1.toOption
  let slots := prepared.owners.map fun owner =>
    let role := match owner.role with | .ctrl => "ctrl" | .excl => "excl"
    (owner.ordinal,owner.owner.text,role)
  return ⟨slots,prepared.sourceResult.tree,prepared.hiddenResult⟩

theorem declared_owner_return_follows_the_original_marked_slots :
    declaredResult "pub unitary fn keep(c:ctrl Q<Bits<2>>,tag:Bit,z:excl Q<Unit>)->Unit{()}" =
      some ⟨[(0,"c","ctrl"),(2,"z","excl")],Semantics.RuntimeType.ordinary [.unit],
        Semantics.RuntimeType.tuple 2 [Semantics.RuntimeType.owner [.bits 2],Semantics.RuntimeType.owner [.unit]]⟩ :=
  by decide +kernel

theorem declared_single_owner_return_keeps_the_full_type :
    declaredResult "pub unitary fn keep(q:excl Q<(Bit,Unit)>)->Unit{()}" =
      some ⟨[(0,"q","excl")],Semantics.RuntimeType.ordinary [.unit],
        Semantics.RuntimeType.owner [.pair,.bit,.unit]⟩ := by decide +kernel

theorem declared_access_requires_unit_and_no_unmarked_owners :
    declaredResult "pub unitary fn keep(q:excl Q<Unit>)->Q<Unit>{q}" = none ∧
    declaredResult "pub unitary fn keep(q:excl Q<Unit>,r:Q<Unit>)->Unit{()}" = none ∧
    declaredResult "pub unitary fn keep(q:excl Q<Unit>,r:(Bit,Q<Unit>))->Unit{()}" = none ∧
    declaredResult "pub unitary fn keep(r:Unit)->Unit{()}" = none := by decide +kernel

theorem declared_access_retains_the_public_effect_boundary :
    declaredResult "pub observe fn keep(q:excl Q<Unit>)->Unit{()}" = none ∧
    declaredResult "pub isometry fn keep(q:excl Q<Unit>)->Unit{()}" = none ∧
    declaredResult "pub fn keep(q:excl Q<Unit>)->Unit{()}" = none ∧
    declaredResult "fn keep(q:excl Q<Unit>)->Unit{()}" =
      some ⟨[(0,"q","excl")],Semantics.RuntimeType.ordinary [.unit],Semantics.RuntimeType.owner [.unit]⟩ :=
  by decide +kernel

private def markedInterface (access : List StaticRuntimeSignature.MarkedSlot) :
    Option Semantics.RuntimeType.Tree := do
  let sources := #[("main","pub unitary fn keep(c:ctrl Q<Bit>,tag:Unit,q:excl Q<Unit>)->Unit{()}")]
  let checked ← ((StaticRuntimeSignature.prepareWithArguments sources "main" "keep" {}
    (access := access)).run 10000000).1.toOption
  return checked.result.tree

theorem marked_interface_requires_the_exact_original_slots_and_roles :
    markedInterface [(0,.ctrl),(2,.excl)] =
      some (Semantics.RuntimeType.tuple 2 [Semantics.RuntimeType.owner [.bit],
        Semantics.RuntimeType.owner [.unit]]) ∧
    markedInterface [] = none ∧
    markedInterface [(0,.excl),(2,.excl)] = none ∧
    markedInterface [(0,.ctrl),(1,.excl)] = none := by decide +kernel

end QleisliKernel.Tests.RuntimeStaticHeader
