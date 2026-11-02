import QleisliKernel.SourceTypes.SourceRuntimeNominalValue
import QleisliKernel.SourceTypes.SourceBasisFunction

/-! Small logical nominal value maps. These preparation checks retain full
nominal types and zero-width members, without a runtime source/native handle.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.SourceRuntimeNominalValue
open QleisliKernel QleisliKernel.SourceTypes SourceRuntimeValues

private def sources : Sources :=
  #[("main","pub struct Box{pub first:Bit,pub last:Unit}pub struct Pair{pub field:(Bit,Unit)}pub struct Empty{}pub enum Tag{Off,On}")]

private def construct (reversed : Bool := false) := do
  let tokens ← Finite.lift ((lexLocated "Box{last:(),first:b}").mapError fun _ => .request)
  let written ← Finite.lift ((SourceNominalSyntax.readRecord tokens).mapError fun _ => .request)
  let reference ← SourceNominal.readRecord sources "main" [] written
  let arguments : List Value := if reversed then [[.ordinary [.bit] (.basisInput 0)],[.ordinary [.unit] .unit]]
    else [[.ordinary [.unit] .unit],[.ordinary [.bit] (.basisInput 0)]]
  let value ← Finite.lift ((SourceRuntimeNominalValue.construct reference arguments).mapError fun _ => .request)
  let function ← SourceBasisFunction.read [.bit] reference.nominal.query.basis [] value
  return (function.rows,function.effect,typeOf value == Semantics.RuntimeType.ordinary reference.nominal.query.basis)

#guard ((construct false).run 10000000).1.toOption = some ([[0,1]],.unitary,true)
#guard ((construct true).run 10000000).1.isError

private def projection := do
  let query ← typeExpressionWithSources sources "main" ["Box"]
  let tokens ← Finite.lift ((lexLocated "value.first").mapError fun _ => .request)
  let written ← Finite.lift ((SourceNominalSyntax.readProjection tokens).mapError fun _ => .request)
  let reference ← SourceNominal.readProjection sources "main" query.basis written
  let value ← Finite.lift ((SourceRuntimeNominalValue.project reference (.basisInput 0)).mapError fun _ => .request)
  let function ← SourceBasisFunction.read query.basis [.bit] [] value
  return (function.rows,function.effect)
#guard ((projection).run 10000000).1.toOption = some ([[0,1]],.unitary)

private def nestedProjection := do
  let query ← typeExpressionWithSources sources "main" ["Pair"]
  let tokens ← Finite.lift ((lexLocated "value.field").mapError fun _ => .request)
  let written ← Finite.lift ((SourceNominalSyntax.readProjection tokens).mapError fun _ => .request)
  let reference ← SourceNominal.readProjection sources "main" query.basis written
  let value ← Finite.lift ((SourceRuntimeNominalValue.project reference (.basisInput 0)).mapError fun _ => .request)
  let result ← Finite.lift ((SourceRuntimeValues.bind ["(","b",",","u",")"] value []).mapError fun _ => .request)
  return (result.map (·.name),typeOf value == Semantics.RuntimeType.ordinary [.pair,.bit,.unit])
#guard ((nestedProjection).run 10000000).1.toOption = some (["u","b"],true)

private def emptyRecord := do
  let tokens ← Finite.lift ((lexLocated "Empty{}").mapError fun _ => .request)
  let written ← Finite.lift ((SourceNominalSyntax.readRecord tokens).mapError fun _ => .request)
  let reference ← SourceNominal.readRecord sources "main" [] written
  let value ← Finite.lift ((SourceRuntimeNominalValue.construct reference []).mapError fun _ => .request)
  let function ← SourceBasisFunction.read [.unit] reference.nominal.query.basis [] value
  return (function.rows,function.effect,typeOf value == Semantics.RuntimeType.ordinary [.unit])
#guard ((emptyRecord).run 10000000).1.toOption = some ([[0]],.unitary,false)

private def constructor := do
  let tokens ← Finite.lift ((lexLocated "Tag::On").mapError fun _ => .request)
  let written ← Finite.lift ((SourceNominalSyntax.readVariant tokens).mapError fun _ => .request)
  let reference ← SourceNominal.readVariant sources "main" [] written
  let function ← SourceBasisFunction.read [.unit] reference.nominal.query.basis []
    [.ordinary reference.nominal.query.basis (.ordinal reference.ordinal)]
  return (function.rows,function.effect)
#guard ((constructor).run 10000000).1.toOption = some ([[1]],.iso)

#guard (SourceRuntimeNominalValue.collapse [.owner ⟨0,[.bit]⟩]).isError

#print axioms QleisliKernel.SourceTypes.SourceRuntimeNominalValue.construct
#print axioms QleisliKernel.SourceTypes.SourceRuntimeNominalValue.project
#print axioms QleisliKernel.SourceTypes.SourceRuntimeNominalValue.expand
end QleisliKernel.Tests.SourceRuntimeNominalValue
