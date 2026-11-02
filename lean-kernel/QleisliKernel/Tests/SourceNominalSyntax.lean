import QleisliKernel.SourceTypes.SourceSyntax

/-! Located nominal slices preserve written initializer evaluation order and
receiver calls. No catalogue, privacy, typing or native result is inferred here.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.SourceNominalSyntax
open QleisliKernel QleisliKernel.SourceTypes

private def record (source : String) := do
  let tokens ← lexLocated source
  let written ← SourceNominalSyntax.readRecord tokens
  return (⟨tokens,written⟩ : Sigma SourceNominalSyntax.Record)

#guard (record "Box{second:f(q),first:(),}").toOption.map (fun checked =>
  checked.2.initializers.map (·.name.text)) = some ["second","first"]
#guard (record "Empty{}").toOption.map (fun checked => checked.2.initializers.length) = some 0
#guard (record "Box{first,second:()}").isError
#guard (record "Box{first:()}extra").isError

private def tree (source : String) := do
  let tokens ← lexLocated source
  let parsed ← SourceSyntax.read (tokens.length+1) 0 true tokens
  return (⟨tokens,parsed⟩ : Sigma SourceSyntax.Tree)

#guard (tree "lib::Tag::On").toOption.map (fun checked => match checked.2 with
  | .variant written => written.typeTokens.map (·.text) == ["lib","::","Tag"] && written.member.text == "On"
  | _ => false) = some true
#guard (tree "Box{second:f(q),first:g(q)}").toOption.map (fun checked => match checked.2 with
  | .record written children => written.initializers.map (·.name.text) == ["second","first"] &&
      children.trees.length == 2
  | _ => false) = some true
#guard ((tree "Box{second:f(q),first:g(q)}").bind (fun checked => checked.2.calls)).toOption.map List.length = some 2
#guard ((tree "(f(q)).chosen").bind (fun checked => checked.2.calls)).toOption.map List.length = some 1
#guard (tree "not value.chosen").toOption.map (fun checked => match checked.2 with
  | .boolean .. => true | _ => false) = some true

#print axioms QleisliKernel.SourceTypes.SourceNominalSyntax.readRecord
#print axioms QleisliKernel.SourceTypes.SourceNominalSyntax.readVariant
#print axioms QleisliKernel.SourceTypes.SourceNominalSyntax.readProjection
end QleisliKernel.Tests.SourceNominalSyntax
