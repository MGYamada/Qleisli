import QleisliKernel.SourceTypes.SourceSyntax

/-! Every original ordinary match arm remains present, including complete block
and initializer slices. These syntax controls confer no runtime/native result.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.SourceMatchSyntax
open QleisliKernel QleisliKernel.SourceTypes

private def read (source : String) := do
  let tokens ← lexLocated source
  let written ← QleisliKernel.SourceTypes.SourceMatchSyntax.read tokens
  return (⟨tokens,written⟩ : Sigma SourceMatchSyntax.Checked)

#guard (read "match c{Tag::Off=>{f(q)},Tag::On=>g(q),}").toOption.map (fun checked =>
  (checked.2.parts.arms.map (·.label.member.text),checked.2.parts.arms.map (·.body.opening.isSome))) =
  some (["Off","On"],[true,false])
#guard (read "match (Box{field:Tag::Off}).field{Tag::Off=>(),Tag::On=>()}").isOk
#guard (read "match c{_=>q}").toOption.isNone
#guard (read "match c{Tag::Off= >q}").toOption.isNone
#guard (read "match c{Tag::Off=>q}extra").toOption.isNone
#guard (read "match c{}").toOption.isNone

private def tree := do
  let tokens ← lexLocated "match f(q){Tag::Off=>{g(q)},Tag::On=>h(q)}"
  let parsed ← SourceSyntax.read (tokens.length+1) 0 true tokens
  return (⟨tokens,parsed⟩ : Sigma SourceSyntax.Tree)
#guard (tree.bind (fun checked => checked.2.calls)).toOption.map List.length = some 3

#print axioms QleisliKernel.SourceTypes.SourceMatchSyntax.read
end QleisliKernel.Tests.SourceMatchSyntax
