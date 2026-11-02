import QleisliKernel.SourceTypes.SourceSyntax

/-! Original static comparisons and both untouched branch slices. These syntax
checks grant neither a chosen-instance typing rescue nor recursive access.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.SourceStaticControlSyntax
open QleisliKernel QleisliKernel.SourceTypes

private def read (source : String) := do
  let tokens ← lexLocated source
  let checked ← QleisliKernel.SourceTypes.SourceStaticControlSyntax.read tokens
  return (⟨tokens,checked⟩ : Sigma SourceStaticControlSyntax.Checked)

#guard (read "if static n==0{q}else{f[n-1](q)}").isOk
#guard (read "if static n+1>=next[n](){h(q)}else{q}").isOk
#guard (read "if n==0{q}else{q}").toOption.isNone
#guard (read "if static n{q}else{q}").toOption.isNone
#guard (read "if static n==0{q}else{q}q").toOption.isNone
#guard (read "if static n==0{q}else{q}").toOption.map (fun checked =>
  (checked.2.parts.condition.map (·.text),checked.2.parts.thenBody.map (·.text),
    checked.2.parts.elseBody.map (·.text))) = some (["n","=","=","0"],["q"],["q"])

private def tree := do
  let tokens ← lexLocated "if static n==0{f(q)}else{g(q)}"
  let tree ← SourceSyntax.read (tokens.length+1) 0 true tokens
  return (⟨tokens,tree⟩ : Sigma SourceSyntax.Tree)
#guard tree.toOption.map (fun tree => match tree.2 with
  | .staticConditional .. => true | _ => false) = some true
#guard (tree.bind (fun packed => packed.2.calls)).toOption.map List.length = some 2

#print axioms QleisliKernel.SourceTypes.SourceStaticControlSyntax.read
end QleisliKernel.Tests.SourceStaticControlSyntax
