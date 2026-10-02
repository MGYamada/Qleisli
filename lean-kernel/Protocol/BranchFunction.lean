import Protocol.Observation
import QleisliKernel.Raw.BranchFunction

/-! Experimental full original branch-function attachments and requests.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Protocol.BranchFunction
open Lean Semantics.ObservingFunction

private def fields (value : Json) (names : List String) : Except String Unit := do
  let actual := (← value.getObj?).toList.map (·.1)
  if actual.length != names.length || !actual.all names.contains then throw "unexpected/missing function fields"

def functionInput (value : Json) : Except String Input := do
  fields value ["signature","implementation","specification","identity"]
  let identity ← value.getObjVal? "identity"
  fields identity ["implementation","specification","sources"]
  let sources ← (← (← identity.getObjVal? "sources").getArr?).toList.mapM fun source => do
    fields source ["name","source"]
    return (← (← source.getObjVal? "name").getStr?,← (← source.getObjVal? "source").getStr?)
  return ⟨← FiniteCodec.basis (← value.getObjVal? "signature"),
    ← Observation.program (← value.getObjVal? "implementation"),
    ← Observation.program (← value.getObjVal? "specification"),
    ⟨← (← identity.getObjVal? "implementation").getStr?,
      ← (← identity.getObjVal? "specification").getStr?,sources⟩⟩

def inputs (value : Json) : Except String (List Input) :=
  do (← value.getArr?).toList.mapM functionInput

end QleisliKernel.Protocol.BranchFunction
