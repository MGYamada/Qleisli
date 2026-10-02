import Protocol.BranchFunction
import QleisliKernel.Raw.StreamedInstrument

/-! Experimental original matrix-free instrument envelope; production transport
binding and native packaging remain separate VM-28/29 obligations.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Protocol.StreamedObservation
open Lean

structure Artifact where
  dependencies : List Semantics.ObservingFunction.Input
  bindings : List Semantics.ObservingFunction.Binding
  program : Semantics.Observation.Program

def artifact (value : Json) : Except String Artifact := do
  let actual := (← value.getObj?).toList.map (·.1)
  let names := ["format","version","dependencies","bindings","program"]
  if actual.length != names.length || !actual.all names.contains then throw "unexpected/missing instrument fields"
  if (← (← value.getObjVal? "format").getStr?) != "qleisli.raw-instrument-component" ||
      (← (← value.getObjVal? "version").getNat?) != 1 then throw "unknown instrument profile"
  return ⟨← BranchFunction.inputs (← value.getObjVal? "dependencies"),
    ← BranchFunction.inputs (← value.getObjVal? "bindings"),
    ← Observation.program (← value.getObjVal? "program")⟩

end QleisliKernel.Protocol.StreamedObservation
