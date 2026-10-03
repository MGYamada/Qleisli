import QleisliKernel.Semantics.ObservingFunction

/-! Original QIRF data and budget-independent requested table interpretation.
No acceptance rule, work policy, transport decoder or producer receipt is used.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf
open Semantics.Finite Semantics.Observation

inductive Target where
  | circuit (program : Nat)
  | permutation (table : List Nat)
  | phase8 (table : List Nat)

structure Entry where
  signature : Basis
  implementation : Nat
  target : Target
  implementationName : String
  specificationName : String
  sources : List Nat

structure Artifact where
  programs : Array Program
  entries : Array Entry
  sources : Array (String × String)
  root : Nat
  rootInterface : Option (Basis × Basis)

end QleisliKernel.Qirf

namespace QleisliKernel.Semantics.Qirf
open Finite Observation

/-- Literal low-axis table semantics. Well-formedness and capacity checks are
separate acceptance obligations; neither affects this reference reader. -/
def targetProgram (signature : Basis) (target : QleisliKernel.Qirf.Target) : Option Program := do
  let bits := width signature
  let (permutation,phases) ← match target with
    | .permutation table => some (table,List.replicate table.length 0)
    | .phase8 table => some (List.range table.length,table)
    | .circuit _ => none
  let step : Step := ⟨[],.monomial (List.range bits) permutation phases⟩
  return ⟨[⟨0,List.range bits,bits⟩],[],[.pure (.applyUnitary 0 1 [step])],[1],[],.unitary⟩

end QleisliKernel.Semantics.Qirf
