import QleisliKernel.Tests.OrdinaryInputs

/-! Execute all bounded controls against actual compiled definitions. These
observations are conformance tests, not kernel proofs of their Boolean results.
Generic signature/domain/history postconditions remain proved in the production
modules. Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/

def main : IO Unit := do
  let controls := QleisliKernel.Tests.OrdinaryInputs.controls
  let failures := controls.filter (fun control => !control.2)
  unless controls.length == 20 && failures.isEmpty do
    throw (IO.userError ("ordinary input/history controls failed: " ++
      String.intercalate "; " (failures.map (·.1))))
  IO.println "passed 20 complete input/all-history controls; at most one qubit"
