import QleisliKernel.SourceTypes.GenericBasisInstance
import QleisliKernel.SourceTypes.StaticRuntimeSignature

/-! Small exact instance-closing receipts. These tests intentionally inspect
ports/guards only; no result here replaces finite injectivity or a native body
equation for the corresponding original basis occurrence.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.GenericBasisInstance
open SourceTypes Finite Semantics.FiniteCarrier

private def source :=
  "#![no_implicit_prelude] pub unitary fn root[const n:Nat](q:Q<Bit>)->Q<Bit>{" ++
  "if static n>0 {basis q as b {b}} else {q}}"

private def selected (n : Nat) : Option (Bool × Option (Basis × Basis)) :=
  let action : WorkM (Bool × Option (Basis × Basis)) := do
    let sources : Sources := #[("main",source)]
    let arguments : StaticTypes.Arguments := {naturals := [("n",n)]}
    let signature ← StaticRuntimeSignature.prepareWithArguments sources "main" "root" arguments
    let instantiation : StaticInstantiation.Checked signature.original := .static arguments signature.environment rfl
    let checked ← GenericTypeTrace.readWithInstantiation instantiation
    let [obligation] := checked.basisObligations | throw .request
    let binding ← SourceTypes.GenericBasisInstance.closeBasis instantiation obligation
    match binding.status with
    | .inactive _ => pure (false,none)
    | .active ports => pure (true,some (ports.input,ports.output))
  (action.run 10000000).1.toOption

#guard selected 0 = some (false,none)
#guard selected 1 = some (true,some ([.bit],[.bit]))

private def mixed : Option (Basis × Basis) :=
  let action : WorkM (Basis × Basis) := do
    let sources : Sources := #[("main","#![no_implicit_prelude] " ++
      "pub unitary fn root[const z:Nat,const A:Basis,const a:Nat](q:Q<A>)->Q<A>{basis q as x {x}}")]
    let arguments : StaticTypes.Arguments := {bases := [("A",[.unit])],naturals := [("z",9),("a",3)]}
    let signature ← StaticRuntimeSignature.prepareWithArguments sources "main" "root" arguments
    let instantiation : StaticInstantiation.Checked signature.original := .static arguments signature.environment rfl
    let checked ← GenericTypeTrace.readWithInstantiation instantiation
    let [obligation] := checked.basisObligations | throw .request
    let binding ← SourceTypes.GenericBasisInstance.closeBasis instantiation obligation
    match binding.status with
    | .inactive _ => throw .request
    | .active ports => pure (ports.input,ports.output)
  (action.run 10000000).1.toOption

-- A Basis binder keeps its original MIXED ordinal; the two name-sorted Nat
-- binders cannot replace it. Unit remains the complete zero-width owner type.
#guard mixed = some ([.unit],[.unit])

end QleisliKernel.Tests.GenericBasisInstance
