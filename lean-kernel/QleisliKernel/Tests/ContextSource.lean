import QleisliKernel.Qirf.ContextSector

/-! The legacy source helper shares original audit metadata while preserving
its closed-header boundary. These are small source reads, without a native
handle, maximum-size quantum program or altered context work oracle.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.ContextSource
open QleisliKernel QleisliKernel.Qirf QleisliKernel.Finite

private def sources (header : String) : SourceTypes.Sources :=
  #[("main","#![no_implicit_prelude]\npub unitary fn main" ++ header ++ "{h(q)}")]

private def read (header : String) : WorkM Bool := do
  let source ← ContextSector.readSource (sources header) "main" "main"
  return source.signature.operations.catalogue.isSome

#guard (read "(q:Q<Bit>)->Q<Bit>").run 10000000 |>.1.toOption == some true
-- This canonical generic header independently parses and closes with its
-- actual Nat. The legacy helper supplies no actual and still refuses it;
-- the refusal need not occur at the later closed-header guard.
#guard ((SourceTypes.QuantumSignature.readWithArguments
  (sources "[const n:Nat](q:Q<Bit>)->Q<Bit>") "main" "main" {naturals := [("n",0)]}).run
  10000000 |>.1.toOption.map (·.staticArguments.naturals)) == some [("n",0)]
#guard (match (read "[const n:Nat](q:Q<Bit>)->Q<Bit>").run 10000000 with
  | (.error .request,_) => true | _ => false)
#guard (match (read "(q:Q<Bit>)->Q<Bit> requires 0>=0").run 10000000 with
  | (.error .request,_) => true | _ => false)

end QleisliKernel.Tests.ContextSource
