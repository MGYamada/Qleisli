import QleisliKernel.SourceTypes.SourceTrace
import QleisliKernel.SourceTypes.SourceRuntimeTrace
import QleisliKernel.Qirf.RuntimeBodyDiscovery
import QleisliKernel.SourceTypes.OperationSourceUses
import QleisliKernel.Tests.SourceTraceOriginals

/-! Original per-occurrence operation supply. A private source-selected leaf
keeps its original caller authority when forwarded to another original module;
that receipt does not grant access to another private or public Observe leaf.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.SourceOperationForwarding
open QleisliKernel QleisliKernel.SourceTypes

private def sources (actual : String := "local") : Sources :=
  #[("main","use lib::apply;unitary fn local(q:Q<Bit>)->Q<Bit>{h(q)}" ++
      "pub unitary fn route(q:Q<Bit>)->Q<Bit>{apply[" ++ actual ++ "](q)}"),
    ("lib","pub unitary fn apply[const U:Op<Bit>](q:Q<Bit>)->Q<Bit> requires Applicable(U){U(q)}"),
    ("foreign","unitary fn hidden(q:Q<Bit>)->Q<Bit>{q}pub observe fn conservative(q:Q<Bit>)->Q<Bit>{q}")] ++
    SourceTraceOriginals.bundled

#guard ((SourceTrace.read (sources) "main" "route").run 2000000000).1.isOk
#guard ((SourceRuntimeTrace.read (sources) "main" "route").run 2000000000).1.isOk
#guard ((SourceTrace.read (sources "foreign::hidden") "main" "route").run 2000000000).1.toOption.isNone
#guard ((SourceRuntimeTrace.read (sources "foreign::hidden") "main" "route").run 2000000000).1.toOption.isNone
#guard ((SourceTrace.read (sources "foreign::conservative") "main" "route").run 2000000000).1.toOption.isNone
#guard ((SourceRuntimeTrace.read (sources "foreign::conservative") "main" "route").run 2000000000).1.toOption.isNone

private def unannotatedSpectator : Sources :=
  #[("main","use lib::copy;unitary fn local(q:Q<Bit>)->Q<Bit>{h(q)}pub fn route(c:Bit)->Bit{copy[local](c)}"),
    ("lib","pub fn copy[const U:Op<Bit>](c:Bit)->Bit requires Applicable(U){c}")] ++
    SourceTraceOriginals.bundled

-- The original public family has quantum use through its Op formal, even
-- when the runtime result is ordinary and that formal is unused in the body.
#guard ((SourceRuntimeTrace.read unannotatedSpectator "main" "route").run 2000000000).1.toOption.isNone

private def spectator (parameter : String := "c") : Sources :=
  #[("main","use lib::copy;unitary fn local(q:Q<Bit>)->Q<Bit>{h(q)}pub unitary fn route(" ++
      parameter ++ ":Bit)->Bit{copy[local](" ++ parameter ++ ")}"),
    ("lib","pub unitary fn copy[const U:Op<Bit>](c:Bit)->Bit requires Applicable(U){c}")] ++
    SourceTraceOriginals.bundled
#guard ((SourceRuntimeTrace.read (spectator "c") "main" "route").run 2000000000).1.toOption.map
  (fun checked => checked.summary.inferredEffect) = some .unitary

-- A runtime binding named local cannot supply the private function of that
-- spelling as an operation actual, including an otherwise unused actual.
#guard ((SourceRuntimeTrace.read (spectator "local") "main" "route").run 2000000000).1.toOption.isNone

-- Retain all three written uses of W while checking route from its original
-- entry under one public work allowance. The zero-power child and the unused
-- provider argument have distinct source positions.
private def mixedSource : String := r#"#![no_implicit_prelude]
unitary fn keep(q:Q<Bit>)->Q<Bit>{q}
unitary fn accept[const U:Op<Bit>](q:Q<Bit>)->Q<Bit>
    requires Applicable(U),Adjointable(U),Controllable(U){U(q)}
unitary fn provider[const count:Nat,const action:Op<Bit>,const unused:Op<Bit>](q:Q<Bit>)->Q<Bit>
    requires Applicable(action),Adjointable(action),Controllable(action),
             Applicable(unused),Adjointable(unused),Controllable(unused){action(q)}
unitary fn relay[const seed:Nat,const W:Op<Bit>](q:Q<Bit>)->Q<Bit>
    requires Applicable(W),Adjointable(W),Controllable(W){
    accept[provider[seed,then_op(W,power(W,0)),W]](q)
}
pub unitary fn route(q:Q<Bit>)->Q<Bit>{relay[0,keep](q)}
"#

private def mixedUses : Finite.WorkM (List (List SourceOperation.Edge × Nat × String × Nat × Nat)) := do
  let artifact : Qirf.Artifact := ⟨#[],#[],#[("main",mixedSource)],0,none⟩
  let original ← Qirf.RuntimeBodyDiscovery.prepareSource artifact "main" "route" {}
  let [.named outer] := original.body.checked.events | throw .invalid
  let relay ← SourceRuntimeTrace.readNamedBody outer
  let [.named inner] := relay.checked.events | throw .invalid
  let [incoming] := inner.target.operationActuals.sourceActuals | throw .invalid
  let uses ← OperationSourceUses.readChecked incoming.checked
  uses.uses.mapM fun use => do
    let [token] := use.tokens | throw .invalid
    return (use.path,use.formal.key.ordinal,token.text,token.span.startByte,token.span.endByte)

#guard (mixedUses.run Qirf.WorkProfile.qmatch.limit).1.toOption == some
  [([.actual 1,.child 0],1,"W",592,593),([.actual 1,.child 1,.child 0],1,"W",600,601),
   ([.actual 2],1,"W",606,607)]

#print axioms QleisliKernel.SourceTypes.SourceRuntimeContext.fromPreparedWithArguments
#print axioms QleisliKernel.SourceTypes.SourceRuntimeContext.fromQuantumCore
end QleisliKernel.Tests.SourceOperationForwarding
