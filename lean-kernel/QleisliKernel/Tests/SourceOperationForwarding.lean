import QleisliKernel.SourceTypes.SourceTrace
import QleisliKernel.SourceTypes.SourceRuntimeTrace
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
#guard ((SourceTrace.read (sources "foreign::hidden") "main" "route").run 2000000000).1.isError
#guard ((SourceRuntimeTrace.read (sources "foreign::hidden") "main" "route").run 2000000000).1.isError
#guard ((SourceTrace.read (sources "foreign::conservative") "main" "route").run 2000000000).1.isError
#guard ((SourceRuntimeTrace.read (sources "foreign::conservative") "main" "route").run 2000000000).1.isError

private def spectator : Sources :=
  #[("main","use lib::copy;unitary fn local(q:Q<Bit>)->Q<Bit>{h(q)}pub fn route(c:Bit)->Bit{copy[local](c)}"),
    ("lib","pub fn copy[const U:Op<Bit>](c:Bit)->Bit requires Applicable(U){c}")] ++
    SourceTraceOriginals.bundled
#guard ((SourceRuntimeTrace.read spectator "main" "route").run 2000000000).1.toOption.map
  (fun checked => checked.summary.inferredEffect) = some .unitary

#print axioms QleisliKernel.SourceTypes.SourceRuntimeContext.fromPreparedWithArguments
#print axioms QleisliKernel.SourceTypes.SourceRuntimeContext.fromQuantumCore
end QleisliKernel.Tests.SourceOperationForwarding
