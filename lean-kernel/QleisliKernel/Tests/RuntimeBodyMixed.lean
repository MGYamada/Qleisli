import QleisliKernel.Qirf.RuntimePureBody
import QleisliKernel.Qirf.RuntimeBodyGraph

/-! The single body loop consumes actual classical gaps and observations.
Initial SSA always comes from the same typed source/runtime input gate. These
small controls retain source owner identities and literal mixed steps; complete
history/output/code composition and v5 execution authority remain separate.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.RuntimeBodyMixed
open QleisliKernel QleisliKernel.Finite QleisliKernel.SourceTypes QleisliKernel.Qirf

private def observation (wrongOwner : Bool) : WorkM (List Nat × List Nat × List Nat × Nat) := do
  let text := "#![no_implicit_prelude]\npub observe fn route(a:Q<Bit>,b:Q<Bit>)->(Q<Bit>,Bit){(b,measure_z(a))}"
  let first : Semantics.Raw.Port := ⟨0,[0],1⟩
  let second : Semantics.Raw.Port := ⟨1,[1],1⟩
  let returned := if wrongOwner then first else second
  let program : Semantics.Observation.Program :=
    ⟨[first,second],[],[.measure (if wrongOwner then 1 else 0) 2],[returned.token],[2],.observe⟩
  let artifact : Qirf.Artifact := ⟨#[program],#[],#[("main",text)],0,none⟩
  let signature ← SourceRuntimeContext.readSignature artifact.sources "main" "route" {}
  let body ← SourceRuntimeTrace.readBodyWithSignature signature
  let [.primitive measured] := body.checked.events | throw .request
  let context : RuntimeContextRequest.Context := .mk [⟨measured.call.calleeOffset,0,1⟩] [] [] [] []
  let runtime : RuntimeFamily.Request :=
    ⟨.exported,"main","route",signature.parameters.map (·.tree),
      [[.quantum ⟨first,[.bit]⟩],[.quantum ⟨second,[.bit]⟩]],[[]],signature.result.tree,
      [.tuple 2,.quantum ⟨returned,[.bit]⟩,.ordinary [.bit] (.bit 2)],.observe,{}⟩
  let root ← Validity.checkRootFromRoots artifact #[0] [("main",text)] [0]
  let prepared ← RuntimeInterval.prepare root.dependencies root.program
  let inputs ← RuntimeSourceBoundary.readInputs body prepared runtime.inputStorage
  let ordinary ← RuntimeOrdinaryInputs.read body prepared runtime inputs
  let checked ← RuntimePureBody.checkRuntime artifact root body context runtime prepared inputs ordinary
  return (checked.result.retired.map (·.ordinal),checked.result.bindings.map (·.owner.ordinal),
    checked.result.ordinary.measurements.map (·.output),checked.result.steps.length)

#guard (observation false).run 10000000 |>.1.toOption == some ([0],[1],[2],1)
-- Both Raw programs are structurally valid. Equal-width owners do not permit
-- measuring the held result owner instead of the original source operand.
#guard (match (observation true).run 10000000 with | (.error .request,_) => true | _ => false)

private def gap (extraQuantum : Bool) : WorkM (List Nat × List Nat × Nat) := do
  let text := "#![no_implicit_prelude]\npub unitary fn route(c:Bit,u:Q<Unit>)->(Bit,Q<Unit>){(not c,u)}"
  let unit : Semantics.Raw.Port := ⟨7,[],0⟩
  let operations : List Semantics.Observation.Op :=
    (if extraQuantum then [.pure (.applyUnitary 7 8 [⟨[],.monomial [] [0] [1]⟩])] else []) ++ [.not 2 3]
  let program : Semantics.Observation.Program :=
    ⟨[unit],[2],operations,[if extraQuantum then 8 else 7],[3],.unitary⟩
  let artifact : Qirf.Artifact := ⟨#[program],#[],#[("main",text)],0,none⟩
  let signature ← SourceRuntimeContext.readSignature artifact.sources "main" "route" {}
  let body ← SourceRuntimeTrace.readBodyWithSignature signature
  let runtime : RuntimeFamily.Request :=
    ⟨.exported,"main","route",signature.parameters.map (·.tree),
      [[.ordinary [.bit] (.bit 2)],[.quantum ⟨unit,[.unit]⟩]],[[false],[true]],signature.result.tree,
      [.tuple 2,.ordinary [.bit] (.bit 3),.quantum ⟨⟨if extraQuantum then 8 else 7,[],0⟩,[.unit]⟩],.unitary,{}⟩
  let root ← Validity.checkRootFromRoots artifact #[0] [("main",text)] [0]
  let prepared ← RuntimeInterval.prepare root.dependencies root.program
  let inputs ← RuntimeSourceBoundary.readInputs body prepared runtime.inputStorage
  let ordinary ← RuntimeOrdinaryInputs.read body prepared runtime inputs
  let checked ← RuntimePureBody.checkRuntime artifact root body (.mk [] [] [] [] []) runtime prepared inputs ordinary
  return (checked.result.bindings.map (·.port.token),checked.result.ordinary.table.map Prod.fst,checked.result.steps.length)

#guard (gap false).run 10000000 |>.1.toOption == some ([7],[2,3],1)
-- A source-silent interval must be entirely classical. A scalar phase on the
-- zero-width owner is a real missing source action, even though Raw accepts it.
#guard (match (gap true).run 10000000 with | (.error .request,_) => true | _ => false)

private def completeGraph (wrong : Bool) : WorkM Nat := do
  let text := "#![no_implicit_prelude]\npub unitary fn route(c:Bit,u:Q<Unit>)->(Bit,Q<Unit>){(not c,u)}"
  let unit : Semantics.Raw.Port := ⟨7,[],0⟩
  let program : Semantics.Observation.Program :=
    ⟨[unit],[2],[if wrong then .constant false 3 else .not 2 3],[7],[3],.unitary⟩
  let artifact : Qirf.Artifact := ⟨#[program],#[],#[("main",text)],0,none⟩
  let signature ← SourceRuntimeContext.readSignature artifact.sources "main" "route" {}
  let runtime : RuntimeFamily.Request :=
    ⟨.exported,"main","route",signature.parameters.map (·.tree),
      [[.ordinary [.bit] (.bit 2)],[.quantum ⟨unit,[.unit]⟩]],[[false],[true]],signature.result.tree,
      [.tuple 2,.ordinary [.bit] (.bit 3),.quantum ⟨unit,[.unit]⟩],.unitary,{}⟩
  let checked ← RuntimeBodyGraph.prepareRuntime artifact #[0] "main" "route" {} (.mk [] [] [] [] []) runtime
  return checked.derivation.result.steps.length

-- The common loop, typed root and all-canonical-row final ordinary gate share
-- one fresh graph. A constant-zero mutation agrees at one input but not both.
#guard (completeGraph false).run 10000000 |>.1.toOption == some 1
#guard (match (completeGraph true).run 10000000 with | (.error .equation,_) => true | _ => false)

private def namedObservation (negate : Bool) : WorkM (List Nat × List Nat) := do
  let text := "#![no_implicit_prelude]\nobserve fn read(q:Q<Bit>)->Bit{measure_z(q)}pub observe fn route(q:Q<Bit>)->Bit{read(q)}"
  let input : Semantics.Raw.Port := ⟨0,[0],1⟩
  let output := if negate then 2 else 1
  let program : Semantics.Observation.Program := ⟨[input],[],
    [.measure 0 1] ++ (if negate then [.not 1 2] else []),[],[output],.observe⟩
  let artifact : Qirf.Artifact := ⟨#[program],#[],#[("main",text)],0,none⟩
  let signature ← SourceRuntimeContext.readSignature artifact.sources "main" "route" {}
  let body ← SourceRuntimeTrace.readBodyWithSignature signature
  let [.named call] := body.checked.events | throw .request
  let callee ← SourceRuntimeTrace.readNamedBody call
  let [.primitive measured] := callee.checked.events | throw .request
  let position : SourceSequence.Position := ⟨call.call.calleeOffset,0,program.operations.length⟩
  let context : RuntimeContextRequest.Context := .mk [position] []
    [(position,.mk [⟨measured.call.calleeOffset,0,1⟩] [] [] [] [])] [] []
  let runtime : RuntimeFamily.Request :=
    ⟨.exported,"main","route",signature.parameters.map (·.tree),[[.quantum ⟨input,[.bit]⟩]],[[]],
      signature.result.tree,[.ordinary [.bit] (.bit output)],.observe,{}⟩
  let checked ← RuntimeBodyGraph.prepareRuntime artifact #[0] "main" "route" {} context runtime
  return (checked.derivation.result.retired.map (·.ordinal),
    checked.derivation.result.ordinary.measurements.map (·.calls.length))

-- The preserved minimal observing-call form is exercised here as a component
-- translation. Its literal callee and original measurement path are retained.
#guard (namedObservation false).run 10000000 |>.1.toOption == some ([0],[1])
#guard (match (namedObservation true).run 10000000 with | (.error .equation,_) => true | _ => false)

private def namedAlias : WorkM (List Nat × List Nat) := do
  let text := "#![no_implicit_prelude]\nfn same(a:Bit,b:Bit)->Bit{a xor b}pub unitary fn route(c:Bit,u:Q<Unit>)->(Bit,Q<Unit>){(same(c,c),u)}"
  let unit : Semantics.Raw.Port := ⟨7,[],0⟩
  let program : Semantics.Observation.Program := ⟨[unit],[2],[.xor 2 2 3],[7],[3],.unitary⟩
  let artifact : Qirf.Artifact := ⟨#[program],#[],#[("main",text)],0,none⟩
  let signature ← SourceRuntimeContext.readSignature artifact.sources "main" "route" {}
  let body ← SourceRuntimeTrace.readBodyWithSignature signature
  let [.named call] := body.checked.events | throw .request
  let position : SourceSequence.Position := ⟨call.call.calleeOffset,0,1⟩
  let context : RuntimeContextRequest.Context := .mk [position] [] [(position,.mk [] [] [] [] [])] [] []
  let runtime : RuntimeFamily.Request :=
    ⟨.exported,"main","route",signature.parameters.map (·.tree),
      [[.ordinary [.bit] (.bit 2)],[.quantum ⟨unit,[.unit]⟩]],[[false],[true]],signature.result.tree,
      [.tuple 2,.ordinary [.bit] (.bit 3),.quantum ⟨unit,[.unit]⟩],.unitary,{}⟩
  let checked ← RuntimeBodyGraph.prepareRuntime artifact #[0] "main" "route" {} context runtime
  return (checked.derivation.result.ordinary.table.map Prod.fst,checked.derivation.result.bindings.map (·.port.token))

-- Two original ordinary formals receive the same caller value. The complete
-- actual SSA interface has one input, while source substitution keeps both.
#guard namedAlias.run 10000000 |>.1.toOption == some ([2,3],[7])

end QleisliKernel.Tests.RuntimeBodyMixed
