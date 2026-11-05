import QleisliKernel.SourceTypes.SourceRuntimeTrace
import QleisliKernel.Tests.SourceTraceOriginals

/-! Actual original nominal runtime traversal, including ordinary values around
qmatch and original member privacy. Native SSA/instrument/body equations remain
separate from these full original source checks.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.SourceRuntimeNominal
open QleisliKernel QleisliKernel.SourceTypes SourceRuntimeValues

private def read (source : String) :=
  ((SourceRuntimeTrace.read (#[("main",source)] ++ SourceTraceOriginals.bundled) "main" "route").run 2000000000).1.toOption

private def source :=
  "enum Tag{Off,On}struct Flags{chosen:Bit,empty:Unit}" ++
  "unitary fn idle(q:Q<Bit>)->Q<Bit>{q}unitary fn hi(q:Q<Bit>)->Q<Bit>{h(q)}" ++
  "pub observe fn route(a:Q<Bit>,s:Q<Tag>,q:Q<Bit>)->(Bit,(Q<Tag>,Q<Bit>)){" ++
  "let flags=Flags{empty:(),chosen:measure_z(a)};" ++
  "(flags.chosen,qmatch(s,q){Tag::Off=>idle,Tag::On=>hi})}"
#guard (read source).map (fun checked => ((valueOwners checked.summary.value).map (·.ordinal),
  checked.summary.consumed.map (·.ordinal),checked.summary.generic.inferredEffect)) = some ([1,2],[0],.observe)
#guard (read (source.replace "pub observe fn route" "pub unitary fn route")).isNone

#guard (read "struct Empty{}pub fn route()->Empty{Empty{}}").isSome
#guard (read "struct Empty{}pub fn route()->Unit{Empty{}}").isNone
#guard (read "enum Tag{Off,On}pub fn route()->Tag{Tag::On}").isSome
#guard (read "enum Tag{Off,On}pub fn route()->Tag{Tag::Missing}").isNone
#guard (read "struct Box{field:(Bit,Unit)}pub fn route(value:Box)->(Bit,Unit){let(b,u)=value.field;(b,u)}").isSome
#guard (read "struct Box{field:Bit}pub fn route(value:Box)->Bit{let Box=();value.field}").isSome
#guard (read "struct Box{field:Bit}pub fn route(value:Box)->Box{let Box=();Box{field:1}}").isNone
#guard (read "struct Box{field:Bit}pub unitary fn route(q:Q<Box>)->Bit{q.field}").isNone

private def privateField : Sources :=
  #[("main","use lib::Box;pub fn route(value:Box)->Unit{value.hidden}"),
    ("lib","pub struct Box{hidden:Unit}")] ++ SourceTraceOriginals.bundled
#guard ((SourceRuntimeTrace.read privateField "main" "route").run 2000000000).1.toOption.isNone

private def bodyOnlyType : Sources :=
  #[("main","use lib::Tag;pub fn route()->Bit{let unused=Tag::On;0}"),
    ("lib","pub enum Tag{Off,On}"),
    ("unrelated","pub enum Other{Off,On}")] ++ SourceTraceOriginals.bundled
#guard ((SourceRuntimeTrace.read bodyOnlyType "main" "route").run 2000000000).1.toOption.map
  (fun checked => (checked.summary.staticRows.any (fun row => row.1 == "lib"),
    checked.summary.staticRows.any (fun row => row.1 == "unrelated"))) = some (true,false)

#print axioms QleisliKernel.SourceTypes.SourceRuntimeTrace.read
end QleisliKernel.Tests.SourceRuntimeNominal
