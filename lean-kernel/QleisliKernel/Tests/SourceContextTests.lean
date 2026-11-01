import QleisliKernel.SourceTypes.SourceContext
import QleisliKernel.Tests.SourceTraceOriginals

/-! Bounded original-lookup reuse controls. These compare source identities,
shadowing, visibility and actual work, not complete source/Raw preservation.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.SourceContextTests
open QleisliKernel.SourceTypes
open QleisliKernel QleisliKernel.SourceTypes QleisliKernel.SourceTypes.SourceContext

private structure View where
  selected : String
  name : String := ""
  owner : String := ""
  source : String := ""
  prelude : Option String := none
  route : List String := []
  deriving BEq, DecidableEq, Repr

private def preludeSource {sources name} : {disabled : Bool} →
    CallName.PreludeMiss sources name disabled → Option String
  | _,.disabled => none
  | _,.enabled lookup _ => some lookup.source

private def view {sources caller scope tokens}
    (answer : Except Finite.Error (CallName.Checked sources caller scope tokens)) : View :=
  match answer with
  | .error error => {selected := "error:" ++ reprStr error}
  | .ok checked =>
    match checked.decision with
    | .lexical name .. => {selected := "lexical",name}
    | .named resolution =>
      {selected := "named",name := resolution.result.declaration.name,
        owner := resolution.result.moduleName,source := resolution.result.source,
        route := resolution.result.visited.map (·.moduleName)}
    | .prelude name _ _ _ _ _ lookup _ resolution =>
      {selected := "prelude",name,owner := resolution.result.moduleName,
        source := resolution.result.source,prelude := some lookup.source,
        route := resolution.result.visited.map (·.moduleName)}
    | .primitive name _ _ absence _ miss _ _ =>
      {selected := "primitive",name,source := absence.lookup.source,prelude := preludeSource miss}

private def requests (sources : Sources) (caller : String)
    (queries : List (List String × List LocatedToken)) :
    Finite.WorkM (List View × Context sources caller × Nat) :=
  queries.foldlM (fun (views,context,hits) query => do
    let result ← read sources caller context query.1 query.2
    return (views ++ [view result.answer.checked],result.context,hits + if result.reused then 1 else 0))
    ([],{},0)

private def tokens (source : String) : List LocatedToken := (lexLocated source).toOption.getD []
private def h := tokens "h"
private def standard (source : String := "") : Sources := #[("main",source),("std::prelude","")]
private def privateH := "unitary fn h(q:Q<Bit>)->Q<Bit>{q}"
private def publicH := "pub observe fn h(q:Q<Bit>)->Q<Bit>{q}"
private def publicF := "pub observe fn f(q:Q<Bit>)->Q<Bit>{q}"
private def summary (sources : Sources) (queries : List (List String × List LocatedToken))
    (caller : String := "main") : Option (List View × Nat × Nat) :=
  (((requests sources caller queries).run 10000000).1.toOption).map fun (views,context,hits) =>
    (views,context.entries.length,hits)
private def primitiveH (source : String := "") : View :=
  {selected := "primitive",name := "h",source,prelude := some ""}
private def lexicalH : View := {selected := "lexical",name := "h"}
private def refused : View := {selected := "error:QleisliKernel.Finite.Error.request"}

-- A successful cached primitive never overrides a later/consumed lexical name.
#guard summary (standard) [([],h),(["h"],h),(["q","h"],h),([],h)] =
  some ([primitiveH,lexicalH,lexicalH,primitiveH],1,1)
-- A cached refusal also loses to the current lexical binding.
#guard summary #[("main","")] [([],h),([],h),(["h"],h)] =
  some ([refused,refused,lexicalH],1,1)
-- Lexical lookup needs neither an original caller module nor a valid prelude.
#guard summary #[] [(["h"],h)] = some ([lexicalH],0,0)
#guard summary #[("main","fn broken(){"),("std::prelude","pub use x::h;")]
  [(["h"],h)] = some ([lexicalH],0,0)
-- A different original occurrence reuses only spelling, not its byte span.
#guard summary (standard) [([],h),([],tokens "  /* actual gap */ h")] =
  some ([primitiveH,primitiveH],1,1)
#guard (tokens "  /* actual gap */ h").head?.map (·.span.startByte) != h.head?.map (·.span.startByte)

-- Original binding/category and all import edges survive reuse.
#guard summary #[("main",privateH)] [([],h),([],h)] =
  some ([{selected := "named",name := "h",owner := "main",source := privateH,route := ["main"]},
    {selected := "named",name := "h",owner := "main",source := privateH,route := ["main"]}],1,1)
#guard summary #[("main","use leaf::h;"),("leaf",publicH)] [([],h),([],h)] =
  some (List.replicate 2 {selected := "named",name := "h",owner := "leaf",source := publicH,route := ["main","leaf"]},1,1)
#guard summary #[("main",""),("leaf",publicH)]
  [(["h"],tokens "leaf::h"),(["h"],tokens "leaf::h")] =
  some (List.replicate 2 {selected := "named",name := "h",owner := "leaf",source := publicH,route := ["leaf"]},1,1)
#guard summary #[("main",""),("leaf",privateH)]
  [([],tokens "leaf::h"),([],tokens "leaf::h")] = some ([refused,refused],1,1)
#guard summary (standard) [([],tokens "missing::h"),([],tokens "missing::h")] =
  some ([refused,refused],1,1)
#guard summary (standard "use leaf::{,};") [([],h),([],h)] = some ([refused,refused],1,1)
-- This actual two-module cycle reaches the existing resolver depth refusal.
-- It must propagate rather than become a reusable semantic request refusal.
#guard match ((read #[("main","use leaf::h;"),("leaf","pub use main::h;")]
    "main" {} [] h).run 10000000).1 with | .error .limit => true | _ => false
#guard summary (standard (privateH ++ privateH)) [([],h),([],h)] = some ([refused,refused],1,1)
#guard summary #[("main",""),("main",""),("std::prelude","")]
  [([],h),([],h)] = some ([refused,refused],1,1)

-- Prelude nonexports retain the canonical row; no global eager validation.
#guard summary #[("main",""),("std::prelude",publicH)] [([],h),([],h)] =
  some (List.replicate 2 {selected := "primitive",name := "h",prelude := some publicH},1,1)
#guard summary #[("main",""),("std::prelude","use leaf::h;"),("leaf",publicH)] [([],h),([],h)] =
  some (List.replicate 2 {selected := "primitive",name := "h",prelude := some "use leaf::h;"},1,1)
#guard summary #[("main",""),("std::prelude","pub use leaf::h;"),("leaf",publicH)]
  [([],h),([],h)] = some ([refused,refused],1,1)
#guard summary #[("main",""),("std::prelude","pub use leaf::f;"),("leaf",publicF)]
  [([],tokens "f"),([],tokens "f")] =
  some (List.replicate 2 {selected := "prelude",name := "f",owner := "leaf",source := publicF,prelude := some "pub use leaf::f;",route := ["std::prelude","leaf"]},1,1)
#guard summary #[("main","#![no_implicit_prelude]\n")] [([],h),([],h)] =
  some (List.replicate 2 {selected := "primitive",name := "h",source := "#![no_implicit_prelude]\n"},1,1)
#guard summary (standard "fn x(){} #![no_implicit_prelude]") [([],h),([],h)] =
  some ([refused,refused],1,1)
#guard summary #[("main",""),("std::prelude",""),("unused","fn broken(){")]
  [([],h),([],h)] = some ([primitiveH,primitiveH],1,1)
-- The original scanner limitation is preserved, not promoted to module validity.
#guard summary (standard "fn unrelated(") [([],h),([],h)] =
  some ([primitiveH "fn unrelated(",primitiveH "fn unrelated("],1,1)
#guard summary #[("main","use std::quantum::h;"),("std::quantum",publicH)]
  [([],h),([],h)] = some ([refused,refused],1,1)

-- Exhaustion is not recorded as a semantic refusal or absence.
#guard match ((read (standard) "main" {} [] h).run 0).1 with | .error _ => true | _ => false
-- Thirty units cover fresh parsing, scope/cache search and insertion reservation;
-- the next original-reader charge fails inside capture and remains an error.
#guard match ((read (standard) "main" {} [] h).run 31).1 with
  | .error (.arithmetic _) => true
  | _ => false
#guard summary (standard) [([],h)] = some ([primitiveH],1,0)

private def manySource := "pub unitary fn route(q:Q<Bit>)->Q<Bit>{" ++
  String.join (List.replicate 129 "let q=h(q);") ++ "q}"
private def manySources : Sources := #[("main",manySource)] ++ SourceTraceOriginals.bundled
private def manyQueries : List (List String × List LocatedToken) :=
  ((tokens manySource).filter fun token => token.text == "h").zipIdx.map fun (token,index) =>
    (List.replicate (index+1) "q",[token])
private def legacyMany : Finite.WorkM (List View) :=
  manyQueries.mapM fun (scope,query) => do
    return view (.ok (← CallName.read manySources "main" scope query))
private def cachedMany := (requests manySources "main" manyQueries).run 10000000
private def originalMany := legacyMany.run 10000000
#guard manyQueries.length = 129
#guard cachedMany.1.toOption.map (fun (_,context,hits) => (context.entries.length,hits)) = some (1,128)
#guard cachedMany.1.toOption.map (fun (views,_,_) => views) = originalMany.1.toOption
#guard cachedMany.2 > originalMany.2
#guard (10000000-cachedMany.2,10000000-originalMany.2) = (86079,6262047)

private def costs (sources : Sources) (queries : List (List String × List LocatedToken)) :=
  let cached := (requests sources "main" queries).run 10000000
  let original := (queries.mapM fun (scope,query) => do
    return view (.ok (← CallName.read sources "main" scope query))).run 10000000
  (10000000-cached.2,10000000-original.2)
#guard costs (standard) [([],h),([],h)] = (175,226)
#guard costs (standard) [([],h),(["h"],h)] = (173,228)
#guard costs #[("main","use leaf::h;"),("leaf",publicH)] [([],h),([],h)] = (508,892)
-- Assert the scalar lookup result separately from its work counters.
#guard summary (standard) [([],tokens "global_phase_eighth"),([],tokens "global_phase_eighth")] =
  some (List.replicate 2 {selected := "primitive",name := "global_phase_eighth",prelude := some ""},1,1)
-- Cache bookkeeping is not claimed to reduce work for every small query.
#guard costs (standard) [([],tokens "global_phase_eighth"),([],tokens "global_phase_eighth")] =
  (589,370)

#print axioms QleisliKernel.SourceTypes.SourceContext.read
#print axioms QleisliKernel.SourceTypes.SourceContext.Recorded.original
#print axioms QleisliKernel.SourceTypes.SourceContext.Answer.originalSpelling

end QleisliKernel.Tests.SourceContextTests
