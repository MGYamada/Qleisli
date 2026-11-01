import QleisliKernel.SourceTypes.CallName
import QleisliKernel.SourceTypes.CallSyntax

/-! Bounded executable name-resolution controls. These inputs deliberately vary
lexical scope, original source rows and namespace policy independently of the
candidate. No source-preservation, effect or execution claim is inferred.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.CallNameTests
open QleisliKernel.SourceTypes
open QleisliKernel QleisliKernel.SourceTypes QleisliKernel.SourceTypes.CallName

private structure View where
  selection : String
  name : String
  owner : String := ""
  source : String := ""
  category : String := ""
  preludeSource : Option String := none
  route : List String := []
  deriving BEq, DecidableEq, Repr

private def missSource {sources name} : {disabled : Bool} →
    PreludeMiss sources name disabled → Option String
  | _, .disabled => none
  | _, .enabled lookup _ => some lookup.source

private def view {sources caller scope tokens} (checked : Checked sources caller scope tokens) : View :=
  match checked.decision with
  | .lexical name _ _ => {selection := "lexical",name}
  | .named resolution =>
    {selection := "named", name := resolution.result.declaration.name,
      owner := resolution.result.moduleName, source := resolution.result.source,
      category := resolution.result.declaration.kind,
      route := resolution.result.visited.map (·.moduleName)}
  | .prelude name _ _ _ _ _ lookup _ resolution =>
    {selection := "prelude",name, owner := resolution.result.moduleName,
      source := resolution.result.source,category := resolution.result.declaration.kind,
      preludeSource := some lookup.source,
      route := resolution.result.visited.map (·.moduleName)}
  | .primitive name _ _ localMissing _ preludeMissing _ _ =>
    {selection := "primitive",name,source := localMissing.lookup.source,
      preludeSource := missSource preludeMissing}

private def result (sources : Sources) (expression : String) (scope : List String := [])
    (caller : String := "main") : Option View := do
  let tokens ← (lexLocated expression).toOption
  let checked ← ((read sources caller scope tokens).run 100000).1.toOption
  return view checked

private def standard (source : String := "") : Sources :=
  #[("main",source),("std::prelude","// no public export\n")]
private def privateH := "unitary fn h(q:Q<Bit>)->Q<Bit>{q}"
private def publicH := "pub observe fn h(q:Q<Bit>)->Q<Bit>{q}"
private def publicF := "pub observe fn f(q:Q<Bit>)->Q<Bit>{q}"
private def disabled := "#![no_implicit_prelude]\n"

-- Fallback retains both the absent local lookup and exact prelude absence row.
#guard result (standard "// original caller\n") "h" = some
  {selection := "primitive",name := "h",source := "// original caller\n",
    preludeSource := some "// no public export\n"}
#guard result (standard) "global_phase_eighth" = some
  {selection := "primitive",name := "global_phase_eighth",
    preludeSource := some "// no public export\n"}
#guard result (standard) "phase" = some
  {selection := "primitive",name := "phase",
    preludeSource := some "// no public export\n"}
#guard result (standard) "unknown_primitive" = none
#guard result (standard) "phase" ["phase"] = some {selection := "lexical",name := "phase"}
#guard result (standard "unitary fn phase(q:Q<Bit>)->Q<Bit>{q}") "phase" = some
  {selection := "named",name := "phase",owner := "main",
    source := "unitary fn phase(q:Q<Bit>)->Q<Bit>{q}",category := "fn",route := ["main"]}

-- This is the retained lexical scope, not a live-owner map: consumed and
-- wrong-category names both remain here and block every global lookup tier.
#guard result (standard) "h" ["h"] = some {selection := "lexical",name := "h"}
#guard result (standard privateH) "h" ["h","consumed_owner"] =
  some {selection := "lexical",name := "h"}
#guard result (standard "pub enum h { A, B }") "h" = some
  {selection := "named",name := "h",owner := "main",source := "pub enum h { A, B }",
    category := "enum",route := ["main"]}
#guard result #[("main",privateH)] "h" = some
  {selection := "named",name := "h",owner := "main",source := privateH,
    category := "fn",route := ["main"]}
#guard result #[("main","use leaf::h;"),("leaf",publicH)] "h" = some
  {selection := "named",name := "h",owner := "leaf",source := publicH,
    category := "fn",route := ["main","leaf"]}

-- Qualification ignores lexical bindings and grants no fallback or privacy bypass.
#guard result #[("main",""),("leaf",publicH)] "leaf::h" ["h"] = some
  {selection := "named",name := "h",owner := "leaf",source := publicH,
    category := "fn",route := ["leaf"]}
#guard result (standard) "missing::h" = none
#guard result #[("main",""),("leaf",privateH)] "leaf::h" = none
#guard result #[("main",privateH)] "main::h" = some
  {selection := "named",name := "h",owner := "main",source := privateH,
    category := "fn",route := ["main"]}
#guard result #[("main",""),("std::observe",publicF)] "std::observe::f" = some
  {selection := "named",name := "f",owner := "std::observe",source := publicF,
    category := "fn",route := ["std::observe"]}
#guard result #[("main",""),("self",publicF)] "self::f" = some
  {selection := "named",name := "f",owner := "self",source := publicF,
    category := "fn",route := ["self"]} -- literal module, not relative resolution
#guard result #[("main",""),("std::quantum",publicH)] "std::quantum::h" = none
#guard result #[("main","use std::quantum::h;"),("std::quantum",publicH)] "h" = none
#guard result #[("main","use facade::h;"),("facade","pub use std::quantum::h;"),
    ("std::quantum",publicH)] "h" = none
#guard result #[("std::quantum",privateH)] "h" [] "std::quantum" = some
  {selection := "named",name := "h",owner := "std::quantum",source := privateH,
    category := "fn",route := ["std::quantum"]}

-- Selected source errors cannot be reinterpreted as genuine absence.
#guard result #[("std::prelude","")] "h" = none
#guard result #[("main","")] "h" = none -- canonical enabled prelude row is required
#guard result #[("main",""),("std::prelude",""),("std::prelude","")] "h" = none
#guard result (standard (privateH ++ privateH)) "h" = none
#guard result (standard "use missing::h;") "h" = none
#guard result (standard "use leaf::{,};") "h" = none
#guard result #[("main","use leaf::h;"),("leaf","pub use main::h;")] "h" = none
#guard result (standard (privateH ++ "use leaf::h;")) "h" = none

-- Implicit openings are public reexports, not public local declarations.
#guard result #[("main",""),("std::prelude",publicH)] "h" = some
  {selection := "primitive",name := "h",preludeSource := some publicH}
#guard result #[("main",""),("std::prelude","use leaf::h;"),("leaf",publicH)] "h" = some
  {selection := "primitive",name := "h",preludeSource := some "use leaf::h;"}
#guard result #[("main",""),("std::prelude","pub use leaf::h;"),("leaf",publicH)] "h" = none
#guard result #[("main",""),("std::prelude","pub use leaf::f;"),("leaf",publicF)] "f" = some
  {selection := "prelude",name := "f",owner := "leaf",source := publicF,category := "fn",
    preludeSource := some "pub use leaf::f;",route := ["std::prelude","leaf"]}
#guard result #[("main",""),("std::prelude","use leaf::f;"),("leaf",publicF)] "f" = none
#guard result #[("main",""),("std::prelude","pub use missing::f;")] "f" = none
#guard result #[("main",""),("std::prelude","pub use leaf::f;"),
    ("leaf","pub use std::prelude::f;")] "f" = none

-- Only the real initial directive disables prelude, while primitives remain.
#guard result #[("main",disabled)] "h" = some
  {selection := "primitive",name := "h",source := disabled}
#guard result #[("main",disabled)] "global_phase_eighth" = some
  {selection := "primitive",name := "global_phase_eighth",source := disabled}
#guard result #[("main","/* comment */\n" ++ disabled)] "h" = some
  {selection := "primitive",name := "h",source := "/* comment */\n" ++ disabled}
#guard result #[("main","fn other()->Unit{()}\n" ++ disabled)] "h" = none
#guard result #[("main",disabled ++ disabled)] "h" = none
#guard result #[("main","#![something_else]")] "h" = none
#guard result #[("main","// #![no_implicit_prelude]\n")] "h" = none

-- Callee segmentation deliberately keeps junk intact; the exact name reader refuses it.
private def callCalleeAccepted (expression : String) : Bool :=
  match lexLocated expression with
  | .error _ => false
  | .ok tokens => match CallSyntax.read tokens with
    | .error _ => false
    | .ok call => (readName call.call.callee).isOk
#guard callCalleeAccepted "h(q)"
#guard callCalleeAccepted "leaf::h(q)"
#guard !callCalleeAccepted "h(q);f(r)"
#guard !callCalleeAccepted "power(h,2)(q)"
#guard result (standard) "::h" = none
#guard result (standard) "h::" = none
#guard result (standard) "h h" = none
#guard result (standard) "h[2]" = none

-- The first byte/name charge fails before malformed-source scanning or lookup.
#guard (match lexLocated "h" with
  | .error _ => false
  | .ok tokens => match (read #[("main","/*")] "main" [] tokens).run 0 with
    | (.error (.arithmetic .workLimit),0) => true
    | _ => false)

#print axioms QleisliKernel.SourceTypes.CallName.read
#print axioms QleisliKernel.SourceTypes.CallName.Resolution.originalQuery
#print axioms QleisliKernel.SourceTypes.CallName.Absent.original

end QleisliKernel.Tests.CallNameTests
