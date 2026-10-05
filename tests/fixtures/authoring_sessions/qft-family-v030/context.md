# Informed bounded generic QFT authoring study

This new local-module study follows the human-authorized Issue #317 contract,
whose current 24 acceptance criteria require a canonical parameterized Fourier
family. It was prepared after reading the actual Issue, source-text/primitive
Reference, shared parser/checker/loader, fixed QFT2/3 definitions and the existing
licensed Qualtran-sized translation. It is informed authoring, not a blind model
benchmark. Codex authored it; exact deployment identifier/sampling are unavailable.
No external model or upstream download is used.

The source is saved before its first invocation. The existing translation is
copied with Google LLC attribution and Masahiko G. Yamada's modifications intact;
identity-before.json binds its pinned upstream input and license. The only body
change is an outer static zero-width branch. The declaration becomes ordinary
`pub fn qft[static n: Nat]`, so its effect must be inferred from the checked body;
`requires n >= 1` is removed. The retained manifest declares schema 2 and edition
2026. The explicit-module CLI reads the supplied source path, not this manifest
as a package installation or canonical bundled stdlib import.

The intended independent family is
F_n[y,x] = exp(+2*pi*i*x*y/2^n)/sqrt(2^n), for 0 <= x,y < 2^n.
Axis zero has weight one, output reversal is included and scalar phase is fixed.
F_0=[+1] returns the exact Q<Bits<0>> owner and preserves external references;
it is not Q<Unit>. Existing native named .qft requests reject width zero, so no
such request will be generated. Source ownership/type checking and native
producer-consistency checking do not by themselves establish this formula.

First observations use only check at n=0,1,2,3 in text and JSON, with fixed CLI,
native and wrapper identities before/after every invocation. The commands are
fixed in observe.py; no command will be read from result metadata. If every check
succeeds, a separate fixed small numerical probe may compare actual coefficients
and a retained reference against the positive Fourier formula. If generic
checking fails, preserve that real result and stop dependent semantic probes.
No N=8, maximum-size experiment, Cargo or Lean build is authorized here.

Canonical std::transform exposure, common checked project/bundled loading,
fixed-specialization exact equivalence, general-size phase/termination support,
source preservation and resource certificates remain separate work. Current
finite loading embeds every std source and rejects static Nat declarations;
current sized explicit maps reject std:: names. This local translation does not
silently bypass or complete those boundaries. `qfor` is an unavailable ideal
spelling; this translation retains current `for static`/carry/yield expressions
and structured final expressions, without early return.

Constitutional edition 2026 and adopted QS/PR/RS plus EXACT remain applicable.
Both admitted ordinary QLV1 ownership/scope guarantees retain their exact scope.
Broader obligations remain pending; this study adopts no interpretation, native
rule or guarantee. The parent validated functional commit 238e1f0869c96c8da18f215a4569dd68e2cc98b9;
identity-before.json distinguishes committed code from uncommitted Issue #317
scope/draft records and records the existing binary/source identity limitations.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
