# Ordinary type inference from two examples

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.

This bounded first-attempt study addresses #22 criterion 10. A separate agent
was started with no conversation history. It was given only the prompt below
and was instructed to use no tools, repository reads, execution or repairs.
The model is inherited from the parent session; this is not a model benchmark.
The authoring response will be preserved before checking. Checking and native
execution, if performed, are separate observations rather than author claims.

## Exact author prompt

```text
Perform a bounded first-attempt authoring study. Do not read repository files, use tools, run code or repair an attempt; output your first authored answer only. The complete available language context is these two examples:
Example A:
use std::transform::init0;
use std::observe::measure_z;
pub fn main() -> Bit { measure_z(init0()) }
Example B:
fn duplicate(b: Bit) -> (Bit, Bit) { (b, b) }
fn read(q: Q<Bit>) -> Bit { measure_z(q) }
The intended APIs init0() and measure_z(q) are exactly as used above. Author four separate small main.qli programs, each with copyright 2026 Masahiko G. Yamada and SPDX Apache-2.0 comments, and state your predicted check outcome without checking: (1) a helper that accepts two measured bits, ignores the second and duplicates the first, plus a closed main preparing/measuring two bits and calling it; (2) a helper taking two quantum-owned bits and returning the two explicitly observed ordinary bits as an ordered pair, plus closed main; (3) a deliberately invalid main trying to return an unobserved init0 result as the same type as Example A; (4) a deliberately invalid main trying to use one live quantum-owned bit twice in two observations. Use only constructs visible in the examples, ordinary let bindings and tuple construction. This tests inference from a few examples, not broad LLM capabilities; do not claim acceptance, proof or completion. Return the four original sources and predictions. Do not invent new syntax or API.
```
