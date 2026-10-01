# Initial `.qli` frontend and verified IR pipeline

Implemented bounded Rust checking/lowering/execution profile. [Language](language-spec.md), [grammar](syntax-v0.md), [M1](next-minor-spec.md), [types](type-system.md) and [edition](language-editions.md) fix supported rules; general source/Rust/backend correspondence is open. All filesystem trees explicitly declare edition 2026. Generic bodies are source-checked before concrete specialization, but abstract checking issues no cleanup evidence or VerifiedProgram.

<a id="入口と信頼境界"></a>

## Entry points and trust boundary

check_project loads/checks every declaration and permits libraries without main; compile_project requires parameterless observe main in main.qli, result T=Unit/CBit/n-ary finite classical products (arity 2..64), and no remaining owners, then returns independently verified IR. Bundled source uses identical checks. Files/OS paths remain OS strings, including non-UTF-8 where supported. CLI check/run use exits 0 success, 1 load/check/run failure, 2 usage. run prints approximate probabilities in result tuple order; Unit contributes no bits. doc parses one file only, without resolution/type/evidence authority.

```sh
cargo run --bin qleisli -- check examples/bell
cargo run --bin qleisli -- run examples/bell
cargo run --bin qleisli -- run examples/phase_oracle
cargo run --bin qleisli -- run examples/feedback
```

<a id="検査と変換の規則"></a>

## Checks and lowering

All forms receive independent IR verification. Both classical arms check; complete phi covers returned positions and caller/pending frames, with fresh IDs across arms. Phi inputs precede all merge outputs. Products are not automatically unpacked into multiple function arguments. Restricted computed use accepts expanded identity/Z/T only; general preserving work/borrow signatures remain outside it. Static operations require unitary same-interface/no classical ports, check closed branches and zero repetitions, and charge complete expanded tables/steps.

| Form and classification | Type, ownership, and effect | IR correspondence |
| --- | --- | --- |
| Function call; language form | Resolve declarations and explicit imports in the defining module. Check argument count/types, result, and declared effect. Reject all call cycles, including unused bodies. | Move arguments and expand the body with fresh IDs. No first-class operation values. |
| `let` and block; language forms | Move any value containing `Q<A>`. Copy classical values. Evaluate the right-hand side first; reject shadowing live ownership or dropping it with a wildcard/statement. Return or explicitly consume block-local ownership. | Binding alone adds no quantum operation; subsequent operations use the current token. |
| `basis fn`; language form | `Unit`, `Bit`, and finite products only; enumerate every input. Logical operators and basis calls use a separate context. A multi-parameter declaration has a left-associated semantic product domain, with the first argument in low bits; ordinary calls still require separate arguments. | Compile to a total finite table. A basis function need not itself be injective. |
| `do x <- q; pure e`; language form | Consume `q:Q<A>`, check totality and injectivity of the expressible map to `B`, return `Q<B>`. Equal width is `Unitary`; growth is `Iso`. | `LiftBasis` preserves existing ordered wires and appends fresh wires if needed. |
| Gates, `split/join`, observations; sealed operations | Use the [sealed contracts](standard-library.md); compare exact source product trees. Toffoli returns `((a,b),t)`; `measure_z` returns only `CBit`. | Emit the corresponding constructor, including distinct `Gate`, `Cnot`, and `Toffoli`, and independently reverify. |
| Classical `if`; language form | A `CBit` condition selects exclusive branches with matching result types and outer consumption. Retain caller and pending resources. | Merge result positions and the complete surviving frame with fresh quantum phi IDs and classical phis. Branch-created wires may be returned. |
| `with_computed`; language form | Consume/return `Q<A>` with a total predicate into `Bit`. Its body sees classical captures and one private auxiliary, not outer quantum values. The auxiliary may hide a masked outer name without consuming that outer resource. | Certify an expanded auxiliary identity or Z/T chain, then emit atomic `ComputeUseUncompute`; no standalone `Release0`. |
| Three-argument `with_computed(q,f,u)`; finite semantic language extension | Consume/return `Q<A>`; isolated binders own the data and one computed bit and return both. No outer captures. Require an explicit eligible static unitary u on the exact source type. | Retain the predicate, joint body W and logical u in `CertifiedCompute`; independently check `W E_f=E_f u`. See [specification and bounds](semantic-contracts-v0.1.md). |
| `apply_contract(implementation,specification,input)`; finite semantic language extension | Evaluate input first; require ordinary declared unitary targets with the same exact unary `Q<A> -> Q<A>` signature. Preserve linear ownership, including Unit. | Independently check both concrete raw functions and their exact meaning; retain immutable function evidence in an ordered `CircuitAction::Contract`. See [function contracts](function-contracts-v0.1.md). |

<a id="受理拒否の例"></a>

## Accepted and rejected examples

Accepted/rejected examples assume declared imports/types. Bit basis literals and coherent labels differ from ordinary CBit Booleans; evaluate operands once in order, including effects. Injectivity covers the full domain and actual type tree, not just observed support.

| Example | Decision |
| --- | --- |
| `do x <- q; pure (x,x)` | Accept when it fits the profile: distinct basis inputs have distinct images. This can use a whole product basis value. |
| `with_computed(q,p) { \|a\| phase(a) }`, where `phase(a) { z(a) }` | Accept after checking the expanded phase chain. |
| `if b { x(r) } else { r }` | Accept: both branches return the same input ownership. |
| `(q,q)`, or `h(q)` after `measure_z(q)` | Reject reuse of consumed ownership. |
| `let _ = init0();` or `init0();` | Reject implicit quantum disposal. |
| `do x <- q; pure 0` for `q:Q<Bit>` | Reject the well-typed but noninjective lift. |
| `do x <- q; pure xor2(x)` for `q:Q<(Bit,Bit)>` and the bundled `xor2` | Reject argument count: a product is not unpacked into two parameters. |
| `measure_z` in `iso`, or `init0` in `unitary` | Reject the effect violation. |
| Auxiliary `h(a)`, measurement, or an attempted capture of outer quantum ownership | Reject the certificate, effect, or ownership violation. |

<a id="診断と上限"></a>

## Diagnostics and limits

CompileError carries category/path/UTF-8 span/one-based Unicode line-column and explanatory text; LF/CRLF supported, bare CR located lexical failure. Codes include Arity, TypeMismatch, Effect, UnknownName, RecursiveCall, Ownership, InvalidEntry, Unsupported, Limit, Project and InvalidIr. Ownership includes failed injectivity; parse/load wraps Project, contract failures InvalidIr. Calls locate actual argument or call, body failures locate body; IR maps locate source operations. Exact mismatches report first input-column/output-row entries. Effect failures retain cause/declared effects; only one error is reported. Exact prose/multi-error order is not normative.

Widths <=12 bits; syntax/expansion/basis/type/value depth <=64, type/value nodes <=4096. Shared lowering work <=1, 000, 000 charges retention, copies, tables, snapshots/phis; whole project declarations/call expansion share it. Shared exact work <=10, 000, 000 per compilation, including unused static providers and every complete receipt. Conservative matrix work is charged before execution. Source retention is once per allocation, first provider/contract snapshot: <=128 modules, name <=4096 bytes and records including names <=1 MiB. Every receipt still rechecks metadata and copied raw/pair cost under FC-CACHE; explicit public identity views may materialize bounded copies.

On macOS, descriptor-relative `openat`/`O_NOFOLLOW` checks each component while retaining its parent descriptor; it does not require `O_NOFOLLOW_ANY` or a higher minimum OS version. The listed Linux architectures use held descriptors through readable `/proc/self/fd`, without a link-following fallback. Other targets retain the filesystem trust assumption. Input byte overrides do not override work. Source and simulator limits differ; [source-byte capacities](machine-interface-spec.md#source-input-capacities-and-migration) give the exact policy.

<a id="確認した結果と残件"></a>

## Evidence and remaining obligations

Source tests, independent small complex/instrument oracles, exact equation checks and actual-definition Lean components establish separate finite scopes. The complete compiler and numerical execution are not formally proved. [Rule inventory](rule-inventory.md) records remaining obligations.

| Source project | Ideal result | Finite evidence |
| --- | --- | --- |
| `examples/bell` | `00`, `11`, each with probability 1/2 | Source checking, IR verification, and reference execution. |
| `examples/phase_oracle` | `1` with probability 1 | Expanded auxiliary phase followed by interference. |
| `examples/feedback` | `00`, `10`, each with probability 1/2 | Measure one Bell half and conditionally correct the other. |
| `examples/grover` | `11` with probability 1 | Shared preparation, oracle, and one reflection step. |
| `examples/bernstein_vazirani` | `10` with probability 1 | Reuse Hadamard preparation and recover the hidden linear function. |
| `examples/bit_flip_code` | `11000` with probability 1 | Middle X error: syndrome `11`, logical X result `0`, decoded auxiliaries `00`. |
| `examples/phase_estimation` | `1001` with probability 1 | T phase 1/8 as low-bit-first `100`, followed by target Z result `1`. |
| `examples/order_finding` | `000,010,001,011`, each with probability 1/4 | N=15, base 2; the Rust Shor example obtains factors 3 and 5 or a retry, each with probability 1/2. |

## Machine-readable check and run results

JSON v1 fields, diagnostics and normalization follow [machine interfaces](machine-interface-spec.md#diagnostics). Every invocation emits one result envelope; check yields verification, run approximate distributions and failures null results. The Python/interop adapters retain the same independent boundary.
