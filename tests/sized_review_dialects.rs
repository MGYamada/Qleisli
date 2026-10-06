//! Small source-level comparisons of the generic Rust frontend and the
//! experimental concrete Python oracle. Neither result supplies IR evidence.
// Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
mod common;

use qleisli::frontend::sized::ParsedProgram;
use std::collections::BTreeMap;
use std::io::Write;
use std::path::PathBuf;
use std::process::{Command, Stdio};

fn prepare(source: &str, naturals: BTreeMap<String, u32>) -> Result<(), String> {
    ParsedProgram::parse(BTreeMap::from([("main".into(), source.into())]))
        .and_then(|program| program.instantiate("main::f", naturals, BTreeMap::new()))
        .and_then(|instance| instance.elaborate())
        .map(|_| ())
        .map_err(|e| e.to_string())
}

fn python(cases: &[(String, BTreeMap<String, u32>)]) -> Vec<bool> {
    let script = r#"
import sys
sys.path.insert(0, 'scripts')
from compile_sized_corpus import compile_source, SourceError
for line in sys.stdin:
    source, arguments = line.rstrip('\n').split('\t')
    sizes = dict((name, int(value)) for name, value in
                 (arg.split('=') for arg in arguments.split(',') if arg))
    try:
        compile_source(bytes.fromhex(source).decode(), 'f', sizes)
        print('accept')
    except SourceError:
        print('reject')
"#;
    let mut child = Command::new("python3")
        .args(["-c", script])
        .current_dir(env!("CARGO_MANIFEST_DIR"))
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("Python 3.11+ is required for the sized dialect comparison");
    let mut input = String::new();
    for (source, values) in cases {
        use std::fmt::Write as _;
        for byte in source.bytes() {
            write!(&mut input, "{byte:02x}").unwrap();
        }
        input.push('\t');
        input.push_str(
            &values
                .iter()
                .map(|(key, value)| format!("{key}={value}"))
                .collect::<Vec<_>>()
                .join(","),
        );
        input.push('\n');
    }
    // Concurrent draining avoids filling either pipe with generated cases.
    let mut stdin = child.stdin.take().unwrap();
    let writer = std::thread::spawn(move || stdin.write_all(input.as_bytes()));
    let output = child.wait_with_output().unwrap();
    writer.join().unwrap().unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let results: Vec<_> = String::from_utf8(output.stdout)
        .unwrap()
        .lines()
        .map(|line| match line {
            "accept" => true,
            "reject" => false,
            other => panic!("unexpected oracle response: {other}"),
        })
        .collect();
    assert_eq!(results.len(), cases.len());
    results
}

#[test]
#[ignore = "requires the development Python 3.11+ oracle"]
fn python_static_comparisons_keep_type_angles_separate_in_both_dialects() {
    let mut cases = Vec::new();
    for comparison in ["<", ">", "!=", "<=", ">=", "=="] {
        for n in [0, 1, 3] {
            cases.push((
                format!("pub unitary fn f[static n: Nat](q: Q<Bits<n>>) -> Q<Bits<n>> {{ if static 1 {comparison} n {{ q }} else {{ q }} }}"),
                BTreeMap::from([("n".into(), n)]),
            ));
        }
    }
    for name in ["Q", "Bits", "CBits", "Op"] {
        cases.push((format!("pub unitary fn f[static {name}: Nat](q: Q<Bit>) -> Q<Bit> {{ if static {name} < 2 {{ q }} else {{ q }} }}"), BTreeMap::from([(name.into(), 1)])));
    }
    let oracle = python(&cases);
    for ((source, values), oracle) in cases.iter().zip(oracle) {
        assert!(prepare(source, values.clone()).is_ok(), "{source}");
        assert!(oracle, "{source}");
    }
}

#[test]
fn lowering_profile_diagnostics_are_available_before_proposal_generation() {
    for source in [
        "use std::quantum::init0; pub iso fn f(q:Q<Bit>)->(Q<Bit>,Q<Bit>,Bit){(q,init0(),0)}",
        "pub unitary fn f(q: Q<Bit>, c: Bit) -> (Q<Bit>,Bit) { (q,c) }",
        "use std::classical::empty_bits; pub unitary fn f() -> Bits<0> { empty_bits() }",
    ] {
        let elaborated = ParsedProgram::parse(BTreeMap::from([("main".into(), source.into())]))
            .unwrap()
            .instantiate("main::f", BTreeMap::new(), BTreeMap::new())
            .unwrap()
            .elaborate()
            .unwrap();
        let profile = elaborated.check_lowering_profile().unwrap_err();
        assert_eq!(profile.code(), "unsupported", "{profile}");
        assert_eq!(profile.module(), Some("main"));
        assert_eq!(profile.span().start, source.find("pub ").unwrap());
        assert_eq!(profile.span().end, source.len());
        assert!(profile.message().contains("lowering"), "{profile}");
        assert_eq!(profile, elaborated.lower().unwrap_err());
    }
    let source = "use std::quantum::init0; pub iso fn f(q:Q<Bit>)->(Q<Bit>,Q<Bit>){(q,init0())}";
    let preparation = ParsedProgram::parse(BTreeMap::from([("main".into(), source.into())]))
        .unwrap()
        .instantiate("main::f", BTreeMap::new(), BTreeMap::new())
        .unwrap()
        .elaborate()
        .unwrap();
    preparation.check_lowering_profile().unwrap();
    assert_eq!(
        preparation.definitions()[preparation.root()].effect(),
        "iso"
    );
    assert!(preparation.lower().unwrap().is_instrument());
    let source = "use std::quantum::h; pub unitary fn f(q: Q<Bit>) -> Q<Bit> { h(q) }";
    let elaborated = ParsedProgram::parse(BTreeMap::from([("main".into(), source.into())]))
        .unwrap()
        .instantiate("main::f", BTreeMap::new(), BTreeMap::new())
        .unwrap()
        .elaborate()
        .unwrap();
    elaborated.check_lowering_profile().unwrap();
    elaborated.lower().unwrap();
}

#[test]
#[ignore = "requires the development Python 3.11+ oracle"]
fn python_concrete_execution_does_not_replace_generic_size_obligations() {
    let first = include_str!(
        "fixtures/frontend_v030/ordinary-type-cutover/current/sized_review/unguarded_take.qli"
    );
    let corrected = first.replace("Q<Bits<n>> {", "Q<Bits<n>> requires n >= 1 {");
    let cases = vec![
        (first.into(), BTreeMap::from([("n".into(), 1)])),
        (first.into(), BTreeMap::from([("n".into(), 3)])),
        (corrected.clone(), BTreeMap::from([("n".into(), 1)])),
        (corrected, BTreeMap::from([("n".into(), 3)])),
    ];
    assert_eq!(python(&cases), [true, true, true, true]);
    for (i, (source, values)) in cases.into_iter().enumerate() {
        let result = prepare(&source, values);
        if i < 2 {
            assert!(result.unwrap_err().contains("size"));
        } else {
            result.unwrap();
        }
    }
}

#[test]
#[ignore = "requires the development Python 3.11+ oracle"]
fn python_common_quantum_subset_has_matching_acceptance_under_seeded_mutations() {
    let mut cases = Vec::new();
    let mut random = 0x7220_0323_u64;
    for i in 0..400 {
        let mut body = String::new();
        for _ in 0..(1 + i % 8) {
            random ^= random << 13;
            random ^= random >> 7;
            random ^= random << 17;
            body.push_str(match random % 5 {
                0 => "let a = h(a);",
                1 => "let b = x(b);",
                2 => "let (a,b) = cnot(a,b);",
                3 => "let pair = (a,b); let (a,b) = pair;",
                _ => "let a = x(h(a));",
            });
        }
        body.push_str(match i % 5 {
            0 => "(a,b)",
            1 => "let (a,b) = cnot(a,a); (a,b)",
            2 => "let moved = a; let a = h(a); (moved,b)",
            3 => "let a = b; (a,a)",
            _ => "a",
        });
        cases.push((format!("use std::quantum::h; use std::quantum::x; use std::quantum::cnot; pub unitary fn f(a: Q<Bit>, b: Q<Bit>) -> (Q<Bit>,Q<Bit>) {{ {body} }}"), BTreeMap::new()));
    }
    let oracle = python(&cases);
    let mut accepted = 0;
    for ((source, values), oracle) in cases.into_iter().zip(oracle) {
        let rust = prepare(&source, values).is_ok();
        assert_eq!(rust, oracle, "{source}");
        accepted += usize::from(rust);
    }
    assert_eq!(accepted, 80);
}

fn corpus_modules() -> BTreeMap<String, String> {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    [
        ("prepare", "katas_ghz/prepare.qli"),
        ("bitwise", "qualtran_xor/bitwise.qli"),
        ("controls", "qualtran_arithmetic/controls.qli"),
        ("increment", "qualtran_arithmetic/increment.qli"),
        ("addition", "qualtran_arithmetic/addition.qli"),
        ("comparison", "qualtran_arithmetic/comparison.qli"),
        ("negation", "qualtran_arithmetic/negation.qli"),
    ]
    .into_iter()
    .map(|(module, path)| {
        (
            module.into(),
            std::fs::read_to_string(common::current_namespace_fixture(
                &root.join("corpus/sized").join(path),
            ))
            .unwrap(),
        )
    })
    .collect()
}

#[test]
fn ghz_and_arithmetic_corpus_prepare_and_lower_through_rust() {
    let program = ParsedProgram::parse(corpus_modules()).unwrap();
    for n in 0..=3 {
        for entry in [
            "controls::all_ones",
            "increment::increment",
            "addition::add_k",
            "comparison::equals",
        ] {
            let mut sizes = BTreeMap::from([("n".into(), n)]);
            if entry == "addition::add_k" {
                sizes.insert("K".into(), 2);
            }
            let proposal = program
                .instantiate(entry, sizes, BTreeMap::new())
                .unwrap()
                .elaborate()
                .unwrap()
                .lower()
                .unwrap();
            assert!(!proposal.is_instrument(), "{entry}[{n}]");
            assert!(!proposal.payload().is_empty());
        }
        if n > 0 {
            program
                .instantiate(
                    "prepare::ghz",
                    BTreeMap::from([("n".into(), n)]),
                    BTreeMap::new(),
                )
                .unwrap()
                .elaborate()
                .unwrap()
                .lower()
                .unwrap();
        }
    }
}

#[test]
#[ignore = "requires the development Python 3.11+ oracle"]
fn python_ghz_and_arithmetic_corpus_agree_with_rust_preparation() {
    ghz_and_arithmetic_corpus_prepare_and_lower_through_rust();
    let oracle = Command::new("python3")
        .args([
            "-c",
            r#"
import sys
from pathlib import Path
sys.path.insert(0, 'scripts')
from compile_sized_corpus import compile_source
from current_source_fixtures import current_source_file
root = Path('corpus/sized')
modules = {path.stem: current_source_file(path).read_text() for path in (root/'qualtran_arithmetic').glob('*.qli')}
modules['prepare'] = current_source_file(root/'katas_ghz/prepare.qli').read_text()
modules['bitwise'] = current_source_file(root/'qualtran_xor/bitwise.qli').read_text()
count = 0
for n in range(4):
    for module, entry in [('controls','all_ones'), ('increment','increment'),
                          ('addition','add_k'), ('comparison','equals')]:
        values = dict(n=n, **({'K': 2} if module == 'addition' else {}))
        compile_source(modules[module], entry, values, modules=modules)
        count += 1
    if n:
        compile_source(modules['prepare'], 'ghz', dict(n=n), modules=modules)
        count += 1
print(count)
"#,
        ])
        .current_dir(env!("CARGO_MANIFEST_DIR"))
        .output()
        .unwrap();
    assert!(
        oracle.status.success(),
        "{}",
        String::from_utf8_lossy(&oracle.stderr)
    );
    assert_eq!(String::from_utf8(oracle.stdout).unwrap().trim(), "19");
}

#[test]
fn transparent_operation_groups_keep_tuple_shapes_and_quantum_ownership() {
    let provider = "use std::quantum::x; pub unitary fn flip(a: Q<Bit>, b: Q<Bit>) -> (Q<Bit>,Q<Bit>) { (a,x(b)) }";
    let template = "use dep::flip; pub unitary fn f(c: Q<Bit>, a: Q<Bit>, b: Q<Bit>) -> (Q<Bit>,Q<Bit>,Q<Bit>) { let (c,(a,b)) = controlled(flip)(c,(a,b)); (c,a,b) }";
    for main in [
        template.to_string(),
        template.replace("controlled(flip)(c,(a,b))", "(c,adjoint(flip,(a,b)))"),
    ] {
        ParsedProgram::parse(BTreeMap::from([
            ("main".into(), main),
            ("dep".into(), provider.into()),
        ]))
        .unwrap()
        .instantiate("main::f", BTreeMap::new(), BTreeMap::new())
        .unwrap()
        .elaborate()
        .unwrap()
        .lower()
        .unwrap();
    }
    for wrong in [
        template.replace("(c,(a,b))", "(c,(a,a))"),
        template.replace("controlled(flip)(c,(a,b))", "controlled(flip)(c,(a,(b,)))"),
    ] {
        assert!(
            ParsedProgram::parse(BTreeMap::from([
                ("main".into(), wrong),
                ("dep".into(), provider.into())
            ]))
            .is_err()
        );
    }
    let classical = "pub unitary fn flip(a: Q<Bit>, b: Bit) -> (Q<Bit>,Bit) { (a,b) }";
    assert!(
        ParsedProgram::parse(BTreeMap::from([
            ("main".into(), template.into()),
            ("dep".into(), classical.into())
        ]))
        .is_err()
    );
    let zero_owner = "pub unitary fn identity(q: Q<Bits<0>>) -> Q<Bits<0>> { q }";
    let zero_client = "use dep::identity; pub unitary fn f(c: Q<Bit>, q: Q<Bits<0>>) -> (Q<Bit>,Q<Bits<0>>) { controlled(identity)(c,q) }";
    ParsedProgram::parse(BTreeMap::from([
        ("main".into(), zero_client.into()),
        ("dep".into(), zero_owner.into()),
    ]))
    .unwrap()
    .instantiate("main::f", BTreeMap::new(), BTreeMap::new())
    .unwrap()
    .elaborate()
    .unwrap()
    .lower()
    .unwrap();
    let copyable_unit = "pub unitary fn identity(q: Unit) -> Unit { q }";
    let unit_client = "use dep::identity; pub unitary fn f(c: Q<Bit>) -> Q<Bit> { let (c,()) = controlled(identity)(c,()); c }";
    assert!(
        ParsedProgram::parse(BTreeMap::from([
            ("main".into(), unit_client.into()),
            ("dep".into(), copyable_unit.into())
        ]))
        .is_err()
    );
    // Ordinary copyable-unit arguments remain supported; this restriction
    // concerns only the complete quantum target of operation constructors.
    let ordinary_unit_client =
        "use dep::identity; pub unitary fn f(c: Q<Bit>) -> Q<Bit> { let () = identity(()); c }";
    ParsedProgram::parse(BTreeMap::from([
        ("main".into(), ordinary_unit_client.into()),
        ("dep".into(), copyable_unit.into()),
    ]))
    .unwrap()
    .instantiate("main::f", BTreeMap::new(), BTreeMap::new())
    .unwrap()
    .elaborate()
    .unwrap();
}

#[test]
#[ignore = "requires the separately built and audited Lean kernel"]
fn rust_arithmetic_and_ghz_proposals_preserve_small_reference_columns_natively() {
    use qleisli::interchange::hierarchical::{Kernel, execution::ExecutionLimits};
    let kernel =
        Kernel::new(std::env::var_os("QLEISLI_HIERARCHY_KERNEL").expect("select audited kernel"));
    let program = ParsedProgram::parse(corpus_modules()).unwrap();
    let limits = ExecutionLimits {
        max_amplitudes: 256,
        max_steps: 1_000_000,
    };
    for (entry, widths) in [
        ("controls::all_ones", 0..=2),
        ("increment::increment", 0..=3),
        ("addition::add_k", 0..=3),
        ("comparison::equals", 0..=1),
        ("prepare::ghz", 1..=3),
    ] {
        for n in widths {
            let mut sizes = BTreeMap::from([("n".into(), n)]);
            if entry == "addition::add_k" {
                sizes.insert("K".into(), 2);
            }
            let proposal = program
                .instantiate(entry, sizes, BTreeMap::new())
                .unwrap()
                .elaborate()
                .unwrap()
                .lower()
                .unwrap();
            let checked = kernel
                .check_against(proposal.payload(), proposal.comparison_request())
                .unwrap();
            let bits = match entry {
                "controls::all_ones" => n + 1,
                "comparison::equals" => 2 * n + 1,
                _ => n,
            };
            let d = 1usize << bits;
            let mut input = vec![[0.0, 0.0]; d * d];
            let mut expected = vec![[0.0, 0.0]; d * d];
            for column in 0..d {
                input[column + d * column] = [1.0, 0.0];
                let mask = (1usize << n) - 1;
                if entry == "prepare::ghz" {
                    let tail = column & !1;
                    expected[tail + d * column] = [std::f64::consts::FRAC_1_SQRT_2, 0.0];
                    expected[((tail ^ (mask & !1)) | 1) + d * column] = [
                        if column & 1 == 0 {
                            std::f64::consts::FRAC_1_SQRT_2
                        } else {
                            -std::f64::consts::FRAC_1_SQRT_2
                        },
                        0.0,
                    ];
                } else {
                    let row = match entry {
                        "controls::all_ones" => {
                            column ^ if column & mask == mask { 1 << n } else { 0 }
                        }
                        "increment::increment" => (column + 1) & mask,
                        "addition::add_k" => (column + 2) & mask,
                        "comparison::equals" => {
                            column
                                ^ if column & mask == (column >> n) & mask {
                                    1 << (2 * n)
                                } else {
                                    0
                                }
                        }
                        _ => unreachable!(),
                    };
                    expected[row + d * column] = [1.0, 0.0];
                }
            }
            let result = checked.execute(&input, d, limits).unwrap();
            for (actual, expected) in result.amplitudes.iter().zip(expected) {
                assert!(
                    (actual[0] - expected[0]).abs() < 1e-12 && actual[1].abs() < 1e-12,
                    "{entry}[{n}]: {actual:?} != {expected:?}"
                );
            }
        }
    }
}
