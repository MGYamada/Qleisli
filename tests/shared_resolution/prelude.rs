//! Bounded prelude/reexport conformance; all native controls use at most two bits.
use super::*;
use qleisli::contract::FunctionEvidence;
use qleisli::frontend::compile::compile_project;
use qleisli::frontend::parser::parse_module;
use qleisli::ir::{CircuitAction, RawOp, RawProgram};
use qleisli::sim::{SimulationLimits, run_closed};

const BELL: &str =
    "observe fn main()->(Bit,Bit){let(a,b)=cnot(h(init0()),init0());(measure_z(a),measure_z(b))}";
const IMPORTS: &str = "use std::state::init0;use std::gate::cnot;";
const OFF: &str = "#![no_implicit_prelude]\n";

fn cnot_evidence(program: &RawProgram) -> &FunctionEvidence {
    program
        .operations
        .iter()
        .find_map(|operation| {
            let RawOp::ApplyUnitary { steps, .. } = operation else {
                return None;
            };
            steps.iter().find_map(|step| match &step.action {
                CircuitAction::Contract { evidence, .. } => Some(evidence.as_ref()),
                _ => None,
            })
        })
        .expect("ordinary controlled X retains its checked function evidence")
}

fn facade(root: &common::SourceRoot) {
    root.write("facade.qli", "pub use inner::{init0,cnot};");
    root.write("inner.qli", "pub use std::prelude::{init0,cnot};");
}

fn selected_error(sources: &[(&str, &str)], code: &str) {
    let error = ParsedProgram::parse(
        qleisli::edition::Edition::E2026,
        sources
            .iter()
            .map(|(name, source)| (name.to_string(), source.to_string()))
            .collect(),
    )
    .unwrap_err();
    assert_eq!(error.code(), code, "{sources:?}: {error}");
}

#[test]
fn header_and_reexport_syntax_keep_original_paths_and_spans() {
    let source = "//! Module docs\n#![no_implicit_prelude]\npub use std::gate::{id,x};\nunitary fn f(q:Q<Bit>)->Q<Bit>{std::gate::id[type(Bit)](q)}";
    let ast = parse_module(source).unwrap();
    assert!(ast.no_implicit_prelude);
    assert_eq!(ast.uses.len(), 2);
    assert!(ast.uses.iter().all(|usage| usage.public));
    let documented = qleisli::frontend::parser::parse_documented_module(
        "//! Before\n#![no_implicit_prelude]\n//! After\n/// Export notes\npub use std::gate::x;",
    )
    .unwrap();
    assert_eq!(documented.module_docs.len(), 2);
    assert_eq!(documented.import_docs[0][0].text.trim(), "Export notes");
    for usage in &ast.uses {
        let last = usage.path.last().unwrap();
        assert_eq!(&source[last.span.start..last.span.end], last.text);
    }
    for source in [
        "#![unknown]",
        "#![no_implicit_prelude]#![no_implicit_prelude]",
        "use std::gate::x;#![no_implicit_prelude]",
        "#![no_implicit_prelude(x)]",
        "pub use std::gate::*;",
        "pub use std::gate::x as flip;",
    ] {
        assert!(parse_module(source).is_err(), "{source}");
    }
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn default_explicit_optout_qualified_and_reexport_bell_have_equivalent_checked_core() {
    let variants = [
        BELL.to_string(), format!("{IMPORTS}{BELL}"), format!("{OFF}{IMPORTS}{BELL}"),
        format!("use std::prelude::{{init0,cnot}};{BELL}"),
        format!("{OFF}use std::prelude::{{init0,cnot}};{BELL}"),
        format!("use facade::{{init0,cnot}};{BELL}"),
        "observe fn main()->(Bit,Bit){let(a,b)=std::gate::cnot(h(std::state::init0()),std::state::init0());(measure_z(a),measure_z(b))}".into(),
    ];
    let explicit = common::SourceRoot::new(&variants[1]);
    facade(&explicit);
    let expected = compile_project(&explicit.0).unwrap();
    for source in variants {
        let root = common::SourceRoot::new(&source);
        facade(&root);
        let actual = compile_project(&root.0).unwrap_or_else(|e| panic!("{source}: {e}"));
        // Both full artifacts are checked independently. Eq on FunctionEvidence
        // compares issued proof identities, not exact semantic equality.
        let receipt = cnot_evidence(actual.program());
        let reference = cnot_evidence(expected.program());
        assert_eq!(receipt.identity().implementation, "std::gate::x");
        assert_eq!(receipt.identity().specification, "std::gate::x");
        assert_eq!(receipt.signature(), reference.signature());
        assert_eq!(receipt.meaning(), reference.meaning());
        assert_eq!(receipt.implementation(), reference.implementation());
        assert_eq!(receipt.specification(), reference.specification());
        let distribution = run_closed(&actual, SimulationLimits::default()).unwrap();
        assert_eq!(distribution.len(), 2);
        for bits in [vec![false, false], vec![true, true]] {
            assert!((distribution[&bits] - 0.5).abs() < 1e-12);
        }
        // Compare the complete emitted observing instruments through the native
        // contract gate, retaining both original bodies and their source bytes.
        let candidate = source.replace(
            "observe fn main()->(Bit,Bit){",
            "observe fn candidate(u:Q<Unit>)->(Bit,Bit){finish(u);",
        );
        let reference = "observe fn reference(u:Q<Unit>)->(Bit,Bit){finish(u);let(a,b)=std::gate::cnot(h(std::state::init0()),std::state::init0());(measure_z(a),measure_z(b))}";
        let checked = common::SourceRoot::new(&format!(
            "{candidate}{reference}observe fn main()->(Bit,Bit){{apply_contract(candidate,reference,unit(()))}}"
        ));
        facade(&checked);
        let instrument = compile_project(&checked.0).unwrap();
        assert!(format!("{instrument:?}").contains("InstrumentCall"));
    }
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn selected_raw_cli_uses_the_same_prelude_and_public_export_targets() {
    let qualified = "observe fn main()->(Bit,Bit){let(a,b)=std::gate::cnot(h(std::state::init0()),std::state::init0());(measure_z(a),measure_z(b))}";
    for source in [
        BELL.to_string(),
        format!("{OFF}{IMPORTS}{BELL}"),
        qualified.to_string(),
        format!("use facade::{{init0,cnot}};{BELL}"),
    ] {
        // Host selection requires a public entry. This is a separate current
        // translation, not a rewrite of the saved first private-main sources.
        let source = source.replace("observe fn main", "pub observe fn main");
        let root = common::SourceRoot::new(&source);
        facade(&root);
        let mut command = std::process::Command::new(env!("CARGO_BIN_EXE_qleisli"));
        command.args([
            "run",
            "--format=json",
            "--ir-profile=raw",
            "--entry=main::main",
        ]);
        for name in ["main", "facade", "inner"] {
            command.arg(format!(
                "--module={name}={}",
                root.0.join(format!("{name}.qli")).display()
            ));
        }
        let output = command.output().unwrap();
        assert!(output.status.success(), "{source}: {output:?}");
        let text = String::from_utf8(output.stdout).unwrap();
        assert_eq!(text.matches("\"probability\":").count(), 2, "{text}");
        for bits in ["[false,false]", "[true,true]"] {
            let probability: f64 = text
                .split_once(&format!("\"bits\":{bits},\"probability\":"))
                .unwrap_or_else(|| panic!("missing outcome in {text}"))
                .1
                .split_once('}')
                .unwrap()
                .0
                .parse()
                .unwrap();
            assert!((probability - 0.5).abs() < 1e-12, "{text}");
        }
    }
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn provider_receipts_retain_original_prelude_and_public_export_sources() {
    for (prefix, call, expected) in [
        ("", "x(q)", vec!["main", "std::prelude", "std::gate"]),
        ("", "std::gate::x(q)", vec!["main", "std::gate"]),
        (
            "",
            "std::prelude::x(q)",
            vec!["main", "std::prelude", "std::gate"],
        ),
        (
            "",
            "facade::x(q)",
            vec!["main", "facade", "inner", "std::gate"],
        ),
        (
            "use facade::x;",
            "x(q)",
            vec!["main", "facade", "inner", "std::gate"],
        ),
    ] {
        let source = format!(
            "{prefix}unitary fn flip(q:Q<Bit>)->Q<Bit>{{{call}}}observe fn main()->(Bit,Bit){{let(a,b)=controlled(flip)(h(init0()),init0());(measure_z(a),measure_z(b))}}"
        );
        let root = common::SourceRoot::new(&source);
        root.write("facade.qli", "pub use inner::x;");
        root.write("inner.qli", "pub use std::gate::x;");
        let program = compile_project(&root.0).unwrap();
        let receipt = cnot_evidence(program.program());
        assert_eq!(receipt.identity().implementation, "main::flip");
        for name in expected {
            assert!(
                receipt
                    .identity()
                    .sources
                    .iter()
                    .any(|(module, _)| module == name),
                "missing {name} for {call}"
            );
        }
        assert!(
            receipt
                .identity()
                .sources
                .iter()
                .any(|(name, bytes)| name == "main" && bytes == &source)
        );
        for name in ["facade", "inner"] {
            if let Some((_, bytes)) = receipt
                .identity()
                .sources
                .iter()
                .find(|(module, _)| module == name)
            {
                assert_eq!(
                    bytes,
                    &fs::read_to_string(root.0.join(format!("{name}.qli"))).unwrap()
                );
            }
        }
    }
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn host_selected_project_entry_retains_its_export_chain() {
    let main = "pub use facade::main;";
    let facade = "pub use middle::main;";
    let middle = "pub use leaf::main;";
    let leaf = "unitary fn flip(q:Q<Bit>)->Q<Bit>{x(q)} pub observe fn main()->(Bit,Bit){let(a,b)=controlled(flip)(h(init0()),init0());(measure_z(a),measure_z(b))}";
    let root = common::SourceRoot::new(main);
    for (name, source) in [("facade", facade), ("middle", middle), ("leaf", leaf)] {
        root.write(&format!("{name}.qli"), source);
    }
    root.write("unrelated.qli", "pub unitary fn idle(q:Q<Bit>)->Q<Bit>{q}");
    let program = compile_project(&root.0).unwrap();
    let receipt = cnot_evidence(program.program());
    assert_eq!(receipt.identity().implementation, "leaf::flip");
    for (name, source) in [
        ("main", main),
        ("facade", facade),
        ("middle", middle),
        ("leaf", leaf),
    ] {
        assert!(
            receipt
                .identity()
                .sources
                .iter()
                .any(|(module, bytes)| module == name && bytes == source),
            "missing host selection source {name}"
        );
    }
    assert!(
        !receipt
            .identity()
            .sources
            .iter()
            .any(|(module, _)| module == "unrelated")
    );
    let changed = "// Changed host selection source.\npub use middle::main;";
    root.write("facade.qli", changed);
    let other = compile_project(&root.0).unwrap();
    let changed_receipt = cnot_evidence(other.program());
    assert_eq!(receipt.meaning(), changed_receipt.meaning());
    assert_ne!(
        receipt.identity().sources,
        changed_receipt.identity().sources
    );
    assert!(
        changed_receipt
            .identity()
            .sources
            .iter()
            .any(|(module, bytes)| module == "facade" && bytes == changed)
    );
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn selected_host_entry_and_operation_aliases_keep_their_original_source_packet() {
    let sources = BTreeMap::from([
        ("facade".into(), "pub use middle::{entry,flip};".into()),
        ("middle".into(), "pub use leaf::{entry,flip};".into()),
        ("leaf".into(), "pub unitary fn flip(q:Q<Bit>)->Q<Bit>{q} pub unitary fn entry[const U:Op<Bit>](q:Q<Bit>)->Q<Bit> requires Applicable(U){U(q)}".into()),
    ]);
    let parsed = ParsedProgram::parse(qleisli::edition::Edition::E2026, sources.clone()).unwrap();
    let binding = OperationBinding::new("facade::flip", BTreeMap::new());
    let source = parsed
        .instantiate(
            "facade::entry",
            BTreeMap::new(),
            BTreeMap::from([("U".into(), binding.clone())]),
        )
        .unwrap()
        .elaborate()
        .unwrap();
    let proposal = source.lower_raw_operation("U").unwrap();
    let instance = proposal.source().instantiation();
    assert_eq!(instance.entry(), "facade::entry");
    assert_eq!(instance.operations()["U"], binding);
    assert_eq!(proposal.definition().path(), "leaf::flip");
    for (name, bytes) in sources {
        assert_eq!(instance.program().source(&name), Some(bytes.as_str()));
    }
    let kernel =
        qleisli::interchange::native::Kernel::selected(qleisli::edition::Edition::E2026).unwrap();
    let accepted = kernel.accept(proposal.proposal()).unwrap();
    proposal.validate_source_steps(&accepted).unwrap();
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn local_and_explicit_import_shadows_keep_their_meaning_without_fallback() {
    for main in [
        "unitary fn x(q:Q<Bit>)->Q<Bit>{q}observe fn main()->Bit{measure_z(x(init0()))}",
        "use helper::x;observe fn main()->Bit{measure_z(x(init0()))}",
    ] {
        let root = common::SourceRoot::new(main);
        root.write("helper.qli", "pub unitary fn x(q:Q<Bit>)->Q<Bit>{q}");
        let program = compile_project(&root.0).unwrap();
        let distribution = run_closed(&program, SimulationLimits::default()).unwrap();
        assert_eq!(distribution, BTreeMap::from([(vec![false], 1.0)]));
    }
    selected_error(
        &[(
            "main",
            "observe fn main()->Bit{let x=0;measure_z(x(init0()))}",
        )],
        "type",
    );
    selected_error(
        &[(
            "main",
            "observe fn main()->(Bit,Bit){let q=init0();let r=x(q);(measure_z(q),measure_z(r))}",
        )],
        "ownership",
    );
    selected_error(
        &[("main", "use std::gate::x;unitary fn x(q:Q<Bit>)->Q<Bit>{q}")],
        "name",
    );
    selected_error(&[("main", "use std::gate::x;use std::prelude::x;")], "name");
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn optout_preserves_bare_primitives_and_explicit_complete_basis_actuals() {
    let source = format!("{OFF}observe fn main()->Bit{{measure_z(h(basis unit(()) as _ {{0}}))}}");
    let root = common::SourceRoot::new(&source);
    compile_project(&root.0).unwrap();
    let missing = format!("{OFF}observe fn main()->Bit{{measure_z(init0())}}");
    selected_error(&[("main", &missing)], "name");
    selected_error(
        &[("main", "observe fn main()->Bit{measure_z(id(init0()))}")],
        "static",
    );
    for function in ["id", "std::gate::id", "std::prelude::id"] {
        let source = format!(
            "observe fn main()->(Bit,Bit){{let(a,b)=cnot(h(init0()),init0());let p={function}[type((Bit,Bit))](join(a,b));let(a,b)=split(p);(measure_z(a),measure_z(b))}}"
        );
        let root = common::SourceRoot::new(&source);
        compile_project(&root.0).unwrap();
    }
}

#[test]
fn reexport_chains_enforce_original_visibility_effects_and_cycles() {
    for public_path in [
        "std::gate::scalar_eighth",
        "std::prelude::h",
        "std::quantum::h",
    ] {
        let source = format!("unitary fn f(q:Q<Bit>)->Q<Bit>{{{public_path}(q)}}");
        let error = ParsedProgram::parse(
            qleisli::edition::Edition::E2026,
            BTreeMap::from([("main".into(), source)]),
        )
        .unwrap_err();
        assert!(matches!(error.code(), "visibility" | "name"), "{error}");
    }
    selected_error(
        &[("main", "pub use std::gate::scalar_eighth;")],
        "visibility",
    );
    selected_error(&[("a", "pub use b::x;"), ("b", "pub use a::x;")], "name");
    let library = "pub observe fn broad(q:Q<Bit>)->Q<Bit>{q}";
    for call in ["broad(q)", "facade::broad(q)", "library::broad(q)"] {
        let main = format!("use facade::broad;pub unitary fn f(q:Q<Bit>)->Q<Bit>{{{call}}}");
        selected_error(
            &[
                ("main", &main),
                ("facade", "pub use library::broad;"),
                ("library", library),
            ],
            "effect",
        );
    }
    selected_error(
        &[(
            "main",
            "pub unitary fn f(q:Q<Bit>)->Q<Bit>{let b=measure_z(q);init0()}",
        )],
        "effect",
    );
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn transparent_gates_reach_an_independent_exact_meaning_and_reject_hidden_phase() {
    let oracle = "classical fn flip(b:Bit)->Bit{not b}meaning Flip:Bit=permutation_by(flip);";
    let invoke =
        "unitary fn invoke[const U:Op<Bit>](q:Q<Bit>)->Q<Bit> requires Applicable(U){U(q)}";
    for gate in ["x", "std::gate::x", "std::prelude::x", "facade::x"] {
        let source = format!(
            "{oracle}{invoke}observe fn main()->Bit{{measure_z(invoke[checked_op({gate},Flip)](init0()))}}"
        );
        let root = common::SourceRoot::new(&source);
        root.write("facade.qli", "pub use inner::x;");
        root.write("inner.qli", "pub use std::gate::x;");
        let program = compile_project(&root.0).unwrap();
        let distribution = run_closed(&program, SimulationLimits::default()).unwrap();
        assert!((distribution[&vec![true]] - 1.0).abs() < 1e-12);
    }
    let source = format!(
        "{oracle}{invoke}unitary fn wrong(q:Q<Bit>)->Q<Bit>{{let u=global_phase_eighth(unit(()));finish(u);x(q)}}observe fn main()->Bit{{measure_z(invoke[checked_op(wrong,Flip)](init0()))}}"
    );
    ParsedProgram::parse(
        qleisli::edition::Edition::E2026,
        BTreeMap::from([("main".into(), source.clone())]),
    )
    .unwrap();
    let root = common::SourceRoot::new(&source);
    let error = compile_project(&root.0).unwrap_err();
    assert_eq!(error.code, ErrorCode::Contract, "{error}");
}
