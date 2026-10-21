//! First-failure ordering survives shared retained-source storage.
mod common;

use qleisli::frontend::compile::ParsedProgram;
use qleisli::frontend::project::{Project, SourcePolicy};
use std::collections::BTreeMap;

#[test]
fn parsed_nominal_declarations_cannot_be_silently_ignored_by_either_source_route() {
    use qleisli::frontend::compile::check_project_with_kernel;
    use qleisli::interchange::native::Kernel;
    for declaration in [
        "enum Tri { A, B, C }",
        "struct Empty {}",
        "struct Tagged { tag: Bit }",
    ] {
        let source = format!("pub fn main()->Unit{{()}} {declaration}");
        let error = ParsedProgram::parse(
            qleisli::edition::Edition::E2026,
            BTreeMap::from([("main".into(), source.clone())]),
        )
        .unwrap()
        .instantiate("main::main", BTreeMap::new(), BTreeMap::new())
        .unwrap()
        .elaborate()
        .unwrap_err();
        assert_eq!(error.code(), "unsupported");
        assert_eq!(&source[error.span().start..error.span().end], declaration);
        let root = common::SourceRoot::new(&source);
        let absent = root.0.join("must-not-run-native");
        let error = check_project_with_kernel(
            &root.0,
            SourcePolicy::default(),
            &Kernel::new(absent, qleisli::edition::Edition::E2026),
        )
        .unwrap_err();
        assert_eq!(error.code, "unsupported");
        assert_eq!(
            error.message,
            "finite type declarations require typed native transport before source execution"
        );
    }
    let error = ParsedProgram::parse(
        qleisli::edition::Edition::E2026,
        BTreeMap::from([
            ("a_type".into(), "enum Tri { A, B, C }".into()),
            ("z_bad".into(), "fn broken(".into()),
        ]),
    )
    .unwrap_err();
    assert_eq!(error.module(), Some("z_bad"));
    assert_eq!(error.code(), "parse");
}

#[test]
fn nominal_registration_checks_real_names_before_the_pending_carrier_gate() {
    for (source, message) in [
        (
            "enum Empty {}",
            "finite enum `Empty` must have at least one variant",
        ),
        ("enum Tri { A, B, A }", "duplicate member `A` in type `Tri`"),
        (
            "struct R { a:Bit, a:Bits<0> }",
            "duplicate member `a` in type `R`",
        ),
    ] {
        let error = ParsedProgram::parse(
            qleisli::edition::Edition::E2026,
            BTreeMap::from([("main".into(), source.into())]),
        )
        .unwrap_err();
        assert_eq!(error.code(), "type");
        assert_eq!(error.message(), message);
        let root = common::SourceRoot::new(source);
        assert_eq!(Project::load(&root.0).unwrap_err().message, message);
    }
    let modules = BTreeMap::from([
        (
            "main".into(),
            "use alias::Tri; pub fn main()->Unit{()}".into(),
        ),
        ("alias".into(), "pub use leaf::Tri;".into()),
        ("leaf".into(), "pub enum Tri { A, B, C }".into()),
    ]);
    let error = ParsedProgram::parse(qleisli::edition::Edition::E2026, modules)
        .unwrap()
        .instantiate("main::main", BTreeMap::new(), BTreeMap::new())
        .unwrap()
        .elaborate()
        .unwrap_err();
    assert_eq!(error.code(), "unsupported");
    assert!(error.message().contains("typed native transport"));
}

#[test]
fn completed_projections_keep_effects_and_unsupported_sibling_locations() {
    let unsupported = "pub fn sibling(c:Bit)->Bit{if c {1} else {0}}";
    for (supported, effect) in [
        ("pub unitary fn f(q:Q<Bit>)->Q<Bit>{let q=q;q}", "unitary"),
        ("pub isometry fn f()->Q<Bit>{let q=init0();q}", "iso"),
        (
            "pub observe fn f(q:Q<Bit>)->Bit{let bit=measure_z(q);let bit=not bit;bit}",
            "observe",
        ),
    ] {
        for declarations in [
            format!("{unsupported} {supported}"),
            format!("{supported} {unsupported}"),
        ] {
            let source = format!("use std::state::init0;  {declarations}");
            let program = ParsedProgram::parse(
                qleisli::edition::Edition::E2026,
                BTreeMap::from([("main".into(), source.clone())]),
            )
            .unwrap();
            let graph = program
                .instantiate("main::f", BTreeMap::new(), BTreeMap::new())
                .unwrap()
                .elaborate()
                .unwrap();
            assert_eq!(graph.definitions()[graph.root()].effect(), effect);
            let error = program
                .instantiate("main::sibling", BTreeMap::new(), BTreeMap::new())
                .unwrap_err();
            assert_eq!(error.code(), "unsupported");
            assert_eq!(error.module(), Some("main"));
            assert_eq!(
                error.message(),
                "sized preparation profile: unsupported runtime expression"
            );
            assert_eq!(
                &source[error.span().start..error.span().end],
                "if c {1} else {0}"
            );
        }
    }
}

#[test]
fn explicit_modules_finish_parsing_before_profile_eligibility() {
    let basis = std::fs::read_to_string(common::current_namespace_fixture(
        &std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join(
            "tests/fixtures/authoring_sessions/common-source-collection-v030/attempt-01/profile-before-late-parse/a_basis.qli",
        ),
    )).unwrap();
    let malformed = include_str!(
        "fixtures/authoring_sessions/common-source-collection-v030/attempt-01/profile-before-late-parse/z_malformed.qli"
    );
    let error = ParsedProgram::parse(
        qleisli::edition::Edition::E2026,
        BTreeMap::from([
            ("a_basis".into(), basis.clone()),
            ("z_malformed".into(), malformed.into()),
        ]),
    )
    .unwrap_err();
    assert_eq!(error.module(), Some("z_malformed"));
    assert_eq!(error.code(), "parse");
    // FIRST source and its earlier profile refusal remain frozen in the session.
    // Complete original parsing now exposes the same retained malformed EOF.
    assert_eq!((error.span().start, error.span().end), (114, 114));

    let error = ParsedProgram::parse(
        qleisli::edition::Edition::E2026,
        BTreeMap::from([
            ("a_malformed".into(), malformed.into()),
            ("z_basis".into(), basis),
        ]),
    )
    .unwrap_err();
    assert_eq!(error.module(), Some("a_malformed"));
    assert_eq!(error.code(), "parse");
    assert_eq!((error.span().start, error.span().end), (114, 114));
}

#[test]
fn filesystem_modules_keep_a_duplicate_before_a_later_parse_failure() {
    let root = common::SourceRoot::new("fn main() -> Bit { 0 }");
    let source = "// π\nfn item() -> Bit { 0 }\nfn item() -> Bit { 1 }\n";
    root.write("a_duplicate.qli", source);
    root.write("z_malformed.qli", "fn broken(");
    let error = Project::load_with_policy(&root.0, SourcePolicy::default()).unwrap_err();
    assert_eq!(error.code, "project");
    assert_eq!(error.message, "duplicate declaration `item`");
    let location = error.primary.unwrap();
    assert!(location.path.ends_with("a_duplicate.qli"));
    let start = source.rfind("item").unwrap();
    assert_eq!((location.span.start, location.span.end), (start, start + 4));
}
