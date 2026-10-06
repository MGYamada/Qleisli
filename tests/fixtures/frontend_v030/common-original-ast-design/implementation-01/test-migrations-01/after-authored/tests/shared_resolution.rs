//! Shared source judgments retain explicit loader policies and concrete limits.
mod common;
use qleisli::frontend::{
    compile::{ErrorCode, check_project},
    project::Project,
    sized::{OperationBinding, ParsedProgram},
};
use std::{collections::BTreeMap, fs, path::PathBuf};

#[test]
fn recorded_profile_differences_and_adopted_convergence_remain_explicit() {
    let fixture = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/frontend_v030/ordinary-type-cutover/current/frontend_v030/shared-resolution/initial-study");
    for (case, finite, sized) in [
        ("unused-import-cycle", true, true),
        ("self-import-public", false, false),
        ("self-import-private", false, false),
        ("reserved-module", false, true),
        ("underscore-module", false, true),
        ("private-unused-import", false, false),
        // #32 removes this adapter restriction; historical outputs stay intact.
        ("same-module-two-declarations", true, true),
        ("duplicate-declarations", false, false),
        ("moved-local-shadows-import", true, false),
        ("declaration-call-cycle", true, false),
    ] {
        let root = fixture.join(case);
        let sources = fs::read_dir(&root)
            .unwrap()
            .map(|entry| entry.unwrap().path())
            .filter(|path| path.extension().is_some_and(|extension| extension == "qli"))
            .map(|path| {
                (
                    path.file_stem().unwrap().to_str().unwrap().to_owned(),
                    fs::read_to_string(path).unwrap(),
                )
            })
            .collect();
        assert_eq!(Project::load(&root).is_ok(), finite, "finite load: {case}");
        let selected = ParsedProgram::parse(sources);
        assert_eq!(selected.is_ok(), sized, "sized check: {case}");
        match case {
            "moved-local-shadows-import" | "declaration-call-cycle" => {
                // Loading is name resolution only. Both actual source consumers
                // reject the same moved-name or dependency-cycle program.
                let error = check_project(&root).unwrap_err();
                let (finite_code, selected_code) = if case == "moved-local-shadows-import" {
                    (ErrorCode::UnknownName, "name")
                } else {
                    (ErrorCode::Cycle, "cycle")
                };
                assert_eq!(error.code, finite_code, "{case}: {error}");
                assert_eq!(selected.unwrap_err().code(), selected_code, "{case}");
            }
            "self-import-public" | "self-import-private" => {
                let error = selected.unwrap_err();
                assert_eq!(error.code(), "name", "{case}: {error}");
                let source = fs::read_to_string(root.join("a.qli")).unwrap();
                let start = source.find("::f").unwrap() + 2;
                assert_eq!((error.span().start, error.span().end), (start, start + 1));
            }
            _ => {}
        }
    }
}

#[test]
fn unused_concrete_declaration_still_requires_native_eligible_effects() {
    let root = common::SourceRoot::new(
        "use std::quantum::init0; unitary fn unused()->Q<Bit>{init0()} observe fn main()->Bit{0}",
    );
    assert_eq!(check_project(&root.0).unwrap_err().code, ErrorCode::Effect);
}

#[test]
fn same_named_host_providers_keep_distinct_definition_and_instance_identity() {
    let program = ParsedProgram::parse(BTreeMap::from([
        (
            "main".into(),
            "pub unitary fn f[static U:Op<Bit>](q:Q<Bit>)->Q<Bit> requires Apply(U){U(q)}".into(),
        ),
        (
            "a".into(),
            "use std::quantum::h; pub unitary fn gate(q:Q<Bit>)->Q<Bit>{h(q)}".into(),
        ),
        (
            "b".into(),
            "use std::quantum::x; pub unitary fn gate(q:Q<Bit>)->Q<Bit>{x(q)}".into(),
        ),
    ]))
    .unwrap();
    let mut proposals = Vec::new();
    for path in ["a::gate", "b::gate", "a::gate"] {
        let source = program
            .instantiate(
                "main::f",
                BTreeMap::new(),
                BTreeMap::from([("U".into(), OperationBinding::new(path, BTreeMap::new()))]),
            )
            .unwrap()
            .elaborate()
            .unwrap();
        assert_eq!(source.definitions()[0].path(), path);
        proposals.push(source.lower().unwrap().payload().to_vec());
    }
    assert_ne!(proposals[0], proposals[1]);
    assert_eq!(proposals[0], proposals[2]);
}
