//! First-failure ordering survives shared retained-source storage.
mod common;

use qleisli::frontend::project::{Project, SourcePolicy};
use qleisli::frontend::sized::ParsedProgram;
use std::collections::BTreeMap;

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
    let error = ParsedProgram::parse(BTreeMap::from([
        ("a_basis".into(), basis.clone()),
        ("z_malformed".into(), malformed.into()),
    ]))
    .unwrap_err();
    assert_eq!(error.module(), Some("z_malformed"));
    assert_eq!(error.code(), "parse");
    // FIRST source and its earlier profile refusal remain frozen in the session.
    // Complete original parsing now exposes the same retained malformed EOF.
    assert_eq!((error.span().start, error.span().end), (114, 114));

    let error = ParsedProgram::parse(BTreeMap::from([
        ("a_malformed".into(), malformed.into()),
        ("z_basis".into(), basis),
    ]))
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
