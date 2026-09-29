//! Diagnostics retain source positions through independent IR validation.

mod common;

use common::SourceRoot;
use qleisli::frontend::compile::{ErrorCode, check_project};
use qleisli::frontend::compile::{check_project_diagnostic, compile_project_diagnostic};

const IMPORTS: &str = "use std::quantum::x;
use std::quantum::z;
basis fn predicate(x: Bit) -> Bit { x }
unitary fn identity(q: Q<Bit>) -> Q<Bit> { q }
";

#[test]
fn structured_parse_diagnostics_preserve_unicode_crlf_and_eof_spans() {
    for source in [
        "/* 🦀日本語 */ @",
        "// 日本語\r\nobserve fn main() -> Unit {",
        "@",
    ] {
        let root = SourceRoot::new(source);
        let diagnostic = check_project_diagnostic(&root.0).unwrap_err();
        assert_eq!(diagnostic.code, "parse");
        let location = diagnostic.primary.unwrap();
        let start = source.find('@').unwrap_or(source.len());
        assert_eq!(location.span.start, start);
        assert_eq!(
            location.span.end,
            if start == source.len() {
                start
            } else {
                start + 1
            }
        );
        let prefix = &source[..start];
        assert_eq!(
            location.line,
            prefix.chars().filter(|c| *c == '\n').count() + 1
        );
        assert_eq!(
            location.column,
            prefix.rsplit('\n').next().unwrap().chars().count() + 1
        );
        let legacy = check_project(&root.0).unwrap_err();
        assert_eq!(legacy.code, ErrorCode::Project);
        assert_eq!(
            (legacy.span, legacy.line, legacy.column),
            (location.span, location.line, location.column)
        );
    }
}

#[test]
fn structured_load_errors_distinguish_source_spans_from_missing_files() {
    let root = SourceRoot::new("/* 日本語 */ use absent::name;");
    let error = check_project_diagnostic(&root.0).unwrap_err();
    assert_eq!(error.code, "project");
    let location = error.primary.unwrap();
    assert_eq!(
        (location.span.start, location.line, location.column),
        (16, 1, 11)
    );
    let error = check_project_diagnostic(&root.0.join("missing")).unwrap_err();
    assert_eq!(error.code, "project");
    assert!(error.primary.is_none());
    root.write("main.qli", "");
    assert!(check_project_diagnostic(&root.0).is_ok());
    let error = compile_project_diagnostic(&root.0).unwrap_err();
    assert_eq!(error.code, "invalid_entry");
    assert!(error.primary.is_none());
}

#[test]
fn invalid_computed_contract_points_to_its_expression_including_nested_branches() {
    let dirty = "with_computed(q, predicate, identity) { |d,a| (d,x(a)) }";
    for body in [
        dirty.to_owned(),
        format!("if flag {{ q }} else {{\n        {dirty}\n    }}"),
        format!("if flag {{ if false {{ q }} else {{\n        {dirty}\n    }} }} else {{ q }}"),
        format!("let q = with_computed(q, predicate) {{ |a| z(z(a)) }};\n    {dirty}"),
    ] {
        let source = format!(
            "{IMPORTS}pub unitary fn candidate(flag: CBit, q: Q<Bit>) -> Q<Bit> {{\n    {body}\n}}"
        );
        let root = SourceRoot::new("use candidate::candidate;\n");
        root.write("candidate.qli", &source);
        let failure = check_project(&root.0).unwrap_err();
        assert_eq!(failure.code, ErrorCode::InvalidIr, "{failure}");
        assert!(failure.path.ends_with("candidate.qli"), "{failure}");
        let start = source.find(dirty).unwrap();
        assert_eq!(failure.span.start, start, "{failure}");
        assert_eq!(failure.span.end, start + dirty.len(), "{failure}");
        assert_eq!(failure.line, source[..start].lines().count(), "{failure}");
        assert!(failure.message.contains("U E_in = E_out u"), "{failure}");
        assert!(
            failure.message.contains("input column 0, output row 0"),
            "{failure}"
        );
        assert!(
            failure.message.contains("actual 0, expected 1"),
            "{failure}"
        );
    }
}

#[test]
fn function_contract_mismatch_reports_an_exact_phase_counterexample() {
    let source = format!(
        "{IMPORTS}unitary fn negative_z(q: Q<Bit>) -> Q<Bit> {{ x(z(x(q))) }}
unitary fn specification(q: Q<Bit>) -> Q<Bit> {{ z(q) }}
unitary fn candidate(q: Q<Bit>) -> Q<Bit> {{
    apply_contract(negative_z, specification, q)
}}"
    );
    let root = SourceRoot::new(&source);
    let failure = check_project(&root.0).unwrap_err();
    assert_eq!(failure.code, ErrorCode::InvalidIr, "{failure}");
    assert_eq!(failure.span.start, source.find("apply_contract").unwrap());
    assert!(
        failure.message.contains("input column 0, output row 0"),
        "{failure}"
    );
    assert!(
        failure.message.contains("actual -1, expected 1"),
        "{failure}"
    );
}

#[test]
fn parser_failure_remains_project_category_with_explicit_parse_context() {
    let root = SourceRoot::new("observe fn main() -> CBit {\n    @\n}");
    let failure = check_project(&root.0).unwrap_err();
    assert_eq!(failure.code, ErrorCode::Project);
    assert_eq!((failure.line, failure.column), (2, 5));
    assert!(failure.message.starts_with("parse error:"), "{failure}");
}

#[test]
fn invalid_contract_inside_an_isolated_computed_body_keeps_its_source_span() {
    let dirty = "with_computed(d, predicate, identity) { |e,b| (e,x(b)) }";
    let source = format!(
        "{IMPORTS}unitary fn candidate(q: Q<Bit>) -> Q<Bit> {{
    with_computed(q, predicate, identity) {{ |d,a|
        let d = {dirty};
        (d,a)
    }}
}}"
    );
    let root = SourceRoot::new(&source);
    let failure = check_project(&root.0).unwrap_err();
    assert_eq!(failure.code, ErrorCode::InvalidIr, "{failure}");
    assert_eq!(failure.span.start, source.find(dirty).unwrap(), "{failure}");
    assert_eq!(failure.span.end - failure.span.start, dirty.len());
}
