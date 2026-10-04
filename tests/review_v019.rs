//! Review regressions: hidden code and exact work on unused static arguments.
mod common;
use common::SourceRoot;
use qleisli::frontend::compile::{ErrorCode, check_project, compile_project};
use qleisli::frontend::parser::parse_module;
use qleisli::sim::{SimulationLimits, run_closed};

#[test]
fn bare_cr_is_rejected_in_every_lexical_context_at_original_byte_offset() {
    for source in [
        "\r",
        "\r\r\n",
        "observe\r fn main()->Bit{1}",
        "// comment\r hidden code",
        "/* comment\r hidden code */",
        "/// documentation\r hidden code",
        "/*! documentation\r hidden code */",
        "// Japanese 日本語\r hidden code",
        "/* nested /* x\r */ */",
    ] {
        let error = parse_module(source).unwrap_err();
        assert!(error.message.contains("bare carriage return"), "{error:?}");
        assert_eq!(error.span.start, source.find('\r').unwrap());
        assert_eq!(error.span.end, error.span.start + 1);
    }
    // The canonical derivative retains the literal CR; its source map preserves
    // the earlier CBit input without compiling obsolete syntax after CR repair.
    let original = include_str!(
        "fixtures/review_v030alpha/hosted-source-clients/current/review_v019/bare_cr/main.qli"
    );
    let root = SourceRoot::new(original);
    let error = check_project(&root.0).unwrap_err();
    assert_eq!(error.span.start, original.find('\r').unwrap());
    assert_eq!(
        error.line,
        original[..error.span.start]
            .bytes()
            .filter(|b| *b == b'\n')
            .count()
            + 1
    );
    // Explicit line-ending repair makes the formerly hidden X executable.
    root.write("main.qli", &original.replace('\r', "\r\n"));
    let distribution = run_closed(
        &compile_project(&root.0).unwrap(),
        SimulationLimits::default(),
    )
    .unwrap();
    assert_eq!(distribution[&vec![true]], 1.0);
}

#[test]
fn unused_static_arguments_share_exact_work_across_calls() {
    let base = include_str!(
        "fixtures/frontend_v030/ordinary-type-cutover/current/review_v019/static_budget/main.qli"
    );
    let expression = format!("{}p{}", "repeat_op(150,".repeat(10), ")".repeat(10));
    let once = base.replace("repeat_op(150,repeat_op(150,p))", &expression);
    let root = SourceRoot::new(&once);
    check_project(&root.0).unwrap();
    let calls = format!("let q=keep[{expression}](q);keep[{expression}](q)");
    root.write(
        "main.qli",
        &once.replace(&format!("keep[{expression}](q)"), &calls),
    );
    let error = check_project(&root.0).unwrap_err();
    assert_eq!(error.code, ErrorCode::Limit, "{error}");
    assert!(
        error.message.contains("exact matrix work budget"),
        "{error}"
    );
}
