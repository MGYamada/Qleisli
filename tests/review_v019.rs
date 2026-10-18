//! Review regressions: hidden code and exact work on unused static arguments.
mod common;
use common::SourceRoot;
use qleisli::frontend::compile::{ErrorCode, check_project, compile_project};
use qleisli::frontend::parser::parse_module;
use qleisli::sim::{SimulationLimits, run_closed};

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
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
    let original = common::current_source_text(
        "tests/fixtures/review_v030alpha/hosted-source-clients/current/review_v019/bare_cr/main.qli",
    );
    let original = original.as_str();
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
    assert!(distribution.contains_key(&vec![true]));
    for (bits, probability) in &distribution {
        assert_eq!(bits.len(), 1);
        assert!(probability.is_finite() && *probability >= 0.0);
        let expected = if bits[0] { 1.0 } else { 0.0 };
        assert!((probability - expected).abs() < 1e-12);
    }
    assert!((distribution.values().sum::<f64>() - 1.0).abs() < 1e-12);
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn unused_static_arguments_share_exact_work_across_calls() {
    let base = common::current_source_text(
        "tests/fixtures/frontend_v030/ordinary-type-cutover/current/review_v019/static_budget/main.qli",
    );
    // Original closed actuals are checked during the call and again while
    // replaying dormant obligations. Four layers fit once; two calls exceed
    // the unchanged exact-work ceiling even though keep never applies U.
    let original = "power(power(p,150),150)";
    assert_eq!(
        base.matches(original).count(),
        1,
        "static-budget fixture drift"
    );
    let expression = format!("{}p{}", "power(".repeat(4), ",150)".repeat(4));
    let once = base.replace(original, &expression);
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
