//! Retained data comparison and actual fresh-boundary conformance.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::interchange::{execution_view, json};

fn cases() -> json::Value {
    json::parse(include_bytes!(
        "../../../../tests/fixtures/qmatch_v030/execution-cases.json"
    ))
    .unwrap()
}

fn proposal(row: &json::Value) -> (Arc<Subject>, Request) {
    let artifact = json::encode(row.field("artifact").unwrap()).unwrap();
    let request = json::encode(row.field("request").unwrap()).unwrap();
    let decoded = Request::decode(&request).unwrap();
    (
        Arc::new(Subject {
            edition: Edition::E2026,
            artifact: artifact.into(),
            request: Some(request.into()),
            checker: PathBuf::from("comparison-data-only"),
            decisions: None,
        }),
        decoded,
    )
}

fn expected(row: &json::Value) -> Vec<u8> {
    execution_view::encode(&execution_view::tests::vector_value(
        row.field("view").unwrap(),
    ))
    .unwrap()
}

#[test]
fn actual_retained_graph_and_caches_match_both_independent_exact_phase_views() {
    let rows = cases();
    let mut count = 0;
    let mut views = Vec::new();
    for row in rows.field("cases").unwrap().array().unwrap() {
        if !row.field("accepted").unwrap().boolean().unwrap() {
            continue;
        }
        let (subject, request) = proposal(row);
        let prepared = prepare(Arc::clone(&subject), &request).unwrap();
        assert!(Arc::ptr_eq(&subject, &prepared.subject));
        let actual = qmatch::complete(prepared.graph(), &request).unwrap();
        assert_eq!(actual, expected(row));
        assert_eq!(prepared.decoded.evidence.len(), 1);
        assert_eq!(prepared.decoded.programs.len(), 3);
        views.push(actual);
        count += 1;
    }
    assert_eq!(count, 2);
    assert_ne!(views[0], views[1]);
}

#[test]
fn typed_request_and_retained_objects_participate_in_the_actual_view() {
    let rows = cases();
    let row = &rows.field("cases").unwrap().array().unwrap()[0];
    let (subject, request) = proposal(row);
    let mut prepared = prepare(subject, &request).unwrap();
    let original = qmatch::complete(prepared.graph(), &request).unwrap();
    let mut changes = Vec::new();
    let mut changed = request.clone();
    changed.source.offset += 1;
    changes.push(changed);
    let mut changed = request.clone();
    changed.arms[0].controlled = 1;
    changes.push(changed);
    let mut changed = request.clone();
    changed.arms[0].evidence = 1;
    changes.push(changed);
    let mut changed = request.clone();
    changed.attached.inputs.swap(0, 1);
    changes.push(changed);
    let mut changed = request.clone();
    changed.required.outputs[0].basis = vec![crate::interchange::carrier::Atom::Bits(0)];
    changes.push(changed);
    for changed in changes {
        assert_ne!(
            qmatch::complete(prepared.graph(), &changed).unwrap(),
            original
        );
    }
    prepared.derived_effect = crate::ir::Effect::Observe;
    assert_ne!(
        qmatch::complete(prepared.graph(), &request).unwrap(),
        original
    );
    prepared.derived_effect = crate::ir::Effect::Unitary;
    Arc::get_mut(&mut prepared.decoded).unwrap().sources[0]
        .1
        .push(' ');
    assert_ne!(
        qmatch::complete(prepared.graph(), &request).unwrap(),
        original
    );
}

#[test]
fn proposal_roots_do_not_relax_ordinary_reachability_or_hide_unrelated_nodes() {
    let rows = cases();
    for row in rows.field("cases").unwrap().array().unwrap() {
        let name = row.field("name").unwrap().text().unwrap();
        let (subject, request) = proposal(row);
        if name == "original-exact-i" {
            let mut budget =
                crate::contract::exact::Budget::new(crate::contract::DEFAULT_EXACT_WORK);
            assert!(
                crate::interchange::decode_subject(&subject, &mut budget)
                    .unwrap_err()
                    .message
                    .contains("unused")
            );
            assert!(prepare(subject, &request).is_ok());
        } else if matches!(
            name,
            "unrelated-original-program"
                | "wrong-original-arm-evidence"
                | "wrong-original-arm-controlled"
        ) {
            assert!(prepare(subject, &request).is_err(), "{name}");
        } else if name == "unrelated-original-source" {
            // Only the fresh original-source gate decides relevance. The
            // untrusted complete proposal grants no local acceptance handle.
            let prepared = prepare(subject, &request).unwrap();
            assert_eq!(prepared.decoded.sources.len(), 2);
        }
    }
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn fresh_native_mode_checks_independent_views_and_all_original_substitutions() {
    let kernel = Kernel::selected(Edition::E2026).unwrap();
    let rows = cases();
    for row in rows.field("cases").unwrap().array().unwrap() {
        let name = row.field("name").unwrap().text().unwrap();
        let artifact = json::encode(row.field("artifact").unwrap()).unwrap();
        let request_bytes = json::encode(row.field("request").unwrap()).unwrap();
        let request = Request::decode(&request_bytes).unwrap();
        let accepted = row.field("accepted").unwrap().boolean().unwrap();
        let subject = kernel.subject(&artifact, Some(&request_bytes)).unwrap();
        let result = (|| -> Result<Checked> {
            let prepared = prepare(Arc::clone(&subject), &request)?;
            let supplied = expected(row);
            let native = Kernel::submit_subject(
                subject,
                "--qmatch-source-check",
                Some(View {
                    graph: &supplied,
                    caller: None,
                }),
            )?;
            prepared.bind(native)
        })();
        assert_eq!(result.is_ok(), accepted, "{name}: {result:?}");
    }
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn component_retains_the_same_fresh_native_mode_and_original_request() {
    let (kernel, log) = Kernel::selected(Edition::E2026).unwrap().recording();
    let rows = cases();
    let row = &rows.field("cases").unwrap().array().unwrap()[0];
    let artifact = json::encode(row.field("artifact").unwrap()).unwrap();
    let request = json::encode(row.field("request").unwrap()).unwrap();
    let checked = kernel.check_qmatch_source(&artifact, &request).unwrap();
    assert_eq!(checked.artifact(), artifact);
    assert_eq!(checked.request_bytes(), request);
    assert_eq!(checked.request(), &Request::decode(&request).unwrap());
    assert_eq!(checked.native().mode(), "--qmatch-source-check");
    let summary = log.summary();
    assert!(summary.complete());
    assert_eq!(summary.decisions(), 1);
    assert_eq!(summary.requests_checked(), 1);
}
