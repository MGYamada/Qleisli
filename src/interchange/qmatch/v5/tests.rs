//! Data-only strictness controls. No source/type/IR acceptance is exercised.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0
use super::*;

const EMPTY: &str = r#"{"positions":[],"sites":[],"calls":[],"branches":[],"bodies":[]}"#;
const RUNTIME: &str = r#"{"format":"qleisli.runtime-root-request","version":2,"profile":"finite-runtime-root-v2",
 "selection":"internal","module":"m","declaration":"f","static_bases":[],"static_naturals":[],
 "parameters":[],"input_storage":[],"input_rows":[[]],"result":[{"tag":"finite","atom":{"tag":"unit"}}],
 "storage":[{"tag":"ordinary","basis":[{"tag":"unit"}],"storage":{"tag":"unit"}}],"public_effect":"unitary"}"#;

fn value() -> Value {
    json::parse(format!(r#"{{"format":"qleisli.qmatch-request","version":5,"profile":"finite-source-qmatch-context-v5",
      "source":{{"module":"m","function":"f","static_bases":[],"static_naturals":[],"static_operations":[]}},
      "runtime":{RUNTIME},
      "positions":[],"sites":[],"calls":[],"branches":[],"bodies":[
       {{"subject":{{"kind":"function","evidence":7}},"body":{EMPTY}}},
       {{"subject":{{"kind":"pure","program":9}},"body":{EMPTY}}}]}}"#).as_bytes()).unwrap()
}

fn object(value: &mut Value) -> &mut std::collections::BTreeMap<String,Value> {
    let Value::Object(value) = value else { panic!("expected object") };
    value
}

#[test]
fn unified_body_subject_variants_are_exact_and_old_profiles_refuse() {
    let decoded = Request::decode(&json::encode(&value()).unwrap()).unwrap();
    assert_eq!(decoded.context.bodies[0].subject, ProviderSubject::Function { evidence:7 });
    assert_eq!(decoded.context.bodies[1].subject, ProviderSubject::Pure { program:9 });
    for old in 1..5 {
        let mut changed = value();
        object(&mut changed).insert("version".into(), Value::Number(old));
        assert!(Request::decode(&json::encode(&changed).unwrap()).is_err());
    }
    for extra in ["accepted", "logical", "roots", "providers", "source_preserved"] {
        let mut changed = value();
        object(&mut changed).insert(extra.into(), Value::Bool(true));
        assert!(Request::decode(&json::encode(&changed).unwrap()).is_err(), "{extra}");
    }
    for missing in ["runtime", "calls", "branches", "bodies"] {
        let mut changed = value();
        object(&mut changed).remove(missing);
        assert!(Request::decode(&json::encode(&changed).unwrap()).is_err(), "{missing}");
    }
}

#[test]
fn retained_runtime_identity_and_static_actuals_match_the_same_source_instance() {
    let initial = value();
    let decoded = Request::decode(&json::encode(&initial).unwrap()).unwrap();
    assert_eq!(Request::decode(&decoded.encode().unwrap()).unwrap(), decoded);
    for field in ["module", "declaration"] {
        let mut changed = initial.clone();
        object(object(&mut changed).get_mut("runtime").unwrap())
            .insert(field.into(), Value::String("other".into()));
        assert!(Request::decode(&json::encode(&changed).unwrap()).is_err());
    }
    for field in ["static_bases", "static_naturals"] {
        let actual = if field == "static_bases" { r#"[{"name":"A","basis":[{"tag":"unit"}]}]"# }
            else { r#"[{"name":"unused","value":17}]"# };
        let actual = json::parse(actual.as_bytes()).unwrap();
        let mut changed = initial.clone();
        object(object(&mut changed).get_mut("runtime").unwrap()).insert(field.into(), actual.clone());
        assert!(Request::decode(&json::encode(&changed).unwrap()).is_err());
        object(object(&mut changed).get_mut("source").unwrap()).insert(field.into(), actual);
        assert!(Request::decode(&json::encode(&changed).unwrap()).is_ok());
    }
    let mut changed = initial;
    object(object(&mut changed).get_mut("runtime").unwrap())
        .insert("static_operations".into(), Value::Array(vec![]));
    assert!(Request::decode(&json::encode(&changed).unwrap()).is_err());
}

#[test]
fn body_cannot_masquerade_as_old_context_or_claim_an_effect_or_success() {
    for bad in [
        EMPTY.to_owned(),
        format!(r#"{{"subject":{{"kind":"function","evidence":7,"accepted":true}},"body":{EMPTY}}}"#),
        format!(r#"{{"subject":{{"kind":"pure","program":9,"effect":"unitary"}},"body":{EMPTY}}}"#),
        format!(r#"{{"subject":{{"kind":"scalar","program":9}},"body":{EMPTY}}}"#),
    ] {
        let mut changed = value();
        object(&mut changed).insert("bodies".into(), Value::Array(vec![json::parse(bad.as_bytes()).unwrap()]));
        assert!(Request::decode(&json::encode(&changed).unwrap()).is_err());
    }
}

#[test]
fn both_original_branch_contexts_are_required_without_a_condition_receipt() {
    let branch = format!(r#"{{"position":{{"offset":31,"start":0,"count":1}},"then":{EMPTY},"else":{EMPTY}}}"#);
    let mut changed = value();
    object(&mut changed).insert("branches".into(), Value::Array(vec![json::parse(branch.as_bytes()).unwrap()]));
    let decoded = Request::decode(&json::encode(&changed).unwrap()).unwrap();
    assert_eq!(decoded.context.branches.len(),1);
    for field in ["then", "else"] {
        let mut branch = json::parse(branch.as_bytes()).unwrap();
        object(&mut branch).remove(field);
        object(&mut changed).insert("branches".into(), Value::Array(vec![branch]));
        assert!(Request::decode(&json::encode(&changed).unwrap()).is_err());
    }
    let mut branch = json::parse(branch.as_bytes()).unwrap();
    object(&mut branch).insert("condition".into(), Value::Bool(false));
    object(&mut changed).insert("branches".into(), Value::Array(vec![branch]));
    assert!(Request::decode(&json::encode(&changed).unwrap()).is_err());
}

#[test]
fn arm_has_actual_programs_and_cannot_supply_a_duplicate_provider_table() {
    let interface = r#"{"inputs":[],"outputs":[],"public_effect":"unitary"}"#;
    let site = |arm: &str| json::parse(format!(r#"{{"attached":{interface},"required":{interface},
      "position":{{"offset":19,"start":0,"count":0}},"arms":[{arm}]}}"#).as_bytes()).unwrap();
    let mut changed = value();
    object(&mut changed).insert("sites".into(),Value::Array(vec![site(r#"{"implementation":3,"controlled":4}"#)]));
    let decoded = Request::decode(&json::encode(&changed).unwrap()).unwrap();
    assert_eq!(decoded.context.sites[0].arms[0].implementation,3);
    for arm in [r#"{"evidence":3,"controlled":4}"#,r#"{"implementation":3,"controlled":4,"providers":[]}"#] {
        object(&mut changed).insert("sites".into(),Value::Array(vec![site(arm)]));
        assert!(Request::decode(&json::encode(&changed).unwrap()).is_err());
    }
}
