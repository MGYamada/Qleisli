//! Literal QDV expectations independent of the v5 JSON encoder. All subjects
//! are untrusted data here; these controls grant no native/source acceptance.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::interchange::{execution_view, json};

fn write(body: impl FnOnce(&mut View<'_>) -> Result<()>) -> Vec<u8> {
    let dependencies = BTreeMap::new();
    let mut writer = Writer { bytes:b"QDV1".to_vec(), limit:MAX_BYTES, depth:0 };
    body(&mut View { writer:&mut writer, dependencies:&dependencies }).unwrap();
    writer.bytes
}

fn expected(text: &str) -> Vec<u8> {
    fn convert(value: &json::Value) -> execution_view::Value {
        match value {
            json::Value::String(value) => execution_view::Value::Text(value.clone()),
            json::Value::Number(value) => execution_view::Value::Natural(*value),
            json::Value::Array(values) => execution_view::Value::Array(values.iter().map(convert).collect()),
            _ => panic!("literal QDV test expects only records, strings and naturals"),
        }
    }
    execution_view::encode(&convert(&json::parse(text.as_bytes()).unwrap())).unwrap()
}

#[test]
fn equal_subject_indices_keep_both_original_occurrences_in_exact_order() {
    let mut value = data::Context::default();
    for offset in [101,202] {
        value.bodies.push(data::BodyRequest {
            subject:data::ProviderSubject::Function { evidence:7 },
            body:data::Context { positions:vec![data::Position { offset,start:0,count:0 }], ..Default::default() },
        });
    }
    let actual = write(|w| context(w,&value));
    assert_eq!(actual, expected(r#"["source-context",[],[],[],[],[
      ["source-body",["qmatch-function-provider",7],["source-context",[["source-interval",101,0,0]],[],[],[],[]]],
      ["source-body",["qmatch-function-provider",7],["source-context",[["source-interval",202,0,0]],[],[],[],[]]]]]"#));
    let mut swapped = value.clone();
    swapped.bodies.swap(0,1);
    assert_ne!(actual,write(|w| context(w,&swapped)));
    let mut missing = value.clone();
    missing.bodies.pop();
    assert_ne!(actual,write(|w| context(w,&missing)));
    value.bodies[0].subject = data::ProviderSubject::Pure { program:7 };
    assert_ne!(actual,write(|w| context(w,&value)));
}

#[test]
fn both_branch_paths_and_zero_count_call_positions_participate_in_view() {
    let mut value = data::Context::default();
    value.calls.push(data::Call {
        position:data::Position { offset:17,start:0,count:0 }, body:Default::default(),
    });
    value.branches.push(data::Branch {
        position:data::Position { offset:31,start:0,count:1 },
        then_body:Default::default(), else_body:Default::default(),
    });
    let actual = write(|w| context(w,&value));
    assert_eq!(actual,expected(r#"["source-context",[],[],[
      ["source-call",["source-interval",17,0,0],["source-context",[],[],[],[],[]]]],[
      ["source-branch",["source-interval",31,0,1],["source-context",[],[],[],[],[]],["source-context",[],[],[],[],[]]]],[]]"#));
    value.branches[0].else_body.positions.push(data::Position { offset:41,start:0,count:0 });
    assert_ne!(actual,write(|w| context(w,&value)));
    value.branches[0].else_body.positions.clear();
    value.calls[0].position.offset += 1;
    assert_ne!(actual,write(|w| context(w,&value)));
}

#[test]
fn source_actuals_and_original_meaning_selector_have_independent_literal_view() {
    let mut value = data::v5::Source {
        module:"m".into(), function:"f".into(),
        arguments:data::StaticArguments {
            bases:vec![("A".into(),vec![Atom::Unit])], naturals:vec![("unused".into(),17)],
            operations:vec![("U".into(),data::Description {
                nodes:vec![
                    data::OperationNode::Provider { module:"p".into(),function:"op".into(),bases:vec![],naturals:vec![("n".into(),3)],operations:vec![] },
                    data::OperationNode::Requested { child:0,module:"m".into(),function:"Meaning".into() },
                ], root:1,
            })],
        },
    };
    let actual = write(|w| source(w,&value));
    assert_eq!(actual,expected(r#"["source-function","m","f",[["source-static-basis","A",[["unit"]]]],
      [["source-static-natural","unused",17]],[["source-static-operation","U",["source-operation-description",[
      ["source-operation-provider","p","op",[],[["source-static-natural","n",3]],[]],
      ["source-operation-requested",0,"m","Meaning"]],1]]]]"#));
    value.arguments.bases[0].1 = vec![Atom::Bits(0)];
    assert_ne!(actual,write(|w| source(w,&value)));
    value.arguments.bases[0].1 = vec![Atom::Unit];
    value.arguments.naturals[0].1 += 1;
    assert_ne!(actual,write(|w| source(w,&value)));
}
