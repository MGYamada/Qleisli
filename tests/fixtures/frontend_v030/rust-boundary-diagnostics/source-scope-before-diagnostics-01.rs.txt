//! External regressions for block-scope projection, not a proof of the compiler.

mod common;

use std::collections::BTreeMap;

use common::SourceRoot;
use qleisli::frontend::compile::{ErrorCode, check_project, compile_project};
use qleisli::sim::{SimulationLimits, run_closed};

const IMPORTS: &str = "
use std::quantum::init0; use std::quantum::h; use std::quantum::x;
use std::quantum::z; use std::quantum::cnot; use std::quantum::split;
use std::observe::measure_z; use std::observe::discard;
";

fn assert_distribution(source: &str, expected: BTreeMap<Vec<bool>, f64>) {
    let root = SourceRoot::new(source);
    let program = compile_project(&root.0).unwrap_or_else(|error| panic!("{source}\n{error}"));
    let actual = run_closed(&program, SimulationLimits::default()).unwrap();
    assert!((actual.values().sum::<f64>() - 1.0).abs() < 1e-12);
    for output in actual.keys().chain(expected.keys()) {
        let actual_weight = actual.get(output).copied().unwrap_or(0.0);
        let expected_weight = expected.get(output).copied().unwrap_or(0.0);
        assert!(
            (actual_weight - expected_weight).abs() < 1e-12,
            "{source}\n{output:?}: {actual_weight}, expected {expected_weight}"
        );
    }
}

#[test]
fn nested_projection_restores_classical_entries_and_preserves_mixed_pending_ownership() {
    for flag in [false, true] {
        let flag_literal = u8::from(flag);
        let source = format!(
            "{IMPORTS}
unitary fn relay(flag: Bit, payload: (Bit,(Q<Unit>,Q<Bit>)))
    -> (Bit,(Bit,(Bit,(Q<Unit>,Q<Bit>)))) {{
    if flag {{ let flag=0; () }} else {{ let flag=1; () }};
    let result = if flag {{
        let flag=not flag;
        let payload=if flag {{ let carry=payload; let payload=carry; payload }}
                    else {{ let carry=payload; let payload=carry; payload }};
        let (tag,(u,q))=payload;
        (flag,(tag,(u,z(q))))
    }} else {{
        let flag=not flag;
        let payload=if flag {{ let carry=payload; let payload=carry; payload }}
                    else {{ let carry=payload; let payload=carry; payload }};
        let (tag,(u,q))=payload;
        (flag,(tag,(u,q)))
    }};
    (flag,result)
}}
observe fn read(held: Q<Bit>, result: (Bit,(Bit,(Bit,(Q<Unit>,Q<Bit>)))))
    -> ((Bit,Bit),(Bit,(Bit,Bit))) {{
    let (outer,(inner,(tag,(u,q))))=result;
    discard(u);
    ((outer,inner),(tag,(measure_z(h(held)),measure_z(h(q)))))
}}
observe fn main() -> ((Bit,Bit),(Bit,(Bit,Bit))) {{
    let (q,r)=cnot(h(init0()),init0());
    let (u,q)=split(basis q as b {{ ((),b) }});
    let flag={flag_literal};
    read(r,relay(flag,(1,(u,q))))
}}"
        );
        // The first branch leaves the entry mixed owner untouched. Later
        // move-back bindings have fresh lexical identities, even when their
        // values/slots are unchanged, and escape only through the result.
        // The outer flag is restored; the separately returned inner flag is
        // its complement. r is already pending while relay evaluates.
        // Z^flag on one Bell half gives X-read parity flag, without an inverse
        // circuit or compiler-generated expectation as the oracle.
        let expected = [false, true]
            .into_iter()
            .map(|x| (vec![flag, !flag, true, x, x ^ flag], 0.5))
            .collect();
        assert_distribution(&source, expected);
    }
}

#[test]
fn equal_value_rebinding_cannot_hide_a_local_leak_or_revive_an_outer_owner() {
    for ty in ["Q<Unit>", "(Bit,(Q<Unit>,Q<Bit>))"] {
        let block = "{ let carry=v; let v=carry; () }";
        let source = format!(
            "unitary fn bad(flag: Bit, v: {ty}) -> {ty} {{
    if flag {block} else {{ () }};
    v
}}"
        );
        let root = SourceRoot::new(&source);
        let error = check_project(&root.0).unwrap_err();
        assert_eq!(error.code, ErrorCode::Ownership, "{source}\n{error}");
        assert_eq!(
            error.message,
            "local quantum ownership `v` escapes neither through the result nor an explicit discard"
        );
        let binding_start = source.find("let v=carry").unwrap() + "let ".len();
        assert_eq!(error.span.start, binding_start);
        assert_eq!(error.span.end, binding_start + 1);
        assert_eq!(&source[error.span.start..error.span.end], "v");
        // No operation or phi intervenes between the entry value and the
        // final local v here: equality of spelling, type, slot, and Value
        // cannot substitute for the identity of the original binding.

        let arm = "{
        let result=if flag { let carry=v; let v=1; carry }
                       else { let carry=v; let v=0; carry };
        let v=();
        result
    }";
        let source = format!(
            "unitary fn bad(flag: Bit, v: {ty}) -> ({ty},{ty}) {{
    let result=if flag {arm} else {arm};
    (result,v)
}}"
        );
        let root = SourceRoot::new(&source);
        let error = check_project(&root.0).unwrap_err();
        assert_eq!(error.code, ErrorCode::Ownership, "{source}\n{error}");
        assert_eq!(
            error.message,
            "quantum ownership `v` has already been consumed"
        );
        let use_position = source.rfind("(result,v)").unwrap() + "(result,".len();
        assert_eq!(
            (error.span.start, error.span.end),
            (use_position, use_position + 1)
        );
        // The inner/outer classical v shadows expire. Neither can resurrect
        // the old linear v, whose ownership is already held by result.
    }
}

#[test]
fn local_spent_names_expire_but_entry_spent_names_still_hide_functions() {
    let move_through_local = "
    let q=if flag {
        let flip=q;
        let moved=if flag { let flip=flip; flip } else { flip };
        moved
    } else {
        let flip=q; let moved=flip; moved
    };";
    for (call, expected_bit, diagnostic) in [
        ("flip(q)", true, "a local value is not callable"),
        (
            "adjoint(flip,q)",
            true,
            "static operation requires a function name, not a local value",
        ),
        (
            "repeat_static(0,flip,q)",
            false,
            "static operation requires a function name, not a local value",
        ),
    ] {
        // A new branch-local flip is spent before the branch exits, and its
        // tombstone must disappear so the declaration becomes visible again.
        for flag in [false, true] {
            let flag_literal = u8::from(flag);
            let source = format!(
                "{IMPORTS}
unitary fn flip(q: Q<Bit>) -> Q<Bit> {{ x(q) }}
unitary fn accepted(flag: Bit, q: Q<Bit>) -> Q<Bit> {{
    {move_through_local}
    {call}
}}
observe fn main() -> Bit {{ measure_z(accepted({flag_literal},init0())) }}"
            );
            assert_distribution(&source, BTreeMap::from([(vec![expected_bit], 1.0)]));
        }

        // Here flip existed on entry and was moved before the same nested
        // scopes. Rebinding that spelling to a different quantum value inside
        // them must leave the original spent marker at the outer boundary.
        let source = format!(
            "{IMPORTS}
unitary fn flip(q: Q<Bit>) -> Q<Bit> {{ x(q) }}
unitary fn rejected(flag: Bit, flip: Q<Unit>, q: Q<Bit>) -> (Q<Unit>,Q<Bit>) {{
    let held=flip;
    {move_through_local}
    (held,{call})
}}"
        );
        let root = SourceRoot::new(&source);
        let error = check_project(&root.0).unwrap_err();
        assert_eq!(error.code, ErrorCode::TypeMismatch, "{source}\n{error}");
        assert_eq!(error.message, diagnostic);
        let call_position = source.rfind(call).unwrap();
        let name_position = call_position + call.find("flip").unwrap();
        assert_eq!(
            (error.span.start, error.span.end),
            (name_position, name_position + 4)
        );
    }
}
