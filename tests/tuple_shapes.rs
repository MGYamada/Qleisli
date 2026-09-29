//! Tuple arity is semantic metadata, never inferred from bit width.
mod common;
use common::SourceRoot;
use qleisli::contract::{BasisType, Circuit};
use qleisli::frontend::compile::{ErrorCode, check_project, compile_project};
use qleisli::interchange::{self, Version};
use qleisli::sim::{SimulationLimits, run_closed};

fn reject(source: &str, code: ErrorCode) {
    let source = format!("{source}\nobserve fn main() -> Unit {{ () }}");
    let root = SourceRoot::new(&source);
    let error = check_project(&root.0).unwrap_err();
    assert_eq!(error.code, code, "{source}: {error}");
}

#[test]
fn formerly_silent_reassociation_now_rejects() {
    let source = include_str!("fixtures/tuple_shapes/first_source/main.qli");
    let root = SourceRoot::new(source);
    let error = check_project(&root.0).unwrap_err();
    assert_eq!(error.code, ErrorCode::TypeMismatch);
    assert!(error.message.contains("expected `((Bit,Bit),Bit)`"));
    assert!(error.message.contains("found `(Bit,Bit,Bit)`"));
    for source in [
        "basis fn f((a,b,c): ((Bit,Bit),Bit)) -> Bit { a }",
        "basis fn f(((a,b),c): (Bit,Bit,Bit)) -> Bit { a }",
        "basis fn f(x:Bit) -> (Bit,Bit,Bit) { ((x,x),x) }",
        "unitary fn f() -> ((CBit,CBit),CBit) { (true,false,true) }",
        "unitary fn f() -> (CBit,CBit,CBit) { ((true,false),true) }",
        "unitary fn f(x:(CBit,CBit,CBit)) -> CBit { let ((a,b),c)=x; a }",
        "unitary fn f(x:((CBit,CBit),CBit)) -> CBit { let (a,b,c)=x; c }",
        "unitary fn f(c:CBit) -> (CBit,CBit,CBit) { if c { (c,c,c) } else { ((c,c),c) } }",
    ] {
        reject(source, ErrorCode::TypeMismatch);
    }
}

#[test]
fn explicit_layout_is_exact_and_preserves_an_entangled_reference() {
    let root = SourceRoot::new(include_str!("fixtures/tuple_shapes/explicit_layout.qli"));
    let program = compile_project(&root.0).unwrap();
    let result = run_closed(&program, SimulationLimits::default()).unwrap();
    assert!((result[&vec![false, false, true, false]] - 1.0).abs() < 1e-12);
    assert!((result.values().sum::<f64>() - 1.0).abs() < 1e-12);
    // Reconstruct the source-generated n-ary function evidence from both formats.
    for version in [Version::V1, Version::V2] {
        let bytes = interchange::export(&program, None, version).unwrap();
        let imported = interchange::import(&bytes, None).unwrap();
        assert_eq!(
            run_closed(&imported.program, SimulationLimits::default()).unwrap(),
            result
        );
    }
}

#[test]
fn same_shape_wrong_permutation_does_not_pass_identity_evidence() {
    let root = SourceRoot::new(include_str!("fixtures/tuple_shapes/wrong_permutation.qli"));
    let error = check_project(&root.0).unwrap_err();
    assert_eq!(error.code, ErrorCode::InvalidIr);
    assert!(error.message.contains("exact"), "{error}");
}

#[test]
fn nary_static_meanings_retain_shape_and_order() {
    let prefix = "basis fn id((a,b,c):(Bit,Bit,Bit))->(Bit,Bit,Bit){(a,b,c)}
        meaning Id: (Bit,Bit,Bit) = permutation_by(id);
        unitary fn apply[static U:Op<(Bit,Bit,Bit),Id>](q:Q<(Bit,Bit,Bit)>)->Q<(Bit,Bit,Bit)>
        requires Apply(U) { U(q) }
        unitary fn identity(q:Q<(Bit,Bit,Bit)>)->Q<(Bit,Bit,Bit)>{q}
        unitary fn client(q:Q<(Bit,Bit,Bit)>)->Q<(Bit,Bit,Bit)>{apply[bind_op(identity,Id)](q)}";
    let root = SourceRoot::new(&format!("{prefix} observe fn main()->Unit {{()}}"));
    check_project(&root.0).unwrap();
    reject(
        &prefix.replace(
            "unitary fn identity(q:Q<(Bit,Bit,Bit)>)->Q<(Bit,Bit,Bit)>{q}",
            "unitary fn identity(q:Q<((Bit,Bit),Bit)>)->Q<((Bit,Bit),Bit)>{q}",
        ),
        ErrorCode::TypeMismatch,
    );
    reject(
        &prefix.replace("{q}", "{do (a,b,c) <- q; pure (c,b,a)}"),
        ErrorCode::Contract,
    );
}

#[test]
fn nary_owners_include_units_pending_fields_and_branch_frames() {
    let root = SourceRoot::new(
        "unitary fn f(q:Q<Unit>,c:CBit)->(Q<Unit>,CBit,Unit) {
        let t = if c { (q,c,()) } else { (q,not c,()) }; t
    } observe fn main()->(CBit,CBit,CBit) {
        let t=(true,false,true); let (a,b,c)=t; let (d,e,f)=t;
        (a xor d,b xor e,c xor f)
    }",
    );
    let program = compile_project(&root.0).unwrap();
    assert_eq!(
        run_closed(&program, SimulationLimits::default()).unwrap()[&vec![false, false, false]],
        1.0
    );
    reject(
        "unitary fn f(q:Q<Unit>)->(Q<Unit>,Q<Unit>,Unit){(q,q,())}",
        ErrorCode::Ownership,
    );
    reject(
        "unitary fn f(q:Q<Unit>)->Unit {let (_,a,b)=(q,(),());()}",
        ErrorCode::Ownership,
    );
    let root = SourceRoot::new(
        "use std::quantum::init0; use std::quantum::x;
        use std::observe::measure_z;
        observe fn main()->(CBit,CBit,CBit){
            let c=measure_z(init0());
            let (a,b,d)=(x(init0()),if c {init0()} else {x(init0())},init0());
            (measure_z(a),measure_z(b),measure_z(d))
        }",
    );
    let ir = compile_project(&root.0).unwrap();
    assert_eq!(
        run_closed(&ir, SimulationLimits::default()).unwrap()[&vec![true, true, false]],
        1.0
    );
}

#[test]
fn nary_type_capacity_and_rejected_deep_drops_are_bounded() {
    for fields in [vec![], vec![BasisType::Bit], vec![BasisType::Bit; 2]] {
        assert!(Circuit::new(BasisType::Tuple(fields), vec![]).is_err());
    }
    let flat = BasisType::Tuple(vec![BasisType::Bit; 3]);
    let nested = BasisType::pair(
        BasisType::pair(BasisType::Bit, BasisType::Bit),
        BasisType::Bit,
    );
    assert_eq!(flat.bits(), nested.bits());
    assert_ne!(flat, nested);
    std::thread::Builder::new()
        .stack_size(256 * 1024)
        .spawn(|| {
            let mut tree = BasisType::Unit;
            for _ in 0..10_000 {
                tree = BasisType::Tuple(vec![tree, BasisType::Unit, BasisType::Unit]);
            }
            assert!(tree.bits().is_err());
            drop(tree);
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn flat_arity_and_nested_depth_have_distinct_bounds() {
    use qleisli::frontend::parser::parse_module;
    for count in [64, 65] {
        let source = format!(
            "unitary fn f()->({}){{({})}} observe fn main()->Unit{{()}}",
            vec!["Unit"; count].join(","),
            vec!["()"; count].join(",")
        );
        if count == 64 {
            check_project(&SourceRoot::new(&source).0).unwrap();
        } else {
            let error = parse_module(&source).unwrap_err();
            assert!(error.message.contains("64-field"));
        }
    }
    let mut ty = "Bit".to_owned();
    for _ in 0..65 {
        ty = format!("(Unit,Unit,{ty})");
    }
    assert!(
        parse_module(&format!("basis fn f(x:{ty})->Bit{{0}}"))
            .unwrap_err()
            .message
            .contains("limit")
    );
}

#[test]
fn documented_type_categories_and_explicit_only_conversions() {
    for source in [
        "unitary fn f(x:Bit)->Unit{()}",
        "unitary fn f(x:Q<CBit>)->Q<CBit>{x}",
        "unitary fn f(x:Q<Q<Bit>>)->Q<Q<Bit>>{x}",
        "basis fn f(x:CBit)->CBit{x}",
        "unitary fn f(x:Q<(Bit,Bit)>)->(Q<Bit>,Q<Bit>){x}",
        "unitary fn f(x:Q<Unit>)->Unit{x}",
        "unitary fn f(x:(Unit,CBit))->CBit{x}",
        "unitary fn f(x:Bits<3>)->Unit{()}",
        "unitary fn f(x:CBits<3>)->Unit{()}",
    ] {
        let root = SourceRoot::new(&format!("{source} observe fn main()->Unit{{()}}"));
        assert!(check_project(&root.0).is_err(), "{source}");
    }
    let root = SourceRoot::new(
        "basis fn id((a,b,c):(Unit,Bit,Unit))->(Unit,Bit,Unit){(a,b,c)}
        unitary fn f(q:Q<(Unit,Unit,Unit)>)->Q<(Unit,Unit,Unit)>{q}
        observe fn main()->(Unit,CBit,Unit){((),true,())}",
    );
    let ir = compile_project(&root.0).unwrap();
    assert_eq!(
        run_closed(&ir, SimulationLimits::default()).unwrap()[&vec![true]],
        1.0
    );
}
