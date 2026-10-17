//! Source judgments precede and do not grant native semantic evidence.
use super::*;

fn checked(source: &str) -> Result<()> {
    let module = crate::frontend::parser::parse_module(source).unwrap();
    program_with(
        BTreeMap::from([("main", &module)]),
        SourceLimits::selected(),
        |_, _, _, _, _, _, _| Ok(()),
    )
    .map(|_| ())
}

const PREP: &str = "use std::state::init0;
    isometry fn prepare(q:Q<Unit>)->Q<Bit>{finish(q);h(init0())}
    meaning Plus:Unit -> Bit=reference(prepare);";

#[test]
fn rectangular_meaning_source_keeps_both_ports_in_references_and_refinements() {
    checked(&format!(
        "{PREP}
        fn apply[const U:Op<Unit -> Bit,Plus>](q:Q<Unit>)->Q<Bit> requires Applicable(U){{U(q)}}
        isometry fn use_it(q:Q<Unit>)->Q<Bit>{{apply[checked_op(prepare,Plus)](q)}}"
    ))
    .unwrap();
    let wrong = format!(
        "{PREP}
        fn apply[const U:Op<Bit,Plus>](q:Q<Bit>)->Q<Bit> requires Applicable(U){{U(q)}}"
    );
    assert_eq!(checked(&wrong).unwrap_err().code, "type");
    // The existing endomorphic apply_contract API must match both Meaning
    // ports, including different trees with the same physical width.
    let wrong_contract = "
        unitary fn strip(q:Q<(Unit,Bit)>)->Q<Bit>{let(u,b)=split(q);finish(u);b}
        meaning Strip:(Unit,Bit) -> Bit=reference(strip);
        unitary fn id(q:Q<(Unit,Bit)>)->Q<(Unit,Bit)>{q}
        fn wrong(q:Q<(Unit,Bit)>)->Q<(Unit,Bit)>{apply_contract(id,Strip,q)}";
    assert_eq!(checked(wrong_contract).unwrap_err().code, "type");
    let syntax = crate::frontend::parser::parse_module(PREP).unwrap();
    let meaning = &syntax.decls[1];
    assert!(matches!(
        meaning.meaning_domain.as_ref().unwrap().kind,
        ast::TypeKind::Unit
    ));
    assert!(matches!(meaning.return_type.kind, ast::TypeKind::Bit));
}

#[test]
fn rectangular_meaning_composition_and_tensor_require_exact_ordered_trees() {
    let declarations = format!(
        "{PREP}
        fn id(q:Q<Bit>)->Q<Bit>{{q}}
        meaning I:Bit=reference(id);
        meaning C:Unit -> Bit=compose(Plus,I);
        meaning T:(Unit,Bit) -> (Bit,Bit)=tensor(Plus,I);"
    );
    checked(&declarations).unwrap();
    for wrong in [
        declarations.replace("compose(Plus,I)", "compose(I,Plus)"),
        declarations.replace("(Unit,Bit) -> (Bit,Bit)", "(Bit,Unit) -> (Bit,Bit)"),
        declarations.replace("Unit -> Bit=compose", "Bit -> Bit=compose"),
    ] {
        assert_eq!(checked(&wrong).unwrap_err().code, "type");
    }
}

#[test]
fn rectangular_meaning_does_not_hide_observation_or_grant_adjoint() {
    let observed = "use std::state::init0; 
        fn prepare(q:Q<Unit>)->Q<Bit>{finish(q);let _=measure_z(init0());init0()}
        meaning Bad:Unit -> Bit=reference(prepare);";
    assert_eq!(checked(observed).unwrap_err().code, "effect");
    let inverse = format!(
        "{PREP}
        fn invoke[const U:Op<Bit -> Unit>](q:Q<Bit>)->Q<Unit> requires Applicable(U){{U(q)}}
        fn reverse(q:Q<Bit>)->Q<Unit>{{invoke[adjoint(prepare)](q)}}"
    );
    assert!(checked(&inverse).is_err());
}
