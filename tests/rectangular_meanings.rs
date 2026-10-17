//! Small ordinary-project regressions for general operation arrows.
mod common;
use common::SourceRoot;
use qleisli::contract::{DEFAULT_EXACT_WORK, exact::Budget};
use qleisli::frontend::compile::ParsedProgram;
use qleisli::frontend::compile::compile_project;
use qleisli::interchange::native::Kernel;
use qleisli::sim::{SimulationLimits, run_closed};

const PREP: &str = "use std::state::init0; use std::gate::x; use std::gate::z;
\x20\x20\x20\x20
    isometry fn prepare(q:Q<Unit>)->Q<Bit>{finish(q);h(init0())}
    meaning Plus:Unit -> Bit=reference(prepare);";

fn run(source: &str) -> std::collections::BTreeMap<Vec<bool>, f64> {
    let root = SourceRoot::new(source);
    let program = compile_project(&root.0).unwrap_or_else(|e| panic!("{e}\n{source}"));
    assert!(!program.source_pure_equations().is_empty());
    for equation in program.source_pure_equations() {
        assert!(
            equation
                .sources()
                .iter()
                .any(|(name, text)| name == "main" && text == source)
        );
        assert_eq!(
            equation.implementation().boundary().domain(),
            equation.specification().boundary().domain()
        );
        assert_eq!(
            equation.implementation().boundary().codomain(),
            equation.specification().boundary().codomain()
        );
        assert_eq!(
            equation.implementation().meaning(),
            equation.specification().meaning()
        );
        assert!(equation.names().0.starts_with("main::"));
    }
    let expected = run_closed(&program, SimulationLimits::default()).unwrap();
    let kernel = Kernel::selected().unwrap();
    let selected = ParsedProgram::parse(std::collections::BTreeMap::from([(
        "main".into(),
        source.into(),
    )]))
    .unwrap()
    .instantiate("main::main", Default::default(), Default::default())
    .unwrap()
    .elaborate()
    .unwrap()
    .check_function_contracts(&kernel, &mut Budget::new(DEFAULT_EXACT_WORK))
    .unwrap();
    let meanings = selected
        .check_operation_meanings(&kernel, &mut Budget::new(DEFAULT_EXACT_WORK))
        .unwrap();
    let raw = meanings
        .lower_raw(&kernel, &mut Budget::new(DEFAULT_EXACT_WORK))
        .unwrap();
    let accepted = kernel.accept(raw.proposal()).unwrap();
    raw.validate_source_steps(&accepted).unwrap();
    assert_eq!(
        run_closed(&accepted, SimulationLimits::default()).unwrap(),
        expected
    );
    expected
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn ordinary_project_preparation_with_and_without_meaning() {
    for refinement in ["", ",Plus"] {
        let provider = if refinement.is_empty() {
            "prepare"
        } else {
            "checked_op(prepare,Plus)"
        };
        let result = run(&format!("{PREP}
            fn invoke[const U:Op<Unit -> Bit{refinement}>](q:Q<Unit>)->Q<Bit> requires Applicable(U){{U(q)}}
            pub observe fn main()->Bit{{measure_z(invoke[{provider}](unit(())))}}"));
        for value in [false, true] {
            assert!((result[&vec![value]] - 0.5).abs() < 1e-12);
        }
    }
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn ordinary_project_composition_and_tensor_preserve_ordered_ports() {
    let result = run(&format!("{PREP}
        unitary fn flip(q:Q<Bit>)->Q<Bit>{{x(q)}}
        meaning X:Bit=reference(flip);
        meaning PX:Unit -> Bit=compose(Plus,X);
        meaning Both:(Unit,Bit) -> (Bit,Bit)=tensor(PX,X);
        isometry fn px(q:Q<Unit>)->Q<Bit>{{flip(prepare(q))}}
        fn invoke[const U:Op<(Unit,Bit) -> (Bit,Bit),Both>](q:Q<(Unit,Bit)>)->Q<(Bit,Bit)> requires Applicable(U){{U(q)}}
        pub observe fn main()->(Bit,Bit){{
            let (a,b)=split(invoke[tensor_op(checked_op(px,PX),checked_op(flip,X))](join(unit(()),init0())));
            (measure_z(a),measure_z(b))
        }}"));
    for low in [false, true] {
        assert!((result[&vec![low, true]] - 0.5).abs() < 1e-12);
    }
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn rectangular_composition_preserves_an_entangled_caller() {
    let result = run(&format!("{PREP}
        use std::gate::cnot;
        isometry fn duplicate(q:Q<Bit>)->Q<(Bit,Bit)>{{let(a,b)=cnot(q,init0());join(a,b)}}
        meaning Copy:Bit -> (Bit,Bit)=reference(duplicate);
        unitary fn ident(q:Q<(Bit,Bit)>)->Q<(Bit,Bit)>{{q}}
        fn invoke[const U:Op<Bit -> (Bit,Bit),Copy>](q:Q<Bit>)->Q<(Bit,Bit)> requires Applicable(U){{U(q)}}
        pub observe fn main()->(Bit,Bit,Bit){{
            let(a,r)=cnot(h(init0()),init0());
            let(a,b)=split(invoke[then_op(checked_op(duplicate,Copy),ident)](a));
            (measure_z(a),measure_z(b),measure_z(r))
        }}"));
    for value in [false, true] {
        assert!((result[&vec![value, value, value]] - 0.5).abs() < 1e-12);
    }
    assert!(
        result
            .iter()
            .filter(|(_, p)| **p > 1e-12)
            .all(|(bits, _)| bits.iter().all(|b| *b == bits[0]))
    );
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn ordinary_project_equal_width_distinct_trees_and_inverse() {
    let result = run(&format!("{PREP}
        unitary fn strip(q:Q<(Unit,Bit)>)->Q<Bit>{{let(u,b)=split(q);finish(u);b}}
        meaning Strip:(Unit,Bit) -> Bit=reference(strip);
        fn invoke[const U:Op<(Unit,Bit) -> Bit,Strip>](q:Q<(Unit,Bit)>)->Q<Bit> requires Applicable(U){{U(q)}}
        pub observe fn main()->Bit{{
            let b=invoke[checked_op(strip,Strip)](join(unit(()),x(init0())));
            let(u,b)=split(adjoint(strip)(b));finish(u);measure_z(b)
        }}"));
    assert!((result[&vec![true]] - 1.0).abs() < 1e-12);
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn ordinary_rectangular_basis_lift_binds_every_input_column() {
    // The selected Raw basis-expression profile remains separate (#250).
    // Exercise the ordinary adapter's matrix proposal against the native body.
    let source = format!("{PREP}
        isometry fn duplicate(q:Q<Bit>)->Q<(Bit,Bit)>{{basis q as b {{(b,b)}}}}
        meaning Copy:Bit -> (Bit,Bit)=reference(duplicate);
        fn invoke[const U:Op<Bit -> (Bit,Bit),Copy>](q:Q<Bit>)->Q<(Bit,Bit)> requires Applicable(U){{U(q)}}
        pub observe fn main()->(Bit,Bit){{
            let(a,b)=split(invoke[checked_op(duplicate,Copy)](h(init0())));
            (measure_z(a),measure_z(b))
        }}");
    let root = SourceRoot::new(&source);
    let accepted = compile_project(&root.0).unwrap();
    let equation = &accepted.source_pure_equations()[0];
    let matrix = equation.implementation().meaning();
    assert_eq!((matrix.rows(), matrix.cols()), (4, 2));
    for row in 0..4 {
        for col in 0..2 {
            let expected = if row == 3 * col {
                qleisli::contract::exact::Exact::one()
            } else {
                qleisli::contract::exact::Exact::zero()
            };
            assert_eq!(matrix.get(row, col), Some(expected));
        }
    }
    let distribution = run_closed(&accepted, SimulationLimits::default()).unwrap();
    assert!((distribution[&vec![false, false]] - 0.5).abs() < 1e-12);
    assert!((distribution[&vec![true, true]] - 0.5).abs() < 1e-12);
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn rectangular_reference_rejects_phase_observation_and_missing_inverse() {
    for extra in [
        "isometry fn wrong(q:Q<Unit>)->Q<Bit>{z(prepare(q))}
         pub observe fn main()->Bit{measure_z(invoke[checked_op(wrong,Plus)](unit(())))}",
        "fn wrong(q:Q<Unit>)->Q<Bit>{let _=measure_z(init0());prepare(q)}
         pub observe fn main()->Bit{measure_z(invoke[checked_op(wrong,Plus)](unit(())))}",
        "fn reverse(q:Q<Bit>)->Q<Unit>{adjoint(prepare)(q)} pub observe fn main()->Bit{measure_z(init0())}",
        "fn repeat(q:Q<Unit>)->Q<Bit>{power(prepare,0)(q)} pub observe fn main()->Bit{measure_z(init0())}",
        "fn control(c:Q<Bit>,q:Q<Unit>)->(Q<Bit>,Q<Bit>){controlled(prepare)(c,q)} pub observe fn main()->Bit{measure_z(init0())}",
    ] {
        let source = format!("{PREP}
            fn invoke[const U:Op<Unit -> Bit,Plus>](q:Q<Unit>)->Q<Bit> requires Applicable(U){{U(q)}} {extra}");
        let root = SourceRoot::new(&source);
        assert!(compile_project(&root.0).is_err(), "{source}");
        let kernel = Kernel::selected().unwrap();
        let selected = ParsedProgram::parse(std::collections::BTreeMap::from([(
            "main".into(),
            source.clone(),
        )]))
        .and_then(|program| {
            program.instantiate("main::main", Default::default(), Default::default())
        })
        .and_then(|instance| instance.elaborate())
        .and_then(|program| {
            program.check_function_contracts(&kernel, &mut Budget::new(DEFAULT_EXACT_WORK))
        })
        .and_then(|program| {
            program
                .check_operation_meanings(&kernel, &mut Budget::new(DEFAULT_EXACT_WORK))
                .map(|_| ())
        });
        assert!(selected.is_err(), "selected Raw accepted {source}");
    }
}
