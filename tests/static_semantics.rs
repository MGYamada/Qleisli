//! Exact finite operator checks, including global phase, not a general proof.

mod common;

use std::ops::{Add, Mul, Neg};

use common::SourceRoot;
use qleisli::frontend::compile::compile_project;
use qleisli::ir::{CircuitAction, CircuitStep, RawOp};

// Z[zeta, 1/2], where zeta = exp(i*pi/4) and zeta^4 = -1.
// Normalization makes equality exact; checked arithmetic fails on overflow.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Exact {
    coefficients: [i128; 4],
    denominator_power: u32,
}

impl Exact {
    const ZERO: Self = Self {
        coefficients: [0; 4],
        denominator_power: 0,
    };
    const ONE: Self = Self {
        coefficients: [1, 0, 0, 0],
        denominator_power: 0,
    };

    fn new(mut coefficients: [i128; 4], mut denominator_power: u32) -> Self {
        while denominator_power > 0 && coefficients.iter().all(|x| x % 2 == 0) {
            coefficients = coefficients.map(|x| x / 2);
            denominator_power -= 1;
        }
        Self {
            coefficients,
            denominator_power,
        }
    }

    fn phase(exponent: usize) -> Self {
        let exponent = exponent % 8;
        let mut coefficients = [0; 4];
        coefficients[exponent % 4] = if exponent < 4 { 1 } else { -1 };
        Self::new(coefficients, 0)
    }

    fn inverse_sqrt_two() -> Self {
        Self::new([0, 1, 0, -1], 1)
    }
}

impl Add for Exact {
    type Output = Self;

    fn add(self, rhs: Self) -> Self {
        let power = self.denominator_power.max(rhs.denominator_power);
        let left_scale = 2_i128.checked_pow(power - self.denominator_power).unwrap();
        let right_scale = 2_i128.checked_pow(power - rhs.denominator_power).unwrap();
        Self::new(
            std::array::from_fn(|i| {
                self.coefficients[i]
                    .checked_mul(left_scale)
                    .unwrap()
                    .checked_add(rhs.coefficients[i].checked_mul(right_scale).unwrap())
                    .unwrap()
            }),
            power,
        )
    }
}

impl Neg for Exact {
    type Output = Self;

    fn neg(self) -> Self {
        Self::new(
            self.coefficients.map(|x| x.checked_neg().unwrap()),
            self.denominator_power,
        )
    }
}

impl Mul for Exact {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self {
        let mut coefficients = [0_i128; 4];
        for (i, left) in self.coefficients.into_iter().enumerate() {
            for (j, right) in rhs.coefficients.into_iter().enumerate() {
                let product = left.checked_mul(right).unwrap();
                let product = if i + j >= 4 {
                    product.checked_neg().unwrap()
                } else {
                    product
                };
                coefficients[(i + j) % 4] = coefficients[(i + j) % 4].checked_add(product).unwrap();
            }
        }
        Self::new(
            coefficients,
            self.denominator_power
                .checked_add(rhs.denominator_power)
                .unwrap(),
        )
    }
}

const IMPORTS: &str = "
use std::quantum::init0; use std::quantum::h; use std::quantum::x;
use std::quantum::z; use std::quantum::t; use std::quantum::cnot;
use std::quantum::join; use std::quantum::split; use std::observe::discard;
";

fn compiled_steps(definitions: &str, preparation: &str, operation: &str) -> Vec<CircuitStep> {
    let root = SourceRoot::new(&format!(
        "{IMPORTS}\n{definitions}\nobserve fn main() -> Unit {{
            {preparation} let result = {operation}; discard(result); ()
        }}"
    ));
    let verified = compile_project(&root.0).unwrap();
    let mut circuits = verified
        .program()
        .operations
        .iter()
        .filter_map(|op| match op {
            RawOp::ApplyUnitary { steps, .. } => Some(steps.clone()),
            _ => None,
        });
    let steps = circuits.next().expect("one outer static operation");
    assert!(
        circuits.next().is_none(),
        "nested operations must be flattened"
    );
    steps
}

// Execute the specified circuit action on each basis column, independently of
// the production simulator and compiler's inversion/remapping helpers. Axis 0
// is the least significant bit, matching the finite IR's ordered basis.
fn assert_operator(width: usize, steps: &[CircuitStep], expected: impl Fn(usize, usize) -> Exact) {
    assert!(
        width <= 3,
        "this exact checker intentionally covers small examples"
    );
    let dimension = 1 << width;
    for column in 0..dimension {
        let mut amplitudes = vec![Exact::ZERO; dimension];
        amplitudes[column] = Exact::ONE;
        for step in steps {
            let mut next = vec![Exact::ZERO; dimension];
            for (basis, amplitude) in amplitudes.into_iter().enumerate() {
                if !step
                    .controls
                    .iter()
                    .all(|control| ((basis >> control.index) & 1 != 0) == control.when_one)
                {
                    next[basis] = next[basis] + amplitude;
                    continue;
                }
                match &step.action {
                    CircuitAction::Contract { .. } => {
                        panic!(
                            "function evidence is covered by the dedicated function contract suite"
                        )
                    }
                    CircuitAction::Hadamard { target } => {
                        let mask = 1 << target;
                        let zero = basis & !mask;
                        let scaled = amplitude * Exact::inverse_sqrt_two();
                        next[zero] = next[zero] + scaled;
                        next[zero | mask] =
                            next[zero | mask] + if basis & mask == 0 { scaled } else { -scaled };
                    }
                    CircuitAction::Monomial {
                        indices,
                        permutation,
                        phases,
                    } => {
                        let label = indices.iter().enumerate().fold(0, |label, (place, axis)| {
                            label | (((basis >> axis) & 1) << place)
                        });
                        let output =
                            indices
                                .iter()
                                .enumerate()
                                .fold(basis, |output, (place, axis)| {
                                    (output & !(1 << axis))
                                        | (((usize::from(permutation[label]) >> place) & 1) << axis)
                                });
                        next[output] =
                            next[output] + amplitude * Exact::phase(usize::from(phases[label]));
                    }
                }
            }
            amplitudes = next;
        }
        for (row, amplitude) in amplitudes.into_iter().enumerate() {
            assert_eq!(
                amplitude,
                expected(row, column),
                "matrix entry ({row}, {column})"
            );
        }
    }
}

#[test]
fn exact_scalar_arithmetic_matches_cyclotomic_and_hadamard_identities() {
    assert_eq!(Exact::phase(1) * Exact::phase(3), -Exact::ONE);
    assert_eq!(Exact::phase(1) * Exact::phase(7), Exact::ONE);
    let half = Exact::new([1, 0, 0, 0], 1);
    assert_eq!(Exact::inverse_sqrt_two() * Exact::inverse_sqrt_two(), half);
    assert_eq!(half + half, Exact::ONE);
    assert_eq!(half + -half, Exact::ZERO);
    for i in 0..8 {
        for j in 0..8 {
            assert_eq!(Exact::phase(i) * Exact::phase(j), Exact::phase(i + j));
        }
    }
}

const MIX: &str = "
unitary fn mix(q: Q<(Bit,Bit)>) -> Q<(Bit,Bit)> {
    let (a,b) = split(q);
    let a = t(h(a));
    let b = basis b as label { not label };
    let (a,b) = cnot(a,b);
    join(b,a)
}
";

#[test]
fn adjoint_and_nested_axis_remapping_match_all_exact_matrix_entries() {
    // U|a,b> = sum_r (-1)^(a*r) zeta^r |b xor 1 xor r,r>/sqrt(2).
    let preparation = "let q = join(init0(),init0());";
    let forward = compiled_steps(MIX, preparation, "repeat_static(1,mix,q)");
    assert_operator(2, &forward, |row, column| {
        let (a, b, r) = (column & 1, column >> 1, row >> 1);
        if row & 1 == b ^ 1 ^ r {
            Exact::inverse_sqrt_two() * Exact::phase(r + 4 * a * r)
        } else {
            Exact::ZERO
        }
    });
    // U^dagger|c,d> = sum_a (-1)^(a*d) zeta^(-d)|a,c xor 1 xor d>/sqrt(2).
    let backward = compiled_steps(MIX, preparation, "adjoint(mix,q)");
    assert_operator(2, &backward, |row, column| {
        let (c, d, a, b) = (column & 1, column >> 1, row & 1, row >> 1);
        if b == c ^ 1 ^ d {
            Exact::inverse_sqrt_two() * Exact::phase(8 - d + 4 * a * d)
        } else {
            Exact::ZERO
        }
    });
    let nested = format!(
        "{MIX}
unitary fn nested(q: Q<((Bit,Bit),Bit)>) -> Q<((Bit,Bit),Bit)> {{
    let (ab,c) = split(q); let (a,b) = split(ab);
    let (c,a) = split(repeat_static(1,mix,join(c,a)));
    join(join(b,c),a)
}}"
    );
    let steps = compiled_steps(
        &nested,
        "let q = join(join(init0(),init0()),init0());",
        "repeat_static(1,nested,q)",
    );
    // Apply U to the ordered, nonadjacent pair (c,a), then return (b,c',a').
    assert_operator(3, &steps, |row, column| {
        let (a, b, c, r) = (column & 1, (column >> 1) & 1, column >> 2, row >> 2);
        if row & 1 == b && (row >> 1) & 1 == a ^ 1 ^ r {
            Exact::inverse_sqrt_two() * Exact::phase(r + 4 * c * r)
        } else {
            Exact::ZERO
        }
    });
}

#[test]
fn finite_repetition_preserves_the_phase_of_a_noncommuting_operator() {
    // V = T X, so V|b> = zeta^(1-b)|1-b> and V^2 = zeta I.
    let definitions = "unitary fn forward(q: Q<Bit>) -> Q<Bit> { t(x(q)) }";
    for count in [0, 1, 2, 3, 8] {
        let steps = compiled_steps(
            definitions,
            "let q = init0();",
            &format!("repeat_static({count},forward,q)"),
        );
        assert_operator(1, &steps, |row, column| {
            if row == column ^ (count % 2) {
                Exact::phase(count / 2 + (count % 2) * (1 - column))
            } else {
                Exact::ZERO
            }
        });
    }
}

#[test]
fn nested_qif_preserves_zero_one_controls_and_branch_phases() {
    let definitions = "
unitary fn forward(q: Q<Bit>) -> Q<Bit> { t(x(q)) }
unitary fn backward(q: Q<Bit>) -> Q<Bit> { adjoint(forward,q) }
unitary fn first(q: Q<(Bit,Bit)>) -> Q<(Bit,Bit)> {
    let (b,c) = split(q); let (b,c) = qif(b,c) { 0 => forward, 1 => backward }; join(b,c)
}
unitary fn second(q: Q<(Bit,Bit)>) -> Q<(Bit,Bit)> {
    let (b,c) = split(q); let (b,c) = qif(b,c) { 0 => z, 1 => t }; join(b,c)
}
unitary fn nested(q: Q<(Bit,(Bit,Bit))>) -> Q<(Bit,(Bit,Bit))> {
    let (a,bc) = split(q); let (a,bc) = qif(a,bc) { 0 => first, 1 => second }; join(a,bc)
}";
    let steps = compiled_steps(
        definitions,
        "let q = join(init0(),join(init0(),init0()));",
        "repeat_static(1,nested,q)",
    );
    assert_operator(3, &steps, |row, column| {
        let (a, b, c) = (column & 1, (column >> 1) & 1, column >> 2);
        let (output, phase) = match (a, b) {
            (0, 0) => (column ^ 4, 1 - c), // V on c.
            (0, 1) => (column ^ 4, 8 - c), // V^dagger on c.
            (1, 0) => (column, 4 * c),     // Z on c.
            (1, 1) => (column, c),         // T on c.
            _ => unreachable!(),
        };
        if row == output {
            Exact::phase(phase)
        } else {
            Exact::ZERO
        }
    });
}

#[test]
fn computed_scalar_phase_is_retained_on_unit_and_under_adjoint_and_control() {
    let definitions = "
classical fn yes(value: Unit) -> Bit { 1 }
unitary fn identity(q: Q<Unit>) -> Q<Unit> { q }
unitary fn phase(q: Q<Unit>) -> Q<Unit> { with_computed(q,yes) { |a| z(t(t(t(a)))) } }
unitary fn controlled(q: Q<(Bit,Unit)>) -> Q<(Bit,Unit)> {
    let (c,u) = split(q); let (c,u) = qif(c,u) { 0 => phase, 1 => identity }; join(c,u)
}";
    let preparation =
        "let pair = basis init0() as b { ((),b) }; let (u,b) = split(pair); discard(b);";
    // C_yes^dagger Z T^3 C_yes contributes zeta^7 on the one-dimensional space.
    for (operation, phase) in [("repeat_static(1,phase,u)", 7), ("adjoint(phase,u)", 1)] {
        let steps = compiled_steps(definitions, preparation, operation);
        assert_operator(0, &steps, |_, _| Exact::phase(phase));
    }
    let steps = compiled_steps(
        definitions,
        &format!("{preparation} let q = join(init0(),u);"),
        "repeat_static(1,controlled,q)",
    );
    assert_operator(1, &steps, |row, column| {
        if row == column {
            Exact::phase(if column == 0 { 7 } else { 0 })
        } else {
            Exact::ZERO
        }
    });
}

#[test]
fn sealed_phase_aliases_match_exact_operators_and_their_static_clients() {
    let imports = "use std::quantum::{s,sdg,tdg,id,phase_eighth};";
    for (name, exponent) in [("s", 2), ("sdg", 6), ("tdg", 7)] {
        for (operation, power) in [
            (format!("repeat_static(1,{name},q)"), exponent),
            (format!("adjoint({name},q)"), 8 - exponent),
            (format!("repeat_static(3,{name},q)"), 3 * exponent),
        ] {
            let steps = compiled_steps(imports, "let q = init0();", &operation);
            assert_operator(1, &steps, |row, column| {
                if row == column {
                    Exact::phase(power * column)
                } else {
                    Exact::ZERO
                }
            });
        }
        let definitions = format!(
            "{imports}
            unitary fn controlled(q:Q<(Bit,Bit)>)->Q<(Bit,Bit)> {{
                let (c,t) = split(q);
                let (c,t) = qif(c,t) {{ 0 => id, 1 => {name} }};
                join(c,t)
            }}"
        );
        let steps = compiled_steps(
            &definitions,
            "let q = join(init0(),init0());",
            "repeat_static(1,controlled,q)",
        );
        assert_operator(2, &steps, |row, column| {
            if row == column {
                Exact::phase(if column == 3 { exponent } else { 0 })
            } else {
                Exact::ZERO
            }
        });
    }
    // Direct aliases must agree too, independently of static-call expansion.
    let steps = compiled_steps(
        &format!(
            "{imports}
        unitary fn direct(q:Q<Bit>)->Q<Bit>{{ phase_eighth(tdg(sdg(s(id(q))))) }}"
        ),
        "let q = init0();",
        "repeat_static(1,direct,q)",
    );
    assert_operator(1, &steps, |row, column| {
        if row == column {
            Exact::phase(1 + 15 * column)
        } else {
            Exact::ZERO
        }
    });
}

#[test]
fn sealed_scalar_phase_retains_zero_width_control_and_basis_specific_expectations() {
    let imports = "use std::quantum::{id,phase_eighth};";
    let unit = "let pair = basis init0() as b { ((),b) };
        let (q,b) = split(pair); discard(b);";
    for (operation, exponent) in [
        ("repeat_static(1,id,q)", 0),
        ("repeat_static(1,phase_eighth,q)", 1),
        ("adjoint(phase_eighth,q)", 7),
        ("repeat_static(8,phase_eighth,q)", 0),
    ] {
        let steps = compiled_steps(imports, unit, operation);
        assert_operator(0, &steps, |_, _| Exact::phase(exponent));
    }
    // Within one compiler, check both Unit and Bit meanings for the same names.
    let definitions = format!(
        "{imports}
        unitary fn mixed(q:Q<((Bit,Unit),Bit)>)->Q<((Bit,Unit),Bit)> {{
            let (cu,b) = split(q); let (c,u) = split(cu);
            let (c,u) = qif(c,u) {{ 0 => id, 1 => phase_eighth }};
            let (c,b) = qif(c,b) {{ 0 => id, 1 => phase_eighth }};
            join(join(c,u),b)
        }}"
    );
    let steps = compiled_steps(
        &definitions,
        &format!("{unit} let q = join(join(init0(),q),init0());"),
        "repeat_static(1,mixed,q)",
    );
    assert_operator(2, &steps, |row, column| {
        if row == column {
            Exact::phase(2 * (column & 1))
        } else {
            Exact::ZERO
        }
    });
    let steps = compiled_steps(
        imports,
        "let q = join(init0(),init0());",
        "adjoint(phase_eighth,q)",
    );
    assert_operator(2, &steps, |row, column| {
        if row == column {
            Exact::phase(7)
        } else {
            Exact::ZERO
        }
    });
}

#[test]
fn scalar_source_action_adds_no_auxiliary_wire_and_aliases_keep_linear_types() {
    use qleisli::frontend::compile::{ErrorCode, check_project};
    let root = SourceRoot::new(
        "use std::quantum::{init0,phase_eighth};
        use std::observe::discard;
        observe fn main()->Unit { discard(phase_eighth(init0())); () }",
    );
    let verified = compile_project(&root.0).unwrap();
    assert_eq!(verified.program().operations.len(), 3);
    assert!(
        matches!(&verified.program().operations[1], RawOp::ApplyUnitary { steps, .. }
        if steps.len() == 1 && matches!(&steps[0].action,
            CircuitAction::Monomial { indices, permutation, phases }
            if indices.is_empty() && permutation == &[0] && phases == &[1]))
    );
    for (source, code) in [
        (
            "use std::quantum::id; unitary fn f(q:Q<Unit>)->(Q<Unit>,Q<Unit>){(id(q),id(q))}",
            ErrorCode::Ownership,
        ),
        (
            "use std::quantum::phase_eighth; unitary fn f(q:Bit)->Bit{phase_eighth(q)}",
            ErrorCode::TypeMismatch,
        ),
        (
            "use std::quantum::s; unitary fn f(q:Q<(Bit,Bit)>)->Q<(Bit,Bit)>{s(q)}",
            ErrorCode::TypeMismatch,
        ),
        (
            "use std::quantum::tdg; unitary fn f(q:Q<Unit>)->Q<Unit>{repeat_static(0,tdg,q)}",
            ErrorCode::TypeMismatch,
        ),
    ] {
        root.write("main.qli", source);
        assert_eq!(check_project(&root.0).unwrap_err().code, code);
    }
}

fn permutation_is_odd(permutation: &[usize]) -> bool {
    let mut odd = false;
    for (i, output) in permutation.iter().enumerate() {
        for later in &permutation[i + 1..] {
            odd ^= output > later;
        }
    }
    odd
}

// Exact determinant of the small monomial/H circuits in this review. This is
// an independent necessary obstruction, not a synthesis decision procedure.
fn determinant_exponent(width: usize, steps: &[CircuitStep]) -> usize {
    let dimension = 1 << width;
    steps
        .iter()
        .map(|step| match &step.action {
            CircuitAction::Hadamard { .. } => {
                4 * ((1usize << (width - step.controls.len() - 1)) % 2)
            }
            CircuitAction::Monomial {
                indices,
                permutation,
                phases,
            } => {
                let mut mapping = Vec::new();
                let mut exponent = 0;
                for basis in 0..dimension {
                    if !step
                        .controls
                        .iter()
                        .all(|c| ((basis >> c.index) & 1 != 0) == c.when_one)
                    {
                        mapping.push(basis);
                        continue;
                    }
                    let label = indices
                        .iter()
                        .enumerate()
                        .fold(0, |label, (i, axis)| label | (((basis >> axis) & 1) << i));
                    exponent += usize::from(phases[label]);
                    mapping.push(indices.iter().enumerate().fold(basis, |output, (i, axis)| {
                        (output & !(1 << axis))
                            | (((usize::from(permutation[label]) >> i) & 1) << axis)
                    }));
                }
                (exponent + 4 * usize::from(permutation_is_odd(&mapping))) % 8
            }
            CircuitAction::Contract { .. } => panic!("outside this determinant regression"),
        })
        .sum::<usize>()
        % 8
}

#[test]
fn review_same_wire_obstructions_do_not_reject_semantic_unitaries() {
    let c3x = include_str!(
        "fixtures/frontend_v030/coherent-basis/current/ordinary-type-cutover/current/review_v023/c3x.qli"
    );
    let root = SourceRoot::new(&format!(
        "{IMPORTS}\n{c3x}
        observe fn main()->Unit {{
            discard(c3x(join(join(init0(),init0()),join(init0(),init0())))); ()
        }}"
    ));
    let verified = compile_project(&root.0).unwrap();
    let table = verified
        .program()
        .operations
        .iter()
        .find_map(|op| match op {
            RawOp::LiftBasis {
                table,
                output_wires,
                ..
            } => {
                assert_eq!(output_wires.len(), 4);
                Some(table)
            }
            _ => None,
        })
        .unwrap();
    let expected: Vec<u16> = (0..14).chain([15, 14]).collect();
    assert_eq!(table, &expected);
    assert!(permutation_is_odd(
        &table.iter().map(|x| usize::from(*x)).collect::<Vec<_>>()
    ));

    let steps = compiled_steps(
        "use std::transform::qft3;",
        "let q = join(join(init0(),init0()),init0());",
        "repeat_static(1,qft3,q)",
    );
    assert_operator(3, &steps, |row, column| {
        Exact::phase(row * column) * Exact::inverse_sqrt_two() * Exact::new([1, 0, 0, 0], 1)
    });
    assert_eq!(determinant_exponent(3, &steps), 2, "det(F8) = i exactly");
    // Embedded H/T/X and NCT generate only +/-1 at width 3 and +1 at width 4.
    for width in [3, 4] {
        let allowed = if width == 3 { vec![0, 4] } else { vec![0] };
        for (local_width, determinant) in [(1usize, 4usize), (1, 1), (2, 4), (3, 4)] {
            assert!(allowed.contains(&((determinant * (1 << (width - local_width))) % 8)));
        }
    }
}

#[test]
fn closed_classical_computation_selects_static_branches_and_preserves_output_axes() {
    let definitions = "
unitary fn choose(q: Q<(Bit,Bit)>) -> Q<(Bit,Bit)> {
    let (a,b) = split(q);
    let flag = if 1 { 0 xor not 0 } else { 0 };
    let a = if flag and 1 { t(x(a)) } else { z(a) };
    join(b,a)
}
unitary fn identity(q: Q<(Bit,Bit)>) -> Q<(Bit,Bit)> { q }
unitary fn control(q: Q<(Bit,(Bit,Bit))>) -> Q<(Bit,(Bit,Bit))> {
    let (c,p) = split(q);
    let (c,p) = qif(c,p) { 0 => identity, 1 => choose };
    join(c,p)
}";
    // U|a,b> = zeta^(1-a)|b,1-a>; both branch phis and final
    // ownership order participate in the exact inverse and controlled matrix.
    let preparation = "let q = join(init0(),init0());";
    let steps = compiled_steps(definitions, preparation, "repeat_static(1,choose,q)");
    assert_operator(2, &steps, |row, column| {
        let a = column & 1;
        let b = column >> 1;
        if row == b | ((1 - a) << 1) {
            Exact::phase(1 - a)
        } else {
            Exact::ZERO
        }
    });
    let inverse = compiled_steps(definitions, preparation, "adjoint(choose,q)");
    assert_operator(2, &inverse, |row, column| {
        let b = column & 1;
        let a = 1 - (column >> 1);
        if row == a | (b << 1) {
            Exact::phase(8 - (1 - a))
        } else {
            Exact::ZERO
        }
    });
    let else_definitions = definitions.replace("if 1 {", "if 0 {");
    let else_steps = compiled_steps(&else_definitions, preparation, "repeat_static(1,choose,q)");
    assert_operator(2, &else_steps, |row, column| {
        let a = column & 1;
        let b = column >> 1;
        if row == b | (a << 1) {
            Exact::phase(4 * a)
        } else {
            Exact::ZERO
        }
    });
    let controlled = compiled_steps(
        definitions,
        "let q = join(init0(),join(init0(),init0()));",
        "repeat_static(1,control,q)",
    );
    assert_operator(3, &controlled, |row, column| {
        let c = column & 1;
        let a = (column >> 1) & 1;
        let b = column >> 2;
        let (output, phase) = if c == 0 {
            (column, 0)
        } else {
            (c | (b << 1) | ((1 - a) << 2), 1 - a)
        };
        if row == output {
            Exact::phase(phase)
        } else {
            Exact::ZERO
        }
    });
    let scalar_definitions = "
classical fn one(u:Unit)->Bit { 1 }
unitary fn identity(q:Q<Unit>)->Q<Unit> { q }
unitary fn scalar(q:Q<Unit>)->Q<Unit> {
    if not 0 {
        if 1 and 0 { q } else { with_computed(q,one) { |a| z(t(a)) } }
    } else { q }
}
unitary fn controlled(q:Q<(Bit,Unit)>)->Q<(Bit,Unit)> {
    let (c,u)=split(q);
    let (c,u)=qif(c,u) { 0=>identity, 1=>scalar };
    join(c,u)
}";
    let scalar = compiled_steps(
        scalar_definitions,
        "let q=basis init0() as b { (b,()) };",
        "repeat_static(1,controlled,q)",
    );
    assert_operator(1, &scalar, |row, column| {
        if row == column {
            Exact::phase(5 * column)
        } else {
            Exact::ZERO
        }
    });
}

#[test]
fn product_pattern_lift_is_a_full_basis_permutation_under_inverse_and_control() {
    let definitions = "
unitary fn permute(q: Q<(Bit,Bit)>) -> Q<(Bit,Bit)> {
    basis q as (a,b) { (b,a xor b) }
}
unitary fn identity(q: Q<(Bit,Bit)>) -> Q<(Bit,Bit)> { q }
unitary fn control(q: Q<(Bit,(Bit,Bit))>) -> Q<(Bit,(Bit,Bit))> {
    let (c,p) = split(q);
    let (c,p) = qif(c,p) { 0 => identity, 1 => permute };
    join(c,p)
}";
    let inverse = compiled_steps(
        definitions,
        "let q=join(init0(),init0());",
        "adjoint(permute,q)",
    );
    assert_operator(2, &inverse, |row, column| {
        let b = column & 1;
        let a = (column >> 1) ^ b;
        if row == a | (b << 1) {
            Exact::ONE
        } else {
            Exact::ZERO
        }
    });
    let controlled = compiled_steps(
        definitions,
        "let q=join(init0(),join(init0(),init0()));",
        "repeat_static(1,control,q)",
    );
    assert_operator(3, &controlled, |row, column| {
        let c = column & 1;
        let a = (column >> 1) & 1;
        let b = column >> 2;
        let output = if c == 0 {
            column
        } else {
            c | (b << 1) | ((a ^ b) << 2)
        };
        if row == output {
            Exact::ONE
        } else {
            Exact::ZERO
        }
    });
}
