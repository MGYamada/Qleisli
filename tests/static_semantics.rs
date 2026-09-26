//! Exact finite operator checks, including global phase, not a general proof.

use std::fs;
use std::ops::{Add, Mul, Neg};
use std::path::PathBuf;
use std::sync::atomic::{AtomicU64, Ordering};

use qleisli_core::frontend::compile::compile_project;
use qleisli_core::ir::{CircuitAction, CircuitStep, RawOp};

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

static NEXT_ROOT: AtomicU64 = AtomicU64::new(0);

struct SourceRoot(PathBuf);

impl Drop for SourceRoot {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

const IMPORTS: &str = "
use std::quantum::init0; use std::quantum::h; use std::quantum::x;
use std::quantum::z; use std::quantum::t; use std::quantum::cnot;
use std::quantum::join; use std::quantum::split; use std::observe::discard;
";

fn compiled_steps(definitions: &str, preparation: &str, operation: &str) -> Vec<CircuitStep> {
    let root = SourceRoot(std::env::temp_dir().join(format!(
        "qleisli-static-semantics-{}-{}",
        std::process::id(),
        NEXT_ROOT.fetch_add(1, Ordering::Relaxed)
    )));
    fs::create_dir(&root.0).unwrap();
    fs::write(
        root.0.join("main.qli"),
        format!(
            "{IMPORTS}\n{definitions}\nobserve fn main() -> Unit {{
            {preparation} let result = {operation}; discard(result); ()
        }}"
        ),
    )
    .unwrap();
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
    let b = do label <- b; pure not label;
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
basis fn yes(value: Unit) -> Bit { 1 }
unitary fn identity(q: Q<Unit>) -> Q<Unit> { q }
unitary fn phase(q: Q<Unit>) -> Q<Unit> { with_computed(q,yes) { |a| z(t(t(t(a)))) } }
unitary fn controlled(q: Q<(Bit,Unit)>) -> Q<(Bit,Unit)> {
    let (c,u) = split(q); let (c,u) = qif(c,u) { 0 => phase, 1 => identity }; join(c,u)
}";
    let preparation =
        "let pair = do b <- init0(); pure ((),b); let (u,b) = split(pair); discard(b);";
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
