//! Finite source/IR correspondence checks against independently specified kets.
//! These numerical checks use tolerance 1e-12; they are not a general proof.

mod common;

use std::collections::BTreeMap;
use std::f64::consts::{FRAC_1_SQRT_2, FRAC_PI_4};

use common::SourceRoot;
use common::accept;
use qleisli::AcceptedProgram;
use qleisli::frontend::compile::{ErrorCode, check_project, compile_project};
use qleisli::ir::RawOp;
use qleisli::sim::{SimulationLimits, run_closed};

const TOLERANCE: f64 = 1e-12;
const IMPORTS: &str = "
use std::quantum::init0; use std::quantum::h; use std::quantum::x;
use std::quantum::z; use std::quantum::t; use std::quantum::cnot;
use std::quantum::join; use std::quantum::split;
use std::observe::measure_z; use std::observe::reset; use std::observe::discard;
";

type Distribution = BTreeMap<Vec<bool>, f64>;

// A small Born-rule oracle, not another circuit interpreter. Tests supply the
// analytic nonzero ket coefficients directly. No compiler/simulator helpers,
// generated tables, inverses, or round trips construct these expected states.
#[derive(Clone, Copy)]
struct Amplitude {
    re: f64,
    im: f64,
}

impl Amplitude {
    fn real(re: f64) -> Self {
        Self { re, im: 0.0 }
    }

    fn polar(magnitude: f64, phase: f64) -> Self {
        Self {
            re: magnitude * phase.cos(),
            im: magnitude * phase.sin(),
        }
    }

    fn add(self, other: Self) -> Self {
        Self {
            re: self.re + other.re,
            im: self.im + other.im,
        }
    }

    fn mul(self, other: Self) -> Self {
        Self {
            re: self.re * other.re - self.im * other.im,
            im: self.re * other.im + self.im * other.re,
        }
    }

    fn weight(self) -> f64 {
        self.re * self.re + self.im * self.im
    }
}

struct History {
    public: Vec<bool>,
    ket: Vec<(usize, Amplitude)>,
}

#[derive(Clone, Copy, Debug)]
enum Axis {
    X,
    Y,
    Z,
}

impl Axis {
    fn read(self, name: &str) -> String {
        match self {
            Self::X => format!("measure_z(h({name}))"),
            Self::Y => {
                // Y readout is Z after H S†, and S† = T^6. Use ordinary
                // gate calls so this readout does not rely on static inversion.
                let rotated = (0..6).fold(name.to_owned(), |q, _| format!("t({q})"));
                format!("measure_z(h({rotated}))")
            }
            Self::Z => format!("measure_z({name})"),
        }
    }

    fn bra(self, outcome: bool, basis: bool) -> Amplitude {
        let sign = if outcome { -1.0 } else { 1.0 };
        match self {
            Self::Z => Amplitude::real(if outcome == basis { 1.0 } else { 0.0 }),
            Self::X => Amplitude::real(if basis { sign } else { 1.0 } * FRAC_1_SQRT_2),
            Self::Y if basis => Amplitude {
                re: 0.0,
                im: -sign * FRAC_1_SQRT_2,
            },
            Self::Y => Amplitude::real(FRAC_1_SQRT_2),
        }
    }
}

fn bits(value: usize, width: usize) -> Vec<bool> {
    (0..width).map(|i| value & (1 << i) != 0).collect()
}

fn settings(width: usize) -> Vec<Vec<Axis>> {
    (0..3usize.pow(width as u32))
        .map(|mut number| {
            (0..width)
                .map(|_| {
                    let axis = [Axis::X, Axis::Y, Axis::Z][number % 3];
                    number /= 3;
                    axis
                })
                .collect()
        })
        .collect()
}

fn born(histories: &[History], axes: &[Axis]) -> Distribution {
    let mut result = Distribution::new();
    for history in histories {
        for outcome in 0..1 << axes.len() {
            let amplitude =
                history
                    .ket
                    .iter()
                    .fold(Amplitude::real(0.0), |sum, &(label, coefficient)| {
                        let projected =
                            axes.iter()
                                .enumerate()
                                .fold(coefficient, |value, (i, axis)| {
                                    value.mul(
                                        axis.bra(outcome & (1 << i) != 0, label & (1 << i) != 0),
                                    )
                                });
                        sum.add(projected)
                    });
            let mut output = history.public.clone();
            output.extend(bits(outcome, axes.len()));
            // Private histories add probabilities, including their original
            // branch weights. Never normalize or add amplitudes across them.
            *result.entry(output).or_default() += amplitude.weight();
        }
    }
    result
}

fn compile(source: &str) -> AcceptedProgram {
    let root = SourceRoot::new(&format!("{IMPORTS}\n{source}"));
    compile_project(&root.0).unwrap_or_else(|error| panic!("{source}\n{error}"))
}

fn assert_distribution(program: &AcceptedProgram, expected: &Distribution) {
    let actual = run_closed(program, SimulationLimits::default()).unwrap();
    assert!((actual.values().sum::<f64>() - 1.0).abs() < TOLERANCE);
    assert!((expected.values().sum::<f64>() - 1.0).abs() < TOLERANCE);
    for output in actual.keys().chain(expected.keys()) {
        let actual_weight = actual.get(output).copied().unwrap_or(0.0);
        let expected_weight = expected.get(output).copied().unwrap_or(0.0);
        assert!(
            (actual_weight - expected_weight).abs() < TOLERANCE,
            "{output:?}: {actual_weight}, expected {expected_weight}"
        );
    }
}

fn prepare_bit(bit: bool) -> &'static str {
    if bit { "x(init0())" } else { "init0()" }
}

fn computed_tables(program: &AcceptedProgram) -> Vec<&[u16]> {
    program
        .program()
        .operations
        .iter()
        .filter_map(|op| match op {
            RawOp::ComputeUseUncompute { function, .. } => Some(function.as_slice()),
            _ => None,
        })
        .collect()
}

#[test]
fn unit_factors_and_product_labels_match_every_explicit_basis_image() {
    // Input label is a + 2b + 4c; output is c + 2(a xor b) + 4b.
    // Unit leaves contribute no bits but remain part of the exact type tree.
    let table = [0, 2, 6, 4, 1, 3, 7, 5];
    for (input, output) in table.into_iter().enumerate() {
        let source = format!(
            "
unitary fn relabel(q: Q<((Bit,Unit),(Bit,(Unit,Bit)))>)
    -> Q<((Unit,Bit),((Bit,Bit),Unit))> {{
    basis q as ((a,_),(b,(_,c))) {{ (((),c),((a xor b,b),())) }}
}}
observe fn main() -> ((Bit,Bit),Bit) {{
    let a = basis {} as a {{ (a,()) }};
    let c = basis {} as c {{ ((),c) }};
    let q = relabel(join(a,join({},c)));
    let (uc,abu) = split(q); let (u,c) = split(uc);
    let (ab,v) = split(abu); let (a,b) = split(ab);
    discard(u); discard(v);
    ((measure_z(c),measure_z(a)),measure_z(b))
}}",
            prepare_bit(input & 1 != 0),
            prepare_bit(input & 4 != 0),
            prepare_bit(input & 2 != 0),
        );
        let checked = compile(&source);
        let tables: Vec<_> = checked
            .program()
            .operations
            .iter()
            .filter_map(|op| match op {
                RawOp::LiftBasis { table, .. } if table.len() == 8 => Some(table),
                _ => None,
            })
            .collect();
        assert_eq!(tables.len(), 1);
        assert_eq!(tables[0].as_slice(), &[0, 2, 6, 4, 1, 3, 7, 5]);
        assert_distribution(&checked, &Distribution::from([(bits(output, 3), 1.0)]));
    }
}

#[test]
fn growing_lift_matches_joint_pauli_statistics_with_two_reference_wires() {
    // V|a,b> = |a,b,a xor b>. Applying V to two phased Bell halves gives
    // (1/2) sum_(a,b) zeta^a |a,b,a xor b,a,b> in (a,b,c,r,s) order.
    // All 3^5 Pauli settings inspect the entire finite joint output, including
    // off-diagonal coherence; computational-basis outputs alone cannot do so.
    let ket = (0..4)
        .map(|input| {
            let a = input & 1;
            let b = input >> 1;
            (
                a | (b << 1) | ((a ^ b) << 2) | (a << 3) | (b << 4),
                Amplitude::polar(0.5, a as f64 * FRAC_PI_4),
            )
        })
        .collect();
    let histories = [History {
        public: vec![],
        ket,
    }];
    for axes in settings(5) {
        let source = format!(
            "
iso fn grow(q: Q<(Bit,Bit)>) -> Q<((Bit,Bit),Bit)> {{
    basis q as (a,b) {{ ((a,b),a xor b) }}
}}
observe fn main() -> (((Bit,Bit),Bit),(Bit,Bit)) {{
    let (a,r) = cnot(t(h(init0())),init0());
    let (b,s) = cnot(h(init0()),init0());
    let (ab,c) = split(grow(join(a,b))); let (a,b) = split(ab);
    ((({},{}),{}),({},{}))
}}",
            axes[0].read("a"),
            axes[1].read("b"),
            axes[2].read("c"),
            axes[3].read("r"),
            axes[4].read("s"),
        );
        let checked = compile(&source);
        assert_distribution(&checked, &born(&histories, &axes));
    }
}

#[test]
fn observation_instruments_preserve_public_weights_and_reference_statistics() {
    // Up to a common phase, T^3 H T H prepares
    // cos(pi/8)|0> + zeta sin(pi/8)|1>. CNOT gives the corresponding
    // biased entangled pair. This tests unequal branch weights and complex
    // coherences, not only a maximally entangled real input.
    let c = (FRAC_PI_4 / 2.0).cos();
    let s = (FRAC_PI_4 / 2.0).sin();
    let preparation = "let (a,r) = cnot(t(t(t(h(t(h(init0())))))),init0());";
    let input = [History {
        public: vec![],
        ket: vec![(0, Amplitude::real(c)), (3, Amplitude::polar(s, FRAC_PI_4))],
    }];
    // The first output is the public measurement outcome. Comparing all nine
    // joint settings checks the corresponding unnormalized reference states.
    for axes in settings(2) {
        let source = format!(
            "observe fn main() -> (Bit,Bit) {{ {preparation} ({},{}) }}",
            axes[0].read("a"),
            axes[1].read("r")
        );
        assert_distribution(&compile(&source), &born(&input, &axes));
    }

    // Reset hides the old bit, prepares a new |0>, and leaves the reference
    // mixture c^2|0><0| + s^2|1><1|. Distinct histories must not interfere.
    let reset_histories = [
        History {
            public: vec![],
            ket: vec![(0, Amplitude::real(c))],
        },
        History {
            public: vec![],
            ket: vec![(2, Amplitude::real(s))],
        },
    ];
    for axes in settings(2) {
        let source = format!(
            "observe fn main() -> (Bit,Bit) {{ {preparation} let a=reset(a); ({},{}) }}",
            axes[0].read("a"),
            axes[1].read("r")
        );
        assert_distribution(&compile(&source), &born(&reset_histories, &axes));
    }
    let discard_histories = [
        History {
            public: vec![],
            ket: vec![(0, Amplitude::real(c))],
        },
        History {
            public: vec![],
            ket: vec![(1, Amplitude::real(s))],
        },
    ];
    for axes in settings(1) {
        let source = format!(
            "observe fn main() -> Bit {{ {preparation} discard(a); {} }}",
            axes[0].read("r")
        );
        assert_distribution(&compile(&source), &born(&discard_histories, &axes));
    }
}

const COMPUTED: &str = "
classical fn predicate((((a,u),b),c): (((Bit,Unit),Bit),Bit)) -> Bit { (a and not b) xor c }
unitary fn oracle(q: Q<(((Bit,Unit),Bit),Bit)>) -> Q<(((Bit,Unit),Bit),Bit)> {
    with_computed(q,predicate) { |ancilla| z(t(t(t(ancilla)))) }
}
unitary fn identity(q: Q<(((Bit,Unit),Bit),Bit)>) -> Q<(((Bit,Unit),Bit),Bit)> { q }
";

#[test]
fn computed_predicate_packing_and_phase_match_coherent_and_controlled_inputs() {
    let predicate = |label: usize| ((label & 1 != 0) && (label & 2 == 0)) ^ (label & 4 != 0);
    let histories = [History {
        public: vec![],
        ket: (0..8)
            .map(|label| {
                (
                    label,
                    Amplitude::polar(
                        1.0 / 8.0_f64.sqrt(),
                        if predicate(label) {
                            7.0 * FRAC_PI_4
                        } else {
                            0.0
                        },
                    ),
                )
            })
            .collect(),
    }];
    for axes in settings(3) {
        let source = format!(
            "{COMPUTED}
observe fn main() -> ((Bit,Bit),Bit) {{
    let au = basis h(init0()) as a {{ (a,()) }};
    let q = oracle(join(join(au,h(init0())),h(init0())));
    let (aub,c) = split(q); let (au,b) = split(aub); let (a,u) = split(au);
    discard(u); (({},{}),{})
}}",
            axes[0].read("a"),
            axes[1].read("b"),
            axes[2].read("c")
        );
        let checked = compile(&source);
        let table: Vec<_> = (0..8).map(|label| u16::from(predicate(label))).collect();
        assert_eq!(computed_tables(&checked), vec![table.as_slice()]);
        assert_distribution(&checked, &born(&histories, &axes));
    }
    // ZT^3 contributes zeta^7 when the predicate is true. A separate coherent
    // control exposes that phase even for a single computational-basis input.
    for input in 0..8 {
        for axis in [Axis::X, Axis::Y] {
            let phase = if predicate(input) {
                7.0 * FRAC_PI_4
            } else {
                0.0
            };
            let expected = born(
                &[History {
                    public: bits(input, 3),
                    ket: vec![
                        (0, Amplitude::real(FRAC_1_SQRT_2)),
                        (1, Amplitude::polar(FRAC_1_SQRT_2, phase)),
                    ],
                }],
                &[axis],
            );
            let source = format!(
                "{COMPUTED}
observe fn main() -> (((Bit,Bit),Bit),Bit) {{
    let au = basis {} as a {{ (a,()) }};
    let q = join(join(au,{}),{});
    let (control,q) = qif(h(init0()),q) {{ 0=>identity, 1=>oracle }};
    let (aub,c) = split(q); let (au,b) = split(aub); let (a,u) = split(au);
    discard(u); (((measure_z(a),measure_z(b)),measure_z(c)),{})
}}",
                prepare_bit(input & 1 != 0),
                prepare_bit(input & 2 != 0),
                prepare_bit(input & 4 != 0),
                axis.read("control")
            );
            assert_distribution(&compile(&source), &expected);
        }
    }

    // Explicit Unit and (Unit,Unit) domains each have one label, but their
    // exact trees are not interchangeable and neither is inferred from arity.
    for (params, basis, label, wrong_basis) in [
        ("_: Unit", "Unit", "()", "(Unit,Unit)"),
        ("(_, _): (Unit,Unit)", "(Unit,Unit)", "((),())", "Unit"),
    ] {
        let definitions = format!(
            "
classical fn one({params}) -> Bit {{ 1 }}
unitary fn scalar(q: Q<{basis}>) -> Q<{basis}> {{
    with_computed(q,one) {{ |a| z(t(t(t(a)))) }}
}}
unitary fn identity(q: Q<{basis}>) -> Q<{basis}> {{ q }}
"
        );
        for axis in [Axis::X, Axis::Y] {
            let source = format!(
                "{definitions}
observe fn main() -> Bit {{
    let (q,b)=split(basis init0() as b {{ ({label},b) }}); discard(b);
    let q=scalar(q);
    let (control,q)=qif(h(init0()),q) {{ 0=>identity, 1=>scalar }};
    discard(q); {}
}}",
                axis.read("control")
            );
            let checked = compile(&source);
            // The first scalar call exposes the emitted one-row predicate;
            // its common phase has no effect on the later control readout.
            assert_eq!(computed_tables(&checked), vec![&[1][..]]);
            let expected = born(
                &[History {
                    public: vec![],
                    ket: vec![
                        (0, Amplitude::real(FRAC_1_SQRT_2)),
                        (1, Amplitude::polar(FRAC_1_SQRT_2, 7.0 * FRAC_PI_4)),
                    ],
                }],
                &[axis],
            );
            assert_distribution(&checked, &expected);
        }
        let rejected = SourceRoot::new(&format!(
            "{IMPORTS}
classical fn one({params}) -> Bit {{ 1 }}
unitary fn wrong(q: Q<{wrong_basis}>) -> Q<{wrong_basis}> {{
    with_computed(q,one) {{ |a| t(a) }}
}}"
        ));
        assert_eq!(
            check_project(&rejected.0).unwrap_err().code,
            ErrorCode::TypeMismatch
        );
    }
}

#[test]
fn complete_branch_phi_transports_measured_results_fresh_wires_and_pending_frames() {
    // Two phased Bell pairs enter route. The flag chooses which half to
    // measure and where the other half/new zero appear in the result. Public
    // fields are (flag,c,d). Output ket axes are (left,right,ra,rb).
    let histories: Vec<_> = [false, true]
        .into_iter()
        .flat_map(|flag| {
            [false, true].into_iter().map(move |measured| History {
                public: vec![
                    flag,
                    if flag { measured } else { !measured },
                    if flag { !measured } else { measured },
                ],
                ket: (0..2)
                    .map(|survivor| {
                        let (label, phase) = if flag {
                            (
                                survivor | (usize::from(measured) << 2) | (survivor << 3),
                                survivor as f64 * 2.0 * FRAC_PI_4,
                            )
                        } else {
                            (
                                (survivor << 1) | (survivor << 2) | (usize::from(measured) << 3),
                                survivor as f64 * FRAC_PI_4,
                            )
                        };
                        (label, Amplitude::polar(0.5 * FRAC_1_SQRT_2, phase))
                    })
                    .collect(),
            })
        })
        .collect();
    for axes in settings(4) {
        let source = format!(
            "
observe fn route(flag: Bit, a: Q<Bit>, b: Q<Bit>) -> ((Bit,Q<Bit>),(Bit,Q<Bit>)) {{
    if flag {{ let m=measure_z(a); ((m,b),(not m,init0())) }}
    else {{ let m=measure_z(b); ((not m,init0()),(m,a)) }}
}}
observe fn read(u: Q<Unit>, result: ((Bit,Q<Bit>),(Bit,Q<Bit>)),
                ra: Q<Bit>, rb: Q<Bit>, flag: Bit)
    -> (Bit,((Bit,Bit),((Bit,Bit),(Bit,Bit)))) {{
    let ((c,left),(d,right))=result; discard(u);
    (flag,((c,d),(({},{}),({},{}))))
}}
observe fn main() -> (Bit,((Bit,Bit),((Bit,Bit),(Bit,Bit)))) {{
    let (a,ra)=cnot(t(h(init0())),init0());
    let (b,rb)=cnot(t(t(h(init0()))),init0());
    let (u,a)=split(basis a as a {{ ((),a) }});
    let flag=measure_z(h(init0()));
    read(u,route(flag,a,b),ra,rb,flag)
}}",
            axes[0].read("left"),
            axes[1].read("right"),
            axes[2].read("ra"),
            axes[3].read("rb")
        );
        let checked = compile(&source);
        let phis: Vec<_> = checked
            .program()
            .operations
            .iter()
            .filter_map(|op| match op {
                RawOp::ClassicalBranch {
                    quantum_phis,
                    classical_phis,
                    ..
                } => Some((quantum_phis, classical_phis)),
                _ => None,
            })
            .collect();
        assert_eq!(phis.len(), 1);
        assert_eq!(phis[0].1.len(), 2);
        let mut widths: Vec<_> = phis[0].0.iter().map(|phi| phi.output_wires.len()).collect();
        widths.sort();
        assert_eq!(widths, [0, 1, 1, 1, 1]);
        assert_distribution(&checked, &born(&histories, &axes));
    }
}

#[test]
fn verified_ir_does_not_by_itself_establish_source_correspondence() {
    let checked = compile(
        "
observe fn main() -> Bit { measure_z(basis init0() as b { not b }) }
",
    );
    let expected = Distribution::from([(vec![true], 1.0)]);
    assert_distribution(&checked, &expected);
    let mut changed = checked.program().clone();
    let mut replacements = 0;
    for op in &mut changed.operations {
        if let RawOp::LiftBasis { table, .. } = op {
            assert_eq!(table.as_slice(), &[1, 0]);
            *table = vec![0, 1]; // A different total injection with valid ownership/effect.
            replacements += 1;
        }
    }
    assert_eq!(replacements, 1);
    let changed = accept(changed).expect("both the identity and NOT are valid unitaries");
    let actual = run_closed(&changed, SimulationLimits::default()).unwrap();
    assert_eq!(actual, Distribution::from([(vec![false], 1.0)]));
    assert_eq!(actual.get(&vec![true]).copied().unwrap_or(0.0), 0.0);
    // Source meaning requires NOT. Acceptance of a well-formed identity table
    // is therefore insufficient evidence for this source-to-IR obligation.
}
