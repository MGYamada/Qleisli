//! Untrusted, finite Qleisli IR. All public fields must be checked by `verify`.

/// A linear SSA ownership token. A gate consumes one token and creates another.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct TokenId(pub u32);

/// A logical quantum wire. Wire IDs may not be allocated twice, even after use.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct WireId(pub u32);

/// A copyable classical bit SSA value. It is never a quantum basis label.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct ClassicalId(pub u32);

/// A finite register of ordered bits. Width zero represents `Unit`.
///
/// The initial verifier limits a *single* register to 12 bits so that an
/// explicit basis-function table cannot grow without bound. This is an
/// implementation limit, not a proposed `.qli` language limit.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct BasisShape {
    pub bits: u8,
}

impl BasisShape {
    pub const UNIT: Self = Self { bits: 0 };
    pub const BIT: Self = Self { bits: 1 };
}

/// The claimed function classification. This declaration order is the
/// verifier's strength order: Unitary < Iso < Observe. It linearizes the
/// pure/observe effect and the Iso/Unitary classification of the formal core.
/// The verifier derives the minimum required classification from commands and
/// rejects a stronger claim.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub enum Effect {
    Unitary,
    Iso,
    Observe,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct QuantumPort {
    pub token: TokenId,
    pub wires: Vec<WireId>,
    pub shape: BasisShape,
}

/// A complete IR function. The final live quantum tokens must be exactly
/// `quantum_outputs`; classical values may be copied or ignored.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RawProgram {
    pub quantum_inputs: Vec<QuantumPort>,
    pub classical_inputs: Vec<ClassicalId>,
    pub operations: Vec<RawOp>,
    pub quantum_outputs: Vec<TokenId>,
    pub classical_outputs: Vec<ClassicalId>,
    pub declared_effect: Effect,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SingleGate {
    H,
    X,
    Z,
    T,
}

/// Scalar phases are retained even when the target system is `Unit`.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ScalarPhase {
    MinusOne,
    EighthTurn,
}

/// One sealed unitary step within a coherent `QuantumIf` arm. All indices
/// refer to the same ordered target register; no step changes its shape.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum UnitaryStep {
    Gate {
        gate: SingleGate,
        target_index: usize,
    },
    Cnot {
        control_index: usize,
        target_index: usize,
    },
    Toffoli {
        control_a_index: usize,
        control_b_index: usize,
        target_index: usize,
    },
    /// A phase times the identity on the whole target, including `Unit`.
    ScalarPhase(ScalarPhase),
}

/// A basis control on the same ordered register as a circuit action.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct BitControl {
    pub index: usize,
    pub when_one: bool,
}

/// Flat, exact finite unitary description. The monomial matrix maps |x> to
/// exp(i*pi*phases[x]/4)|permutation[x]>. Empty indices retain scalar phase.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum CircuitAction {
    /// A known finite implementation carrying immutable independently checked
    /// function evidence. Axis remapping, outer controls and adjoint retain
    /// the evidence rather than replacing it with an unbound gate sequence.
    Contract {
        indices: Vec<usize>,
        evidence: std::sync::Arc<crate::contract::function::FunctionEvidence>,
        adjoint: bool,
    },
    Hadamard {
        target: usize,
    },
    Monomial {
        indices: Vec<usize>,
        permutation: Vec<u16>,
        phases: Vec<u8>,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CircuitStep {
    pub controls: Vec<BitControl>,
    pub action: CircuitAction,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ProtectedRegion {
    Source,
    Ancilla,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ProtectedBit {
    pub region: ProtectedRegion,
    pub index: u8,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Control {
    pub bit: ProtectedBit,
    pub when_one: bool,
}

/// These operations preserve the computational-basis values of the source and
/// computed ancilla. A controlled target gate may entangle the target, but
/// inverse computation still returns the ancilla to zero for every input.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ProtectedUse {
    /// Only Z and T are accepted on protected bits; H and X are rejected.
    ProtectedGate { bit: ProtectedBit, gate: SingleGate },
    ControlledTargetGate {
        controls: Vec<Control>,
        target_index: usize,
        gate: SingleGate,
    },
    /// Applies a scalar phase when every control matches. It has no target
    /// wire, so relative phases on a zero-width target are not erased.
    ControlledPhase {
        controls: Vec<Control>,
        phase: ScalarPhase,
    },
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct TargetTransition {
    pub input: TokenId,
    pub output: TokenId,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct QuantumPhi {
    pub then_token: TokenId,
    pub else_token: TokenId,
    pub output: TokenId,
    pub output_wires: Vec<WireId>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ClassicalPhi {
    pub then_id: ClassicalId,
    pub else_id: ClassicalId,
    pub output: ClassicalId,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum RawOp {
    /// Exact finite semantic contract for compute/use/uncompute. The data
    /// occupy the low axes and one fresh computed bit the highest axis.
    /// Independent verification checks W E_f = E_f u, including phase and
    /// all rows outside the encoded subspace, before permitting cleanup.
    /// Both actual W and the explicitly specified logical u are retained.
    CertifiedCompute {
        source: TokenId,
        source_out: TokenId,
        ancilla_wires: Vec<WireId>,
        function: Vec<u16>,
        use_steps: Vec<CircuitStep>,
        logical_steps: Vec<CircuitStep>,
    },
    /// A flat circuit over one register; the independent verifier checks every
    /// control, axis, permutation and phase. No arbitrary matrix is accepted.
    ApplyUnitary {
        input: TokenId,
        output: TokenId,
        steps: Vec<CircuitStep>,
    },
    Init0 {
        output: TokenId,
        wire: WireId,
    },
    Gate {
        gate: SingleGate,
        input: TokenId,
        output: TokenId,
    },
    Cnot {
        control: TokenId,
        target: TokenId,
        control_out: TokenId,
        target_out: TokenId,
    },
    Toffoli {
        control_a: TokenId,
        control_b: TokenId,
        target: TokenId,
        control_a_out: TokenId,
        control_b_out: TokenId,
        target_out: TokenId,
    },
    /// Coherent selection: |0><0|⊗U0 + |1><1|⊗U1. Both arms are static
    /// circuits over the same target register; relative phase is retained.
    /// Neither the control nor the target is measured or copied.
    QuantumIf {
        control: TokenId,
        target: TokenId,
        control_out: TokenId,
        target_out: TokenId,
        zero_ops: Vec<UnitaryStep>,
        one_ops: Vec<UnitaryStep>,
    },
    Split {
        input: TokenId,
        left: TokenId,
        right: TokenId,
        left_bits: u8,
    },
    Join {
        left: TokenId,
        right: TokenId,
        output: TokenId,
    },
    /// `table[x] = f(x)`, with one entry for every input basis label. The
    /// output wire list starts with all input wires in their original order;
    /// any additional wires must be globally fresh.
    LiftBasis {
        input: TokenId,
        output: TokenId,
        output_wires: Vec<WireId>,
        table: Vec<u16>,
    },
    /// Destructive Z measurement: there is no output quantum token.
    MeasureZ {
        input: TokenId,
        output: ClassicalId,
    },
    /// The old logical wire ends; a fresh logical wire begins in |0>.
    Reset {
        input: TokenId,
        output: TokenId,
        fresh_wire: WireId,
    },
    Discard {
        input: TokenId,
    },
    /// A fresh classical SSA bit, with no quantum preparation or measurement.
    ClassicalConst {
        value: bool,
        output: ClassicalId,
    },
    ClassicalNot {
        input: ClassicalId,
        output: ClassicalId,
    },
    ClassicalXor {
        left: ClassicalId,
        right: ClassicalId,
        output: ClassicalId,
    },
    ClassicalAnd {
        left: ClassicalId,
        right: ClassicalId,
        output: ClassicalId,
    },
    /// Both arms start with the same live quantum and classical contexts. All
    /// live quantum outputs of each arm must be covered by fresh phi tokens.
    ClassicalBranch {
        condition: ClassicalId,
        then_ops: Vec<RawOp>,
        else_ops: Vec<RawOp>,
        quantum_phis: Vec<QuantumPhi>,
        classical_phis: Vec<ClassicalPhi>,
    },
    /// A checked `init0; C_f; W; C_f†; release0` scope. `C_f` is XOR of the
    /// finite, total function table into a fresh ancilla. `W` must preserve
    /// source and ancilla basis labels. No free-standing Release0 exists.
    ComputeUseUncompute {
        source: TokenId,
        source_out: TokenId,
        targets: Vec<TargetTransition>,
        ancilla_wires: Vec<WireId>,
        function: Vec<u16>,
        use_ops: Vec<ProtectedUse>,
    },
}

// Raw IR is untrusted. A depth check in the verifier prevents recursive
// traversal, and this iterative destructor prevents rejection itself from
// recursively dropping an adversarially deep branch tree.
impl Drop for RawOp {
    fn drop(&mut self) {
        let mut pending = Vec::new();
        if let Self::ClassicalBranch {
            then_ops, else_ops, ..
        } = self
        {
            pending.append(then_ops);
            pending.append(else_ops);
        }
        while let Some(mut op) = pending.pop() {
            if let Self::ClassicalBranch {
                then_ops, else_ops, ..
            } = &mut op
            {
                pending.append(then_ops);
                pending.append(else_ops);
            }
            // `op` now has empty child vectors, so its own Drop does not
            // recurse; its ordinary fields are released here.
        }
    }
}
