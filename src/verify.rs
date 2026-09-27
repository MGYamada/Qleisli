use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

use crate::contract::exact::Budget;

use crate::ir::{
    BasisShape, CircuitAction, CircuitStep, ClassicalId, ClassicalPhi, Control, Effect,
    ProtectedBit, ProtectedRegion, ProtectedUse, QuantumPhi, RawOp, RawProgram, SingleGate,
    TargetTransition, TokenId, UnitaryStep, WireId,
};

const MAX_REGISTER_BITS: u8 = 12;
const MAX_NESTED_BRANCHES: usize = 64;

/// An accepted raw program. Its fields are private; only `verify` can create it.
#[derive(Clone, Debug)]
pub struct VerifiedProgram {
    program: RawProgram,
    derived_effect: Effect,
}

impl VerifiedProgram {
    pub fn program(&self) -> &RawProgram {
        &self.program
    }

    pub fn raw(&self) -> &RawProgram {
        &self.program
    }

    pub fn derived_effect(&self) -> Effect {
        self.derived_effect
    }
}

/// `path` is an operation-index path. In a branch, 0 or 1 after the branch
/// index selects the then or else arm.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ValidationError {
    pub path: Vec<usize>,
    pub message: String,
}

impl fmt::Display for ValidationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.path.is_empty() {
            write!(f, "IR: {}", self.message)
        } else {
            write!(f, "IR at {:?}: {}", self.path, self.message)
        }
    }
}

impl std::error::Error for ValidationError {}

fn err(path: &[usize], message: impl Into<String>) -> ValidationError {
    ValidationError {
        path: path.to_vec(),
        message: message.into(),
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct Register {
    wires: Vec<WireId>,
}

impl Register {
    fn shape(&self) -> BasisShape {
        BasisShape {
            bits: self.wires.len() as u8,
        }
    }
}

#[derive(Clone, Debug)]
struct State {
    live: BTreeMap<TokenId, Register>,
    live_wires: BTreeSet<WireId>,
    effect: Effect,
}

/// Freshness and classical definitions span both arms of every branch. These
/// grow with the program and must never be copied for each branch.
#[derive(Debug)]
struct Global<'a> {
    seen_tokens: BTreeSet<TokenId>,
    seen_wires: BTreeSet<WireId>,
    classical_scopes: BTreeMap<ClassicalId, usize>,
    active_scopes: BTreeSet<usize>,
    current_scope: usize,
    next_scope: usize,
    contract_budget: &'a mut Budget,
}

impl Default for State {
    fn default() -> Self {
        Self {
            live: BTreeMap::new(),
            live_wires: BTreeSet::new(),
            effect: Effect::Unitary,
        }
    }
}

impl<'a> Global<'a> {
    fn new(contract_budget: &'a mut Budget) -> Self {
        Self {
            seen_tokens: BTreeSet::new(),
            seen_wires: BTreeSet::new(),
            classical_scopes: BTreeMap::new(),
            active_scopes: BTreeSet::from([0]),
            current_scope: 0,
            next_scope: 1,
            contract_budget,
        }
    }
}

impl Global<'_> {
    fn reserve_wire(&mut self, wire: WireId, path: &[usize]) -> Result<(), ValidationError> {
        if !self.seen_wires.insert(wire) {
            return Err(err(path, format!("wire {:?} is not globally fresh", wire)));
        }
        Ok(())
    }

    fn insert_classical(&mut self, id: ClassicalId, path: &[usize]) -> Result<(), ValidationError> {
        if self
            .classical_scopes
            .insert(id, self.current_scope)
            .is_some()
        {
            return Err(err(
                path,
                format!("classical SSA value {:?} is not fresh", id),
            ));
        }
        Ok(())
    }

    fn require_classical(&self, id: ClassicalId, path: &[usize]) -> Result<(), ValidationError> {
        if !self.is_classical_visible(id) {
            return Err(err(
                path,
                format!("classical bit {:?} was not defined in this scope", id),
            ));
        }
        Ok(())
    }

    fn is_classical_visible(&self, id: ClassicalId) -> bool {
        self.classical_scopes
            .get(&id)
            .is_some_and(|scope| self.active_scopes.contains(scope))
    }

    fn is_classical_visible_in_arm(&self, id: ClassicalId, arm_scope: usize) -> bool {
        self.classical_scopes
            .get(&id)
            .is_some_and(|scope| *scope == arm_scope || self.active_scopes.contains(scope))
    }

    fn enter_scope(&mut self) -> (usize, usize) {
        let parent = self.current_scope;
        let scope = self.next_scope;
        self.next_scope += 1;
        self.current_scope = scope;
        self.active_scopes.insert(scope);
        (parent, scope)
    }

    fn leave_scope(&mut self, parent: usize, scope: usize) {
        self.active_scopes.remove(&scope);
        self.current_scope = parent;
    }
}

impl State {
    fn insert_token(
        &mut self,
        global: &mut Global,
        token: TokenId,
        register: Register,
        path: &[usize],
    ) -> Result<(), ValidationError> {
        if register.wires.len() > usize::from(MAX_REGISTER_BITS) {
            return Err(err(path, "register exceeds the initial 12-bit IR limit"));
        }
        let mut local = BTreeSet::new();
        for wire in &register.wires {
            if !local.insert(*wire) || self.live_wires.contains(wire) {
                return Err(err(path, format!("quantum wire {:?} is live twice", wire)));
            }
        }
        if !global.seen_tokens.insert(token) {
            return Err(err(path, format!("token {:?} is not fresh", token)));
        }
        self.live_wires.extend(register.wires.iter().copied());
        self.live.insert(token, register);
        Ok(())
    }

    fn consume(
        &mut self,
        tokens: &[TokenId],
        path: &[usize],
    ) -> Result<Vec<Register>, ValidationError> {
        let mut unique = BTreeSet::new();
        for token in tokens {
            if !unique.insert(*token) {
                return Err(err(path, format!("token {:?} used twice", token)));
            }
            if !self.live.contains_key(token) {
                return Err(err(
                    path,
                    format!("token {:?} is unavailable or already consumed", token),
                ));
            }
        }
        let registers: Vec<_> = tokens
            .iter()
            .map(|token| self.live.remove(token).expect("checked present"))
            .collect();
        for register in &registers {
            for wire in &register.wires {
                self.live_wires.remove(wire);
            }
        }
        Ok(registers)
    }

    fn verify_ops(
        &mut self,
        global: &mut Global,
        operations: &[RawOp],
        prefix: &[usize],
    ) -> Result<(), ValidationError> {
        for (index, operation) in operations.iter().enumerate() {
            let mut path = prefix.to_vec();
            path.push(index);
            self.verify_op(global, operation, &path)?;
        }
        Ok(())
    }

    fn verify_op(
        &mut self,
        global: &mut Global,
        operation: &RawOp,
        path: &[usize],
    ) -> Result<(), ValidationError> {
        if path.len() > 2 * MAX_NESTED_BRANCHES + 1 {
            return Err(err(
                path,
                "nested branch exceeds the initial IR depth limit",
            ));
        }
        match operation {
            RawOp::CertifiedCompute {
                source,
                source_out,
                ancilla_wires,
                function,
                use_steps,
                logical_steps,
            } => {
                let reg = self.consume(&[*source], path)?.pop().expect("one input");
                if ancilla_wires.len() != 1 {
                    return Err(err(
                        path,
                        "semantic contract requires exactly one computed bit",
                    ));
                }
                for wire in ancilla_wires {
                    global.reserve_wire(*wire, path)?;
                }
                crate::contract::check_computed_diagnostic_with_budget(
                    reg.wires.len(),
                    function,
                    use_steps,
                    logical_steps,
                    global.contract_budget,
                )
                .map_err(|error| err(path, format!("semantic contract: {error}")))?;
                self.insert_token(global, *source_out, reg, path)?;
            }
            RawOp::ApplyUnitary {
                input,
                output,
                steps,
            } => {
                let reg = self.consume(&[*input], path)?.pop().expect("one input");
                check_circuit(steps, reg.wires.len(), path)?;
                self.insert_token(global, *output, reg, path)?;
            }
            RawOp::Init0 { output, wire } => {
                global.reserve_wire(*wire, path)?;
                self.insert_token(global, *output, Register { wires: vec![*wire] }, path)?;
                self.effect = self.effect.max(Effect::Iso);
            }
            RawOp::Gate { input, output, .. } => {
                let mut regs = self.consume(&[*input], path)?;
                let reg = regs.pop().expect("one input");
                require_width(&reg, 1, path)?;
                self.insert_token(global, *output, reg, path)?;
            }
            RawOp::Cnot {
                control,
                target,
                control_out,
                target_out,
            } => {
                let regs = self.consume(&[*control, *target], path)?;
                for reg in &regs {
                    require_width(reg, 1, path)?;
                }
                self.insert_token(global, *control_out, regs[0].clone(), path)?;
                self.insert_token(global, *target_out, regs[1].clone(), path)?;
            }
            RawOp::Toffoli {
                control_a,
                control_b,
                target,
                control_a_out,
                control_b_out,
                target_out,
            } => {
                let regs = self.consume(&[*control_a, *control_b, *target], path)?;
                for reg in &regs {
                    require_width(reg, 1, path)?;
                }
                for (out, reg) in [*control_a_out, *control_b_out, *target_out]
                    .into_iter()
                    .zip(regs)
                {
                    self.insert_token(global, out, reg, path)?;
                }
            }
            RawOp::QuantumIf {
                control,
                target,
                control_out,
                target_out,
                zero_ops,
                one_ops,
            } => {
                let regs = self.consume(&[*control, *target], path)?;
                require_width(&regs[0], 1, path)?;
                let target_width = regs[1].wires.len();
                check_unitary_steps(zero_ops, target_width, path)?;
                check_unitary_steps(one_ops, target_width, path)?;
                self.insert_token(global, *control_out, regs[0].clone(), path)?;
                self.insert_token(global, *target_out, regs[1].clone(), path)?;
            }
            RawOp::Split {
                input,
                left,
                right,
                left_bits,
            } => {
                let mut regs = self.consume(&[*input], path)?;
                let reg = regs.pop().expect("one input");
                let split = usize::from(*left_bits);
                if split > reg.wires.len() {
                    return Err(err(path, "split exceeds the input register width"));
                }
                self.insert_token(
                    global,
                    *left,
                    Register {
                        wires: reg.wires[..split].to_vec(),
                    },
                    path,
                )?;
                self.insert_token(
                    global,
                    *right,
                    Register {
                        wires: reg.wires[split..].to_vec(),
                    },
                    path,
                )?;
            }
            RawOp::Join {
                left,
                right,
                output,
            } => {
                let regs = self.consume(&[*left, *right], path)?;
                let wires = regs.into_iter().flat_map(|r| r.wires).collect();
                self.insert_token(global, *output, Register { wires }, path)?;
            }
            RawOp::LiftBasis {
                input,
                output,
                output_wires,
                table,
            } => {
                let mut regs = self.consume(&[*input], path)?;
                let reg = regs.pop().expect("one input");
                let input_width = reg.wires.len();
                let output_width = output_wires.len();
                if output_width > usize::from(MAX_REGISTER_BITS) {
                    return Err(err(path, "lift output exceeds the initial 12-bit IR limit"));
                }
                if output_width < input_width || !output_wires.starts_with(&reg.wires) {
                    return Err(err(
                        path,
                        "lift must preserve its ordered input wires and may append fresh wires",
                    ));
                }
                check_table(table, input_width, output_width, true, path)?;
                for wire in &output_wires[input_width..] {
                    global.reserve_wire(*wire, path)?;
                }
                self.insert_token(
                    global,
                    *output,
                    Register {
                        wires: output_wires.clone(),
                    },
                    path,
                )?;
                if output_width > input_width {
                    self.effect = self.effect.max(Effect::Iso);
                }
            }
            RawOp::MeasureZ { input, output } => {
                let mut regs = self.consume(&[*input], path)?;
                require_width(&regs.pop().expect("one input"), 1, path)?;
                global.insert_classical(*output, path)?;
                self.effect = Effect::Observe;
            }
            RawOp::Reset {
                input,
                output,
                fresh_wire,
            } => {
                let mut regs = self.consume(&[*input], path)?;
                require_width(&regs.pop().expect("one input"), 1, path)?;
                global.reserve_wire(*fresh_wire, path)?;
                self.insert_token(
                    global,
                    *output,
                    Register {
                        wires: vec![*fresh_wire],
                    },
                    path,
                )?;
                self.effect = Effect::Observe;
            }
            RawOp::Discard { input } => {
                self.consume(&[*input], path)?;
                self.effect = Effect::Observe;
            }
            RawOp::ClassicalConst { output, .. } => {
                global.insert_classical(*output, path)?;
            }
            RawOp::ClassicalNot { input, output } => {
                global.require_classical(*input, path)?;
                global.insert_classical(*output, path)?;
            }
            RawOp::ClassicalXor {
                left,
                right,
                output,
            }
            | RawOp::ClassicalAnd {
                left,
                right,
                output,
            } => {
                global.require_classical(*left, path)?;
                global.require_classical(*right, path)?;
                global.insert_classical(*output, path)?;
            }
            RawOp::ClassicalBranch {
                condition,
                then_ops,
                else_ops,
                quantum_phis,
                classical_phis,
            } => self.verify_branch(
                global,
                *condition,
                then_ops,
                else_ops,
                quantum_phis,
                classical_phis,
                path,
            )?,
            RawOp::ComputeUseUncompute {
                source,
                source_out,
                targets,
                ancilla_wires,
                function,
                use_ops,
            } => self.verify_compute(
                global,
                *source,
                *source_out,
                targets,
                ancilla_wires,
                function,
                use_ops,
                path,
            )?,
        }
        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    fn verify_branch(
        &mut self,
        global: &mut Global,
        condition: ClassicalId,
        then_ops: &[RawOp],
        else_ops: &[RawOp],
        quantum_phis: &[QuantumPhi],
        classical_phis: &[ClassicalPhi],
        path: &[usize],
    ) -> Result<(), ValidationError> {
        global.require_classical(condition, path)?;

        let mut then_state = self.clone();
        let mut then_path = path.to_vec();
        then_path.push(0);
        let (parent, then_scope) = global.enter_scope();
        let then_result = then_state.verify_ops(global, then_ops, &then_path);
        global.leave_scope(parent, then_scope);
        then_result?;

        let mut else_state = self.clone();
        // SSA IDs are globally fresh, including across mutually exclusive arms.
        let mut else_path = path.to_vec();
        else_path.push(1);
        let (parent, else_scope) = global.enter_scope();
        let else_result = else_state.verify_ops(global, else_ops, &else_path);
        global.leave_scope(parent, else_scope);
        else_result?;

        let mut then_covered = BTreeSet::new();
        let mut else_covered = BTreeSet::new();
        for phi in quantum_phis {
            let then_reg = then_state.live.get(&phi.then_token).ok_or_else(|| {
                err(
                    path,
                    format!("then phi token {:?} is not live", phi.then_token),
                )
            })?;
            let else_reg = else_state.live.get(&phi.else_token).ok_or_else(|| {
                err(
                    path,
                    format!("else phi token {:?} is not live", phi.else_token),
                )
            })?;
            if !then_covered.insert(phi.then_token) || !else_covered.insert(phi.else_token) {
                return Err(err(path, "a branch quantum output is merged twice"));
            }
            if then_reg.shape() != else_reg.shape()
                || phi.output_wires.len() != then_reg.wires.len()
            {
                return Err(err(path, "branch quantum output shapes do not match"));
            }
        }
        if then_covered.len() != then_state.live.len()
            || else_covered.len() != else_state.live.len()
        {
            return Err(err(path, "a branch leaves an unmerged quantum token"));
        }

        self.effect = then_state.effect.max(else_state.effect);
        self.live.clear();
        self.live_wires.clear();
        for phi in quantum_phis {
            for wire in &phi.output_wires {
                global.reserve_wire(*wire, path)?;
            }
            self.insert_token(
                global,
                phi.output,
                Register {
                    wires: phi.output_wires.clone(),
                },
                path,
            )?;
        }
        for phi in classical_phis {
            if !global.is_classical_visible_in_arm(phi.then_id, then_scope)
                || !global.is_classical_visible_in_arm(phi.else_id, else_scope)
            {
                return Err(err(path, "classical phi references an undefined arm value"));
            }
        }
        // Phi inputs are simultaneous: no output of this merge is available
        // in either arm, including outputs listed earlier in this same merge.
        for phi in classical_phis {
            global.insert_classical(phi.output, path)?;
        }
        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    fn verify_compute(
        &mut self,
        global: &mut Global,
        source: TokenId,
        source_out: TokenId,
        targets: &[TargetTransition],
        ancilla_wires: &[WireId],
        function: &[u16],
        use_ops: &[ProtectedUse],
        path: &[usize],
    ) -> Result<(), ValidationError> {
        let mut inputs = vec![source];
        inputs.extend(targets.iter().map(|target| target.input));
        let regs = self.consume(&inputs, path)?;
        let source_reg = &regs[0];
        let source_width = source_reg.wires.len();
        let ancilla_width = ancilla_wires.len();
        if ancilla_width > usize::from(MAX_REGISTER_BITS) {
            return Err(err(
                path,
                "computed ancilla exceeds the initial 12-bit IR limit",
            ));
        }
        check_table(function, source_width, ancilla_width, false, path)?;
        for target_reg in &regs[1..] {
            require_width(target_reg, 1, path)?;
        }
        for wire in ancilla_wires {
            global.reserve_wire(*wire, path)?;
        }
        for use_op in use_ops {
            match use_op {
                ProtectedUse::ProtectedGate { bit, gate } => {
                    check_protected_bit(*bit, source_width, ancilla_width, path)?;
                    if !matches!(gate, SingleGate::Z | SingleGate::T) {
                        return Err(err(
                            path,
                            "use gate changes a protected basis label; zero return is unproved",
                        ));
                    }
                }
                ProtectedUse::ControlledTargetGate {
                    controls,
                    target_index,
                    ..
                } => {
                    if *target_index >= targets.len() {
                        return Err(err(path, "controlled gate target is out of range"));
                    }
                    check_controls(controls, source_width, ancilla_width, path)?;
                }
                ProtectedUse::ControlledPhase { controls, .. } => {
                    check_controls(controls, source_width, ancilla_width, path)?;
                }
            }
        }
        self.insert_token(global, source_out, source_reg.clone(), path)?;
        for (target, reg) in targets.iter().zip(&regs[1..]) {
            self.insert_token(global, target.output, reg.clone(), path)?;
        }
        Ok(())
    }
}

fn require_width(reg: &Register, width: usize, path: &[usize]) -> Result<(), ValidationError> {
    if reg.wires.len() != width {
        return Err(err(
            path,
            format!("operation requires a {width}-bit register"),
        ));
    }
    Ok(())
}

pub(crate) fn check_circuit(
    steps: &[CircuitStep],
    width: usize,
    path: &[usize],
) -> Result<(), ValidationError> {
    for step in steps {
        let mut seen = BTreeSet::new();
        let mut axis = |index| {
            if index >= width || !seen.insert(index) {
                Err(err(
                    path,
                    "circuit axis is out of range or overlaps another axis/control",
                ))
            } else {
                Ok(())
            }
        };
        for control in &step.controls {
            axis(control.index)?;
        }
        match &step.action {
            CircuitAction::Contract {
                indices, evidence, ..
            } => {
                let expected = evidence
                    .signature()
                    .bits()
                    .map_err(|error| err(path, error.to_string()))?;
                if indices.len() != expected {
                    return Err(err(
                        path,
                        "contract application does not match its owned interface",
                    ));
                }
                for index in indices {
                    axis(*index)?;
                }
            }
            CircuitAction::Hadamard { target } => axis(*target)?,
            CircuitAction::Monomial {
                indices,
                permutation,
                phases,
            } => {
                for index in indices {
                    axis(*index)?;
                }
                check_table(permutation, indices.len(), indices.len(), true, path)?;
                if phases.len() != permutation.len() || phases.iter().any(|phase| *phase >= 8) {
                    return Err(err(
                        path,
                        "circuit phase table must be total with exponents in 0..8",
                    ));
                }
            }
        }
    }
    Ok(())
}

fn check_unitary_steps(
    steps: &[UnitaryStep],
    target_width: usize,
    path: &[usize],
) -> Result<(), ValidationError> {
    let check_index = |index: usize| {
        if index >= target_width {
            Err(err(path, "qif target index is out of range"))
        } else {
            Ok(())
        }
    };
    for step in steps {
        match step {
            UnitaryStep::Gate { target_index, .. } => check_index(*target_index)?,
            UnitaryStep::Cnot {
                control_index,
                target_index,
            } => {
                check_index(*control_index)?;
                check_index(*target_index)?;
                if control_index == target_index {
                    return Err(err(path, "qif CNOT uses one target bit twice"));
                }
            }
            UnitaryStep::Toffoli {
                control_a_index,
                control_b_index,
                target_index,
            } => {
                check_index(*control_a_index)?;
                check_index(*control_b_index)?;
                check_index(*target_index)?;
                if control_a_index == control_b_index
                    || control_a_index == target_index
                    || control_b_index == target_index
                {
                    return Err(err(path, "qif Toffoli uses one target bit twice"));
                }
            }
            UnitaryStep::ScalarPhase(_) => {}
        }
    }
    Ok(())
}

fn check_table(
    table: &[u16],
    input_width: usize,
    output_width: usize,
    require_injective: bool,
    path: &[usize],
) -> Result<(), ValidationError> {
    let expected = 1usize
        .checked_shl(input_width as u32)
        .ok_or_else(|| err(path, "basis table input dimension overflows"))?;
    if table.len() != expected {
        return Err(err(path, "basis table is not total on its input"));
    }
    let output_size = 1usize
        .checked_shl(output_width as u32)
        .ok_or_else(|| err(path, "basis table output dimension overflows"))?;
    let mut seen = BTreeSet::new();
    for output in table {
        if usize::from(*output) >= output_size {
            return Err(err(
                path,
                "basis table output is outside its declared shape",
            ));
        }
        if require_injective && !seen.insert(*output) {
            return Err(err(path, "basis lift is not injective"));
        }
    }
    Ok(())
}

fn check_protected_bit(
    bit: ProtectedBit,
    source_width: usize,
    ancilla_width: usize,
    path: &[usize],
) -> Result<(), ValidationError> {
    let limit = match bit.region {
        ProtectedRegion::Source => source_width,
        ProtectedRegion::Ancilla => ancilla_width,
    };
    if usize::from(bit.index) >= limit {
        return Err(err(path, "protected bit index is out of range"));
    }
    Ok(())
}

fn check_controls(
    controls: &[Control],
    source_width: usize,
    ancilla_width: usize,
    path: &[usize],
) -> Result<(), ValidationError> {
    let mut seen = BTreeSet::new();
    for control in controls {
        check_protected_bit(control.bit, source_width, ancilla_width, path)?;
        let key = (
            match control.bit.region {
                ProtectedRegion::Source => 0,
                ProtectedRegion::Ancilla => 1,
            },
            control.bit.index,
        );
        if !seen.insert(key) {
            return Err(err(path, "a protected bit is used twice as a control"));
        }
    }
    Ok(())
}

/// Recheck every constructor, SSA reference, live wire, effect, and restricted
/// `ComputeUseUncompute` proof from the untrusted raw IR.
pub fn verify(program: RawProgram) -> Result<VerifiedProgram, ValidationError> {
    let mut budget = Budget::new(crate::contract::DEFAULT_EXACT_WORK);
    verify_with_budget(program, &mut budget)
}

pub(crate) fn verify_with_budget(
    program: RawProgram,
    budget: &mut Budget,
) -> Result<VerifiedProgram, ValidationError> {
    let mut state = State::default();
    let mut global = Global::new(budget);
    let mut input_bits = 0usize;
    for port in &program.quantum_inputs {
        if port.shape.bits > MAX_REGISTER_BITS || port.wires.len() != usize::from(port.shape.bits) {
            return Err(err(
                &[],
                "quantum input does not match its finite basis shape",
            ));
        }
        for wire in &port.wires {
            global.reserve_wire(*wire, &[])?;
        }
        state.insert_token(
            &mut global,
            port.token,
            Register {
                wires: port.wires.clone(),
            },
            &[],
        )?;
        input_bits += port.wires.len();
    }
    for id in &program.classical_inputs {
        global.insert_classical(*id, &[])?;
    }
    state.verify_ops(&mut global, &program.operations, &[])?;

    let mut outputs = BTreeSet::new();
    for token in &program.quantum_outputs {
        if !outputs.insert(*token) {
            return Err(err(
                &[],
                format!("quantum output {:?} is listed twice", token),
            ));
        }
        if !state.live.contains_key(token) {
            return Err(err(&[], format!("quantum output {:?} is not live", token)));
        }
    }
    if outputs.len() != state.live.len() {
        return Err(err(&[], "live quantum ownership was omitted from outputs"));
    }
    for id in &program.classical_outputs {
        global.require_classical(*id, &[])?;
    }
    if state.effect > program.declared_effect {
        return Err(err(
            &[],
            format!(
                "declared {:?} effect is stronger than derived {:?} effect",
                program.declared_effect, state.effect
            ),
        ));
    }
    let output_bits = state
        .live
        .values()
        .map(|reg| reg.wires.len())
        .sum::<usize>();
    if program.declared_effect == Effect::Unitary && input_bits != output_bits {
        return Err(err(&[], "unitary function changes quantum dimension"));
    }
    Ok(VerifiedProgram {
        program,
        derived_effect: state.effect,
    })
}
