use qleisli::contract::{BasisType, FunctionEvidence, FunctionIdentity, DEFAULT_EXACT_WORK};
use qleisli::contract::exact::Budget;
use qleisli::ir::*;
fn identity() -> RawProgram {
    RawProgram { quantum_inputs: vec![QuantumPort {token: TokenId(0), wires: vec![], shape: BasisShape::UNIT}], classical_inputs: vec![], operations: vec![], quantum_outputs: vec![TokenId(0)], classical_outputs: vec![], declared_effect: Effect::Unitary }
}
fn main() {
    let depth: usize = std::env::args().nth(1).unwrap().parse().unwrap();
    std::thread::spawn(move || {
        let mut body = vec![];
        for _ in 0..depth { body = vec![RawOp::ClassicalBranch {condition: ClassicalId(0), then_ops: body, else_ops: vec![], quantum_phis: vec![], classical_phis: vec![]}]; }
        let mut implementation = identity();
        implementation.operations = body;
        eprintln!("Calling FunctionEvidence::check with {depth} branch levels, zero qubits");
        if std::env::var_os("REVIEW_DIRECT_RAW").is_some() {
            let result = qleisli::interchange::native::Kernel::selected().unwrap().accept_raw(implementation);
            eprintln!("direct_raw_result={result:?}");
            return;
        }
        let result = FunctionEvidence::check(BasisType::Unit, implementation, identity(), FunctionIdentity {implementation: "impl".into(), specification: "spec".into(), sources: vec![]}, &mut Budget::new(DEFAULT_EXACT_WORK));
        eprintln!("result={result:?}");
    }).join().unwrap();
}
