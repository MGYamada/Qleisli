use qleisli::contract::{BasisType, FunctionEvidence, FunctionIdentity, ContractError};
use qleisli::contract::exact::Budget;
use qleisli::ir::*;

fn main() {
    let retained = BasisType::Tuple(vec![BasisType::Bit; 3]);
    let expected = BasisType::pair(BasisType::Bit, BasisType::pair(BasisType::Bit, BasisType::Bit));
    let program = RawProgram {
        quantum_inputs: vec![QuantumPort {
            token: TokenId(0), wires: vec![WireId(0), WireId(1), WireId(2)],
            shape: BasisShape { bits: 3 },
        }],
        classical_inputs: vec![], operations: vec![], quantum_outputs: vec![TokenId(0)],
        classical_outputs: vec![], declared_effect: Effect::Unitary,
    };
    let identity = FunctionIdentity {
        implementation: "attachment::identity".into(),
        specification: "reference::identity".into(),
        sources: vec![("attachment".into(), "independent three-bit identity".into())],
    };
    let receipt = FunctionEvidence::check(retained, program.clone(), program.clone(), identity.clone(),
        &mut Budget::new(100_000_000)).unwrap();
    assert_eq!(receipt.signature().bits().unwrap(), expected.bits().unwrap());
    assert_ne!(receipt.signature(), &expected);
    let result = receipt.check_binding(&expected, &identity, &program, &program);
    println!("same_width=true different_tree=true binding={result:?}");
    assert_eq!(result, Err(ContractError::EvidenceMismatch));
    assert_eq!(receipt.check_binding(receipt.signature(), &identity, &program, &program), Ok(()));
}
