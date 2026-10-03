use qleisli::interchange::native::Kernel;

#[test]
fn raw_transport_rejects_excessive_nesting_before_serialization() {
    use qleisli::contract::BasisType;
    use qleisli::interchange::{RootInterface, Version};
    use qleisli::ir::{ClassicalId, Effect, RawOp, RawProgram};
    let kernel = Kernel::new("/missing-explicit-native-kernel");
    let mut program = RawProgram {
        quantum_inputs: vec![],
        classical_inputs: vec![],
        operations: vec![],
        quantum_outputs: vec![],
        classical_outputs: vec![],
        declared_effect: Effect::Unitary,
    };
    for _ in 0..65 {
        program.operations = vec![RawOp::ClassicalBranch {
            condition: ClassicalId(0),
            then_ops: std::mem::take(&mut program.operations),
            else_ops: vec![],
            quantum_phis: vec![],
            classical_phis: vec![],
        }];
    }
    assert_eq!(kernel.verify(&program).unwrap_err().code, "limit");
    program.operations.clear();
    let mut input = BasisType::Unit;
    for _ in 0..33 {
        input = BasisType::pair(input, BasisType::Unit);
    }
    let interface = RootInterface {
        input,
        output: BasisType::Unit,
    };
    assert_eq!(
        kernel
            .check_raw(&program, Some(&interface), Version::V2, None)
            .unwrap_err()
            .code,
        "limit"
    );
}

#[test]
#[ignore = "requires the freshly built native Lean checker"]
fn native_report_retains_the_exact_artifact_request_and_reconstructed_program() {
    let kernel = Kernel::new(std::env::var_os("QLEISLI_KERNEL").expect("explicit native checker"));
    let mut bytes = include_bytes!("fixtures/verification_v022/finite/t.v2.qirf").to_vec();
    let mut request = br#"{"format":"qleisli.request","version":1,"signature":{"tag":"bit"},"meaning":{"tag":"phase8","table":[0,1]},"source_snapshot":null}"#.to_vec();
    let checked = kernel.check(&bytes, Some(&request)).unwrap();
    let before = checked.program().raw().clone();
    bytes.fill(0);
    request.fill(0);
    assert!(checked.artifact().starts_with(b"{\"evidence\""));
    assert!(checked.request().unwrap().starts_with(b"{\"format\""));
    assert!(checked.imported().request_checked);
    assert!(checked.native_exact_work() > 0);
    assert_eq!(checked.program().raw(), &before);
    assert!(kernel.check(&bytes, Some(&request)).is_err());
    assert!(kernel.check(checked.artifact(), Some(b"")).is_err());
    assert_eq!(checked.into_program().raw(), &before);
}

#[test]
#[ignore = "requires the freshly built native Lean checker"]
fn raw_exports_conversions_and_native_reports_share_the_original_byte_gate() {
    use qleisli::contract::BasisType;
    use qleisli::interchange::{self, RootInterface, Version};
    use qleisli::ir::{RawOp, TokenId};
    let kernel = Kernel::new(std::env::var_os("QLEISLI_KERNEL").unwrap());
    let bytes = include_bytes!("fixtures/verification_v022/finite/t.v2.qirf");
    let program = interchange::import(bytes, None).unwrap().program;
    let request = br#"{"format":"qleisli.request","version":1,"signature":{"tag":"bit"},"meaning":{"tag":"phase8","table":[0,1]},"source_snapshot":null}"#;
    let interface = RootInterface {
        input: BasisType::Bit,
        output: BasisType::Bit,
    };
    let checked = kernel
        .check_raw(program.raw(), Some(&interface), Version::V2, Some(request))
        .unwrap();
    let native = kernel
        .inspect(checked.artifact(), checked.request())
        .unwrap();
    assert_eq!(native.artifact(), checked.artifact());
    assert_eq!(native.request(), checked.request());
    assert_eq!(native.exact_work(), checked.native_exact_work());
    for version in [Version::V1, Version::V2] {
        let converted = kernel
            .convert(checked.artifact(), version, Some(request))
            .unwrap();
        assert_eq!(converted.program().raw(), program.raw());
    }
    assert_eq!(
        kernel.verify(program.raw()).unwrap().program().raw(),
        program.raw()
    );
    assert_eq!(
        kernel.check_program(&program).unwrap().program().raw(),
        program.raw()
    );
    assert_eq!(
        kernel
            .check_with_meanings(&program, Some(&interface), &[], Some(request))
            .unwrap()
            .program()
            .raw(),
        program.raw()
    );
    let mut invalid = program.raw().clone();
    invalid
        .operations
        .push(RawOp::Discard { input: TokenId(0) });
    assert!(kernel.verify(&invalid).is_err());
    let mut wrong = request.to_vec();
    let offset = wrong.windows(3).position(|w| w == b"0,1").unwrap();
    wrong[offset] = b'4';
    assert!(
        kernel
            .check_raw(program.raw(), Some(&interface), Version::V2, Some(&wrong))
            .is_err()
    );
}
