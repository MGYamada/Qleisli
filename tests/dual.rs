use qleisli::interchange::dual::Kernel;

#[test]
#[ignore = "requires the freshly built native Lean checker"]
fn dual_report_retains_the_exact_artifact_request_and_reconstructed_program() {
    let kernel =
        Kernel::new(std::env::var_os("QLEISLI_DUAL_KERNEL").expect("explicit native checker"));
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
