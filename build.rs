// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
fn main() {
    println!("cargo:rustc-check-cfg=cfg(qleisli_native_tests)");
    println!("cargo:rerun-if-env-changed=QLEISLI_KERNEL");
    if std::env::var_os("QLEISLI_KERNEL").is_some_and(|path| !path.is_empty()) {
        println!("cargo:rustc-cfg=qleisli_native_tests");
    }
}
