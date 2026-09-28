use super::profile::{Gate, TerminalCircuit};
use std::collections::BTreeSet;
use std::fmt::Write;

fn pointer(index: usize) -> String {
    if index == 0 {
        "ptr null".to_owned()
    } else {
        format!("ptr inttoptr (i64 {index} to ptr)")
    }
}

fn symbol(gate: Gate) -> String {
    let name = match gate {
        Gate::Cx => "cnot__body",
        Gate::Sdg => "s__adj",
        Gate::Tdg => "t__adj",
        _ => return format!("__quantum__qis__{}__body", gate.name()),
    };
    format!("__quantum__qis__{name}")
}

pub(super) fn write(circuit: &TerminalCircuit) -> String {
    let mut out =
        String::from("; Qleisli terminal profile v1; QIR 2.0 Base; explicit QIS required.\n");
    let labels = std::iter::once("result".to_owned())
        .chain((0..circuit.measurements.len()).map(|i| format!("bit.{i}")))
        .collect::<Vec<_>>();
    for (i, label) in labels.iter().enumerate() {
        writeln!(
            out,
            "@label.{i} = private constant [{} x i8] c\"{label}\\00\"",
            label.len() + 1
        )
        .unwrap();
    }
    out.push_str("\ndefine i64 @main() #0 {\nentry:\n  call void @__quantum__rt__initialize(ptr null)\n  br label %body\nbody:\n");
    let mut declarations = BTreeSet::new();
    for op in &circuit.gates {
        let symbol = symbol(op.gate);
        let args = op
            .wires
            .iter()
            .map(|q| pointer(*q))
            .collect::<Vec<_>>()
            .join(", ");
        writeln!(out, "  call void @{symbol}({args})").unwrap();
        declarations.insert(format!(
            "declare void @{symbol}({})",
            vec!["ptr"; op.wires.len()].join(", ")
        ));
    }
    out.push_str("  br label %measurements\nmeasurements:\n");
    for (i, q) in circuit.measurements.iter().enumerate() {
        writeln!(
            out,
            "  call void @__quantum__qis__mz__body({}, {})",
            pointer(*q),
            pointer(i)
        )
        .unwrap();
    }
    out.push_str("  br label %output\noutput:\n");
    writeln!(
        out,
        "  call void @__quantum__rt__array_record_output(i64 {}, ptr @label.0)",
        circuit.measurements.len()
    )
    .unwrap();
    for i in 0..circuit.measurements.len() {
        writeln!(
            out,
            "  call void @__quantum__rt__result_record_output({}, ptr @label.{})",
            pointer(i),
            i + 1
        )
        .unwrap();
    }
    out.push_str("  ret i64 0\n}\n\ndeclare void @__quantum__rt__initialize(ptr)\ndeclare void @__quantum__qis__mz__body(ptr, ptr writeonly) #1\ndeclare void @__quantum__rt__array_record_output(i64, ptr)\ndeclare void @__quantum__rt__result_record_output(ptr, ptr)\n");
    for declaration in declarations {
        writeln!(out, "{declaration}").unwrap();
    }
    writeln!(out, "\nattributes #0 = {{ \"entry_point\" \"qir_profiles\"=\"base_profile\" \"output_labeling_schema\"=\"qleisli.bit-vector.v1\" \"required_num_qubits\"=\"{}\" \"required_num_results\"=\"{}\" }}", circuit.qubits, circuit.measurements.len()).unwrap();
    out.push_str("attributes #1 = { \"irreversible\" }\n\n!llvm.module.flags = !{!0, !1, !2, !3}\n!0 = !{i32 1, !\"qir_major_version\", i32 2}\n!1 = !{i32 7, !\"qir_minor_version\", i32 0}\n!2 = !{i32 1, !\"dynamic_qubit_management\", i1 false}\n!3 = !{i32 1, !\"dynamic_result_management\", i1 false}\n");
    out
}
