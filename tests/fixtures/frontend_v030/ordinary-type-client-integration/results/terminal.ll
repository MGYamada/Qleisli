; Qleisli terminal profile v1; QIR 2.0 Base; explicit QIS required.
@label.0 = private constant [7 x i8] c"result\00"
@label.1 = private constant [6 x i8] c"bit.0\00"
@label.2 = private constant [6 x i8] c"bit.1\00"

define i64 @main() #0 {
entry:
  call void @__quantum__rt__initialize(ptr null)
  br label %body
body:
  call void @__quantum__qis__h__body(ptr null)
  call void @__quantum__qis__cnot__body(ptr null, ptr inttoptr (i64 1 to ptr))
  br label %measurements
measurements:
  call void @__quantum__qis__mz__body(ptr inttoptr (i64 1 to ptr), ptr null)
  call void @__quantum__qis__mz__body(ptr null, ptr inttoptr (i64 1 to ptr))
  br label %output
output:
  call void @__quantum__rt__array_record_output(i64 2, ptr @label.0)
  call void @__quantum__rt__result_record_output(ptr null, ptr @label.1)
  call void @__quantum__rt__result_record_output(ptr inttoptr (i64 1 to ptr), ptr @label.2)
  ret i64 0
}

declare void @__quantum__rt__initialize(ptr)
declare void @__quantum__qis__mz__body(ptr, ptr writeonly) #1
declare void @__quantum__rt__array_record_output(i64, ptr)
declare void @__quantum__rt__result_record_output(ptr, ptr)
declare void @__quantum__qis__cnot__body(ptr, ptr)
declare void @__quantum__qis__h__body(ptr)

attributes #0 = { "entry_point" "qir_profiles"="base_profile" "output_labeling_schema"="qleisli.bit-vector.v1" "required_num_qubits"="2" "required_num_results"="2" }
attributes #1 = { "irreversible" }

!llvm.module.flags = !{!0, !1, !2, !3}
!0 = !{i32 1, !"qir_major_version", i32 2}
!1 = !{i32 7, !"qir_minor_version", i32 0}
!2 = !{i32 1, !"dynamic_qubit_management", i1 false}
!3 = !{i32 1, !"dynamic_result_management", i1 false}
