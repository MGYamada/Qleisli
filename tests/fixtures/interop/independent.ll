; Independently authored terminal QIR input, not exporter-generated.
; Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
; Prepare physical [1,0]; write resource results [1,0]; output [0,1] -> [0,1].
@root = private constant [5 x i8] c"bits\00"
@first = private constant [2 x i8] c"a\00"
@second = private constant [2 x i8] c"b\00"

define void @external_entry() #0 {
start:
  call void @__quantum__rt__initialize(ptr null)
  call void @__quantum__qis__x__body(ptr null)
  br label %readout
readout:
  call void @__quantum__qis__mz__body(ptr null, ptr inttoptr (i64 1 to ptr))
  call void @__quantum__qis__mz__body(ptr inttoptr (i64 1 to ptr), ptr null)
  call void @__quantum__rt__array_record_output(i64 2, ptr @root)
  call void @__quantum__rt__result_record_output(ptr null, ptr @first)
  call void @__quantum__rt__result_record_output(ptr inttoptr (i64 1 to ptr), ptr @second)
  ret void
}

declare void @__quantum__rt__initialize(ptr)
declare void @__quantum__qis__x__body(ptr)
declare void @__quantum__qis__mz__body(ptr, ptr writeonly) #1
declare void @__quantum__rt__array_record_output(i64, ptr)
declare void @__quantum__rt__result_record_output(ptr, ptr)
attributes #0 = { "entry_point" "qir_profiles"="base_profile" "output_labeling_schema"="qleisli.bit-vector.v1" "required_num_qubits"="2" "required_num_results"="2" }
attributes #1 = { "irreversible" }
!llvm.module.flags = !{!0, !1, !2, !3}
!0 = !{i32 1, !"qir_major_version", i32 2}
!1 = !{i32 7, !"qir_minor_version", i32 0}
!2 = !{i32 1, !"dynamic_qubit_management", i1 false}
!3 = !{i32 1, !"dynamic_result_management", i1 false}
