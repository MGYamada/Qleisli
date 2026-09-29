"""Isolated LLVM reader for the declared QIR Base terminal subset.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
No input module is executed. LLVM parses/verifies before profile inspection.
"""
import importlib.metadata
import json
import re
import sys


class ReaderError(ValueError):
    pass


def require(condition, message):
    if not condition:
        raise ReaderError(message)


def translate(data):
    try:
        import pyqir as q
    except ImportError as e:
        raise ReaderError("QIR input requires the optional qir extra (pyqir==0.12.5)") from e
    require(importlib.metadata.version("pyqir") == "0.12.5", "expected PyQIR 0.12.5")
    require(len(data) <= 1 << 20, "QIR input exceeds 1 MiB")
    try:
        context = q.Context()
        module = (q.Module.from_bitcode(context, data) if data.startswith(b"BC\xc0\xde")
                  else q.Module.from_ir(context, data.decode("utf-8")))
        error = module.verify()
    except (ValueError, UnicodeError, RuntimeError) as e:
        raise ReaderError(f"invalid LLVM module: {e}") from e
    require(error is None, f"LLVM verification failed: {error}")

    # These checks inspect LLVM's canonical output, never parse input LLVM
    # ourselves. PyQIR does not expose module assembly, aliases or call attrs.
    canonical = str(module)
    require(not any(line.startswith("module asm") for line in canonical.splitlines()),
            "module assembly is unsupported")
    globals = module.global_variables
    require(len(globals) <= 64, "too many label globals")
    require(sum(line.startswith("@") for line in canonical.splitlines()) == len(globals),
            "global aliases and indirect functions are unsupported")
    labels = {}
    for g in globals:
        require(g.is_constant and isinstance(g.initializer, q.ArrayConstant), "only constant label strings are supported")
        require(isinstance(g.initializer.type.element, q.IntType) and g.initializer.type.element.width == 8,
                "labels must contain bytes")
        require(g.initializer.count <= 256, "label is too long")
        # extract_byte_string is only called for a validated global byte array.
        value = q.extract_byte_string(g)
        require(value is not None and value.endswith(b"\0") and b"\0" not in value[:-1],
                "labels must be null-terminated strings")
        labels[g.name] = value

    for name, width, expected in [("qir_major_version", 32, 2), ("qir_minor_version", 32, 0),
                                  ("dynamic_qubit_management", 1, 0), ("dynamic_result_management", 1, 0)]:
        flag = module.get_flag(name)
        require(isinstance(flag, q.ConstantAsMetadata) and isinstance(flag.value, q.IntConstant)
                and flag.value.type.width == width and flag.value.value == expected,
                f"unsupported or missing module flag {name}")

    gates = {"h__body": ("h", 1), "x__body": ("x", 1), "y__body": ("y", 1),
             "z__body": ("z", 1), "s__body": ("s", 1), "s__adj": ("sdg", 1),
             "t__body": ("t", 1), "t__adj": ("tdg", 1), "cnot__body": ("cx", 2),
             "cz__body": ("cz", 2), "swap__body": ("swap", 2), "ccx__body": ("ccx", 3)}
    gates = {"__quantum__qis__" + name: value for name, value in gates.items()}
    init, mz = "__quantum__rt__initialize", "__quantum__qis__mz__body"
    array, record = "__quantum__rt__array_record_output", "__quantum__rt__result_record_output"
    signatures = {name: ", ".join(["ptr"] * arity) for name, (_, arity) in gates.items()}
    signatures.update({init: "ptr", mz: "ptr, ptr writeonly", array: "i64, ptr", record: "ptr, ptr"})
    functions = module.functions
    require(len(functions) <= 17, "too many functions")
    defined = [f for f in functions if f.basic_blocks]
    require(len(defined) == 1, "exactly one entry definition is required")
    entry = defined[0]
    header = str(entry).splitlines()[0]
    require(re.fullmatch(r"define (i64|void) @[A-Za-z_][A-Za-z_0-9]*\(\) #\d+ \{", header),
            "entry must have a plain void/i64 no-argument signature")
    attrs = {a.string_kind: a.string_value for a in entry.attributes.func}
    require(set(attrs) == {"entry_point", "qir_profiles", "output_labeling_schema", "required_num_qubits", "required_num_results"},
            "unexpected entry attributes")
    require(attrs["entry_point"] == "" and attrs["qir_profiles"] == "base_profile"
            and attrs["output_labeling_schema"] == "qleisli.bit-vector.v1", "unsupported entry profile/output schema")
    counts = []
    for name in ["required_num_qubits", "required_num_results"]:
        value = attrs[name]
        require(isinstance(value, str) and re.fullmatch(r"0|[1-9][0-9]?", value), "invalid resource count")
        counts.append(int(value))
    qubits, results = counts
    require(qubits <= 12 and results <= 12, "terminal resource limit exceeded")
    declarations = {}
    for f in functions:
        if f == entry:
            continue
        require(f.name in signatures, f"unsupported declaration {f.name}")
        expected = f"declare void @{f.name}({signatures[f.name]})"
        declaration = str(f).strip().splitlines()[-1]
        require(re.fullmatch(re.escape(expected) + r"(?: #\d+)?", declaration),
                f"wrong signature/attributes for {f.name}")
        attributes = [(a.string_kind, a.string_value) for a in f.attributes.func]
        require(attributes == ([("irreversible", "")] if f.name == mz else []),
                f"unsupported attributes for {f.name}")
        declarations[f.name] = f

    def pointer(value, bound):
        require(type(value) is q.Constant and isinstance(value.type, q.PointerType)
                and value.type.address_space == 0, "expected a static resource pointer")
        # Restrict a parsed Constant to the pinned printer's null/inttoptr atoms.
        # ptr_id on arbitrary globals/expressions is not a safe reader API.
        spelling = str(value)
        match = re.fullmatch(r"ptr inttoptr \(i64 ([1-9][0-9]*) to ptr\)", spelling)
        require(spelling == "ptr null" or match is not None, "unsupported resource pointer expression")
        index = 0 if spelling == "ptr null" else int(match[1])
        require(index < bound, "resource ID out of range")
        return index

    used_labels = set()

    def label(value):
        require(isinstance(value, q.GlobalVariable) and value.name in labels, "expected a direct constant label")
        content = labels[value.name]
        require(content not in used_labels, "duplicate output label")
        used_labels.add(content)

    blocks = entry.basic_blocks
    require(1 <= len(blocks) <= 64, "block limit exceeded")
    require(sum(len(b.instructions) for b in blocks) <= 8192, "instruction limit exceeded")
    block = blocks[0]
    visited = set()
    instructions = []
    while True:
        require(block.name not in visited, "cyclic CFG")
        visited.add(block.name)
        contents = block.instructions
        require(contents, "empty block")
        instructions.extend(contents[:-1])
        terminator = contents[-1]
        if terminator.opcode == q.Opcode.RET:
            expected_return = "ret void" if entry.type.ret.is_void else "ret i64 0"
            require(str(terminator).strip() == expected_return, "unsupported return")
            break
        require(terminator.opcode == q.Opcode.BR and len(terminator.operands) == 1
                and len(terminator.successors) == 1, "only unconditional branches are supported")
        block = terminator.successors[0]
    require(len(visited) == len(blocks), "unvisited blocks are unsupported")

    prepared, measuring, output_count = False, False, None
    circuit, measured, outputs = [], {}, []
    measured_qubits = set()
    for inst in instructions:
        require(isinstance(inst, q.Call) and isinstance(inst.callee, q.Function), "only direct calls are supported")
        name, args = inst.callee.name, inst.args
        require(name in declarations and inst.callee == declarations[name], f"unsupported call {name}")
        printed_args = [f"ptr @{a.name}" if isinstance(a, q.GlobalVariable) else str(a) for a in args]
        require(str(inst).strip() == f"call void @{name}(" + ", ".join(printed_args) + ")",
                "call attributes/bundles are unsupported")
        if name == init:
            require(not prepared and not circuit and not measured and output_count is None
                    and len(args) == 1 and type(args[0]) is q.Constant and str(args[0]) == "ptr null",
                    "initialization must occur exactly once before all operations")
            prepared = True
            continue
        require(prepared, "runtime initialization is required first")
        if name in gates:
            gate, arity = gates[name]
            require(not measuring and output_count is None and len(args) == arity, "gate after measurement/output")
            wires = [pointer(a, qubits) for a in args]
            require(len(set(wires)) == len(wires), "aliased gate operands")
            circuit.append(f"{gate} " + ", ".join(f"q[{i}]" for i in wires) + ";")
            require(len(circuit) <= 4096, "gate limit exceeded")
        elif name == mz:
            require(output_count is None and len(args) == 2, "measurement after output")
            wire, result = pointer(args[0], qubits), pointer(args[1], results)
            require(wire not in measured_qubits and result not in measured, "reused qubit or result")
            measuring = True
            measured_qubits.add(wire)
            measured[result] = wire
        elif name == array:
            require(output_count is None and len(args) == 2 and isinstance(args[0], q.IntConstant)
                    and args[0].type.width == 64, "expected a single result array")
            output_count = args[0].value
            require(0 <= output_count <= 12, "output count limit exceeded")
            label(args[1])
        elif name == record:
            require(output_count is not None and len(args) == 2 and len(outputs) < output_count,
                    "result outside declared output array")
            result = pointer(args[0], results)
            require(result in measured and result not in outputs, "unwritten or duplicate output result")
            outputs.append(result)
            label(args[1])
    require(prepared and output_count == len(outputs), "missing initialization or incomplete output array")
    lines = ["OPENQASM 3.0;", 'include "stdgates.inc";']
    if qubits:
        lines.append(f"qubit[{qubits}] q;")
    if outputs:
        lines.append(f"bit[{len(outputs)}] c;")
    if qubits:
        lines.append("reset q;")
    lines.extend(circuit)
    lines.extend(f"c[{i}] = measure q[{measured[result]}];" for i, result in enumerate(outputs))
    # Hidden terminal measurements and unmeasured wires become explicit Rust
    # discards; there is no future use, so their closed reduced instrument agrees.
    return "\n".join(lines) + "\n"


def main():
    try:
        data = sys.stdin.buffer.read((1 << 20) + 1)
        output = {"qasm": translate(data)}
        status = 0
    except (ReaderError, ValueError, RuntimeError, UnicodeError) as e:
        output, status = {"code": "qir", "message": str(e)}, 1
    print(json.dumps(output))
    return status


if __name__ == "__main__":
    sys.exit(main())
