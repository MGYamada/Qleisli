#!/usr/bin/env python3
"""VM-23: actual native Lean arithmetic vs Rust and independent rational formulas.

Temporary harnesses receive raw inputs only. No Rust result, success flag or
reference summary is passed to Lean. No production protocol or seal is added.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
"""
import argparse
import copy
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import random
import struct
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
FIXTURE = ROOT / "tests/fixtures/verification_v023"


def scalar(ns, exponent=0):
    return (list(ns), exponent)


ZERO = scalar([0, 0, 0, 0])
ONE = scalar([1, 0, 0, 0])
HALF_ROOT = scalar([0, 1, 0, 0], 1)
NEG_ROOT = scalar([0, -1, 0, 0], 1)
H = (2, 2, [HALF_ROOT, HALF_ROOT, HALF_ROOT, NEG_ROOT])
T = (2, 2, [ONE, ZERO, ZERO, scalar([0, 1, 0, 1], 1)])


def cases():
    result = []
    values = [0, 1, -1, 2, -2, 3, 2**126, -(2**127), 2**127 - 1]
    for n in values:
        for exponent in [0, 1, 2, 125, 126, 127, 128, 2**32 - 1]:
            result.append(("make", scalar([n, 0, 0, 0], exponent)))
    rng = random.Random(23092026)
    small = [scalar([rng.randrange(-8, 9) for _ in range(4)], rng.randrange(8))
             for _ in range(100)]
    small += [scalar([2**127 - 1, 0, 0, 0]), scalar([-(2**127), 0, 0, 0]),
              scalar([1, 0, 0, 0], 126), scalar([0, 0, -(2**127), 0])]
    for x in small:
        result.extend([("neg", x), ("conjugate", x)])
    for x, y in zip(small, small[1:] + small[:1]):
        result.extend([("add", x, y), ("mul", x, y)])
    result += [("equal", scalar([2*n, 0, 0, 0], 1), scalar([n, 0, 0, 0]))
               for n in range(-8, 9)]
    result += [("equal", ONE, scalar([-1, 0, 0, 0])),
               ("add", scalar([2**127 - 1, 0, 0, 0]), scalar([1, 0, 0, 0])),
               ("add", scalar([2**127 - 1, 0, 0, 0]), scalar([-(2**127 - 1), 0, 0, 0], 1)),
               ("mul", scalar([1, 0, 0, 0], 126), scalar([1, 0, 0, 0], 1))]
    result += [("phase", n) for n in list(range(-16, 17)) + [-(2**31), 2**31 - 1]]
    for op in ["compose", "tensor"]:
        for budget in [0, 3, 4, 15, 16, 17, 32, 100]:
            result.append((op, T, H, budget))
    for op in ["adjoint", "isometry"]:
        for matrix in [H, T, (1, 1, [scalar([-1, 0, 0, 0])]),
                       (1, 1, [scalar([2, 0, 0, 0])]),
                       (1, 1, [scalar([-(2**127), 0, 0, 0])]),
                       (1, 2, [ONE, ZERO]), (2, 1, [ONE, ZERO])]:
            for budget in [0, 1, 3, 4, 19, 20, 100]:
                result.append((op, matrix, budget))
    result += [("compose", (1, 1, [scalar([2**127 - 1, 0, 0, 0])]),
                (1, 1, [scalar([2, 0, 0, 0])]), budget) for budget in [1, 2, 3]]
    result += [("compose", H, (1, 1, [ONE]), 100),
               ("tensor", (1, 1, [scalar([-1, 0, 0, 0])]), H, 4),
               ("compose", (1, 1, [scalar([-1, 0, 0, 0])]), (1, 1, [ONE]), 2),
               ("tensor", (9, 1, [ONE] * 9), (8, 1, [ONE] * 8), 100),
               ("matrix", (0, 1, [])), ("matrix", (65, 1, [])),
               ("matrix", (2, 2, [ONE])), ("chain", T, H, 35),
               ("chain", T, H, 36), ("chain", T, H, 52)]
    # i128::MIN has 127 removable powers of two: exponent 253 becomes
    # canonical exponent 126, while 254 remains outside the admitted profile.
    for slot in range(4):
        for n in [-(2**127), 2**127 - 1, -2, 0, 2]:
            for exponent in [0, 126, 127, 253, 254, 2**32 - 1]:
                ns = [0, 0, 0, 0]
                ns[slot] = n
                result.append(("make", scalar(ns, exponent)))
    result.extend(probe["input"] for probe in capacity_probes())
    return result


def capacity_probes():
    """Named public-contract expectations, not an arithmetic-loop emulator."""
    maximum = 2**127 - 1
    minimum = -(2**127)
    usize_maximum = 2**(struct.calcsize("P") * 8) - 1
    imaginary_minimum = (1, 1, [scalar([0, 0, minimum, 0])])
    real_maximum = (1, 1, [scalar([maximum, 0, 0, 0])])
    two = (1, 1, [scalar([2, 0, 0, 0])])
    one = (1, 1, [ONE])

    def error(name, request, code, remaining=None):
        expected = {"error": code}
        if remaining is not None:
            expected = {"result": expected, "remaining": remaining}
        return dict(name=name, input=request, expected=expected)

    probes = [
        error("dimension_before_entry_count", ("matrix", (0, 2, [ONE])), "dimension"),
        error("entry_count_for_valid_dimensions", ("matrix", (2, 2, [ONE])), "entryCount"),
        error("identity_zero_rejected_before_allocation", ("identity", 0), "dimension"),
        error("identity_excess_dimension_rejected_before_allocation", ("identity", 65), "dimension"),
        error("shape_before_precharge", ("compose", H, one, 0), "shapeMismatch", 0),
        error("tensor_dimension_before_precharge", ("tensor", (9, 1, [ONE]*9),
                                                     (8, 1, [ONE]*8), 0), "dimension", 0),
        error("compose_budget_before_arithmetic", ("compose", real_maximum, two, 1), "workLimit", 1),
        error("compose_arithmetic_keeps_precharge", ("compose", real_maximum, two, 5),
              "arithmeticCapacity", 3),
        error("adjoint_budget_before_arithmetic", ("adjoint", imaginary_minimum, 0), "workLimit", 0),
        error("adjoint_arithmetic_keeps_precharge", ("adjoint", imaginary_minimum, 3),
              "arithmeticCapacity", 2),
        error("isometry_shares_adjoint_and_compose_budget", ("isometry", real_maximum, 2), "workLimit", 1),
        error("isometry_arithmetic_keeps_both_precharges", ("isometry", real_maximum, 4),
              "arithmeticCapacity", 1),
        error("alignment_intermediate_overflow_despite_representable_sum",
              ("add", scalar([maximum, 0, 0, 0]), scalar([-maximum, 0, 0, 0], 1)),
              "arithmeticCapacity"),
        error("multiplication_intermediate_overflow_despite_representable_product",
              ("mul", scalar([maximum, maximum, 0, 0]), scalar([1, -1, 0, 0])),
              "arithmeticCapacity"),
        error("negative_overflow_in_last_coefficient", ("neg", scalar([0, 0, 0, minimum])),
              "arithmeticCapacity"),
        error("conjugation_overflow_in_last_coefficient", ("conjugate", scalar([0, 0, 0, minimum])),
              "arithmeticCapacity"),
        error("charge_failure_retains_word_maximum", ("charge", usize_maximum, 0), "workLimit", 0),
    ]
    probes += [
        dict(name="zero_charge", input=("charge", 0, 0),
             expected={"result": {"ok": None}, "remaining": 0}),
        dict(name="charge_word_maximum", input=("charge", usize_maximum, usize_maximum),
             expected={"result": {"ok": None}, "remaining": 0}),
        dict(name="charge_one_from_word_maximum", input=("charge", 1, usize_maximum),
             expected={"result": {"ok": None}, "remaining": usize_maximum - 1}),
        dict(name="wide_isometry_returns_false_before_conjugation",
             input=("isometry", (1, 2, [scalar([0, 0, minimum, 0]), ZERO]), 0),
             expected={"result": {"ok": False}, "remaining": 0}),
    ]
    probes.extend(dict(name=f"identity_dimension_{dim}", input=("identity", dim)) for dim in [1, 2, 3])
    return probes


def lean_scalar(x):
    ns, e = x
    return "(Scalar.make " + " ".join(f"({n})" for n in ns) + f" {e})"


def lean_matrix(x):
    rows, cols, entries = x
    return f"(mk {rows} {cols} [" + ",".join(lean_scalar(s) for s in entries) + "])"


def lean_case(case):
    op, *args = case
    if op == "make":
        return "showScalar " + lean_scalar(args[0])
    if op == "phase":
        return f"showScalar (.ok (Scalar.phase ({args[0]})))"
    if op in ["add", "mul"]:
        return f"showScalar (do let x ← {lean_scalar(args[0])}; let y ← {lean_scalar(args[1])}; Scalar.{op} x y)"
    if op == "equal":
        return f"IO.println ((result toJson (do let x ← {lean_scalar(args[0])}; let y ← {lean_scalar(args[1])}; pure (x == y))).compress)"
    if op in ["neg", "conjugate"]:
        return f"showScalar ({lean_scalar(args[0])}.bind Scalar.{op})"
    if op == "matrix":
        return f"showMatrix {lean_matrix(args[0])}"
    if op == "identity":
        return f"showMatrix (Matrix.identity {args[0]})"
    if op == "charge":
        return f"showCharge ((charge {args[0]}).run {args[1]})"
    if op in ["compose", "tensor", "chain"]:
        return f"showWork (binary {json.dumps(op)} {lean_matrix(args[0])} {lean_matrix(args[1])} {args[2]})"
    if op == "isometry":
        return f"showBool (isometry {lean_matrix(args[0])} {args[1]})"
    return f"showWork (adjoint {lean_matrix(args[0])} {args[1]})"


LEAN = '''import QleisliKernel.Exact
import Lean
open QleisliKernel.Semantics.Exact QleisliKernel.Exact Lean
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
def errorName : Error → String
  | .arithmeticCapacity => "arithmeticCapacity" | .workLimit => "workLimit"
  | .dimension => "dimension" | .entryCount => "entryCount" | .shapeMismatch => "shapeMismatch"
def coeff (x : Coefficient) : Json := Json.arr #[toJson (toString x.numerator), toJson x.exponent]
def sc (x : Scalar) : Json := Json.arr #[coeff x.a, coeff x.b, coeff x.c, coeff x.d]
def mat (x : Matrix) : Json := Json.mkObj [("rows", toJson x.rows), ("cols", toJson x.cols),
  ("entries", toJson (x.entries.map sc))]
def result {α : Type} (encode : α → Json) : Except Error α → Json
  | .ok x => Json.mkObj [("ok", encode x)]
  | .error e => Json.mkObj [("error", toJson (errorName e))]
def showScalar (x : Except Error Scalar) : IO Unit := IO.println ((result sc x).compress)
def showMatrix (x : Except Error Matrix) : IO Unit := IO.println ((result mat x).compress)
def showWork (x : Except Error Matrix × Nat) : IO Unit :=
  IO.println ((Json.mkObj [("result", result mat x.1), ("remaining", toJson x.2)]).compress)
def showBool (x : Except Error Bool × Nat) : IO Unit :=
  IO.println ((Json.mkObj [("result", result toJson x.1), ("remaining", toJson x.2)]).compress)
def showCharge (x : Except Error Unit × Nat) : IO Unit :=
  IO.println ((Json.mkObj [("result", result (fun _ => Json.null) x.1), ("remaining", toJson x.2)]).compress)
def mk (r c : Nat) (entries : List (Except Error Scalar)) : Except Error Matrix := do
  let values ← entries.mapM id
  Matrix.make r c values
def binary (op : String) (left right : Except Error Matrix) (work : Nat) : Except Error Matrix × Nat :=
  (do
    let x ← liftExact left
    let y ← liftExact right
    if op == "tensor" then Matrix.tensorWork x y
    else if op == "chain" then do
      let z ← Matrix.composeWork x y
      let _ ← Matrix.isometryWork z
      Matrix.composeWork z y
    else Matrix.composeWork x y).run work
def adjoint (input : Except Error Matrix) (work : Nat) : Except Error Matrix × Nat :=
  (do let x ← liftExact input; Matrix.adjointWork x).run work
def isometry (input : Except Error Matrix) (work : Nat) : Except Error Bool × Nat :=
  (do let x ← liftExact input; Matrix.isometryWork x).run work
'''


def rust_scalar(x):
    ns, e = x
    return "Exact::new([" + ",".join(str(n) for n in ns) + f"], {e})"


def rust_matrix(x):
    rows, cols, entries = x
    return f"mk({rows},{cols},vec![" + ",".join(rust_scalar(s) for s in entries) + "])"


def rust_case(case):
    op, *args = case
    if op == "make":
        return f"show_scalar({rust_scalar(args[0])});"
    if op == "phase":
        return f"show_scalar(Ok(Exact::phase({args[0]})));"
    if op in ["add", "mul"]:
        return f"show_scalar((||{{let x={rust_scalar(args[0])}?;let y={rust_scalar(args[1])}?;x.{op}(y)}})());"
    if op == "equal":
        return f"show_equal((||{{let x={rust_scalar(args[0])}?;let y={rust_scalar(args[1])}?;Ok(x==y)}})());"
    if op in ["neg", "conjugate"]:
        return f"show_scalar({rust_scalar(args[0])}.and_then(Exact::{op}));"
    if op == "matrix":
        return f"show_matrix({rust_matrix(args[0])});"
    if op == "identity":
        return f"show_matrix(Matrix::identity({args[0]}));"
    if op == "charge":
        return f"show_charge({args[0]}, {args[1]});"
    if op in ["compose", "tensor", "chain"]:
        return f"binary({json.dumps(op)},{rust_matrix(args[0])},{rust_matrix(args[1])},{args[2]});"
    return f"unary({json.dumps(op)},{rust_matrix(args[0])},{args[1]});"


RUST = '''use qleisli::contract::exact::{Budget, Exact, ExactError, Matrix};
use qleisli::interchange::finite_matrix;
fn error(e: ExactError)-> &'static str { match e {
 ExactError::ArithmeticCapacity=>"arithmeticCapacity", ExactError::WorkLimit=>"workLimit",
 ExactError::Dimension{..}=>"dimension", ExactError::EntryCount{..}=>"entryCount",
 ExactError::ShapeMismatch=>"shapeMismatch" } }
fn encode(x: Result<Matrix,ExactError>)->String {match x {
 Ok(m)=>format!("{{\\"ok\\":{}}}",String::from_utf8(finite_matrix::encode(&m).unwrap()).unwrap().trim()),
 Err(e)=>format!("{{\\"error\\":\\"{}\\"}}",error(e))}}
fn show_matrix(x:Result<Matrix,ExactError>){println!("{}",encode(x));}
fn show_scalar(x:Result<Exact,ExactError>){show_matrix(x.and_then(|s|Matrix::new(1,1,vec![s])));}
fn show_equal(x:Result<bool,ExactError>){match x {
 Ok(v)=>println!("{{\\"ok\\":{v}}}"),Err(e)=>println!("{{\\"error\\":\\"{}\\"}}",error(e))}}
fn show_charge(amount:usize,work:usize){
 let mut budget=Budget::new(work);
 let result=match budget.charge(amount) {
 Ok(())=>"{\\\"ok\\\":null}".to_owned(),Err(e)=>format!("{{\\\"error\\\":\\\"{}\\\"}}",error(e))};
 println!("{{\\\"result\\\":{},\\\"remaining\\\":{}}}",result,budget.remaining()); }
fn mk(r:usize,c:usize,es:Vec<Result<Exact,ExactError>>)->Result<Matrix,ExactError>{
 Matrix::new(r,c,es.into_iter().collect::<Result<Vec<_>,_>>()?) }
fn binary(op:&str,left:Result<Matrix,ExactError>,right:Result<Matrix,ExactError>,work:usize){
 let mut b=Budget::new(work);
 let result=(||{let x=left?;let y=right?;
 if op=="tensor" {x.tensor(&y,&mut b)} else if op=="chain" {
 let z=x.compose(&y,&mut b)?;let _=z.is_isometry(&mut b)?;z.compose(&y,&mut b)
 } else {x.compose(&y,&mut b)}})();
 println!("{{\\"result\\":{},\\"remaining\\":{}}}",encode(result),b.remaining()); }
fn unary(op:&str,input:Result<Matrix,ExactError>,work:usize){
 let mut b=Budget::new(work);
 let result=if op=="isometry" {match input.and_then(|x|x.is_isometry(&mut b)) {
 Ok(v)=>format!("{{\\"ok\\":{v}}}"),Err(e)=>format!("{{\\"error\\":\\"{}\\"}}",error(e))
 }} else {encode(input.and_then(|x|x.adjoint(&mut b)))};
 println!("{{\\"result\\":{},\\"remaining\\":{}}}",result,b.remaining()); }
fn main(){
'''


def command(cmd, cwd, log, timeout=180):
    run = subprocess.run(cmd, cwd=cwd, text=True, capture_output=True, timeout=timeout)
    retain_stdout = run.returncode or cmd[-1] in ["--version", "-vV"]
    log.append(dict(command=cmd, exit=run.returncode, stdout=run.stdout if retain_stdout else "",
                    stderr=run.stderr))
    assert run.returncode == 0, run.stdout + run.stderr
    return run.stdout


def native(all_cases, log):
    command(["lake", "env", "lean", "--version"], ROOT / "lean-kernel", log)
    command(["lake", "env", "leanc", "--version"], ROOT / "lean-kernel", log)
    command(["rustc", "-vV"], ROOT, log)
    command(["cc", "--version"], ROOT, log)
    with tempfile.TemporaryDirectory(prefix="qleisli-exact-native-") as directory:
        project = Path(directory)
        (project / "lean-toolchain").write_text((ROOT / "lean-kernel/lean-toolchain").read_text())
        (project / "lakefile.toml").write_text('name = "exact_test"\nversion = "0.0.0"\n'
            'defaultTargets = ["exact-test"]\n[[require]]\nname = "qleisli_kernel"\npath = ' +
            json.dumps(str(ROOT / "lean-kernel")) +
            '\n[[lean_exe]]\nname = "exact-test"\nroot = "Main"\n')
        definitions = "\n".join(f"def case{i} : IO Unit := {lean_case(c)}" for i, c in enumerate(all_cases))
        actions = ",".join(f"case{i}" for i in range(len(all_cases)))
        (project / "Main.lean").write_text(LEAN + definitions +
            f"\ndef main : IO Unit := do\n  for action in [{actions}] do action\n")
        command(["lake", "build"], project, log)
        binary = project / ".lake/build/bin/exact-test"
        lean = [json.loads(line) for line in command([str(binary)], project, log).splitlines()]
        (project / "Cargo.toml").write_text('[package]\nname="qleisli_exact_test"\nversion="0.0.0"\n'
            'edition="2024"\n[dependencies]\nqleisli={path=' + json.dumps(str(ROOT)) + '}\n'
            '[[bin]]\nname="exact-test"\npath="main.rs"\n')
        (project / "main.rs").write_text(RUST + "\n".join(rust_case(c) for c in all_cases) + "\n}\n")
        stdout = command(["cargo", "run", "--offline", "--quiet"], project, log)
        rust = [json.loads(line) for line in stdout.splitlines()]
        return lean, rust


def rational(x):
    ns, e = x
    return [Fraction(n, 2**e) if n else Fraction(0) for n in ns]


def oracle_mul(x, y):
    # Independent closed polynomial product, not a sixteen-step accumulator.
    a, b, c, d = x
    e, f, g, h = y
    return [a*e + 2*b*f - c*g - 2*d*h, a*f + b*e - c*h - d*g,
            a*g + c*e + 2*b*h + 2*d*f, a*h + b*g + c*f + d*e]


def decoded(x):
    return [Fraction(int(n), 2**e) for n, e in x]


def oracle_matrix(matrix):
    rows, cols, es = matrix
    return [[rational(es[r * cols + c]) for c in range(cols)] for r in range(rows)]


def oracle_compose(x, y):
    return [[list(map(sum, zip(*(oracle_mul(x[r][k], y[k][c]) for k in range(len(y))))))
             for c in range(len(y[0]))] for r in range(len(x))]


def oracle_adjoint(x):
    return [[x[c][r][:2] + [-a for a in x[c][r][2:]] for c in range(len(x))]
            for r in range(len(x[0]))]


def oracle_tensor(x, y):
    # Kronecker Y⊗X, formed as blocks, rather than quotient-index extraction.
    result = []
    for yrow in y:
        for xrow in x:
            result.append([oracle_mul(xentry, yentry) for yentry in yrow for xentry in xrow])
    return result


def rust_shape(case, record):
    """Normalize the existing Rust transport, preserving independent exponents."""
    if "result" in record:
        return dict(result=rust_shape(("matrix",), record["result"]), remaining=record["remaining"])
    if "error" in record or record["ok"] is None or isinstance(record["ok"], bool):
        return record
    matrix = record["ok"]
    es = [[[d["numerator"], d["denominator_bits"]] for d in s] for s in matrix["entries"]]
    if case[0] in ["make", "add", "mul", "neg", "conjugate", "phase"]:
        return dict(ok=es[0])
    return dict(ok=dict(rows=matrix["rows"], cols=matrix["cols"], entries=es))


def compare(all_cases, lean, rust):
    assert len(lean) == len(rust) == len(all_cases)
    mathematical = 0
    matrices = 0
    for i, (case, left, right) in enumerate(zip(all_cases, lean, rust)):
        right = rust_shape(case, right)
        assert left == right, (i, case, left, right)
        op = case[0]
        result = left.get("result", left)
        if op == "equal" and "ok" in result:
            assert result["ok"] == (rational(case[1]) == rational(case[2]))
            mathematical += 1
        if "ok" in result and op in ["matrix", "identity", "compose", "tensor", "adjoint", "isometry", "chain"]:
            if op == "identity":
                x = [[rational(ONE if r == c else ZERO) for c in range(case[1])]
                     for r in range(case[1])]
            else:
                x = oracle_matrix(case[1])
            expected = x
            if op in ["compose", "chain"]: expected = oracle_compose(x, oracle_matrix(case[2]))
            if op == "chain": expected = oracle_compose(expected, oracle_matrix(case[2]))
            if op == "tensor": expected = oracle_tensor(x, oracle_matrix(case[2]))
            if op == "adjoint": expected = oracle_adjoint(x)
            if op == "isometry":
                gram = oracle_compose(oracle_adjoint(x), x)
                expected = all(value == [Fraction(int(r == c)), Fraction(0), Fraction(0), Fraction(0)]
                               for r, row in enumerate(gram) for c, value in enumerate(row))
                assert result["ok"] == expected, (i, case, result, expected)
            else:
                actual = result["ok"]
                assert actual["rows"] == len(expected) and actual["cols"] == len(expected[0])
                assert [decoded(s) for s in actual["entries"]] == [s for row in expected for s in row]
            matrices += 1
        if "ok" not in left or op not in ["make", "add", "mul", "neg", "conjugate"]:
            continue
        # Never construct an enormous Fraction for failed extreme exponents.
        x = rational(case[1])
        expected = x
        if op == "add": expected = [a+b for a,b in zip(x, rational(case[2]))]
        if op == "mul": expected = oracle_mul(x, rational(case[2]))
        if op == "neg": expected = [-a for a in x]
        if op == "conjugate": expected = x[:2] + [-a for a in x[2:]]
        assert decoded(left["ok"]) == expected, (i, case, left, expected)
        mathematical += 1
    for probe in capacity_probes():
        if "expected" in probe:
            i = all_cases.index(probe["input"])
            assert lean[i] == probe["expected"], (probe["name"], lean[i], probe["expected"])
    return mathematical, matrices


def runtime_capacity_contract(all_cases, outcomes):
    """Audited common domain and native assumptions; this is no proof claim."""
    return dict(
        issue=99,
        audit_policy_source_sha256={str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
                                    for p in [ROOT / "scripts/check_lean_kernel.py",
                                              ROOT / "lean-kernel/Audit.lean", ROOT / "lean/Audit.lean"]},
        common_input_domain={
            "numerator": "signed i128, -2^127 through 2^127-1",
            "constructor_exponent": "u32, 0 through 2^32-1; canonical nonzero exponent <=126",
            "phase_input": "signed i32; Euclidean residue modulo 8; global phase retained",
            "matrix": "created by Matrix.make/new or identity; dimensions 1..64; canonical scalar entries; exact row-major count",
            "budget": "0 through target usize::MAX; one shared state across all operations",
            "budget_source_storage": "Rust Budget also retains a source-allocation cache; the VM-23 arithmetic harness compares remaining exact work only and does not import/cache source allocations",
            "local_target_pointer_bits": struct.calcsize("P") * 8,
            "local_platform": sys.platform,
            "raw_lean_structures": "Raw Coefficient/Scalar/Matrix constructors are not validated evidence and have no Rust public counterpart",
        },
        audited_operation_contracts={
            "constructor": "Range-check signed numerator and u32 exponent; zero becomes (0,0); remove even numerator factors before canonical exponent check",
            "addition": "Zero shortcut; align denominators with representable positive powers; reject intermediate i128 multiplication/addition overflow before normalizing",
            "multiplication": "Fixed coefficient-pair fold i,j=0..3; checked product, sqrt(2) pair factor 2, imaginary pair negation, then checked accumulation",
            "conjugation": "Retain real coefficients and negate imaginary coefficients with i128::MIN rejection",
            "composition": "Reject shape mismatch before charging 2*left.rows*left.cols*right.cols; arithmetic failure retains full charge",
            "tensor": "Low-order left component; reject product dimensions before charging output cells; arithmetic failure retains full charge",
            "adjoint": "Charge input cells once, transpose and conjugate; arithmetic failure retains full charge",
            "isometry": "Wide matrices return false without charging; otherwise adjoint and composition share budget, compare exactly with identity",
            "charge": "Insufficient work leaves the state unchanged; sufficient work subtracts exactly without machine-word wrap",
        },
        observable_comparison={
            "success": "Full canonical scalar coefficients and independent exponents, matrix dimensions/entries, Bool result, remaining work",
            "error": "Error class and remaining work; Rust Dimension/EntryCount diagnostic payloads are not represented by Lean Error and are outside this comparison",
            "evaluation_order": "Lean addition evaluates both factors before scaled numerators; Lean adjoint enumerates output row-major while Rust enumerates input row-major. Observable error class and prepaid work agree; exact internal failure trace is not claimed",
        },
        declared_native_assumptions=[
            "Lean 4.30.0 kernel validates proof terms; fresh leanchecker replay does not prove native compilation",
            "Pinned Lean code generation, C compiler, native runtime, allowed Init/Std primitives, operating system and hardware execute the audited definitions correctly",
            "Project source and compiled declaration audits exclude unsafe/partial/extern/implemented_by substitutions, including private/generated helpers",
            "Temporary test harnesses provide raw values only, serialize results faithfully, and independently execute Rust; no Rust success result is fed to Lean",
        ],
        not_discharged=[
            "General Rust-to-Lean refinement for all common-domain success/failure decisions, rather than finite differential examples",
            "Full payload correspondence for Rust Dimension and EntryCount errors, or an explicitly adopted diagnostic mapping for a future adapter",
            "Production exact-arithmetic transport reconstruction, immutable artifact/request binding and platform-word budget validation; VM-28/29 remain separate",
            "Rust source-storage deduplication/accounting is outside these scalar/matrix definitions and must stay explicit when evidence/producer boundaries are integrated",
            "Native compiler/runtime correctness is an explicit existing trust assumption, not an axiom proved by differential testing",
        ],
        named_capacity_probes=[dict(probe, actual=outcomes[all_cases.index(probe["input"])])
                               for probe in capacity_probes()],
        formal_equivalence_proved=False,
        production_authority="Rust",
        production_transport_added=False,
    )


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--record", type=Path)
    args = parser.parse_args()
    log = []
    all_cases = cases()
    left, right = native(all_cases, log)
    count, matrix_count = compare(all_cases, left, right)
    faults = []
    for kind in ["erased_unit_phase", "tensor_axis_order", "refund_arithmetic_failure", "reset_shared_work",
                 "shape_after_precharge", "failed_charge_changes_work", "machine_word_budget_wrap"]:
        wrong = copy.deepcopy(left)
        if kind == "erased_unit_phase":
            i = all_cases.index(("compose", (1, 1, [scalar([-1, 0, 0, 0])]), (1, 1, [ONE]), 2))
            wrong[i]["result"]["ok"]["entries"][0][0][0] = "1"
        elif kind == "tensor_axis_order":
            i = all_cases.index(("tensor", T, H, 16))
            wrong[i]["result"]["ok"]["entries"][1], wrong[i]["result"]["ok"]["entries"][2] = (
                wrong[i]["result"]["ok"]["entries"][2], wrong[i]["result"]["ok"]["entries"][1])
        elif kind == "refund_arithmetic_failure":
            i = all_cases.index(("compose", (1, 1, [scalar([2**127 - 1, 0, 0, 0])]),
                                 (1, 1, [scalar([2, 0, 0, 0])]), 3))
            wrong[i]["remaining"] = 3
        elif kind == "reset_shared_work":
            i = all_cases.index(("chain", T, H, 35))
            wrong[i]["remaining"] = 35
        elif kind == "shape_after_precharge":
            i = all_cases.index(("compose", H, (1, 1, [ONE]), 0))
            wrong[i]["result"]["error"] = "workLimit"
        elif kind == "failed_charge_changes_work":
            i = all_cases.index(("isometry", (1, 1, [scalar([2**127-1, 0, 0, 0])]), 2))
            wrong[i]["remaining"] = 0
        else:
            usize_maximum = 2**(struct.calcsize("P") * 8) - 1
            i = all_cases.index(("charge", 1, usize_maximum))
            wrong[i]["remaining"] = 0
        try:
            compare(all_cases, wrong, right)
        except AssertionError:
            faults.append(kind)
        else:
            raise AssertionError(f"oracle missed {kind}")
    selected = [dict(input=case, lean=out) for case, out in zip(all_cases, left)
                if case[0] in ["chain", "tensor"] or case == ("compose", T, H, 16)]
    report = dict(native_comparisons=len(all_cases), independent_rational_comparisons=count,
                  independent_matrix_comparisons=matrix_count,
                  detected_semantic_faults=faults,
                  largest_arithmetic_matrix_dimension=4, production_authority="Rust",
                  cases_sha256=hashlib.sha256(json.dumps(all_cases).encode()).hexdigest(),
                  outcomes_sha256=hashlib.sha256(json.dumps(left, sort_keys=True).encode()).hexdigest(),
                  selected_actual_decisions=selected,
                  runtime_capacity_contract=runtime_capacity_contract(all_cases, left),
                  commands=log, source_sha256={str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
                    for p in [ROOT / "lean-kernel/QleisliKernel/Exact.lean",
                              ROOT / "lean-kernel/QleisliKernel/ExactCapacity.lean",
                              ROOT / "lean-kernel/QleisliKernel/ExactMatrix.lean",
                              ROOT / "lean-kernel/QleisliKernel/Semantics/Exact.lean",
                              ROOT / "lean/Qleisli/Exact.lean", ROOT / "lean/Qleisli/ExactMatrix.lean",
                              ROOT / "lean/Qleisli/Semantics/Exact.lean",
                              ROOT / "src/contract/exact.rs", Path(__file__).resolve()]})
    if args.record:
        args.record.write_text(json.dumps(report, indent=2) + "\n")
    print(f"{len(all_cases)} native Rust/Lean comparisons; {count} rational and {matrix_count} matrix checks")


if __name__ == "__main__":
    main()
