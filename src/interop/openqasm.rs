use super::profile::{Gate, TerminalCircuit};
use super::{InteropError, InteropErrorKind, MAX_OPENQASM_BYTES, MAX_QUBITS, MAX_TOKENS};
use crate::AcceptedProgram;
use crate::frontend::ast::Span;
use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write;

#[derive(Clone, Copy)]
struct Token<'a> {
    text: &'a str,
    span: Span,
}

fn lex(source: &str) -> Result<Vec<Token<'_>>, InteropError> {
    if source.len() > MAX_OPENQASM_BYTES {
        return Err(InteropError::limit("OpenQASM input exceeds 1 MiB"));
    }
    let bytes = source.as_bytes();
    let mut i = 0;
    let mut tokens = Vec::new();
    while i < bytes.len() {
        if matches!(bytes[i], b' ' | b'\t' | b'\r' | b'\n') {
            i += 1;
            continue;
        }
        if bytes[i..].starts_with(b"//") {
            while i < bytes.len() && bytes[i] != b'\n' && bytes[i] != b'\r' {
                i += 1;
            }
            continue;
        }
        if bytes[i..].starts_with(b"/*") {
            let start = i;
            i += 2;
            while i < bytes.len() && !bytes[i..].starts_with(b"*/") {
                if bytes[i..].starts_with(b"/*") {
                    return Err(InteropError::unsupported("nested block comments").at(Span {
                        start: i,
                        end: i + 2,
                    }));
                }
                i += 1;
            }
            if i == bytes.len() {
                return Err(InteropError::new(
                    InteropErrorKind::Parse,
                    "unterminated block comment",
                )
                .at(Span { start, end: i }));
            }
            i += 2;
            continue;
        }
        let start = i;
        match bytes[i] {
            b'a'..=b'z' | b'A'..=b'Z' | b'_' => {
                i += 1;
                while i < bytes.len() && (bytes[i].is_ascii_alphanumeric() || bytes[i] == b'_') {
                    i += 1;
                }
            }
            b'0'..=b'9' => {
                i += 1;
                while i < bytes.len() && bytes[i].is_ascii_digit() {
                    i += 1;
                }
            }
            b'"' => {
                i += 1;
                while i < bytes.len() && bytes[i] != b'"' && bytes[i] != b'\n' && bytes[i] != b'\r'
                {
                    i += 1;
                }
                if i == bytes.len() || bytes[i] != b'"' {
                    return Err(InteropError::new(
                        InteropErrorKind::Parse,
                        "unterminated include string",
                    )
                    .at(Span { start, end: i }));
                }
                i += 1;
            }
            b'-' if bytes[i..].starts_with(b"->") => i += 2,
            b';' | b'[' | b']' | b',' | b'=' | b'.' => i += 1,
            _ => {
                return Err(InteropError::unsupported(
                    "token outside the OpenQASM terminal subset",
                )
                .at(Span {
                    start,
                    end: start
                        + source[start..]
                            .chars()
                            .next()
                            .expect("character")
                            .len_utf8(),
                }));
            }
        }
        if tokens.len() >= MAX_TOKENS {
            return Err(
                InteropError::limit("at most 65536 OpenQASM tokens").at(Span { start, end: i })
            );
        }
        tokens.push(Token {
            text: &source[start..i],
            span: Span { start, end: i },
        });
    }
    tokens.push(Token {
        text: "",
        span: Span { start: i, end: i },
    });
    Ok(tokens)
}

struct Register {
    quantum: bool,
    array: bool,
    start: usize,
    len: usize,
}
struct Parser<'a> {
    tokens: Vec<Token<'a>>,
    pos: usize,
    registers: BTreeMap<String, Register>,
    circuit: TerminalCircuit,
    bits: Vec<Option<usize>>,
    measured: BTreeSet<usize>,
    initialized: BTreeSet<usize>,
    included: bool,
    declared: bool,
    started: bool,
}

impl Parser<'_> {
    fn peek(&self) -> &str {
        self.tokens[self.pos].text
    }
    fn token(&mut self) -> Token<'_> {
        let token = self.tokens[self.pos];
        if !token.text.is_empty() {
            self.pos += 1;
        }
        token
    }
    fn take(&mut self, text: &str) -> bool {
        if self.peek() == text {
            self.pos += 1;
            true
        } else {
            false
        }
    }
    fn error(&self, kind: InteropErrorKind, message: impl Into<String>) -> InteropError {
        InteropError::new(kind, message).at(self.tokens[self.pos].span)
    }
    fn expect(&mut self, text: &str) -> Result<(), InteropError> {
        if self.take(text) {
            Ok(())
        } else {
            Err(self.error(
                InteropErrorKind::Parse,
                format!("expected {text:?}, found {:?}", self.peek()),
            ))
        }
    }
    fn number(&mut self) -> Result<usize, InteropError> {
        let t = self.token();
        if t.text.is_empty()
            || !t.text.bytes().all(|b| b.is_ascii_digit())
            || (t.text.len() > 1 && t.text.starts_with('0'))
        {
            return Err(InteropError::new(
                InteropErrorKind::Parse,
                "expected a canonical decimal integer",
            )
            .at(t.span));
        }
        t.text
            .parse()
            .map_err(|_| InteropError::limit("integer exceeds host index range").at(t.span))
    }
    fn declaration(&mut self, quantum: bool) -> Result<(), InteropError> {
        if self.started {
            return Err(self.error(
                InteropErrorKind::Unsupported,
                "declarations must precede initialization, gates and measurements",
            ));
        }
        self.pos += 1;
        let array = self.take("[");
        let len = if array {
            let n = self.number()?;
            self.expect("]")?;
            n
        } else {
            1
        };
        if len == 0 {
            return Err(self.error(InteropErrorKind::Unsupported, "zero-size arrays"));
        }
        let start = if quantum {
            self.circuit.qubits
        } else {
            self.bits.len()
        };
        if len > MAX_QUBITS - start {
            return Err(self.error(
                InteropErrorKind::Limit,
                "at most 12 qubits and 12 classical bits",
            ));
        }
        let t = self.tokens[self.pos];
        self.pos += 1;
        let reserved = [
            "OPENQASM",
            "include",
            "qubit",
            "bit",
            "measure",
            "reset",
            "gate",
            "def",
            "defcal",
            "cal",
            "let",
            "const",
            "input",
            "output",
            "if",
            "else",
            "for",
            "while",
            "int",
            "uint",
            "float",
            "angle",
            "bool",
            "array",
            "duration",
            "stretch",
            "true",
            "false",
            "delay",
            "barrier",
            "gphase",
            "ctrl",
            "negctrl",
            "inv",
            "pow",
            "box",
            "break",
            "continue",
            "return",
            "end",
            "switch",
            "case",
            "default",
            "extern",
            "sizeof",
            "durationof",
            "defcalgrammar",
            "creg",
            "qreg",
            "void",
            "complex",
            "readonly",
            "mutable",
            "pi",
            "tau",
            "euler",
            "U",
            "CX",
            "p",
            "phase",
            "sx",
            "rx",
            "ry",
            "rz",
            "cy",
            "ch",
            "cp",
            "cphase",
            "crx",
            "cry",
            "crz",
            "cu",
            "cswap",
            "u1",
            "u2",
            "u3",
            "id",
        ];
        if !t
            .text
            .starts_with(|c: char| c.is_ascii_alphabetic() || c == '_')
            || reserved.contains(&t.text)
            || Gate::parse(t.text).is_some()
            || self.registers.contains_key(t.text)
        {
            return Err(
                InteropError::unsupported("expected a fresh, non-reserved register name")
                    .at(t.span),
            );
        }
        self.expect(";")?;
        self.registers.insert(
            t.text.to_owned(),
            Register {
                quantum,
                array,
                start,
                len,
            },
        );
        if quantum {
            self.circuit.qubits += len;
        } else {
            self.bits.resize(start + len, None);
        }
        self.declared = true;
        Ok(())
    }
    fn reference(&mut self, quantum: bool) -> Result<(Vec<usize>, bool), InteropError> {
        let t = self.tokens[self.pos];
        if !t.text.is_empty() {
            self.pos += 1;
        }
        let reg = self
            .registers
            .get(t.text)
            .ok_or_else(|| InteropError::unsupported("unknown register").at(t.span))?;
        if reg.quantum != quantum {
            return Err(InteropError::unsupported("wrong register kind").at(t.span));
        }
        let (start, len, array) = (reg.start, reg.len, reg.array);
        if self.take("[") {
            let index = self.number()?;
            self.expect("]")?;
            if !array || index >= len {
                return Err(InteropError::unsupported("index outside a fixed register").at(t.span));
            }
            Ok((vec![start + index], false))
        } else {
            Ok(((start..start + len).collect(), array))
        }
    }
    fn measurement(&mut self, target: Option<(Vec<usize>, bool)>) -> Result<(), InteropError> {
        self.require_initialized()?;
        self.expect("measure")?;
        let (qubits, array) = self.reference(true)?;
        let target = if self.take("->") {
            if target.is_some() {
                return Err(self.error(InteropErrorKind::Parse, "measurement has two destinations"));
            }
            Some(self.reference(false)?)
        } else {
            target
        };
        self.expect(";")?;
        for &q in &qubits {
            if !self.measured.insert(q) {
                return Err(self.error(
                    InteropErrorKind::Unsupported,
                    "qubit measured more than once",
                ));
            }
        }
        if let Some((bits, target_array)) = target {
            if array != target_array || qubits.len() != bits.len() {
                return Err(self.error(
                    InteropErrorKind::Unsupported,
                    "measurement register shapes differ",
                ));
            }
            for (b, q) in bits.into_iter().zip(qubits) {
                if self.bits[b].replace(q).is_some() {
                    return Err(self.error(
                        InteropErrorKind::Unsupported,
                        "classical bit assigned more than once",
                    ));
                }
            }
        }
        self.started = true;
        Ok(())
    }
    fn require_initialized(&self) -> Result<(), InteropError> {
        if self.initialized.len() != self.circuit.qubits {
            return Err(self.error(
                InteropErrorKind::Unsupported,
                "all qubits require one initial reset before gates or measurements",
            ));
        }
        Ok(())
    }
    fn initialization(&mut self) -> Result<(), InteropError> {
        if !self.circuit.gates.is_empty() || !self.measured.is_empty() {
            return Err(self.error(
                InteropErrorKind::Unsupported,
                "reset is supported only in the initialization prefix",
            ));
        }
        self.expect("reset")?;
        let (qubits, _) = self.reference(true)?;
        self.expect(";")?;
        for q in qubits {
            if !self.initialized.insert(q) {
                return Err(self.error(
                    InteropErrorKind::Unsupported,
                    "repeated initialization reset",
                ));
            }
        }
        self.started = true;
        Ok(())
    }
    fn parse(mut self) -> Result<TerminalCircuit, InteropError> {
        self.expect("OPENQASM")?;
        let version_start = self.tokens[self.pos].span.start;
        self.expect("3")?;
        self.expect(".")?;
        if !self.take("0") && !self.take("1") {
            return Err(self.error(
                InteropErrorKind::Unsupported,
                "only OpenQASM 3.0 and 3.1 headers",
            ));
        }
        self.expect(";")?;
        if self.tokens[self.pos - 2].span.end != version_start + 3 {
            return Err(self.error(
                InteropErrorKind::Parse,
                "version must be one contiguous 3.0 or 3.1 token",
            ));
        }
        while !self.peek().is_empty() {
            match self.peek() {
                "include" => {
                    if self.included || self.declared || self.started {
                        return Err(self.error(
                            InteropErrorKind::Unsupported,
                            "include must occur once before declarations",
                        ));
                    }
                    self.pos += 1;
                    if self.peek() != "\"stdgates.inc\"" {
                        return Err(self.error(InteropErrorKind::Unsupported, "only the fixed stdgates.inc contract is supported; includes are never loaded"));
                    }
                    self.pos += 1;
                    self.expect(";")?;
                    self.included = true;
                }
                "qubit" => self.declaration(true)?,
                "bit" => self.declaration(false)?,
                "reset" => self.initialization()?,
                "measure" => self.measurement(None)?,
                name if self.registers.contains_key(name) => {
                    let target = self.reference(false)?;
                    self.expect("=")?;
                    self.measurement(Some(target))?;
                }
                name => {
                    let gate = Gate::parse(name).ok_or_else(|| {
                        self.error(
                            InteropErrorKind::Unsupported,
                            "statement or gate outside the terminal subset",
                        )
                    })?;
                    self.require_initialized()?;
                    if !self.included {
                        return Err(self.error(
                            InteropErrorKind::Unsupported,
                            "standard gates require stdgates.inc",
                        ));
                    }
                    if !self.measured.is_empty() {
                        return Err(self.error(
                            InteropErrorKind::Unsupported,
                            "gate after terminal measurement",
                        ));
                    }
                    let span = self.tokens[self.pos].span;
                    self.pos += 1;
                    let mut wires = Vec::new();
                    for i in 0..gate.arity() {
                        if i > 0 {
                            self.expect(",")?;
                        }
                        let (args, array) = self.reference(true)?;
                        if array {
                            return Err(InteropError::unsupported(
                                "gate broadcasting is unsupported; index array elements",
                            )
                            .at(span));
                        }
                        wires.extend(args);
                    }
                    self.expect(";")?;
                    self.circuit.push(gate, wires).map_err(|e| e.at(span))?;
                    self.started = true;
                }
            }
        }
        self.require_initialized()?;
        for bit in &self.bits {
            self.circuit.measurements.push(bit.ok_or_else(|| {
                self.error(
                    InteropErrorKind::Unsupported,
                    "every declared classical bit must be measured exactly once",
                )
            })?);
        }
        Ok(self.circuit)
    }
}

/// Parse the bounded terminal subset and independently verify generated IR.
/// No include file, external function or imported evidence is trusted/executed.
pub fn import_openqasm3(source: &str) -> Result<AcceptedProgram, InteropError> {
    let kernel = crate::interchange::native::Kernel::selected()
        .map_err(|e| InteropError::new(InteropErrorKind::InvalidIr, e.to_string()))?;
    import_openqasm3_with_kernel(source, &kernel)
}

/// Parse and submit to the explicitly selected native acceptance boundary.
pub fn import_openqasm3_with_kernel(
    source: &str,
    kernel: &crate::interchange::native::Kernel,
) -> Result<AcceptedProgram, InteropError> {
    Parser {
        tokens: lex(source)?,
        pos: 0,
        registers: BTreeMap::new(),
        circuit: TerminalCircuit {
            qubits: 0,
            gates: vec![],
            measurements: vec![],
        },
        bits: vec![],
        measured: BTreeSet::new(),
        initialized: BTreeSet::new(),
        included: false,
        declared: false,
        started: false,
    }
    .parse()?
    .lower_with_kernel(kernel)
}

pub(super) fn write(circuit: &TerminalCircuit) -> String {
    let mut out = String::from("OPENQASM 3.0;\ninclude \"stdgates.inc\";\n");
    if circuit.qubits > 0 {
        writeln!(out, "qubit[{}] q;", circuit.qubits).unwrap();
    }
    if !circuit.measurements.is_empty() {
        writeln!(out, "bit[{}] c;", circuit.measurements.len()).unwrap();
    }
    if circuit.qubits > 0 {
        out.push_str("reset q;\n");
    }
    for op in &circuit.gates {
        let args = op
            .wires
            .iter()
            .map(|q| format!("q[{q}]"))
            .collect::<Vec<_>>()
            .join(", ");
        writeln!(out, "{} {args};", op.gate.name()).unwrap();
    }
    for (i, q) in circuit.measurements.iter().enumerate() {
        writeln!(out, "c[{i}] = measure q[{q}];").unwrap();
    }
    out
}
