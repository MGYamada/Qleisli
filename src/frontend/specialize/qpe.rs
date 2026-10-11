//! Untrusted candidate discovery. Native checking and exact reconstruction are mandatory.
use super::{Error, HierarchyProposal, Result, Span};
use crate::interchange::{
    self,
    json::{self, Value},
};
use std::collections::BTreeSet;
type DecodeResult<T> = std::result::Result<T, interchange::Error>;

/// Independent provider request plus an untrusted QPE layout/component proposal.
#[derive(Clone, Debug)]
pub struct QpeBindingProposal {
    request: Vec<u8>,
    candidate: Vec<u8>,
}
impl QpeBindingProposal {
    pub fn request(&self) -> &[u8] {
        &self.request
    }
    pub fn candidate(&self) -> &[u8] {
        &self.candidate
    }
}
fn fail(s: &str) -> interchange::Error {
    interchange::Error::new("unsupported", s)
}
fn index(v: &Value) -> DecodeResult<usize> {
    usize::try_from(v.number()?).map_err(|_| fail("QPE index exceeds host capacity"))
}
fn numbers(xs: impl IntoIterator<Item = usize>) -> Value {
    Value::Array(xs.into_iter().map(|n| Value::Number(n as u64)).collect())
}
fn text(s: &str) -> Value {
    Value::String(s.into())
}
fn axes(side: &Value) -> DecodeResult<Vec<usize>> {
    let mut result = Vec::new();
    for p in side.field("quantum")?.array()? {
        for a in p.field("axes")?.array()? {
            result.push(index(a)?);
        }
    }
    Ok(result)
}
struct Selection<'a> {
    definitions: &'a [Value],
    atoms: Vec<usize>,
    order: Vec<usize>,
    seen: BTreeSet<usize>,
    visits: usize,
}
impl<'a> Selection<'a> {
    fn new(definitions: &'a [Value]) -> Self {
        Self {
            definitions,
            atoms: vec![],
            order: vec![],
            seen: BTreeSet::new(),
            visits: 0,
        }
    }
    fn definition(&self, i: usize) -> DecodeResult<&Value> {
        self.definitions
            .get(i)
            .ok_or_else(|| fail("QPE candidate references a missing definition"))
    }
    fn walk(&mut self, i: usize, wiring: bool, depth: usize) -> DecodeResult<()> {
        self.visits += 1;
        if self.visits > 100_000 || depth > 128 {
            return Err(fail("QPE candidate traversal capacity exceeded"));
        }
        let b = self.definition(i)?.field("body")?;
        let children = match b.field("tag")?.text()? {
            "leaf" | "control" | "inverse" if !wiring => {
                self.atoms.push(i);
                vec![]
            }
            "sequence" => b
                .field("children")?
                .array()?
                .iter()
                .map(index)
                .collect::<DecodeResult<Vec<_>>>()?,
            "tensor" => vec![index(b.field("left")?)?, index(b.field("right")?)?],
            "rewire" | "structural" => vec![],
            _ => return Err(fail("unsupported QPE routing node")),
        };
        for child in children {
            self.walk(child, wiring, depth + 1)?;
        }
        if self.seen.insert(i) {
            self.order.push(i);
        }
        Ok(())
    }
    fn atom(&self, i: usize) -> DecodeResult<Value> {
        Ok(Value::object([
            ("index", Value::Number(i as u64)),
            ("interface", self.definition(i)?.field("interface")?.clone()),
        ]))
    }
}
fn build(proposal: &HierarchyProposal, provider: &[u8]) -> DecodeResult<QpeBindingProposal> {
    if !proposal.is_instrument() {
        return Err(fail("named QPE requires an observing proposal"));
    }
    let g = json::parse(proposal.pure_graph())?;
    let boundary = json::parse(proposal.comparison_request())?;
    let provider = json::parse(provider)?;
    let definitions = g.field("definitions")?.array()?;
    let root = index(g.field("entry")?.field("implementation")?)?;
    let mut s = Selection::new(definitions);
    s.walk(root, false, 0)?;
    let (mut hs, mut powers, mut power_orders, mut inverses, mut providers) =
        (vec![], vec![], vec![], vec![], BTreeSet::new());
    for &i in &s.atoms {
        let body = s.definition(i)?.field("body")?;
        match body.field("tag")?.text()? {
            "leaf" => hs.push(s.atom(i)?),
            "inverse" => inverses.push(i),
            "control" => {
                powers.push(s.atom(i)?);
                let child = index(body.field("definition")?)?;
                let shell = s.definition(child)?.field("body")?;
                let children = shell.field("children")?.array()?;
                if shell.field("tag")?.text()? != "sequence" || children.len() != 3 {
                    return Err(fail("QPE power needs the closed provider routing shell"));
                }
                let core = index(&children[1])?;
                let inner = s.definition(core)?.field("body")?;
                providers.insert(if inner.field("tag")?.text()? == "repeat" {
                    index(inner.field("definition")?)?
                } else {
                    core
                });
                power_orders.push(numbers([index(&children[0])?, index(&children[2])?]));
            }
            _ => unreachable!(),
        }
    }
    let prep = boundary.field("preparation")?;
    let n = axes(prep.field("inputs")?)?.len();
    let m = prep.field("fresh")?.array()?.len();
    if !(1..=8).contains(&n)
        || !(1..=8).contains(&m)
        || hs.len() != m
        || powers.len() != m
        || inverses.len() != 1
        || providers.len() != 1
    {
        return Err(fail("candidate is not one complete bounded QPE schedule"));
    }
    let p = *providers
        .first()
        .ok_or_else(|| fail("missing QPE provider"))?;
    let proof = g
        .field("proofs")?
        .array()?
        .iter()
        .enumerate()
        .find_map(|(i, v)| (v.field("implementation").and_then(index).ok() == Some(p)).then_some(i))
        .ok_or_else(|| fail("provider has no proposed proof"))?;
    let inverse = inverses[0];
    let forward = index(s.definition(inverse)?.field("body")?.field("definition")?)?;
    let shell = s.definition(forward)?.field("body")?;
    let children = shell.field("children")?.array()?;
    if shell.field("tag")?.text()? != "sequence" || children.len() < 3 {
        return Err(fail("Fourier operand needs a checked recursive shell"));
    }
    let mut wiring = Selection::new(definitions);
    for (i, child) in children.iter().enumerate() {
        if i != 1 {
            wiring.walk(index(child)?, true, 0)?;
        }
    }
    let interface = s.definition(root)?.field("interface")?.clone();
    let input = axes(interface.field("inputs")?)?;
    let route = axes(interface.field("outputs")?)?
        .into_iter()
        .map(|a| {
            input
                .iter()
                .position(|x| *x == a)
                .ok_or_else(|| fail("QPE output introduced an axis"))
        })
        .collect::<DecodeResult<Vec<_>>>()?;
    let request = Value::object([
        ("format", text("qleisli.qpe-instrument-request")),
        ("version", Value::Number(1)),
        ("profile", text("qpe-dyadic8-v1")),
        ("preparation", prep.clone()),
        ("provider", provider),
        (
            "circuit",
            Value::object([
                ("interface", interface),
                ("phase", numbers((n..n + m).rev())),
                ("target", numbers(0..n)),
                ("route", numbers(route)),
                ("provider", Value::Number(p as u64)),
            ]),
        ),
        ("readout", boundary.field("readout")?.clone()),
        ("outputs", boundary.field("outputs")?.clone()),
    ]);
    let candidate = Value::object([
        ("format", text("qleisli.qpe-instrument-candidate")),
        ("version", Value::Number(1)),
        ("profile", text("qpe-dyadic8-v1")),
        ("provider_proof", Value::Number(proof as u64)),
        ("hadamards", Value::Array(hs)),
        ("powers", Value::Array(powers)),
        ("inverse_fourier", s.atom(inverse)?),
        ("trace_order", numbers(s.order)),
        ("power_orders", Value::Array(power_orders)),
        ("fourier_order", numbers(wiring.order)),
    ]);
    Ok(QpeBindingProposal {
        request: json::encode(&request)?,
        candidate: json::encode(&candidate)?,
    })
}
impl HierarchyProposal {
    /// Propose positive-sign, little-endian measured QPE. The caller supplies the
    /// intended provider request; actual provider meanings are never copied into
    /// it. This can reject equivalent circuits outside the producer shape.
    /// Success requires fresh `Kernel::check_qpe_instrument` before execution.
    pub fn qpe_binding(&self, independent_provider_request: &[u8]) -> Result<QpeBindingProposal> {
        build(self, independent_provider_request)
            .map_err(|e| Error::new("unsupported", Span::default(), e.to_string()))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::frontend::compile::{OperationBinding, ParsedProgram};
    use crate::interchange::hierarchical::{Kernel, execution::ExecutionLimits};
    use std::collections::BTreeMap;
    fn source(n: u32, m: u32, j: u32) -> HierarchyProposal {
        source_with_fourier(n, m, j, None)
    }
    fn source_with_fourier(n: u32, m: u32, j: u32, fourier: Option<&str>) -> HierarchyProposal {
        let modules = [
            ("measurement", "corpus/sized/measured_qpe/measurement.qli"),
            (
                "initialization",
                "corpus/sized/measured_qpe/initialization.qli",
            ),
            ("readout", "corpus/sized/measured_qpe/readout.qli"),
            ("estimation", "tests/fixtures/frontend_v030/qfor/current/corpus/sized/qualtran_qpe/estimation.qli"),
            ("preparation", "tests/fixtures/frontend_v030/qfor/current/corpus/sized/qualtran_qpe/preparation.qli"),
            ("fourier", "tests/fixtures/frontend_v030/qfor/current/corpus/sized/qualtran_qft/fourier.qli"),
            ("evolution", "corpus/sized/qualtran_qpe/evolution.qli"),
        ]
        .into_iter()
        .map(|(name, path)| {
            let body = if name == "fourier" {
                fourier.map(str::to_owned)
            } else {
                None
            }
            .unwrap_or_else(|| {
                let script = "import sys; from pathlib import Path; sys.path.insert(0, 'scripts'); from current_source_fixtures import current_source_file; print(current_source_file(Path(sys.argv[1]).resolve()).read_text(), end='')";
                let output = std::process::Command::new("python3")
                    .args(["-c", script, path])
                    .current_dir(env!("CARGO_MANIFEST_DIR"))
                    .output()
                    .unwrap();
                assert!(output.status.success(), "{}", String::from_utf8_lossy(&output.stderr));
                String::from_utf8(output.stdout).unwrap()
            });
            let body = if name == "fourier" {
                // Preserve historical QFT bytes; translate only this test input.
                let old = "fourier[static n: Nat]";
                assert_eq!(body.matches(old).count(), 1);
                body.replacen(old, "fourier[const n: Nat]", 1)
            } else { body };
            (name.into(), body)
        })
        .collect();
        ParsedProgram::parse(modules)
            .unwrap()
            .instantiate(
                "measurement::qpe",
                BTreeMap::from([("n".into(), n), ("m".into(), m)]),
                BTreeMap::from([(
                    "U".into(),
                    OperationBinding::new(
                        "evolution::evolve",
                        BTreeMap::from([("n".into(), n), ("j".into(), j), ("d".into(), 3)]),
                    ),
                )]),
            )
            .unwrap()
            .elaborate()
            .unwrap()
            .lower()
            .unwrap()
    }
    // This freezes a previously chosen provider graph for mutation regressions.
    // It is not an independent mathematical proof. Full complex coefficients
    // below use a separate low-target-bit phase formula.
    fn frozen_provider(p: &HierarchyProposal) -> Vec<u8> {
        let placeholder = br#"{}"#;
        let discovered = p.qpe_binding(placeholder).unwrap();
        let request = json::parse(discovered.request()).unwrap();
        let g = json::parse(p.pure_graph()).unwrap();
        let provider = index(request.field("circuit").unwrap().field("provider").unwrap()).unwrap();
        let proof = g
            .field("proofs")
            .unwrap()
            .array()
            .unwrap()
            .iter()
            .find(|v| index(v.field("implementation").unwrap()).unwrap() == provider)
            .unwrap();
        let entry = index(proof.field("meaning").unwrap()).unwrap();
        let meanings = g.field("meanings").unwrap().array().unwrap();
        let mut seen = BTreeSet::new();
        let mut todo = vec![entry];
        while let Some(i) = todo.pop() {
            if !seen.insert(i) {
                continue;
            }
            let body = meanings[i].field("body").unwrap();
            match body.field("tag").unwrap().text().unwrap() {
                "sequence" => todo.extend(
                    body.field("children")
                        .unwrap()
                        .array()
                        .unwrap()
                        .iter()
                        .map(|v| index(v).unwrap()),
                ),
                "tensor" => todo.extend([
                    index(body.field("left").unwrap()).unwrap(),
                    index(body.field("right").unwrap()).unwrap(),
                ]),
                "inverse" | "control" | "power" => {
                    todo.push(index(body.field("child").unwrap()).unwrap())
                }
                _ => {}
            }
        }
        let remap: BTreeMap<_, _> = seen.iter().enumerate().map(|(i, &old)| (old, i)).collect();
        let required = seen
            .into_iter()
            .map(|i| {
                let Value::Object(mut value) = meanings[i].clone() else {
                    panic!("meaning")
                };
                let Value::Object(mut body) = value.remove("body").unwrap() else {
                    panic!("body")
                };
                let tag = body["tag"].text().unwrap();
                let fields = match tag {
                    "tensor" => vec!["left", "right"],
                    "inverse" | "control" | "power" => vec!["child"],
                    _ => vec![],
                };
                if tag == "sequence" {
                    let ids = body["children"]
                        .array()
                        .unwrap()
                        .iter()
                        .map(|v| remap[&index(v).unwrap()])
                        .collect::<Vec<_>>();
                    body.insert("children".into(), numbers(ids));
                }
                for field in fields {
                    let target = remap[&index(&body[field]).unwrap()];
                    body.insert(field.into(), Value::Number(target as u64));
                }
                value.insert("body".into(), Value::Object(body));
                Value::Object(value)
            })
            .collect();
        json::encode(&Value::object([
            ("format", text("qleisli.hierarchy-request")),
            ("version", Value::Number(1)),
            ("profile", text("qpe-dyadic8-v1")),
            ("kind", text("equation")),
            ("effect", text("unitary")),
            (
                "interface",
                g.field("definitions").unwrap().array().unwrap()[provider]
                    .field("interface")
                    .unwrap()
                    .clone(),
            ),
            ("meanings", Value::Array(required)),
            ("entry", Value::Number(remap[&entry] as u64)),
        ]))
        .unwrap()
    }
    #[test]
    fn qpe_candidate_retains_a_separate_caller_request_and_actual_h_roles() {
        let p = source(1, 2, 1);
        let independent = br#"{"independent":"caller supplied"}"#;
        let b = p.qpe_binding(independent).unwrap();
        let request = json::parse(b.request()).unwrap();
        assert_eq!(
            request.field("provider").unwrap(),
            &json::parse(independent).unwrap()
        );
        let candidate = json::parse(b.candidate()).unwrap();
        let hs = candidate.field("hadamards").unwrap().array().unwrap();
        assert_eq!(hs.len(), 2);
        // Finite leaves use their actual source ports directly. Distinct axes
        // need distinct interfaces; every complete H program is checked fresh.
        assert_ne!(hs[0], hs[1]);
        let graph = json::parse(p.pure_graph()).unwrap();
        let definitions = graph.field("definitions").unwrap().array().unwrap();
        for h in hs {
            let definition = &definitions[h.field("index").unwrap().number().unwrap() as usize];
            let body = definition.field("body").unwrap();
            assert_eq!(body.field("tag").unwrap().text().unwrap(), "leaf");
            let program = body.field("program").unwrap().text().unwrap();
            let imported = crate::interchange::import(program.as_bytes(), None).unwrap();
            assert!(matches!(
                imported.program.raw().operations.as_slice(),
                [crate::ir::RawOp::Gate {
                    gate: crate::ir::SingleGate::H,
                    ..
                }]
            ));
        }
    }
    #[test]
    #[ignore = "requires freshly built native kernel; CI runs explicitly"]
    fn native_named_qpe_commuting_fourier_variants_have_the_same_outcome() {
        let kernel =
            Kernel::new(std::env::var_os("QLEISLI_HIERARCHY_KERNEL").expect("kernel path"));
        let delayed = include_str!(
            "../../../tests/fixtures/frontend_v030/qfor/current/tests/fixtures/frontend_v030/ordinary-type-cutover/current/sized_clients/delayed_fourier.qli"
        );
        for m in [2, 3] {
            let textbook = source(1, m, 1);
            // This detached provider is fixed before building the reordered
            // circuit. Existing native QPE tests separately check its phase
            // against the low-bit mathematical formula and mutate the provider.
            let provider = frozen_provider(&textbook);
            let reordered = source_with_fourier(1, m, 1, Some(delayed));
            let mut outcomes = vec![];
            for (variant, proposal) in [("textbook", &textbook), ("delayed", &reordered)] {
                let binding = proposal.qpe_binding(&provider).unwrap();
                if let Some(directory) = std::env::var_os("QLEISLI_QPE_PERF_PROPOSALS") {
                    let directory = std::path::PathBuf::from(directory);
                    std::fs::create_dir_all(&directory).unwrap();
                    for (suffix, bytes) in [
                        ("payload", proposal.payload()),
                        ("request", binding.request()),
                        ("candidate", binding.candidate()),
                        ("precursor", proposal.lowering_precursor()),
                    ] {
                        std::fs::write(
                            directory.join(format!("n1-m{m}-{variant}-{suffix}.json")),
                            bytes,
                        )
                        .unwrap();
                    }
                }
                let result = kernel.check_qpe_instrument(
                    proposal.payload(),
                    binding.request(),
                    binding.candidate(),
                );
                outcomes.push(match result {
                    Ok(checked) => {
                        proposal
                            .validate_initialization_moves(checked.instrument())
                            .unwrap();
                        let input = [[0.3, 0.2], [0.4, -0.1], [-0.2, 0.5], [0.1, 0.3]];
                        let output = checked
                            .instrument()
                            .execute(
                                &input,
                                2,
                                ExecutionLimits {
                                    max_amplitudes: 4096,
                                    max_steps: 1_000_000,
                                },
                            )
                            .unwrap();
                        for (y, branch) in output.branches.iter().enumerate() {
                            for (i, z) in input.iter().enumerate() {
                                let theta = ((i % 2) & 1) as f64 / 8.0;
                                let mut k = [0.0, 0.0];
                                let count = (1usize << m) as f64;
                                for a in 0..1usize << m {
                                    let angle = std::f64::consts::TAU
                                        * a as f64
                                        * (theta - y as f64 / count);
                                    k[0] += angle.cos() / count;
                                    k[1] += angle.sin() / count;
                                }
                                let expected =
                                    [z[0] * k[0] - z[1] * k[1], z[0] * k[1] + z[1] * k[0]];
                                assert!(
                                    (branch[i][0] - expected[0]).abs() < 1e-12
                                        && (branch[i][1] - expected[1]).abs() < 1e-12
                                );
                            }
                        }
                        let changed =
                            source_with_fourier(1, m, 2, (variant == "delayed").then_some(delayed));
                        let changed_binding = changed.qpe_binding(&provider).unwrap();
                        let error = kernel
                            .check_qpe_instrument(
                                changed.payload(),
                                changed_binding.request(),
                                changed_binding.candidate(),
                            )
                            .unwrap_err();
                        assert_eq!(error.code, "contract", "provider phase mutation: {error}");
                        (
                            "ok",
                            Some(checked.instrument().reconstruction().structural_work()),
                            Some(checked.instrument().reconstruction().exact_work()),
                        )
                    }
                    Err(error) => panic!("n=1,m={m},variant={variant}: {error}"),
                });
            }
            println!(
                "named QPE n=1,m={m}: textbook {:?}, delayed {:?}",
                outcomes[0], outcomes[1]
            );
            assert_eq!(outcomes[0], outcomes[1]);
        }
    }
    #[test]
    #[ignore = "requires freshly built native kernel; CI runs explicitly"]
    fn native_named_qpe_from_rust_source_checks_phase_reference_and_provider_mutation() {
        let kernel =
            Kernel::new(std::env::var_os("QLEISLI_HIERARCHY_KERNEL").expect("kernel path"));
        for (n, m) in [(1, 1), (1, 2), (2, 2)] {
            let p = source(n, m, 1);
            let provider = frozen_provider(&p);
            let b = p.qpe_binding(&provider).unwrap();
            if let Some(directory) = std::env::var_os("QLEISLI_QPE_PROPOSALS") {
                let directory = std::path::PathBuf::from(directory);
                std::fs::create_dir_all(&directory).unwrap();
                for (suffix, bytes) in [
                    ("payload", p.payload()),
                    ("request", b.request()),
                    ("candidate", b.candidate()),
                ] {
                    std::fs::write(directory.join(format!("n{n}-m{m}-{suffix}.json")), bytes)
                        .unwrap();
                }
            }
            let checked = kernel
                .check_qpe_instrument(p.payload(), b.request(), b.candidate())
                .unwrap_or_else(|e| panic!("n={n},m={m}: {e}"));
            p.validate_initialization_moves(checked.instrument())
                .unwrap();
            let d = 1usize << n;
            let input: Vec<_> = (0..2 * d)
                .map(|i| [(i + 1) as f64 / 7.0, (i % 3) as f64 / -9.0])
                .collect();
            let output = checked
                .instrument()
                .execute(
                    &input,
                    2,
                    ExecutionLimits {
                        max_amplitudes: 1 << 20,
                        max_steps: 10_000_000,
                    },
                )
                .unwrap();
            let count = 1usize << m;
            for (y, branch) in output.branches.iter().enumerate() {
                for (i, z) in input.iter().enumerate() {
                    let theta = ((i % d) & 1) as f64 / 8.0;
                    let mut k = [0.0, 0.0];
                    for a in 0..count {
                        let phase =
                            std::f64::consts::TAU * a as f64 * (theta - y as f64 / count as f64);
                        k[0] += phase.cos() / count as f64;
                        k[1] += phase.sin() / count as f64;
                    }
                    let expected = [z[0] * k[0] - z[1] * k[1], z[0] * k[1] + z[1] * k[0]];
                    assert!(
                        (branch[i][0] - expected[0]).abs() < 1e-12
                            && (branch[i][1] - expected[1]).abs() < 1e-12,
                        "n={n},m={m},y={y},i={i}"
                    );
                }
            }
            let changed = source(n, m, 2);
            let changed_binding = changed.qpe_binding(&provider).unwrap();
            assert!(
                kernel
                    .check_qpe_instrument(
                        changed.payload(),
                        changed_binding.request(),
                        changed_binding.candidate()
                    )
                    .is_err()
            );
        }
    }
}
