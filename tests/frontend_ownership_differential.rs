//! Both source checkers enforce the same ownership rules on their common subset.
//!
//! This deterministic regression compares source acceptance, not lowering profiles,
//! diagnostic ordering, algorithm correctness, or model-authoring performance.
// Copyright 2026 Masahiko G. Yamada
// SPDX-License-Identifier: Apache-2.0

mod common;

use std::collections::BTreeMap;

use common::SourceRoot;
use qleisli::frontend::compile::check_project;
use qleisli::frontend::sized::ParsedProgram;

const SEED: u64 = 0x514c_4549_534c_4932;
const CASES: usize = 4_000;
const IMPORTS: &str = "use std::quantum::h; use std::quantum::x;
use std::quantum::cnot; use std::quantum::init0;
use std::observe::measure_z;\n";

struct Random(u64);

impl Random {
    fn choose(&mut self, count: usize) -> usize {
        self.0 = self
            .0
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        ((self.0 >> 32) % count as u64) as usize
    }
}

#[derive(Clone, Copy, Debug)]
enum Fault {
    None,
    ConsumedUse,
    DuplicateArguments,
    LiveOverwrite,
    ReturnOmission,
    EffectUnderdeclaration,
    QuantumExpressionStatement,
}

impl Fault {
    fn for_case(index: usize) -> Self {
        match index % 8 {
            0 | 1 => Self::None,
            2 => Self::ConsumedUse,
            3 => Self::DuplicateArguments,
            4 => Self::LiveOverwrite,
            5 => Self::ReturnOmission,
            6 => Self::EffectUnderdeclaration,
            _ => Self::QuantumExpressionStatement,
        }
    }

    fn accepted(self) -> bool {
        matches!(self, Self::None)
    }
}

struct Case {
    fault: Fault,
    source: String,
}

fn fresh(serial: &mut usize) -> String {
    let name = format!("v{serial}");
    *serial += 1;
    name
}

fn tuple(fields: &[String]) -> String {
    match fields {
        [field] => field.clone(),
        _ => format!("({})", fields.join(",")),
    }
}

fn generate(random: &mut Random, fault: Fault) -> Case {
    let initial_qubits = 1 + random.choose(2);
    let mut quantum = (0..initial_qubits)
        .map(|index| format!("q{index}"))
        .collect::<Vec<_>>();
    let arguments = quantum
        .iter()
        .map(|name| format!("{name}: Q<Bit>"))
        .chain(std::iter::once("tag: CBit".into()))
        .collect::<Vec<_>>()
        .join(",");
    let mut classical = vec!["tag".into()];
    let mut serial = 0;
    let mut body = String::new();
    // The normal prefix allocates at most two qubits in total. An invalid
    // overwrite can propose one additional init0, keeping every source <= 3.
    let mut allocated = initial_qubits;
    let mut effect = 0;
    for _ in 0..4 + random.choose(13) {
        let index = random.choose(quantum.len());
        let old = quantum[index].clone();
        match random.choose(9) {
            0 | 1 => {
                let new = fresh(&mut serial);
                let gate = if random.choose(2) == 0 { "h" } else { "x" };
                body.push_str(&format!("    let {new}={gate}({old});\n"));
                quantum[index] = new;
            }
            2 => body.push_str(&format!("    let {old}={old};\n")),
            3 if quantum.len() == 2 => {
                let a = fresh(&mut serial);
                let b = fresh(&mut serial);
                let other = quantum[1 - index].clone();
                body.push_str(&format!("    let ({a},{b})=cnot({old},{other});\n"));
                quantum[index] = a;
                quantum[1 - index] = b;
            }
            4 => {
                let packet = fresh(&mut serial);
                let new = fresh(&mut serial);
                let copied = fresh(&mut serial);
                let tag = &classical[random.choose(classical.len())];
                body.push_str(&format!(
                    "    let {packet}=({old},{tag});\n    let ({new},{copied})={packet};\n"
                ));
                quantum[index] = new;
                classical.push(copied);
            }
            5 if quantum.len() == 2 => {
                let packet = fresh(&mut serial);
                let a = fresh(&mut serial);
                let b = fresh(&mut serial);
                let copied = fresh(&mut serial);
                let other = quantum[1 - index].clone();
                let tag = &classical[random.choose(classical.len())];
                let nested = random.choose(2) == 0;
                let value = if nested {
                    format!("({old},({tag},{other}))")
                } else {
                    format!("({old},{tag},{other})")
                };
                let pattern = if nested {
                    format!("({a},({copied},{b}))")
                } else {
                    format!("({a},{copied},{b})")
                };
                body.push_str(&format!(
                    "    let {packet}={value};\n    let {pattern}={packet};\n"
                ));
                quantum[index] = a;
                quantum[1 - index] = b;
                classical.push(copied);
            }
            6 if allocated < 2 => {
                let new = fresh(&mut serial);
                body.push_str(&format!("    let {new}=init0();\n"));
                quantum.push(new);
                allocated += 1;
                effect = effect.max(1);
            }
            7 if quantum.len() > 1 => {
                let measured = fresh(&mut serial);
                body.push_str(&format!("    let {measured}=measure_z({old});\n"));
                quantum.remove(index);
                classical.push(measured);
                effect = 2;
            }
            _ => {
                let tag = &classical[random.choose(classical.len())];
                body.push_str(&format!("    {tag};\n    ();\n"));
            }
        }
    }
    let target = quantum[random.choose(quantum.len())].clone();
    match fault {
        Fault::None => {}
        Fault::ConsumedUse => {
            let moved = fresh(&mut serial);
            let broken = fresh(&mut serial);
            body.push_str(&format!(
                "    let {moved}={target};\n    let {broken}=h({target});\n"
            ));
            for name in &mut quantum {
                if *name == target {
                    *name = moved.clone();
                }
            }
        }
        Fault::DuplicateArguments => {
            let a = fresh(&mut serial);
            let b = fresh(&mut serial);
            body.push_str(&format!("    let ({a},{b})=cnot({target},{target});\n"));
        }
        Fault::LiveOverwrite => {
            body.push_str(&format!("    let {target}=init0();\n"));
            allocated += 1;
            effect = effect.max(1);
        }
        Fault::ReturnOmission => quantum.retain(|name| *name != target),
        Fault::EffectUnderdeclaration => {
            let measured = fresh(&mut serial);
            body.push_str(&format!("    let {measured}=measure_z({target});\n"));
            quantum.retain(|name| *name != target);
            classical.push(measured);
            effect = 2;
        }
        Fault::QuantumExpressionStatement => {
            body.push_str(&format!("    h({target});\n"));
        }
    }
    assert!(allocated <= 3);
    let mut returned = quantum.clone();
    let mut result_types = vec!["Q<Bit>".to_owned(); quantum.len()];
    // Classical owners are copyable: returning a copied tag more than once is
    // a normal control against accidentally applying quantum rules to CBit.
    for _ in 0..1 + random.choose(3) {
        returned.push(classical[random.choose(classical.len())].clone());
        result_types.push("CBit".into());
    }
    let declaration = if matches!(fault, Fault::EffectUnderdeclaration) {
        "unitary"
    } else {
        ["unitary", "iso", "observe"][effect + random.choose(3 - effect)]
    };
    Case {
        fault,
        source: format!(
            "{IMPORTS}pub {declaration} fn candidate({arguments}) -> {} {{\n{body}    {}\n}}\n",
            tuple(&result_types),
            tuple(&returned)
        ),
    }
}

#[test]
fn finite_and_sized_checkers_agree_on_common_linear_ownership() {
    let mut random = Random(SEED);
    // Retain all first sources before either checker runs. Failure context
    // contains the exact source, seed and case for deterministic reproduction.
    let cases = (0..CASES)
        .map(|index| generate(&mut random, Fault::for_case(index)))
        .collect::<Vec<_>>();
    let root = SourceRoot::new("");
    let mut accepted = 0;
    let mut rejected = 0;
    for (index, case) in cases.iter().enumerate() {
        root.write("main.qli", &case.source);
        let finite = check_project(&root.0).map_err(|error| error.to_string());
        let sized = ParsedProgram::parse(BTreeMap::from([("main".into(), case.source.clone())]))
            .map(|_| ())
            .map_err(|error| error.to_string());
        let context = format!(
            "seed={SEED:#x}, case={index}, fault={:?}\n{}\nfinite={finite:?}\nsized={sized:?}",
            case.fault, case.source
        );
        assert_eq!(finite.is_ok(), sized.is_ok(), "{context}");
        assert_eq!(finite.is_ok(), case.fault.accepted(), "{context}");
        if finite.is_ok() {
            accepted += 1;
        } else {
            rejected += 1;
        }
    }
    assert_eq!(accepted + rejected, CASES);
    assert!(accepted > 0 && rejected > 0);
}
