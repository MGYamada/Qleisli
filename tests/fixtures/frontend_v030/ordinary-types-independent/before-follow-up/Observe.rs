// Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
// Bounded independent observation: rejection is recorded, never converted to success.
use qleisli::frontend::{compile, parser::parse_module, sized::ParsedProgram};
use qleisli::interchange::{self, Version, hierarchical};
use std::{collections::BTreeMap, fs, path::Path};

fn main() {
    let args: Vec<_> = std::env::args().collect();
    let root = Path::new(&args[1]);
    let out = Path::new(&args[2]);
    let source = fs::read_to_string(root.join("main.qli")).unwrap();
    match parse_module(&source) {
        Ok(m) => println!("common.parse: ok declarations={}", m.decls.len()),
        Err(e) => println!("common.parse: {e:?}"),
    }
    match compile::check_project_diagnostic(root) {
        Ok(()) => println!("finite.check: ok"),
        Err(e) => println!("finite.check: {e:?}"),
    }
    if args[3] == "main::main" {
        match compile::compile_project_diagnostic(root) {
            Ok(checked) => {
                println!("finite.compile: native accepted");
                fs::write(out.join("finite.qirf.json"), interchange::export(&checked, None, Version::V2).unwrap()).unwrap();
                fs::write(out.join("finite.raw.txt"), format!("{:#?}\n", checked.raw())).unwrap();
                let action = qleisli::sim::run_closed(&checked, qleisli::sim::SimulationLimits::default()).unwrap();
                fs::write(out.join("finite.action.txt"), format!("{action:?}\n")).unwrap();
            }
            Err(e) => println!("finite.compile: {e:?}"),
        }
    }
    let parsed = match ParsedProgram::parse(BTreeMap::from([("main".into(), source)])) {
        Ok(p) => { println!("sized.generic: ok"); p }
        Err(e) => { println!("sized.generic: {e:?}"); return; }
    };
    let naturals = if args.get(4).map(String::as_str) == Some("n=0") {
        BTreeMap::from([("n".into(), 0)])
    } else { BTreeMap::new() };
    let instance = match parsed.instantiate(&args[3], naturals, BTreeMap::new()) {
        Ok(p) => { println!("sized.instance: ok"); p }
        Err(e) => { println!("sized.instance: {e:?}"); return; }
    };
    let graph = match instance.elaborate() {
        Ok(p) => { println!("sized.elaborate: ok"); p }
        Err(e) => { println!("sized.elaborate: {e:?}"); return; }
    };
    let definition = &graph.definitions()[graph.root()];
    println!("sized.inputs: {:?}", definition.inputs());
    println!("sized.output: {:?}", definition.output());
    let proposal = match graph.lower() {
        Ok(p) => { println!("sized.lower: proposed instrument={}", p.is_instrument()); p }
        Err(e) => { println!("sized.lower: {e:?}"); return; }
    };
    for (name, bytes) in [("proposal.json", proposal.payload()), ("request.json", proposal.comparison_request()), ("precursor.json", proposal.lowering_precursor())] {
        fs::write(out.join(name), bytes).unwrap();
    }
    fs::write(out.join("source-events.txt"), format!("{:#?}\n", proposal.source_events())).unwrap();
    let kernel = hierarchical::Kernel::new(std::env::var_os("QLEISLI_KERNEL").unwrap());
    if proposal.is_instrument() {
        let checked = kernel.check_instrument_native(proposal.payload(), proposal.comparison_request()).unwrap();
        println!("sized.native: instrument accepted");
        let validation = proposal.validate_initialization_moves_native(&checked).unwrap();
        println!("sized.source_events: validated {} events, {} movements", validation.events(), validation.movements());
        // Successful instrument cases have exactly one physical input bit and an untouched two-state reference.
        let result = checked.execute_instrument(&[[0.3,0.2],[-0.4,0.1],[0.0,0.7],[0.5,-0.2]], 2,
            hierarchical::execution::ExecutionLimits { max_amplitudes: 64, max_steps: 10000 }).unwrap();
        fs::write(out.join("instrument.action.json"), format!("{:?}\n", result.branches)).unwrap();
    } else {
        kernel.check_against_native(proposal.payload(), proposal.comparison_request()).unwrap();
        println!("sized.native: pure accepted");
    }
}
