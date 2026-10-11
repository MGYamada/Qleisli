// Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
// Bounded source-profile observer. Lowering is an untrusted proposal, not native acceptance.
use std::{collections::BTreeMap, fs, path::Path};
use qleisli::frontend::{compile::check_project_diagnostic, parser::parse_module, sized::ParsedProgram};
fn main() {
    let arg=std::env::args().nth(1).unwrap();
    let root=Path::new(&arg); let source=fs::read_to_string(root.join("main.qli")).unwrap();
    match parse_module(&source) { Ok(m)=>println!("common.parse: ok declarations={}",m.decls.len()),Err(e)=>println!("common.parse: {e:?}") }
    match check_project_diagnostic(root) { Ok(())=>println!("finite.check: ok"),Err(e)=>println!("finite.check: {e:?}") }
    let parsed=match ParsedProgram::parse(BTreeMap::from([("main".into(),source)])) {Ok(p)=>{println!("sized.generic: ok");p},Err(e)=>{println!("sized.generic: {e:?}");return}};
    let instance=match parsed.instantiate("main::f",BTreeMap::new(),BTreeMap::new()) {Ok(i)=>{println!("sized.instance: ok");i},Err(e)=>{println!("sized.instance: {e:?}");return}};
    let elaborated=match instance.elaborate(){Ok(e)=>{println!("sized.elaborate: ok");e},Err(e)=>{println!("sized.elaborate: {e:?}");return}};
    let root=&elaborated.definitions()[elaborated.root()];
    println!("sized.inputs: {:?}",root.inputs());println!("sized.output: {:?}",root.output());
    match elaborated.lower(){Ok(p)=>println!("sized.lower: proposed instrument={} bytes={}",p.is_instrument(),p.payload().len()),Err(e)=>println!("sized.lower: {e:?}")}
}
