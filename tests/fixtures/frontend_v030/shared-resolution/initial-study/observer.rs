use std::{collections::BTreeMap, fs, path::Path};
use qleisli::frontend::{project::Project, sized::ParsedProgram, compile::check_project_diagnostic};
fn main() {
 let args: Vec<String> = std::env::args().collect();
 let root=Path::new(&args[1]);
 let mut sources=BTreeMap::new();
 for item in fs::read_dir(root).unwrap() {let p=item.unwrap().path(); if p.extension().is_some_and(|e|e=="qli") {sources.insert(p.file_stem().unwrap().to_str().unwrap().to_owned(),fs::read_to_string(p).unwrap());}}
 match Project::load(root) { Ok(p)=>println!("finite.load: ok, {} local modules",p.modules.values().filter(|m|m.origin==qleisli::frontend::project::ModuleOrigin::Local).count()),Err(e)=>println!("finite.load: {e}") }
 match ParsedProgram::parse(sources) { Ok(_)=>println!("sized.parse: ok"),Err(e)=>println!("sized.parse: {e}") }
 if args.get(2).is_some_and(|s|s=="check") { match check_project_diagnostic(root) {Ok(())=>println!("finite.check: ok"),Err(e)=>println!("finite.check: {e:?}")}}
}
