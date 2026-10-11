use std::{collections::BTreeMap,fs,path::Path};
use qleisli::frontend::sized::ParsedProgram;
use qleisli::interchange::hierarchical::{Kernel, execution::ExecutionLimits};
fn main() {
 let args:Vec<_>=std::env::args().collect();let root=Path::new(&args[1]);let kernel=Kernel::new(&args[2]);
 for order in args[3..].iter().map(String::as_str) {
  let dir=root.join("sources").join(order);let mut sources=BTreeMap::new();
  for name in ["main","left","right"] {sources.insert(name.into(),fs::read_to_string(dir.join(format!("{name}.qli"))).unwrap());}
  let p=ParsedProgram::parse(sources).unwrap().instantiate("main::f",BTreeMap::new(),BTreeMap::new()).unwrap().elaborate().unwrap().lower().unwrap();
  fs::write(root.join(format!("{order}.json")),p.payload()).unwrap();
  fs::write(root.join(format!("{order}.precursor.json")),p.lowering_precursor()).unwrap();
  fs::write(root.join(format!("{order}.request.json")),p.comparison_request()).unwrap();
  let checked=kernel.inspect_native(p.payload()).unwrap();
  let dim=if order.starts_with("unit-") {4} else {16};let mut input=vec![[0.0,0.0];dim*dim];for i in 0..dim {input[i+dim*i]=[1.0,0.0];}
  let output=checked.execute_pure(&input,dim,ExecutionLimits{max_amplitudes:4096,max_steps:1_000_000}).unwrap();
  fs::write(root.join(format!("{order}.matrix.json")),format!("{:?}\n",output.amplitudes)).unwrap();
  println!("{order}: native whole-artifact inspection passed; {} amplitudes; structural work {}; exact work {}",output.amplitudes.len(),checked.structural_work(),checked.exact_work());
 }
}
