use qleisli::frontend::{parser::parse_module,sized::ParsedProgram};
use std::collections::BTreeMap;
fn main(){ let source=std::fs::read_to_string(std::env::args().nth(1).unwrap()).unwrap();
match parse_module(&source){Ok(m)=>println!("finite: ok declarations={}",m.decls.len()),Err(e)=>println!("finite: error {}..{} {}",e.span.start,e.span.end,e.message)}
match ParsedProgram::parse(BTreeMap::from([("main".into(),source)])){Ok(_)=>println!("sized: ok"),Err(e)=>println!("sized: error {} {}..{} {}",e.code(),e.span().start,e.span().end,e.message())}
}
