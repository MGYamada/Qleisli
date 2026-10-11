#![allow(dead_code)]
mod ast; mod documentation; mod lexer; mod parser; mod scanner;
fn main(){let s=std::env::args().nth(1).unwrap(); println!("{:?}",parser::parse_module(&s));}
