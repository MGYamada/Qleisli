// Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
// Explicit migration recorder, compiled against the preserved pre-cutover library.
// Rewrites located source type/literal tokens only; it is not a production repair path.
use qleisli::frontend::{ast::{Type,TypeKind,StaticParamKind},lexer::{lex,TokenKind},parser::parse_module};
use std::{collections::BTreeMap,fs};
fn ty(t:&Type, edits:&mut BTreeMap<usize,(usize,String)>) {
 match &t.kind {
  TypeKind::CBit=>{edits.insert(t.span.start,(t.span.start+4,"Bit".into()));}
  TypeKind::CBits(_)=>{edits.insert(t.span.start,(t.span.start+5,"Bits".into()));}
  TypeKind::Q(b)=>ty(b,edits),
  TypeKind::Tuple(xs) if xs.is_empty()=>{edits.insert(t.span.start,(t.span.end,"Unit".into()));}
  TypeKind::Tuple(xs)=>for x in xs {ty(x,edits)},
  _=>{}
 }
}
fn main(){
 let path=std::env::args().nth(1).unwrap();let text=fs::read_to_string(path).unwrap();let mut edits=BTreeMap::new();
 let module=parse_module(&text).unwrap();
 for d in module.decls {
  for p in d.params {ty(&p.ty,&mut edits)} ty(&d.return_type,&mut edits);
  for p in d.static_params {if let StaticParamKind::Operation{basis,..}=p.kind {ty(&basis,&mut edits)}}
 }
 for t in lex(&text).unwrap() {
  let value=match t.kind {TokenKind::True=>Some("1"),TokenKind::False=>Some("0"),_=>None};
  if let Some(value)=value {edits.insert(t.span.start,(t.span.end,value.into()));}
 }
 let mut out=text;for (start,(end,replacement)) in edits.into_iter().rev(){out.replace_range(start..end,&replacement)}print!("{out}");
}
