use qleisli::frontend::ast::{Block, Expr, ExprKind, FnBody, StmtKind};
use qleisli::frontend::parser::parse_module;
fn block(b: &Block) { for s in &b.statements { match &s.kind { StmtKind::Let { value, .. } | StmtKind::Expr(value) => expr(value) } } expr(&b.result); }
fn expr(e: &Expr) {
 match &e.kind {
 ExprKind::CoherentLift { binder, input, basis } => {
 println!("{} {} {} {} {} {} {} {}", e.span.start,e.span.end,binder.span.start,binder.span.end,input.span.start,input.span.end,basis.span.start,basis.span.end); expr(input);
 },
 ExprKind::ApplyContract { input, .. } | ExprKind::Adjoint { input, .. } | ExprKind::RepeatStatic { input, .. } | ExprKind::Not(input) => expr(input),
 ExprKind::QuantumIf { control, target, .. } | ExprKind::And(control,target) | ExprKind::Xor(control,target) => { expr(control); expr(target); },
 ExprKind::Tuple(args) | ExprKind::Controlled { args, .. } | ExprKind::Call { args, .. } => { for a in args { expr(a) } },
 ExprKind::If { condition,then_branch,else_branch } => { expr(condition);block(then_branch);block(else_branch); },
 ExprKind::StaticIf { then_branch,else_branch, .. } => { block(then_branch);block(else_branch); },
 ExprKind::StaticFold { initial,body, .. } => { expr(initial);block(body); },
 ExprKind::WithComputed { source,body, .. } | ExprKind::CertifiedComputed { source,body, .. } => { expr(source);block(body); },
 ExprKind::Name(_) | ExprKind::Bit(_) | ExprKind::Unit => {},
 }
}
fn main() {
 let path=std::env::args().nth(1).expect("source path");
 let source=std::fs::read_to_string(path).expect("read source");
 match parse_module(&source) { Ok(module)=>for d in &module.decls { if let FnBody::Quantum(b)=&d.body { block(b); } },Err(e)=>{ eprintln!("{} {} {}",e.span.start,e.span.end,e.message);std::process::exit(2); } }
}
