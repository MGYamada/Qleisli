use qleisli::ir::*;
use qleisli::interchange::native::Kernel;
use qleisli::sim::{SampleLimits,sample_closed};
fn main() {
 let raw = RawProgram { quantum_inputs: vec![], classical_inputs: vec![], quantum_outputs: vec![], classical_outputs: vec![ClassicalId(0)], declared_effect: Effect::Observe, operations: vec![RawOp::Init0 {output:TokenId(0),wire:WireId(0)},RawOp::MeasureZ {input:TokenId(0),output:ClassicalId(0)}] };
 let p = Kernel::selected().unwrap().accept_raw(raw).unwrap();
 for limit in [2,3] {
  let mut draws=0;
  let mut rng=|| {draws+=1; Ok::<u64,()>(0)};
  let result=sample_closed(&p,&mut rng,SampleLimits {max_execution_steps:limit,..SampleLimits::default()});
  println!("limit={limit}, result={result:?}, draws={draws}");
 }
 let mut rng=||Err::<u64,_>("called despite insufficient budget");
 println!("failure precedence: {:?}",sample_closed(&p,&mut rng,SampleLimits {max_execution_steps:2,..SampleLimits::default()}));
}
