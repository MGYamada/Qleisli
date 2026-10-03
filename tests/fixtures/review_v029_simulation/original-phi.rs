use qleisli::ir::*;
use qleisli::interchange::native::Kernel;
use qleisli::sim::{SimulationLimits,run_closed,SampleLimits,sample_closed};
fn main() {
 let mut ops=vec![];
 for i in 0..2 {
  ops.extend([RawOp::Init0 {output:TokenId(i*2),wire:WireId(i)}, RawOp::Gate {gate:SingleGate::H,input:TokenId(i*2),output:TokenId(i*2+1)},RawOp::MeasureZ {input:TokenId(i*2+1),output:ClassicalId(i)}]);
 }
 ops.push(RawOp::ClassicalBranch {condition:ClassicalId(0),then_ops:vec![],else_ops:vec![],quantum_phis:vec![],classical_phis:(2..102).map(|i| ClassicalPhi {output:ClassicalId(i),then_id:ClassicalId(0),else_id:ClassicalId(0)}).collect()});
 let raw = RawProgram { quantum_inputs:vec![],classical_inputs:vec![],quantum_outputs:vec![],classical_outputs:vec![ClassicalId(101)],declared_effect:Effect::Observe,operations:ops };
 let p=Kernel::selected().unwrap().accept_raw(raw).unwrap();
 println!("run 100 metadata copies for each of 4 components with budget=32: {:?}",run_closed(&p,SimulationLimits {max_execution_steps:32,..SimulationLimits::default()}));
 let mut rng=||Ok::<u64,()>(0);
 println!("sample 100 metadata copies budget=16: {:?}",sample_closed(&p,&mut rng,SampleLimits {max_execution_steps:16,..SampleLimits::default()}));
}
