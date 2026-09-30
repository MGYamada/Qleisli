#!/usr/bin/env python3
"""Fresh checked Rust execution versus independent small complex coefficient oracles.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
Includes bounded fresh-shot clients; no maximum-size, named QPE or source proof.
"""
import argparse
import hashlib
import json
import math
import os
from pathlib import Path
import subprocess
import tempfile

from compile_sized_corpus import Operation, compile_source
from compile_sized_instrument import compile_instrument
from test_instrument_host import source_documents
from test_sized_instrument import sources
from test_sized_qft import SOURCE, INVERSE_SOURCE, canonical_boundary, request, expected as fourier
from test_sized_qpe import expected as qpe
from test_sized_qpe_clients import expected as client

ROOT = Path(__file__).resolve().parent.parent


def columns(width):
    dimension = 1 << width
    return [{i: 1} for i in range(dimension)]+[
        {0:1/math.sqrt(3), dimension-1:1j/math.sqrt(6)},
        {i:complex((i+1)%5-2,(2*i+1)%7-3)/7 for i in range(dimension)}]


def ordinary_request(graph):
    root=graph['definitions'][graph['entry']['implementation']]['interface']
    return dict(format='qleisli.hierarchy-request',version=1,profile='qpe-dyadic8-v1',
        kind='equation',effect='unitary',interface=root,meanings=graph['meanings'],
        entry=graph['proofs'][graph['entry']['proof']]['meaning'])


def retiming(column):
    # Direct source-order oracle: observe low input bit, H on the other,
    # initialize and observe zero. The second result bit is always false.
    result={}
    for label,value in column.items():
        for target in range(2):
            key=(label & 1,target)
            result[key]=result.get(key,0)+value*((-1)**((label>>1)*target))/math.sqrt(2)
    return result


def write_case(directory, name, kind, artifact, required, inputs, input_width, output_width, measured, oracle):
    (directory/f'{name}.json').write_text(json.dumps(artifact))
    (directory/f'{name}.request.json').write_text(json.dumps(required))
    def numbers(path,values):
        path.write_text(''.join(f'{complex(z).real:.17g} {complex(z).imag:.17g}\n' for z in values))
    numbers(directory/f'{name}.input',(c.get(i,0) for c in inputs for i in range(1<<input_width)))
    results=[oracle(c) for c in inputs]
    if kind=='pure':
        values=[c.get(i,0) for c in results for i in range(1<<output_width)]
    else:
        values=[c.get((outcome,i),0) for outcome in range(1<<measured)
                for c in results for i in range(1<<output_width)]
    numbers(directory/f'{name}.expected',values)
    return dict(name=name,kind=kind,reference_dimension=len(inputs),input_qubits=input_width,
        output_qubits=output_width,measured_bits=measured,coefficients=len(values),
        artifact_sha256=hashlib.sha256(json.dumps(artifact).encode()).hexdigest())


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--kernel',type=Path,default=ROOT/'lean-kernel/.lake/build/bin/qleisli-kernel')
    parser.add_argument('--record',type=Path)
    args=parser.parse_args()
    rows=[]
    sampling_rows=[]
    with tempfile.TemporaryDirectory(prefix='qleisli-execution-') as temporary:
        directory=Path(temporary)
        modules=sources()
        for width in (1,2,3):
            for inverse in (False,True):
                if inverse:
                    graph=compile_source(INVERSE_SOURCE.read_text(),'inverse_fourier',dict(n=width),
                        modules={'fourier':SOURCE.read_text(),'inverse':INVERSE_SOURCE.read_text()})
                    required=ordinary_request(graph)
                else:
                    graph=canonical_boundary(compile_source(SOURCE.read_text(),'fourier',dict(n=width)))
                    required=request(width)
                rows.append(write_case(directory,f'fourier-{width}-{inverse}','pure',graph,required,
                    columns(width),width,width,0,lambda c:fourier(width,c,inverse)))
        for name,n,m,kind in [('qpe-1-2',1,2,'qpe'),('qpe-1-3',1,3,'qpe'),
                              ('qpe-2-2',2,2,'qpe'),('order',2,2,'order'),('amplitude',1,2,'amplitude')]:
            if kind=='qpe':
                proposal=compile_instrument(modules,'measurement::qpe',dict(n=n,m=m),
                    {'U':Operation('evolution::evolve',(n,1,3))})
            elif kind=='order':
                proposal=compile_instrument(modules,'measured_order::order_readout',dict(n=n,m=m),
                    {'U':Operation('modular::mul_two',(n,))})
            else:
                proposal=compile_instrument(modules,'measured_amplitude::amplitude_readout',dict(n=n,m=m,j=1,d=3))
            artifact,required=source_documents(proposal)
            def oracle(c):
                initialized={x<<m:z for x,z in c.items()}
                result=qpe(n,m,initialized) if kind=='qpe' else client(kind,n,m,initialized)
                return {(x%(1<<m),x>>m):z for x,z in result.items()}
            rows.append(write_case(directory,name,'instrument',artifact,required,columns(n),n,n,m,oracle))
            if name in ('qpe-1-2','order','amplitude'):
                # One unnormalized state entangled with a two-dimensional
                # reference, then ordinary basis inputs for the two clients.
                sample_input=([{0:3},{1:4j}] if kind=='qpe' else
                              [{1:1}] if kind=='order' else [{0:1}])
                sample=write_case(directory,'sample-'+name,'instrument',artifact,required,
                    sample_input,n,n,m,oracle)
                sample.update(shots=256,seed=42,client=kind)
                sampling_rows.append(sample)
        proposal=compile_instrument(modules,'measured_retiming::retimed',dict(n=2))
        artifact,required=source_documents(proposal)
        rows.append(write_case(directory,'retiming','instrument',artifact,required,columns(2),2,1,2,retiming))
        reversed_source=modules['measured_retiming'].replace('prepend_bit[0](second,empty_bits())','prepend_bit[0](first,empty_bits())').replace('prepend_bit[1](first,bits)','prepend_bit[1](second,bits)')
        # Current checked profile requires pack order to equal measurement order.
        reversed_source=reversed_source.replace('    let first = measure_z(first);\n','').replace('let second = measure_z(fresh);','let second = measure_z(fresh);\n    let first = measure_z(first);')
        proposal=compile_instrument(modules|{'measured_retiming':reversed_source},'measured_retiming::retimed',dict(n=2))
        artifact,required=source_documents(proposal)
        rows.append(write_case(directory,'reordered-readout','instrument',artifact,required,columns(2),2,1,2,
            lambda c:{(outcome<<1,target):value for (outcome,target),value in retiming(c).items()}))
        for provider,expression in [('global','x(phase[j,d](x(phase[j,d](bit))))'),
                                    ('conjugated','h(phase[j,d](h(bit)))')]:
            evolution=modules['evolution'].replace('use std::quantum::phase;',
                'use std::quantum::phase;\nuse std::quantum::h;\nuse std::quantum::x;').replace('phase[j,d](bit)',expression)
            proposal=compile_instrument(modules|{'evolution':evolution},'measurement::qpe',dict(n=1,m=2),
                {'U':Operation('evolution::evolve',(1,1,3))})
            artifact,required=source_documents(proposal)
            def oracle(c):
                result=qpe(1,2,{x<<2:z for x,z in c.items()},provider=provider)
                return {(x%4,x>>2):z for x,z in result.items()}
            rows.append(write_case(directory,'qpe-'+provider,'instrument',artifact,required,columns(1),1,1,2,oracle))
        (directory/'cases.tsv').write_text(''.join(f"{r['name']}\t{r['kind']}\t{r['reference_dimension']}\t{r['output_qubits']}\t{r['measured_bits']}\n" for r in rows))
        (directory/'sampling.tsv').write_text(''.join(f"{r['name']}\t{r['client']}\t{r['reference_dimension']}\t{r['output_qubits']}\t{r['measured_bits']}\t{r['shots']}\t{r['seed']}\n" for r in sampling_rows))
        command=['cargo','test','--test','hierarchical_execution','--','--ignored','--nocapture']
        run=subprocess.run(command,cwd=ROOT,env=os.environ|{'QLEISLI_HIERARCHY_KERNEL':str(args.kernel.resolve()),
            'QLEISLI_HIERARCHICAL_EXECUTION':str(directory)},text=True,capture_output=True,timeout=180)
        report=dict(format='qleisli.hierarchical-execution-validation',version=1,
            status='passed' if run.returncode==0 else 'failed',scope='small checked reference execution; no source or named QPE proof',
            cases=rows,sampling_cases=sampling_rows,command=command,exit_code=run.returncode,stdout=run.stdout,stderr=run.stderr,
            kernel_sha256=hashlib.sha256(args.kernel.read_bytes()).hexdigest(),
            source_sha256={name:hashlib.sha256(source.encode()).hexdigest() for name,source in modules.items()},
            implementation_sha256={p:hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in
                ['src/interchange/hierarchical/execution.rs','tests/hierarchical_execution.rs',
                 'scripts/test_hierarchical_execution.py','scripts/compile_sized_corpus.py',
                 'scripts/compile_sized_instrument.py','scripts/compact_sized_graph.py',
                 'scripts/test_instrument_host.py','scripts/test_sized_qft.py',
                 'scripts/test_sized_qpe.py','scripts/test_sized_qpe_clients.py']})
        report['sampling_contract']={
            'entry':'CheckedInstrument::sample_normalized_shots',
            'input':'explicit finite positive-norm normalization; original norm squared returned',
            'freshness':'actual execute called afresh per shot from the same normalized joint input/reference state',
            'random':'one high-53-bit word per complete packed outcome, including deterministic shots; uniform independent words are a caller premise',
            'output':'actual low-bit pack integer, normalized conditional joint residual/reference coefficients, probability and shared total work',
            'limits':'positive bounded shot count; shared total steps; peak amplitude cells include normalized input, retained outputs, execution and real-weight workspace',
            'numerics':'norm guard min(2^-20,2^-40+16*epsilon*actual execution steps); not a certified error bound',
            'clients':'order candidates checked by 2^r mod 3; amplitude uses sin^2(pi*y/2^m) as a finite-resolution grid estimate, not an unbiased or exact ideal amplitude',
            'normalized_reference_coefficients':sum(r['shots']*(1<<r['output_qubits'])*r['reference_dimension'] for r in sampling_rows),
            'production_cli':False,'named_qpe_proof':False,'source_preservation':False}
        report['sampling_results']=[]
        for line in run.stdout.splitlines():
            if line.startswith('SAMPLING|'):
                _,name,shots,steps,counts,candidates,estimate=line.split('|')
                report['sampling_results'].append(dict(name=name,shots=int(shots),steps=int(steps),
                    counts=json.loads(counts),validated_order_candidates=int(candidates),grid_estimate_mean=float(estimate)))
        if args.record:
            args.record.write_text(json.dumps(report,indent=2)+'\n')
        assert run.returncode==0,run.stdout+run.stderr
        print(run.stdout)
        print(f"{len(rows)} small checked execution cases, {sum(r['coefficients'] for r in rows)} complex coefficients")
        print(f"{len(sampling_rows)} fresh-shot clients, {sum(r['shots'] for r in sampling_rows)} seeded outcomes")


if __name__=='__main__': main()
