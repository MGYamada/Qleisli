#!/usr/bin/env python3
"""Native QPE plan checks and independent full branch/reference oracles.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
Numerical comparisons do not issue evidence or prove runtime correspondence.
"""
import native_harness
import argparse
import cmath
import copy
import hashlib
import json
import math
from pathlib import Path
from current_source_fixtures import current_source_fixture, source_hashes
import subprocess
import tempfile

from test_lean_interference import ROOT, literal, execute, h
from test_lean_qft import template
from test_lean_qft_graph import case as graph_case, body_literal

FIXTURE = ROOT / "tests/fixtures/lean_qpe_instrument"


def base(n, m, provider=7):
    return dict(n=n, m=m, provider=provider, powers=[(k, provider, 2**k, True) for k in range(m)],
                initial=[False]*m, preparation=[h(k) for k in range(m)], graph=graph_case(m))


def suite():
    cases = [(f"n{n}-m{m}", base(n, m), True) for n in range(1, 9) for m in range(1, 9)]
    original = base(2, 3)
    def mutation(name, change):
        item = copy.deepcopy(original)
        change(item)
        cases.append((name, item, False))
    for parameter in ("n", "m"):
        for value in (0, 9, 1000000):
            mutation(f"{parameter}-{value}", lambda c, p=parameter, v=value: c.update({f"request_{p}": v}))
    mutation("wrong-provider", lambda c: c.update(request_provider=8))
    mutation("dirty-precision", lambda c: c["initial"].__setitem__(0, True))
    mutation("missing-zero", lambda c: c["initial"].pop())
    mutation("missing-h", lambda c: c["preparation"].pop())
    mutation("wrong-h-axis", lambda c: c["preparation"].__setitem__(1, h(0)))
    mutation("extra-scalar-phase", lambda c: c["preparation"].append(("p", [(1, [])])))
    mutation("reversed-power-order", lambda c: c["powers"].reverse())
    for field, value in ((0, 0), (1, 8), (2, 0), (2, 3), (3, False)):
        def change(c, f=field, v=value):
            row=list(c["powers"][1]);row[f]=v;c["powers"][1]=tuple(row)
        mutation(f"power-field-{field}-{value}", change)
    mutation("missing-power", lambda c: c["powers"].pop())
    header = "Qpe.header 2 3"
    changes = {
        "forward-qft": "orientation := .forward",
        "reverse-measurement": "measurementAxes := [4,3,2]",
        "aliased-precision-axis": "precisionAxes := [0,3,4]",
        "wrong-target-axis": "targetAxes := [1,0]",
        "aliased-owner": "precisionOwner := 0",
        "wrong-target-owner": "targetOwner := 1",
        "measure-target": "targetExit := .measure",
        "discard-target": "targetExit := .discard",
        "unitary-effect": "effect := .unitary",
        "classical-input": "classicalInputs := [.bits 1]",
        "wrong-classical-width": "classicalOutputs := [.bits 2]",
        "cbit-not-cbits": "classicalOutputs := [.bit]",
        "drop-target-output": "outputs := []",
        "extra-bits0-owner": "outputs := QftGraph.interface 2 ++ [⟨[.bits 0],[]⟩]",
        "tuple-not-bits": "inputs := [⟨[.tuple 2,.bit,.bit],[0,1]⟩]",
    }
    for name, field in changes.items():
        mutation(name, lambda c, f=field: c.update(header="{ " + header + " with " + f + " }"))
    def graph_phase(c):
        node=next(n for n in c["graph"]["nodes"] if n["kind"]=="gate" and n["gate"][0]=="p")
        node["gate"]=("p",[(192,node["gate"][1][0][1])])
    mutation("wrong-qft-phase", graph_phase)
    mutation("dangling-qft-entry", lambda c: c["graph"].update(entry=999))
    mutation("wrong-qft-type", lambda c: c["graph"]["nodes"][0].update(
        signature="{ QftGraph.boundary 3 with inputs := [⟨[.tuple 3,.bit,.bit,.bit],[0,1,2]⟩] }"))
    return cases


def plan_literal(item):
    n,m=item["n"],item["m"]
    nodes=[]
    for node in item["graph"]["nodes"]:
        nodes.append("⟨"+node.get("signature",f"QftGraph.boundary {m}")+", "+body_literal(node,m)+"⟩")
    powers="["+",".join(f"⟨{k},{p},{count},{str(polarity).lower()}⟩" for k,p,count,polarity in item["powers"])+"]"
    plan="⟨"+item.get("header",f"Qpe.header {n} {m}")+", "+json.dumps(item["initial"])+", "+literal(item["preparation"])+", "+powers+", ["+",".join(nodes)+f'], {item["graph"]["entry"]}⟩'
    return f'({item.get("request_n",n)}, {item.get("request_m",m)}, {item.get("request_provider",item["provider"])}, {plan})'


def schema_cases():
    """Requests are separate values; expected results follow the fixed contract."""
    rows=[]
    qpe='⟨"qpe-instrument/1",1,[2,3,7],.qpe schemaBase⟩'
    qft='⟨"qft-dyadic8/1",1,[3],.qft schemaBase.fourier schemaBase.fourierEntry⟩'
    powers='⟨"controlled-power/1",1,[3,7],.power ⟨0,7,8,true⟩⟩'
    for name,request,proposal in [('qpe','.qpe 2 3 7',qpe),('qft','.qft 3',qft),
                                  ('powers','.power 3 7',powers)]:
        rows.append((name,request,proposal,True))
        for label,update in [('unknown','rule := "unknown/1"'),
                             ('version','rule := "'+{'qft':'qft-dyadic8','qpe':'qpe-instrument',
                                                      'powers':'controlled-power'}[name]+'/2"'),
                             ('declaration','rule := "Qleisli.Qpe.accepted_plan"'),
                             ('template-zero','templateVersion := 0'),
                             ('template-next','templateVersion := 2'),
                             ('missing-parameters','parameters := []'),
                             ('extra-parameter','parameters := '+({'qpe':'[2,3,7,0]',
                                'qft':'[3,0]','powers':'[3,7,0]'}[name]))]:
            rows.append((name+'-'+label,request,'{ ('+proposal+' : Schema.Proposal) with '+update+' }',False))
    rows += [('qpe-wrong-precision','.qpe 2 2 7',qpe,False),
             ('qpe-wrong-provider','.qpe 2 3 8',qpe,False),
             ('qpe-qft-witness','.qpe 2 3 7','{ ('+qpe+' : Schema.Proposal) with witness := .qft schemaBase.fourier schemaBase.fourierEntry }',False),
             ('qft-qpe-witness','.qft 3','{ ('+qft+' : Schema.Proposal) with witness := .qpe schemaBase }',False),
             ('powers-qpe-witness','.power 3 7','{ ('+powers+' : Schema.Proposal) with witness := .qpe schemaBase }',False)]
    for provider,accepted in [(4294967295,True),(4294967296,False)]:
        rows.append(('provider-'+str(provider),f'.power 0 {provider}',
                     f'⟨"controlled-power/1",1,[0,{provider}],.power ⟨0,{provider},1,true⟩⟩',accepted))
    for exponent,count,accepted in [(0,1,True),(12,4096,True),(13,8192,False),
                                     (1000000,0,False),(3,0,False),(3,7,False)]:
        rows.append((f'power-{exponent}-{count}',f'.power {exponent} 7',
                     f'⟨"controlled-power/1",1,[{exponent},7],.power ⟨0,7,{count},true⟩⟩',accepted))
    for name,stage in [('axis','⟨1,7,8,true⟩'),('polarity','⟨0,7,8,false⟩'),
                        ('provider','⟨0,8,8,true⟩')]:
        rows.append(('power-'+name,'.power 3 7',
                     '⟨"controlled-power/1",1,[3,7],.power '+stage+'⟩',False))
    return rows


def native(cases, log):
    with tempfile.TemporaryDirectory(prefix="qleisli-qpe-native-") as directory:
        project=Path(directory)
        rows=[plan_literal(item) for _,item,_ in cases]
        schemas=schema_cases()
        schema_rows=[f'({request}, {proposal})' for _,request,proposal,_ in schemas]
        (project/"Main.lean").write_text('''import QleisliKernel.Schema
open QleisliKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
def cases : List (Nat × Nat × Nat × Qpe.Plan) := [
'''+",\n".join(rows)+''']
def schemaBase : Qpe.Plan := (show Nat × Nat × Nat × Qpe.Plan from '''+plan_literal(base(2,3))+''').2.2.2
def schemaCases : List (Schema.Request × Schema.Proposal) := [
'''+",\n".join(schema_rows)+''']
def bits (value : Nat) : Interference.Bits := fun i => value / 2^i % 2 == 1
def operation (n provider : Nat) (state : Nat × Nat) : Nat × Nat :=
  ((state.1+1) % 2^n, (state.2 + provider*3 + state.1*5) % 256)
def main : IO Unit := do
  for (n,m,provider,plan) in cases do
    let proposal : Schema.Proposal := ⟨"qpe-instrument/1",1,[n,m,provider],.qpe plan⟩
    match Schema.check (.qpe n m provider) proposal with
    | some (.qpe receipt) =>
      let mut line := toString receipt.stats.nodes ++ "," ++ toString (ControlledPowers.maximumUses plan.powers)
      for control in List.range (2^m) do
        let x := (control*3+1) % 2^n
        let result := ControlledPowers.run (operation n) (bits control) plan.powers (x,5)
        let prepared := PathSum.runFrom plan.preparation (bits control) Uniform.zero
        let output := (List.range m).foldl (fun n i => n + if prepared.bits i then 2^i else 0) 0
        line := line ++ "#" ++ String.intercalate "," ([result.1,result.2,
          ControlledPowers.selectedUses plan.powers (bits control),output,prepared.phase,prepared.hadamards].map toString)
      IO.println line
    | _ => IO.println "reject"
  for (request,proposal) in schemaCases do
    IO.println ("schema:" ++ toString (Schema.check request proposal).isSome)
''')
        binary = native_harness.build(project, log)
        run=subprocess.run([str(binary)],capture_output=True,text=True,timeout=30)
        log.append(dict(command=["qpe-test"],exit=run.returncode,stderr=run.stderr,executable_sha256=hashlib.sha256(binary.read_bytes()).hexdigest()))
        assert run.returncode==0,run.stderr
        lines=run.stdout.splitlines();assert len(lines)==len(cases)+len(schemas)
        for (name,_,_,accepted),line in zip(schemas,lines[len(cases):]):
            assert line=="schema:"+str(accepted).lower(),(name,line,accepted)
        comparisons=0
        for (name,item,accepted),line in zip(cases,lines):
            assert (line!="reject")==accepted,(name,line)
            if not accepted: continue
            n,m,p=item["n"],item["m"],item["provider"]
            fields=line.split("#");nodes,uses=map(int,fields[0].split(","))
            assert nodes==len(item["graph"]["nodes"]) and uses==2**m-1
            assert len(fields)==1+2**m
            for control,field in enumerate(fields[1:]):
                x,phase=(control*3+1)%2**n,5
                for k,target,count,polarity in item["powers"]:
                    if bool(control&(1<<k))==polarity:
                        for _ in range(count):
                            phase=(phase+target*3+x*5)%256;x=(x+1)%2**n
                expected=(x,phase,control,control,0,m)
                assert tuple(map(int,field.split(",")))==expected,(name,control,field,expected)
                comparisons+=1
        return dict(native_decisions=len(cases),accepted=sum(c[2] for c in cases),
                    controlled_path_comparisons=comparisons,preparation_paths=comparisons,
                    largest_target_calls=255,kernel_dense_dimension=0,
                    schema_decisions=len(schemas),schema_accepted=sum(row[3] for row in schemas),
                    schema_results=[dict(name=name,accepted=accepted) for name,_,_,accepted in schemas],
                    decisions=[dict(name=n,accepted=a) for n,_,a in cases])


def eye(n): return [[complex(i==j) for j in range(n)] for i in range(n)]
def multiply(a,b): return [[sum(a[i][k]*b[k][j] for k in range(len(b))) for j in range(len(b[0]))] for i in range(len(a))]
def adjoint(a): return [[a[j][i].conjugate() for j in range(len(a))] for i in range(len(a[0]))]
def max_error(a,b): return max(abs(x-y) for row,other in zip(a,b) for x,y in zip(row,other))


def expected_kraus(U,m):
    d,M=len(U),2**m
    powers=[eye(d)]
    for _ in range(1,M):powers.append(multiply(U,powers[-1]))
    return [[[sum(cmath.exp(-2j*math.pi*j*y/M)*powers[j][a][b] for j in range(M))/M
              for b in range(d)] for a in range(d)] for y in range(M)]


def literal_kraus(U,m):
    """Fresh H, literal controlled repeated U, physical reversal, inverse gates."""
    d,M=len(U),2**m;n=d.bit_length()-1
    result=[[[0j]*d for _ in range(d)] for _ in range(M)]
    inverse=[(kind,data if kind=="h" else [((-ticks)%256,axes) for ticks,axes in data])
             for kind,data in reversed(template(m))]
    reverse=lambda x:int(f"{x:0{m}b}"[::-1],2)
    for column in range(d):
        state=[0j]*(M*d);state[M*column]=1
        state=execute([h(k) for k in range(m)],state,m+n)
        for k in range(m):
            for _ in range(2**k):
                next_state=list(state)
                for p in range(M):
                    if p&(1<<k):
                        for a in range(d):
                            next_state[p+M*a]=sum(U[a][b]*state[p+M*b] for b in range(d))
                state=next_state
        state=[state[reverse(p)+M*a] for a in range(d) for p in range(M)]
        state=execute(inverse,state,m+n)
        for y in range(M):
            for a in range(d): result[y][a][column]=state[y+M*a]
    return result


def with_reference(K,r=2):
    d=len(K)
    return [[K[a//r][b//r] if a%r==b%r else 0j for b in range(d*r)] for a in range(d*r)]


def quantum_checks():
    s=1/math.sqrt(2)
    H=[[s,s],[s,-s]]
    def phase(ticks):return [[1,0],[0,cmath.exp(2j*math.pi*ticks/256)]]
    U4=[[0j]*4 for _ in range(4)]
    for x in range(4):U4[(x+1)%4][x]=cmath.exp(2j*math.pi*(7+11*x)/256)
    operators=[eye(2),phase(32),phase(16),multiply(multiply(H,phase(7)),H),
               [[0,cmath.exp(2j*math.pi/256)],[cmath.exp(2j*math.pi/256),0]],U4]
    entries=references=0;error=0.;largest=0
    for U in operators:
        d=len(U)
        for m in (1,2,3,4):
            expected,actual=expected_kraus(U,m),literal_kraus(U,m)
            largest=max(largest,2**m*d)
            total=[[0j]*d for _ in range(d)]
            total_trace=0j
            v=[complex(i+1,(-1)**i*(i+2)) for i in range(2*d)]
            scale=math.sqrt(sum(abs(x)**2 for x in v));v=[x/scale for x in v]
            w=list(reversed(v))
            rho=[[.6*v[i]*v[j].conjugate()+.4*w[i]*w[j].conjugate() for j in range(2*d)] for i in range(2*d)]
            for A,K in zip(actual,expected):
                error=max(error,max_error(A,K));entries+=d*d
                gram=multiply(adjoint(A),A)
                total=[[total[i][j]+gram[i][j] for j in range(d)] for i in range(d)]
                Ar,Kr=with_reference(A),with_reference(K)
                left=multiply(multiply(Ar,rho),adjoint(Ar))
                right=multiply(multiply(Kr,rho),adjoint(Kr))
                error=max(error,max_error(left,right));references+=1
                total_trace+=sum(left[i][i] for i in range(2*d))
            error=max(error,max_error(total,eye(d)))
            error=max(error,abs(total_trace-sum(rho[i][i] for i in range(2*d))))
    # Branch formulas also hold for nonisometric operators. That does not
    # establish a physical instrument: U=2I gives total Gram matrix 5I/2.
    nonisometric=literal_kraus([[2,0],[0,2]],1)
    gram0=multiply(adjoint(nonisometric[0]),nonisometric[0])
    gram1=multiply(adjoint(nonisometric[1]),nonisometric[1])
    total=[[gram0[i][j]+gram1[i][j] for j in range(2)] for i in range(2)]
    error=max(error,max_error(total,[[2.5,0],[0,2.5]]))
    assert max_error(total,eye(2))>1
    # A unitary provider is necessary but cannot excuse dropping an outcome
    # or confusing the QPE normalization 1/N with the QFT's 1/sqrt(N).
    complete=literal_kraus([[1,0],[0,-1]],1)
    omitted=multiply(adjoint(complete[0]),complete[0])
    assert max_error(omitted,eye(2))>.9
    rescaled=[[[math.sqrt(2)*z for z in row] for row in K] for K in complete]
    wrong0=multiply(adjoint(rescaled[0]),rescaled[0])
    wrong1=multiply(adjoint(rescaled[1]),rescaled[1])
    wrong=[[wrong0[i][j]+wrong1[i][j] for j in range(2)] for i in range(2)]
    assert max_error(wrong,eye(2))>.9
    assert error<2e-12,error
    return dict(kraus_entries=entries,joint_density_branches=references,
                largest_oracle_vector=largest,maximum_error=error,unitary_completeness_cases=24,
                joint_trace_cases=24,completeness_counterexamples=3)


def source_check(binary,log):
    K=expected_kraus([[1,0],[0,cmath.exp(1j*math.pi/4)]],2)
    expected=[]
    for dephased in (False,True):
        distribution={}
        for y in range(4):
            a,b=K[y][0][0]/math.sqrt(2),K[y][1][1]/math.sqrt(2)
            for r in range(2):
                for t in range(2):
                    probability=(abs(a)**2+abs(b)**2)/4 if dephased else abs((a+(-1)**(r+t)*b)/2)**2
                    distribution[y+4*r+8*t]=probability
        expected.append(distribution)
    assert max(abs(expected[0][k]-expected[1][k]) for k in expected[0])>0.06
    for name,expect in zip(("first_source","dephased"),expected):
        project=FIXTURE/name;baseline=json.loads((FIXTURE/(name+"-baseline.json")).read_text())
        for file,digest in baseline["source_sha256"].items():
            assert hashlib.sha256((project/file).read_bytes()).hexdigest()==digest
        project=current_source_fixture(project)
        command=[str(binary.resolve()),"run",str(project),"--format=json"]
        run=subprocess.run(command,capture_output=True,text=True,timeout=30)
        log.append(dict(command=command,exit=run.returncode,stdout=run.stdout,stderr=run.stderr,
                        historical_source_sha256=baseline["source_sha256"],executed_source_sha256=source_hashes(project)))
        assert run.returncode==0,run.stderr
        actual={sum(int(bit)<<i for i,bit in enumerate(row["bits"])):row["probability"]
                for row in json.loads(run.stdout)["result"]["distribution"]}
        assert all(abs(actual.get(k,0)-p)<2e-12 for k,p in expect.items()),(name,actual,expect)
    return dict(source_probabilities=32,off_grid_residual_coherence=True)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-only",type=Path)
    parser.add_argument("--record",type=Path)
    args=parser.parse_args();log=[]
    if args.source_only: report=source_check(args.source_only,log)
    else:
        report=native(suite(),log);report.update(quantum_checks())
    report["commands"]=log
    report["source_sha256"]={p:hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in
        ["lean-kernel/QleisliKernel/ControlledPowers.lean","lean-kernel/QleisliKernel/Uniform.lean",
         "lean-kernel/QleisliKernel/Qpe.lean","lean/Qleisli/Qpe.lean",
         "lean-kernel/QleisliKernel/Schema.lean",
         "lean/Qleisli/QpeComplete.lean","scripts/test_lean_qpe.py"]}
    if args.record:args.record.write_text(json.dumps(report,indent=2)+"\n")
    print(json.dumps({k:v for k,v in report.items() if k not in ['commands','source_sha256','decisions','schema_results']}))


if __name__=="__main__":main()
