#!/usr/bin/env python3
"""Independent integer oracles for sparse controlled phase powers.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
This invokes compiled pure definitions, not a new acceptance/schema endpoint.
"""
import argparse
import hashlib
import json
from pathlib import Path

from test_hierarchical_artifact import build_and_run


SOURCE = '''import QleisliKernel.PhasePolynomial.Operations
open QleisliKernel PhasePolynomial
def bits (word : Nat) : Nat → Bool := fun i => word / (2^i) % 2 == 1
def report (name : String) (terms : Polynomial) (count control word : Nat) : IO Unit := do
  let scaled := scale count terms
  let controlled := controlTrue control scaled
  IO.println s!"{name}|{evaluate scaled (bits word)}|{evaluate controlled (bits word)}|{scaled.length}|{controlled.length}"
def main : IO Unit := do
  for ticks in [:256] do
    for count in #[0,1,3,64,4096] do
      for word in [:4] do
        report s!"mixed-{ticks}-{count}-{word}" [⟨[0],ticks⟩,⟨[],17⟩,⟨[1],255⟩] count 1 word
  for precision in [1:9] do
    for width in [:precision] do
      let terms := (List.range width).map (fun i => (⟨[i+1],2^(8-precision+i)⟩ : Term))
      let count := 2^(precision-(width+1))
      for word in [:2^(width+1)] do
        report s!"gradient-{precision}-{width}-{word}" terms count 0 word
  for word in #[0,1,2,32768,32769,65535] do
    for count in #[0,1,4096] do
      report s!"wide-{count}-{word}" [⟨[0,15],255⟩,⟨[15],1⟩,⟨[],128⟩] count 15 word
'''


def expected():
    rows = {}
    # Integer phase sums, without Lean's syntax traversal or coefficient scaling.
    for ticks in range(256):
        for count in [0,1,3,64,4096]:
            for word in range(4):
                phase = (count*((ticks if word&1 else 0)+17+(255 if word&2 else 0)))%256
                rows[f'mixed-{ticks}-{count}-{word}'] = [phase,phase if word&2 else 0,3,3]
    for precision in range(1,9):
        for width in range(precision):
            for word in range(1 << (width+1)):
                # G_r^(2^(N-r-1)) has phase x / 2^(r+1), independent of N.
                phase = ((word//2)*(1 << (7-width)))%256
                rows[f'gradient-{precision}-{width}-{word}'] = [phase,phase if word&1 else 0,width,width]
    for word in [0,1,2,32768,32769,65535]:
        for count in [0,1,4096]:
            high, low = bool(word&32768), bool(word&1)
            phase = ((255 if high and low else 0)+(1 if high else 0)+128)*count%256
            rows[f'wide-{count}-{word}'] = [phase,phase if high else 0,3,3]
    return rows


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--record', type=Path)
    args = parser.parse_args()
    commands, binary = build_and_run(SOURCE,args.record)
    observed = {}
    for line in commands[-1]['stdout'].splitlines():
        name,*values = line.split('|')
        assert name not in observed, name
        observed[name] = [int(x) for x in values]
    required = expected()
    assert observed.keys() == required.keys()
    for name,value in required.items():
        assert observed[name] == value, (name,observed[name],value)
    # Keep output identity and aggregates; the deterministic source regenerates
    # every individual row without committing thousands of redundant lines.
    stdout = commands[-1].pop('stdout')
    commands[-1]['stdout_sha256'] = hashlib.sha256(stdout.encode()).hexdigest()
    report = dict(format='qleisli.sparse-phase-operations-native',version=1,status='passed',
        cases=len(required),mixed_cases=sum(k.startswith('mixed-') for k in required),
        gradient_cases=sum(k.startswith('gradient-') for k in required),
        wide_cases=sum(k.startswith('wide-') for k in required),
        binary_sha256=binary,source_sha256=hashlib.sha256(SOURCE.encode()).hexdigest(),commands=commands,
        scope='Exact integer/native differential checks and constant term counts, including zero powers, global phases and every shared-QFT gradient at precisions one through eight. No external schema or hierarchy projection is accepted by this helper.')
    if args.record:
        args.record.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k != 'commands'}))


if __name__ == '__main__':
    main()
