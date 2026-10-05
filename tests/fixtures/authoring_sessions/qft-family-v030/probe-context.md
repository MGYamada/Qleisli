# Bounded coefficient and reference follow-up

This follow-up is authored after all eight first text/JSON checks succeeded.
There was no generic check failure and no QFT source repair. Attempt 02 copies
the exact first transform bytes and adds independent local reference clients.
The original session/context/observations remain preserved.

Only N=0,1,2,3 are used. For every input basis x, the oracle is the analytic
positive F_n[y,x] = exp(2*pi*i*x*y/2^n)/sqrt(2^n), using low-axis weight one.
It does not read an artifact's proposed meaning table or generated source gates.
The entangled client prepares (|0>|0>+|1>|1>)/sqrt(2) in the low axis and retained
reference before qft[n]; its expected output coefficient at y+2^n*r is
exp(2*pi*i*y*r/2^n)/sqrt(2*2^n). The zero-reference client separately retains
omega on Q<Bits<0>> and prepares (|0>+i|1>)/sqrt(2) on the reference, so expected
coefficients are omega/sqrt(2), i*omega/sqrt(2).

These numerical checks have an explicitly bounded 1e-11 comparison threshold;
they are corroboration, not epsilon replacements for EXACT or exact native
Fourier evidence. Actual production checks remain producer-consistency requests.
No native .qft0 request, fixed-specialization equality theorem, canonical std
import, source-preservation proof or broader QS/PR/RS discharge is claimed.
The observer uses fixed argument arrays, freezes identities before each run,
and retains every actual JSON result, native invocation log and analytic vector.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
