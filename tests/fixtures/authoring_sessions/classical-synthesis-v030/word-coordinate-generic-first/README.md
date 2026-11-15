# First width-parameterized computed predicate

The [first source](generic.qli) abstracts the width of the three-coordinate
Grover predicate. A width of at least three keeps each referenced bit valid.
The [operation variant](operation-constant.qli) isolates whether the existing
ordinary-result operation header can supply a predicate, using a constant
body to take bit indexing out of that experiment.

The CLI was built from commit
59163c86c8dc0934cdf622fcb2d79290460c7995. The actual invocations used
check --entry=main::oracle --nat=n=3 --module=main=PATH --ir-profile=raw
--format=json with the manifest in this directory. PATH identified each
recorded source by its original temporary absolute path. Both checks exited
with status 1 and empty stderr.

- [Original CLI response](generic.json) records rejection at the classical
  declaration header.
- [Operation variant response](operation-constant.json) records rejection
  at the predicate reference because a classical declaration is required.

CLI SHA-256 3ab6dfb7a40e0157b295ab515dc8c0f0e16cccf9fb2e9a42a4fbe1bc97dc0efc.
Configured native kernel SHA-256
9b05a2f896de1d79ef6fce94032a9cff40e54005316c6fe707c861752d5ce907.
Both refusals occurred in the frontend.

Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
