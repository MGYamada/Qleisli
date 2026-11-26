# Adversarial review agent

A Claude Managed Agents deployment that attacks `main` once a week and reports
only what it reproduced. It follows item 3 of the [trust boundary](../../../TRUSTBOUNDARY.md):
it is an untrusted finder. It accepts nothing, gates no merge or release, and
adopts no interpretation or guarantee. A run with no findings is not evidence
of security.

The sandbox holds no credentials. It clones the public repository anonymously,
has deny-by-default egress and cannot write to GitHub. No API key is stored in
GitHub; the maintainer applies and runs these files from a local `ant` login.
Anthropic hosts the agent loop and the sandbox and keeps each session's history
until it is deleted.

## Files

- `agent.md`: model, tools and the reviewer's instructions.
- `environment.yaml`: the sandbox and its allowed hosts.
- `deployment-weekly.yaml`: schedule, per-run spending cap and report rubric.
- `kickoff-release.yaml`: the manual pre-tag run over all five surfaces.
- `../../claude-lock.json`: resource IDs written by `ant apply`. Git ignores
  it, because it names the maintainer's organization and workspace. Keep a
  copy: without it, `ant apply` creates new resources instead of updating.

## Apply

Run from `.github/`. Inspect the dry-run plan before applying, and create the
deployment paused so that nothing fires before a manual run looks right.

```sh
ant apply --dry-run -v agents/adversarial-review/agent.md agents/adversarial-review/environment.yaml
ant apply agents/adversarial-review/agent.md agents/adversarial-review/environment.yaml
ant apply agents/adversarial-review/deployment-weekly.yaml &&
  ant beta:deployments pause --deployment-id "$(jq -r '.resources["./agents/adversarial-review/deployment-weekly.yaml"].id' claude-lock.json)"
```

## Run and read

`ant beta:deployments run --deployment-id ID` starts a run, also while paused.
`ant beta:deployment-runs list --deployment-id ID` gives each run's session.
`ant beta:files list --scope-id SESSION --beta managed-agents-2026-04-01` lists
`findings.md` and the reproducers. For the pre-tag run, create a session for
the agent and environment and send it `kickoff-release.yaml`.

## Triage

Reproduce each finding locally at the reported commit. File only confirmed ones
as Issues in the Problem, reproduction and Acceptance form of the existing
review Issues, and keep the reproducer as a regression. The agent files no
Issues itself.

Triage the "Spec questions" section with the same care. The agent puts
reproduced behaviour there when the written contracts conflict or are silent,
because it cannot decide what they mean. Deciding that is the maintainer's part.

Changes to these files change what the reviewer can see. Review them like
workflow changes, and apply them only from `main`.
