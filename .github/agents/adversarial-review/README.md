# Adversarial review agent

A Claude Managed Agents deployment that attacks `main` once a week and reports
only what it reproduced. It follows item 3 of the [trust boundary](../../../TRUSTBOUNDARY.md):
it is an untrusted finder. It accepts nothing, gates no merge or release, and
adopts no interpretation or guarantee. A run with no findings is not evidence
of security.

No API key is stored in GitHub; the maintainer applies and runs these files
from a local `ant` login. Anthropic hosts the agent loop and the sandbox and
keeps each session's history until it is deleted.

## What limits the sandbox

- It holds no credentials: no token, no vault and no MCP server. It clones the
  public repository anonymously and cannot write to GitHub.
- Egress is limited to the hosts in `environment.yaml`. That is a host
  allowlist. It does not restrict HTTP methods or what is sent, so the agent
  could still send data to an allowed host.
- "Send nothing out" in `agent.md` is an instruction to the model, not an
  enforced control.

What bounds the damage is that the sandbox has nothing secret to send. Its
inputs are this public repository and the titles of public Issues. Keep it
that way: adding a token, a vault, an MCP server or a private input needs a
new review of this section. In the measured runs a host outside the list did
not resolve. The provider's enforcement beyond that, and the contents of the
sandbox image, have not been verified independently.

## Files

- `agent.md`: model, tools and the reviewer's instructions.
- `environment.yaml`: the sandbox and its allowed hosts.
- `deployment-weekly.yaml`: schedule, per-run spending cap and report rubric.
- `kickoff-release.yaml`: the manual pre-tag run, pinned to a candidate commit.
- `../../claude-lock.json`: resource IDs written by `ant apply`. Git ignores
  it, because it names the maintainer's organization and workspace. Keep a
  copy: without it, `ant apply` creates new resources instead of updating.

## Apply

Apply only from `main`, after the change has been reviewed and merged. Run
from `.github/` and inspect the dry-run plan first.

```sh
ant apply --dry-run -v agents/adversarial-review/agent.md agents/adversarial-review/environment.yaml
ant apply agents/adversarial-review/agent.md agents/adversarial-review/environment.yaml
```

The deployment needs more care. The API creates a deployment live and has no
paused create. A deployment also keeps the agent version it was applied with
until its own file is applied again.

- To create it, apply and pause in one command, at least an hour away from
  the scheduled time. It could fire only in the seconds between the two calls.
- To change it, pause it, check that no session is still running, apply, run
  once manually, and unpause only when that run looks right.

```sh
# Create
ant apply agents/adversarial-review/deployment-weekly.yaml &&
  ant beta:deployments pause --deployment-id "$(jq -r '.resources["./agents/adversarial-review/deployment-weekly.yaml"].id' claude-lock.json)"

# Change
ant beta:deployments pause --deployment-id DEPLOYMENT_ID
ant beta:sessions list --agent-id AGENT_ID --status running
ant apply agents/adversarial-review/deployment-weekly.yaml
ant beta:deployments run --deployment-id DEPLOYMENT_ID
ant beta:deployments unpause --deployment-id DEPLOYMENT_ID
```

## Run and read

`ant beta:deployments run --deployment-id DEPLOYMENT_ID` starts a run, also
while paused. `ant beta:deployment-runs list --deployment-id DEPLOYMENT_ID`
gives each run's session. `ant beta:files list --scope-id SESSION_ID --beta
managed-agents-2026-04-01` lists `findings.md`, the reproducers and the
probes, and `ant beta:files download --file-id FILE_ID --output PATH` fetches
one.

## Pre-tag run

Pin the run to the release candidate and give the session its own spending
cap. The cap can only be set when the session is created.

```sh
CANDIDATE=$(git rev-parse --verify HEAD)   # the release candidate, as a full commit
SID=$(ant beta:sessions create --agent AGENT_ID --environment-id ENVIRONMENT_ID \
  --title "Pre-tag review of $CANDIDATE" \
  --budget '{type: limit, max_list_cost: {amount: "2500", currency: USD}}' \
  --transform id -r)
sed "s/CANDIDATE_SHA/$CANDIDATE/" agents/adversarial-review/kickoff-release.yaml |
  ant beta:sessions:events send --session-id "$SID"
```

The report header must show the same commit. Before relying on this for a
release, run it once against a known commit and check that the report and the
reproducers can be retrieved.

## Triage

The report uses four classes, with the same meaning in `agent.md` and in the
rubric.

- **Finding**: reproduced behaviour that violates a clear, applicable contract.
- **Spec conflict**: reproduced behaviour on which applicable contracts
  contradict each other. Both sides are quoted.
- **Spec gap**: reproduced behaviour where the contracts are silent or
  underspecified.
- **Unverified lead**: a suspected defect that was not reproduced.

Read the header first. A search status of `partial` or `blocked` with no
findings says little, and a deduplication status of `partial` or `unavailable`
means repeats are likely.

Reproduce each finding locally at the reported commit. File only confirmed
ones as Issues in the Problem, reproduction and Acceptance form of the
existing review Issues, and keep the reproducer as a regression. The agent
files no Issues itself.

Read "Spec questions" with the same care. Spec conflicts and spec gaps are
reproduced too, and each carries the severity it would have if the question
is settled against the behaviour. Settling it is the maintainer's part, so a
serious counterexample can sit there.

"Potential duplicates" holds reproduced candidates that may match a known
Issue. The agent sees titles only, and a similar title does not establish the
same cause. The maintainer decides.

Changes to these files change what the reviewer can see. Review them like
workflow changes.
