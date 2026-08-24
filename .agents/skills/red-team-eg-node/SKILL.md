---
name: red-team-eg-node
description: Adversarially audit exactly one node of the 180-node Erdős–Gyárfás cumulative structural-exhaustion proof against its complete incoming residual, selected branch facts, retained ledger, outgoing contracts, manuscript sources, proof-flow graph, and optional Lean implementation. Use when Codex must stress-test, counterexample-search, verify routing, diagnose ambiguity or a local gap, propose the smallest proof-preserving repair, write a per-node red-team report, or advance the repository's EG node-audit campaign.
---

# Red-Team EG Proof Node

Audit one node at a time. Seek a genuine local counterexample aggressively,
but reject every candidate that fails an accumulated fact before it reaches the
node. Never turn a local finding into an unsupported verdict about the whole
theorem.

## Required reading

Before auditing a node, read these files completely:

1. [references/audit-protocol.md](references/audit-protocol.md)
2. [references/eg-source-map.md](references/eg-source-map.md)

Before writing or validating the report, also read
[references/report-template.md](references/report-template.md) completely.

## Keep the semantic unit exact

The semantic unit is:

```text
incoming residual + accumulated path facts + selected branch predicate
+ retained/transferred ledger + local statement
```

Do not audit an isolated lemma. Do not import a sibling fact, a downstream
closure, or a fact suggested only by theorem order. Treat routing as a typed
handoff, not a contradiction. Treat Lean as contract and ledger evidence, not
as a substitute for the manuscript's mathematics.

Audit exactly one numbered node per report and per invocation. A request for a
range or for all 180 nodes is a campaign request: use `status` or `sync`, then
audit the next requested node separately. Never combine several nodes into one
verdict.

## Workflow

1. Announce that this skill is being used and name the single node.
2. Work from the repository root. Generate a fresh dossier from the live
   manuscript graph, not merely the checked-in explorer JSON:

   ```bash
   python3 .agents/skills/red-team-eg-node/scripts/red_team_node.py \
     dossier --repo-root . --node NODE --output /tmp/eg-node-NODE.json
   ```

3. Treat the dossier as a locator and consistency check. Read the actual TeX
   definitions, statements, proofs, diagram edges, ledger rows, and destination
   entry contracts. Where Lean exists, inspect the actual declarations and
   literal incoming `ExactLedger`; do not rely on names or status summaries.
   Query the JSON by top-level field (for example with `jq`); do not dump the
   large `fingerprint_basis` payload into the conversation. Use
   `--format markdown` for a compact human-oriented view.
4. Reconstruct the exact node contract before counterexample search. At a merge,
   preserve the tagged incoming alternatives. In the [89]--[102] loop, state the
   iteration state and decreasing measure explicitly.
5. Number every operative sentence and complete the audit table. Run all five
   mandatory counterexample classes. For arithmetic nodes, perform the exact
   2-adic, divisibility, integer-lift, and finite-range audit. Use the bundled
   modular checker when its input shape applies.
6. Choose exactly one verdict from the closed taxonomy in the protocol. If the
   issue is genuine, propose the smallest local repair that preserves the proof
   strategy and routing graph. Do not edit the manuscript, diagram, Lean source,
   or implementation audit under this skill.
7. Write the canonical report at
   `audits/erdos-64-red-team/reports/node-NNN.md`, following the report template.
   If that file has unrelated uncommitted edits, stop rather than overwrite it.
8. Validate against the current dossier, then record it:

   ```bash
   python3 .agents/skills/red-team-eg-node/scripts/red_team_node.py \
     validate --repo-root . --report audits/erdos-64-red-team/reports/node-NNN.md
   python3 .agents/skills/red-team-eg-node/scripts/red_team_node.py \
     record --repo-root . --report audits/erdos-64-red-team/reports/node-NNN.md
   ```

9. Report the verdict, report path, ledger status, strongest surviving candidate,
   and any residual uncertainty. Say explicitly that no proof source was changed.

## Campaign commands

Initialize or reconcile the dedicated coverage ledger without auditing nodes:

```bash
python3 .agents/skills/red-team-eg-node/scripts/red_team_node.py init --repo-root .
python3 .agents/skills/red-team-eg-node/scripts/red_team_node.py sync --repo-root .
python3 .agents/skills/red-team-eg-node/scripts/red_team_node.py status --repo-root .
```

`sync` preserves completed records whose contract fingerprints still match and
marks changed contracts stale. It never converts a pending node into an audited
one. Test or draft reports must not be recorded as campaign results.

## Arithmetic checker

For a claim that an orbit modulo a factor of `g` yields a power in
`L + R + gZ`, prepare the JSON input described in the audit protocol and run:

```bash
python3 .agents/skills/red-team-eg-node/scripts/check_modular_hit.py spec.json
```

The checker separates odd-part orbit hits from full-modulus compatibility and
central-range realization. Its output is evidence for the report, not a proof
that the arithmetic data are graph-realizable.

## Hard boundaries

- Do not assess or repair a second node.
- Do not infer global theorem failure or global verification.
- Do not edit proof sources under this report-only skill.
- Do not record a report that fails validation or whose fingerprint is stale.
- Do not call a raw no-hit, target-defect, dependence, or overlap residual a
  contradiction without verifying the destination contract.
- Do not let automated ancestry replace source-level cumulative-state
  reconstruction.
