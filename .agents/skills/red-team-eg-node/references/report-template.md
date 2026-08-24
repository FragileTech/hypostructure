# Per-node report contract

## Contents

1. [File and metadata](#1-file-and-metadata)
2. [Required report body](#2-required-report-body)
3. [Verdict and repair rules](#3-verdict-and-repair-rules)
4. [Recording rules](#4-recording-rules)

## 1. File and metadata

Write one canonical file:

```text
audits/erdos-64-red-team/reports/node-NNN.md
```

Begin with a machine-readable JSON comment. Copy current values from the
node dossier; do not invent hashes.

```markdown
<!-- red-team-audit
{
  "schema_version": 1,
  "proof": "erdos-gyarfas",
  "node": 1,
  "node_label": "finite simple graph G",
  "panel": "fig:proof-diagram-part-i",
  "contract_sha256": "COPY_FROM_DOSSIER",
  "manuscript_sha256": "COPY_FROM_DOSSIER",
  "graph_sha256": "COPY_FROM_DOSSIER",
  "lean_audit_sha256": "COPY_FROM_DOSSIER_OR_absent",
  "verdict": "NO ISSUE FOUND",
  "audited_at": "YYYY-MM-DDTHH:MM:SSZ"
}
-->
```

The report title is `# Red-team audit: node [N]`.

## 2. Required report body

Use these headings exactly.

```markdown
## 1. Executive verdict

Verdict: **ONE CLOSED-TAXONOMY VERDICT**

One paragraph limited to this node.

## 2. Exact node contract

### Incoming residual

### Accumulated facts

### Current predicate and exact claim

### Outgoing contracts

## 3. Sentence audit

| Sentence | Exact assertion | Facts used | Hidden obligation | Adversarial test | Status |
|---|---|---|---|---|---|

## 4. Counterexample attempts

### Smallest-parameter test

- **Explicit data:**
- **Hypotheses satisfied:**
- **Accumulated facts violated:**
- **Applicability:**

### Parity or 2-adic test

- **Explicit data:**
- **Hypotheses satisfied:**
- **Accumulated facts violated:**
- **Applicability:**

### Boundary or range test

- **Explicit data:**
- **Hypotheses satisfied:**
- **Accumulated facts violated:**
- **Applicability:**

### Graph-realizability test

- **Explicit data:**
- **Hypotheses satisfied:**
- **Accumulated facts violated:**
- **Applicability:**

### Branch-routing test

- **Explicit data:**
- **Hypotheses satisfied:**
- **Accumulated facts violated:**
- **Applicability:**

## 5. Strongest valid counterexample

Identify the candidate surviving the most accumulated facts. If none reaches
the actual residual, say so explicitly.

## 6. Local repair

### Corrected statement

### Complete local proof

### Counterexample disposition

### Graph patch

### Downstream impact

## 7. Regression audit

List every repeated use inspected, including negative search results and the
commands/patterns used.

## 8. Residual uncertainty

State exactly what remains unproved or uninspected.
```

For each counterexample attempt, use `NON-APPLICABLE TO THE NODE` verbatim when
an accumulated fact excludes it and name the earliest excluding node/label.

## 3. Verdict and repair rules

The metadata verdict and executive verdict must match exactly and must be one
of the eight values in the audit protocol. Do not use a second verdict as a
subtitle or combined classification.

Always keep all five Local Repair subsections:

- For a genuine issue or ambiguity, give the full corrected statement, proof,
  disposition, routing patch, and downstream impact.
- For `ISOLATED-STATEMENT COUNTEREXAMPLE ONLY`, explain why the accumulated
  contract already repairs the isolated wording and whether a prose
  clarification is useful.
- For `NO ISSUE FOUND`, write “No proof-source change required” and explain why
  the strongest candidate is already excluded or routed.

Do not implement the repair in this report.

## 4. Recording rules

Validation is structural, not mathematical. A successful validator confirms
the report shape, current fingerprint, mandatory attempts, and single verdict;
it does not certify the proof.

Record only after independently checking all cited sources. `record` updates
the coverage ledger atomically and only for the report's single node. If the
contract changed, regenerate the dossier and re-audit rather than copying the
new fingerprint into an old report.
