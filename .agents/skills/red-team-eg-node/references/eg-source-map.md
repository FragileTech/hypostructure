# Erdős–Gyárfás audit source map

## Contents

1. [Authority order](#1-authority-order)
2. [Repository sources](#2-repository-sources)
3. [How to reconstruct a node](#3-how-to-reconstruct-a-node)
4. [Graph structures requiring care](#4-graph-structures-requiring-care)
5. [Lean evidence](#5-lean-evidence)
6. [Regression search](#6-regression-search)

## 1. Authority order

Use these authorities without conflating their roles:

1. The manuscript is authoritative for mathematical definitions, statements,
   proofs, hypotheses, and intended alternatives.
2. The directed proof graph is authoritative for ancestry, selected branches,
   merges, routing, loops, and terminal structure.
3. Actual Lean declaration types and bodies are authoritative for what the
   formalization currently states and proves.
4. Audit tables and JSON sidecars are locators and status records. They are not
   substitutes for the manuscript or actual Lean source.

When the generated explorer JSON differs from a fresh graph extraction, use the
fresh graph to locate the live TeX diagram and report the drift. Verify disputed
edges directly in the diagram/table rather than trusting either serialization
blindly.

Also inspect `unwired_routing_candidates`. It is a route-family heuristic, not
an edge list. When a manuscript result says “route to Type B,” “enter route 8,”
or similar but the graph supplies no path to the named destination, verify both
contracts directly and report the discrepancy instead of silently importing the
source as an ancestor.

Use the dossier's boolean `source_fingerprints.graph_drift`, which compares
canonical semantic graph payloads. Do not compare `graph_sha256` with the raw
`checked_graph_sha256`: one hashes normalized live graph data and the other
hashes serialized file bytes, so those values are intentionally incomparable.

## 2. Repository sources

- Mathematical manuscript: `to_formalize/erdos_64_proof.tex`
- Compiled manuscript: `to_formalize/erdos_64_proof.pdf`
- Live graph parser: `web/tools/proof_graph.py`
- EG graph specification and explicit continuations:
  `web/tools/papers/erdos64.py`
- Checked-in explorer graph: `web/frontend/public/data/erdos-gyarfas.json`
- Lean node-status sidecar: `web/data/eg_node_audit.json`
- Human Lean/fidelity tables: `Assembly_node_audit.md`
- Main application assembly:
  `proofs/hypostructure_erdos_64_eg/HypostructureErdos64EG/Assembly.lean`
- Principal row and fact vocabulary sources:
  `hypostructure/Hypostructure/Graph/Strategy/SpineRows.lean` and
  `hypostructure/Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Review-method postmortem: `erdos_64_conversation_mistakes.md`

The manuscript presently exposes 180 numbered nodes across twelve panels. The
campaign script verifies live numbering and does not silently assume that a
checked-in JSON file is current.

## 3. How to reconstruct a node

Use the dossier to locate, then read:

1. the node's TikZ label and every immediate incoming/outgoing edge;
2. the detailed dependency-table row for the node;
3. each exact result attached to the node, including its proof and recursively
   cited prerequisites as needed;
4. the constraint-ledger rows first tracked or consumed on its ancestry;
5. residual definitions and branch predicates on each selected incoming route;
6. the destination node's definitions and entry theorem for each outgoing edge;
7. any corresponding Lean fact key, `Holds` schema, producer, exact ledger
   prefix, and consumer; and
8. every repeated or analogous use relevant to a proposed repair.

The dossier's “common dominators” are graph-theoretic candidates, not a proof
that every fact at those nodes is retained. Its predecessor cones identify
route alternatives, not permission to union sibling facts. Reconstruct
retention from the manuscript and, when available, the literal Lean ledger.
Likewise, `fingerprint_basis` includes outgoing destination material so routing
changes stale the report. It is a drift-detection payload, not the accumulated
state at the node.

At a merge, express the state as a tagged union when the proof remembers the
route. Record common facts separately from route-specific payloads. Do not erase
tags by taking only an intersection and do not create an impossible union of
sibling facts.

## 4. Graph structures requiring care

### Type A peeling loop

Nodes [89], [93], [94], [95], [97], [99], [101], and [102] form a strongly
connected component. The edge [102] -> [89] recomputes `L_4` after peeling one
target-defective load. Audit any node in this component with an iteration index,
the exact updated load/residual, and the manuscript's decreasing measure. A
back edge is not automatically circular reasoning.

### Representative merges

Node [65] has three incoming routes ([66], [64], and decorated handoff [177]).
The common Type B destination does not imply that all three paths carry the same
payload. Similar merge care is required at [25], [54], [70], [75], [76], [84],
[85], [89], [101], [110], [137], [144], [155], and [178]. Always use the live
graph rather than this list as the final authority.

### Routing-only and terminal nodes

A routing box can establish no new proposition while still requiring a complete
handoff check. A terminal node must have no live outgoing edge and must be
supported by a closure result, not merely a name. Some diagram decisions are
collapsed in Lean because an accumulated invariant refutes one arm uniformly;
that is not automatically a nonexhaustive decision.

## 5. Lean evidence

Use `web/data/eg_node_audit.json` and `Assembly_node_audit.md` to locate a
producer, then inspect the source declaration. Check:

- the exact `Holds` proposition, not the fact-key name;
- the literal incoming `ExactLedger` index;
- every `FactInputs.get`/`ExactLedger.get` read;
- the selected decision arm and retained predecessor keys;
- whether the result is actually published and wired; and
- whether the proposition matches the manuscript.

Keep these judgments separate:

- mathematical validity of the manuscript node;
- fidelity of the Lean proposition to the manuscript;
- existence and completeness of a Lean producer;
- wiring/reachability of that producer; and
- kernel checking of the inspected path.

Absence, plumbing, a stub, or a downstream compiler failure may be a
formalization defect without being a mathematical counterexample. Conversely,
kernel checking cannot validate omitted manuscript hypotheses or a weakened
formal statement.

## 6. Regression search

For every corrected label, search the whole manuscript and formalization:

```bash
rg -n 'LABEL|distinctive phrase|word for word|same proof|analog' \
  to_formalize/erdos_64_proof.tex \
  hypostructure proofs Assembly_node_audit.md web/data/eg_node_audit.json
```

Inspect theorem statements, proof references, dependency-table rows, constraint
ledgers, captions, cold/pair analogues, and Lean schemas. A textual occurrence
is a regression candidate, not proof that it needs the same correction.
