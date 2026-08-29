<!-- red-team-audit
{
  "schema_version": 1,
  "proof": "erdos-gyarfas",
  "node": 168,
  "node_label": "surviving pair attaches only at endpoints: not a selected interior half-edge",
  "panel": "fig:proof-diagram-part-xii",
  "contract_sha256": "aae6443eecac880a9270eb1d87fd2535fec091de547488f113780cfc66cce6c8",
  "manuscript_sha256": "106a8205a1718fbf90e1686a107b2143b9edca574e2b0c11415e7f44aee2c0f9",
  "graph_sha256": "dc67fae178f947a9607c167e383d85919633341bdd423e4c4a45e4c317b3a765",
  "lean_audit_sha256": "50324ef5594d635a52d83aeb297f2ca3f3d30ef58de4ce3602816c7e78365b12",
  "verdict": "NO ISSUE FOUND",
  "audited_at": "2026-08-29T00:00:00Z"
}
-->

# Red-team audit: node [168]

## 1. Executive verdict

Verdict: **NO ISSUE FOUND**

Node [168] consumes the same selected interior-incidence family constructed at
[152] and retained through [153]--[167]. The endpoint argument closes the
literal incoming survivor; it neither reselects incidences nor changes the
candidate family.

## 2. Exact node contract

### Incoming residual

The `survives` residual retains an ambient-cubic induced \(P_{13}\), a selected
interior occurrence, the first-failure germ indexed by that occurrence, a
graph-realized second strand, and the complements of the two closing tests.

### Accumulated facts

Node [152] selects the tail obtained by dropping two absorbed incidences from
the eleven one-stub interior incidences. Node [153] constructs all corridors
and candidates from that family. The window-structure fact records one external
stub at every interior vertex and two at every endpoint.

### Current predicate and exact claim

A genuine pair of internally disjoint strands needs two distinct external
stubs at each attachment. Therefore both attachments are endpoints. The
retained selected occurrence is interior and has one external stub, so it
cannot be an attachment stub of the pair. This proves the exact exclusion
published at [168].

### Outgoing contracts

The survivor and endpoint-exclusion facts are incompatible. The canonical
sealed incompatibility executor appends the distinguished closure fact; there
is no unassigned outgoing residual.

## 3. Sentence audit

| Sentence | Exact assertion | Facts used | Hidden obligation | Adversarial test | Status |
|---|---|---|---|---|---|
| S1 | Each interior vertex has one external stub. | Ambient cubicity and induced \(P_{13}\). | Same active window. | Recount degrees. | SUPPORTED |
| S2 | Each endpoint has two external stubs. | Ambient cubicity and induced \(P_{13}\). | Same active window. | Recount degrees. | SUPPORTED |
| S3 | A genuine pair attaches at endpoints. | S1--S2 and internal disjointness. | Distinct first edges at each attachment. | Force a common first edge. | SUPPORTED |
| S4 | The retained selected occurrence is interior. | [152] selection and [153] origin map. | Origin must survive routing. | Trace [153]--[167]. | SUPPORTED |
| S5 | The survivor closes at [168]. | S3--S4. | Literal same-ledger consumption. | Search for reselection. | SUPPORTED |

## 4. Counterexample attempts

### Smallest-parameter test

- **Explicit data:** Two equal outside strands between the endpoints of a \(P_{13}\).
- **Hypotheses satisfied:** The local pair can be simple and internally disjoint.
- **Accumulated facts violated:** Its originating stub is an endpoint stub, not a selected interior occurrence.
- **Applicability:** NON-APPLICABLE TO THE NODE, excluded first by node [152].

### Parity or 2-adic test

- **Explicit data:** Choose lengths for which both closing tests fail.
- **Hypotheses satisfied:** The [167] arithmetic survivor may be nonempty in isolation.
- **Accumulated facts violated:** Arithmetic does not change the interior-origin fact.
- **Applicability:** NON-APPLICABLE TO THE NODE as a counterexample, excluded by node [168]'s geometric incompatibility.

### Boundary or range test

- **Explicit data:** Place both absorbed incidences at interior vertices.
- **Hypotheses satisfied:** This is the worst case for selected cardinality.
- **Accumulated facts violated:** None; exactly nine selected interior incidences remain.
- **Applicability:** Applicable and confirms the sharp count \(11-2=9\).

### Graph-realizability test

- **Explicit data:** Realize two internally disjoint endpoint-to-endpoint strands.
- **Hypotheses satisfied:** The pair can be graph-realized locally.
- **Accumulated facts violated:** It cannot be indexed by the retained selected interior occurrence.
- **Applicability:** NON-APPLICABLE TO THE NODE, excluded first by node [152].

### Branch-routing test

- **Explicit data:** Follow the literal [152] occurrence through [153], [163], and [167].
- **Hypotheses satisfied:** All selected branch facts and origin data are retained.
- **Accumulated facts violated:** The hypothetical genuine survivor conflicts with endpoint exclusion.
- **Applicability:** Applicable and closes through the sealed incompatibility executor.

## 5. Strongest valid counterexample

No candidate reaches the actual residual. The strongest local candidate is a
graph-realized endpoint-to-endpoint pair, but it fails the retained
interior-origin condition established before corridor extraction.

## 6. Local repair

### Corrected statement

No proof-source change required. The live statement already quantifies over
the selected interior-origin survivor.

### Complete local proof

The eleven interior vertices have one external stub each. After two absorbed
incidences, nine selected interior incidences remain. Two internally disjoint
strands require two stubs at an attachment, hence attach only at endpoints.
The selected interior occurrence therefore cannot lie on such an attachment,
contradicting the survivor contract.

### Counterexample disposition

All endpoint-origin candidates are excluded before candidate extraction.

### Graph patch

No graph patch required.

### Downstream impact

Node [176] may invoke [168] on each surviving part because [175] retains the
same selected-origin facts.

## 7. Regression audit

Inspected the manuscript's [152]--[168] path, `interiorStubList`,
`selectedStubs`, `allSelectedStubs`, `coldStubExcessRow`, the germ extraction
rows, `coldWindowStubStructureRow`, `symmetricPairEndpointExclusionRow`, both
Assembly call sites, the node table, campaign summary, and coverage record.
Searches for the superseded extraction coefficient and selected-family prose
return no audit occurrence.

## 8. Residual uncertainty

None for this node contract. This verdict does not assess independent upstream
or downstream nodes.
