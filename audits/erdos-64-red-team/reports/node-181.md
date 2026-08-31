<!-- red-team-audit
{
  "schema_version": 1,
  "proof": "erdos-gyarfas",
  "node": 181,
  "node_label": "OPEN: peeled target-defect demand residual:\\\\exact stage accounting, absorption,\\\\and window blockers",
  "panel": "fig:proof-diagram-part-ix",
  "contract_sha256": "0abce7dcd4a91c838bf12205846b0aa0b8824ca76507d9272f2988fb41dae162",
  "manuscript_sha256": "e189ab7e1412ac42ec3e2a62b50e26078dc8a23d6c15a0ac0ca82cc022e93114",
  "graph_sha256": "3e115264ccba8df33c0e62027ee62a6975de5ed254401cc7e00802c2f8acaebe",
  "lean_audit_sha256": "9a295d79027b0d11669474f2abb3418bcc410bdb06ea378b5c69a60ade2d2d57",
  "verdict": "NONEXHAUSTIVE BRANCH",
  "audited_at": "2026-08-31T00:22:01Z"
}
-->

# Red-team audit: node [181]

## 1. Executive verdict

Verdict: **NONEXHAUSTIVE BRANCH**

The exact node-[181] residual is faithfully retained by the manuscript and
Lean, but the proposed trace--ear consumer in `node_181_structure.md` does not
close it.  The numerical deduction after Lemma 8.1 is correct conditionally,
and the order-eight two-pole-shell lemma is valid.  The missing step is the
claimed exhaustion of a multi-boundary cyclic active region: neither a third
boundary incidence nor failure of an avoiding path yields the asserted single
cubic separator, uncrossing does not turn a laminar family into pairwise
disjoint shells, and no argument injects independent cycle-rank tokens into
those shells.  Thus the proof leaves an unassigned cyclic trace core and the
claim `beta_F <= p` is not established from the incoming ledger.

## 2. Exact node contract

### Incoming residual

The unique incoming edge is
`[123] -- no: failed reduced rate --> [181]`.  Its object is the same finite
simple minimal counterexample and the same selected remainder throughout.  The
incoming exact ledger retains the unified negative Type A collection, Type A
exclusion, Type B bridge reduction and sublinear ledger, extracted-entry
census, unified deficit, quotient-free arm, receiver routing, unified-entry
census, selection, and every earlier fact in `known`.  It appends the peel
chain and the failed-stage fact without replacing any inherited key.

Concretely, the new failed-stage data are a list `chain` satisfying
`Route8Pressure.PeelChain`, exact `StageAccounting`, and the literal negation
of `StageRate` at `chain.toFinset`.  `StageAccounting` retains the reduced and
peeled partition, disjointness, the peeled-cardinality charge, the full and
reduced burden inequalities, and the exact full-deficit decomposition.

### Accumulated facts

- Minimal counterexample: finite, simple, minimum degree at least three,
  target-free, lexicographically minimal, and bridgeless.
- Maximum induced-`P_13` packing, its remainder, boundary-incidence ledger,
  near-cubic surplus control, and the original density/rate facts published by
  the proof graph.
- Canonical Type A pieces are connected, subcubic, zero-surplus,
  `P_13`-free, negative-net-charge supports with receiver/load routing and the
  visible-first silent-excess inequality.
- Every unified entry has the selected trace basin, at least two essential
  carriers, and either the target-complete-minimal arm or the exact
  target-defect arm with its exit-(4) witness.
- Node [124] excludes the true route-8 two-carrier terminal; it does not
  consume the failed-stage target-defect residual.
- The demand partition is lexicographically maximal in its three- and
  two-demand classes and satisfies both no-overcount inequalities.
- The absorption is maximal subject to its dependence set and gives the exact
  open-demand inequality; the blocker map partitions every remaining open
  demand unit by a packed window.
- The sharpened constants `theta*` and `tau*` occur in the exploratory
  `closure_proofs.md`; they are not a fact newly produced by the live
  node-[181] Lean contract.

### Current predicate and exact claim

The live proposition is definitionally

```text
Route8StageRateFailedFact
  and Route8DemandLedgerStatement
  and Route8DemandAbsorptionStatement
  and Route8WindowBlockersStatement.
```

The audited proposed claim is the implication from this complete accumulated
state to `False`, via the marked trace--ear Lemma 8.1, the shell estimate, the
component inequality `7|X| <= 51 def(X)`, and a final global rate collision.

### Outgoing contracts

The authoritative graph has no outgoing edge: [181] is explicitly open.  The
proposed document informally adds one terminal outcome, `False`.  For that
outcome to be valid it must prove, for every marked full-vertex component, the
shell/branch injection and every case of its recursive exposure.  It does not
publish a typed complement for a multi-boundary cyclic active region, so the
informal transition to `False` is nonexhaustive.

## 3. Sentence audit

| Sentence | Exact assertion | Facts used | Hidden obligation | Adversarial test | Status |
|---|---|---|---|---|---|
| S1 | Node [181] is the conjunction of the four stated live propositions on the inherited `ExactLedger`. | `Route8PeeledDemandResidualStatement`; `route8PeeledDemandResidualRow`; `selectedRouteEightCensus` | None. | Compare the row's `Requires`, `Produces`, and returned key list. | SUPPORTED |
| S2 | No incoming fact is dropped at [181]. | `AtomicCT.run`; output keys are six new keys concatenated with `known` | The continuation must keep using the same selected object. | Inspect the exact type of `selectedRouteEightCensus`. | SUPPORTED |
| S3 | A negative connected zero-surplus Type A support has no internal-degree-zero receiver. | Connectedness; `def(X) < |X|/4` | A singleton support must be checked. | For `X={w}`, `def(X)=3>|X|/4`. | SUPPORTED |
| S4 | All full vertices in one component of `X_3` choose the same receiver. | Definition of `TraceTo`; connectedness of `F`; fixed receiver order | The set of traceable receivers must be exactly the receiver neighbours of `F`. | Join any full vertex to any boundary neighbour inside `F`. | SUPPORTED |
| S5 | Each anchored port return produces a receiver-entry return by taking its first-entry prefix and an independently chosen internal path to the receiver. | `lem:bridgeless`; `AnchoredReturn`; connectedness of `X` | The prefix and internal path must meet only at the first entry and avoid the port. | An anchored path with several visits to `X` is handled by discarding its post-entry suffix. | SUPPORTED AFTER THE LOCAL CORRECTION IN §7 |
| S6 | If a trace lies in the union `D` of exposed routes, it is a suffix of one actual receiver-entry channel. | Definition of visibility | Membership in a union must identify one route containing the entire trace with compatible orientation. | A trace switches between two intersecting exposed routes. | FAILED |
| S7 | A third boundary incidence of an ear shore supplies one cubic vertex whose deletion puts all remaining marks in strict components. | Cubicity; fixed edge order | Three routes need a common separating vertex. | A two-connected three-terminal cyclic region has no such articulation vertex. | FAILED |
| S8 | Failure of one path avoiding a common trace segment gives a single separating vertex by vertex Menger. | Menger's theorem | The relevant minimum separator must have order one. | The deleted common segment can be a separator of order two or more. | FAILED |
| S9 | Cut submodularity converts crossing two-pole shores into pairwise disjoint terminal shores while retaining all marks and decreasing the recursion measure. | Bridgelessness; submodularity | Intersection/union must be nonempty proper shores, retain the marked fibres, become disjoint rather than merely laminar, and decrease a recorded coordinate. | Intersection and union are nested; marks in difference regions have no assigned shell, and crossing number is absent from `mu`. | FAILED |
| S10 | Each independent exposed ear gives a distinct terminal two-pole shell, hence `beta_F <= p`. | First-divergence narrative | Rank tokens must survive uncrossing and inject into disjoint cut-two shores. | A cyclic three-terminal core carries positive rank and no cut-two shore. | FAILED |
| S11 | A target-free simple cubic two-pole shell has at least eight vertices. | Degree sum; Bondy--Vince Theorem 1 | The theorem's exact hypothesis is at most two vertices of degree below three. | Orders 2, 4, and 6 are checked separately. | SUPPORTED |
| S12 | Lemma 8.1 implies `10|U(F)| <= 3|F|+7b(F)` and then `7|X| <= 51 def(X)`. | Shell size; silent-excess lower bound; boundary count | None beyond Lemma 8.1. | Recompute every coefficient. | SUPPORTED CONDITIONALLY |
| S13 | The final collision may use `tau*` as an inherited node-[181] fact. | Exploratory Theorem 1.5 | A producer on the live branch, with its hypotheses and exact finite form, is required. | Search the live `Holds` schema and [181] prefix. | FAILED AS AN INCOMING-LEDGER CLAIM |
| S14 | Node [173]'s exact comparison automatically exactifies the new threshold `7/51`. | Existing small-order collision | The compared integer inequality must be the same inequality with the same constants. | [173] decides the manuscript's existing collision, not the new `856 theta < 7` test. | FAILED |

## 4. Counterexample attempts

### Smallest-parameter test

- **Explicit data:** A putative two-pole shell with total internal deficiency
  two and order `2`, `4`, or `6`.
- **Hypotheses satisfied:** Simplicity, connectedness, and the degree-sum
  identity are imposed.
- **Accumulated facts violated:** Order `2` would require parallel edges;
  order `4` is `K_4-e` and has a 4-cycle; at order `6`, Bondy--Vince forces a
  5-cycle and the remaining three edges force a 4-cycle.
- **Applicability:** NON-APPLICABLE TO THE NODE as a surviving shell; target
  avoidance excludes it.  This attempt supports Lemma 9.1 and does not repair
  Lemma 8.1.

### Parity or 2-adic test

- **Explicit data:** For a shell `K`,
  `2|E(K)| = 3|K|-2`.
- **Hypotheses satisfied:** Exactly two ambient incidences leave `K`, and every
  vertex has ambient degree three.
- **Accumulated facts violated:** An odd value of `|K|` makes the right side
  odd while the left side is even.
- **Applicability:** NON-APPLICABLE TO THE NODE for odd shell order, excluded
  by the degree-sum identity itself.  No 2-adic projection is used in the
  later coefficient algebra.

### Boundary or range test

- **Explicit data:** The abstract route diagram consisting of a triangle with
  one formal boundary leaf at each triangle vertex.  It has `b=3`, three cubic
  branch vertices, cycle rank one, and no connected induced shore with exactly
  two boundary edges.
- **Hypotheses satisfied:** The diagram is finite, connected, subcubic before
  the formal leaves are counted, and its only internal cycle has length three.
- **Accumulated facts violated:** No full minimal-counterexample realization,
  negative Type A support, silent mark, or demand token has been supplied.
- **Applicability:** NON-APPLICABLE TO THE NODE as a graph counterexample, but
  it is an isolated counterexample to the rank-token sentence: with `p=0`,
  the claimed `beta_F <= p` reads `1 <= 0`.

### Graph-realizability test

- **Explicit data:** Attempt to place the three-boundary triangle inside a
  connected negative Type A support and attach cubic outside return gadgets at
  its receiver incidences.
- **Hypotheses satisfied:** The local component can be made receiver-free and
  `P_13`-free, with formal degree three at each of its vertices.
- **Accumulated facts violated:** The attempt does not certify a globally
  simple target-free minimum-degree-three graph, the maximum packing, the
  selected silent-excess membership, the target-defect token, or the exact
  failed-stage ledgers.
- **Applicability:** NON-APPLICABLE TO THE NODE.  No actual counterexample to
  the complete node-[181] state is claimed.

### Branch-routing test

- **Explicit data:** An active induced region with three retained terminal
  incidences, no cut vertex separating the three terminal routes, and positive
  cycle rank after all already produced two-pole terminal shores are removed.
- **Hypotheses satisfied:** This is precisely the possible output when the
  proposed ear shore has a third boundary incidence; the incoming ledger
  decides only bridgelessness and does not assert a cut vertex, a cut-two shore,
  or three-way disjointness for every such region.
- **Accumulated facts violated:** None of the facts actually cited by the
  exposure excludes this topology.  The cold-branch overlap consumers are not
  ancestors of [181].
- **Applicability:** Applicable to the proposed transition as an unhandled
  proof state.  Case 2 neither closes it nor proves that the replacement
  regions are strict, and the later rank-token paragraph assumes it away.

## 5. Strongest valid counterexample

No graph satisfying the complete node-[181] residual and falsifying the main
theorem was produced.  The strongest valid adversarial object is instead the
multi-boundary cyclic active state in the branch-routing test.  It survives
every fact used by the proposed exposure, and no ancestor fact supplies the
missing articulation or cut-two shell.  It therefore falsifies the claimed
*exhaustiveness of the proof transition*, which is enough to prevent a closure
certificate without asserting that the main theorem is false.

## 6. Local repair

### Corrected statement

The portion that is actually proved can be stated as follows.

> **Conditional marked-forest estimate.**  Let `F` be a full-vertex
> component with `b` formal boundary leaves and marked set `U`.  Suppose there
> are pairwise vertex-disjoint induced two-pole shells `K_1,...,K_p`, a set
> `Z` outside the shells, an injection `U -> {K_i} disjoint_union Z`, and an
> embedded forest whose leaves are among the `b` boundary leaves and the two
> formal poles of each shell, and in which every vertex of `Z` has degree at
> least three.  If `F` is target-free, then
> `10|U| <= 3|F|+7b`.

This statement separates the textbook forest count from the unproved claim
that the node-[181] traces always generate such a forest.

### Complete local proof

Let `L` be the number of leaves of the forest.  By hypothesis
`L <= b+2p`.  In each nontrivial tree component, the number of vertices of
degree at least three is at most its number of leaves minus two; summing, and
then weakening, gives `|Z| <= L <= b+2p`.  Bondy--Vince plus the elementary
orders `2,4,6` argument gives `|K_i| >= 8` for every shell.  Disjointness gives
`|F| >= 8p+|Z|`, while injectivity gives `|U| <= p+|Z|`.  Therefore

```text
10|U| <= 10(p+|Z|)
        = 3(8p+|Z|) + 7(|Z|-2p)
        <= 3|F| + 7b.
```

Every step is local and textbook.  What it does not prove is the conditional
forest certificate.

### Counterexample disposition

The three-boundary cyclic diagram fails the forest certificate: after the
boundary leaves are fixed, its cycle cannot be represented by a forest with
all three cubic cycle vertices charged as branch vertices without deleting an
uncharged cycle edge.  It is therefore outside the corrected statement rather
than silently assigned a shell.

### Graph patch

Do not add the proposed `[181] -> False` edge.  Keep the current exact edge

```text
[123] -- failed StageRate, with exact peel/demand/absorption/blocker ledger --> [181].
```

The next admissible proof node must *produce* the conditional forest
certificate from the complete [181] state or must give a strictly smaller
typed consumer for the multi-boundary cyclic core.  Merely splitting on the
certificate is not admissible: its negative arm can be the same active region
and hence does not satisfy the structural-exhaustion progress rule.

### Downstream impact

- Lemma 9.1 and the coefficient algebra in (10.1)--(10.5) may be retained as a
  conditional local module.
- Lemma 8.1, (10.6)--(10.9), the declaration that [181] is closed, and the
  proposed Lean interfaces depending on `markedTraceEarExhaustion` must not be
  treated as established.
- `route8PeeledDemandResidualRow`, `selectedRouteEightCensus`, the proof-flow
  edge `[123] -> [181]`, and the audit-table status `OPEN BY DESIGN` remain the
  faithful implementation.
- A sharpened density theorem, if later admitted, needs its own producer and
  exact finite comparison; it cannot be read as an inherited [181] key.

## 7. Regression audit

- Searched the manuscript for node `[181]`,
  `def:typeA-peeled-demand-residual`, stage accounting, demand absorption, and
  blocker statements with `rg` and inspected the defining paragraphs around
  the large-budget descent.
- Inspected `Route8StageRateFailedFact`, `Route8DemandLedgerStatement`,
  `Route8DemandAbsorptionStatement`, `Route8WindowBlockersStatement`, and
  `Route8PeeledDemandResidualStatement` in `SpineVocabulary.lean`.
- Inspected `PeelChain`, `StageAccounting`, and `StageRate` in
  `Route8Pressure.lean`.
- Inspected `route8PeeledDemandResidualRow` in `SpineRows.lean` and the literal
  `selectedRouteEightCensus` composition in `Assembly.lean`.
- Searched for `theta*`, `tau*`, `118.108581006`, and relabeling entropy in the
  manuscript, Lean sources, `closure_proofs.md`, and
  `node_181_structure.md`; the sharpened cap occurs only in the exploratory
  Markdown proof record, not as a live [181] fact.
- Audited every use of `beta_F <= p`, shell injection, uncrossing, Menger,
  final-rate exactification, and the proposed `markedTraceEarExhaustion`
  interface.  No other implemented consumer of that proposed lemma was found.
- Checked Bondy--Vince, Theorem 1, against the primary paper: except for
  `K_1,K_2`, a simple graph with at most two vertices of degree below three has
  two cycles whose lengths differ by one or two.
- Checked the report metadata against a freshly reconstructed node-[181]
  contract; the checked and live graph semantic hashes agree.

## 8. Residual uncertainty

The audit did not enumerate graphs and did not seek a counterexample to the
main theorem.  It does not determine whether a different local argument can
derive the required marked forest, nor whether the sharpened relabeling bound
can be integrated with an exact finite producer.  The precise unresolved
mathematics is the multi-boundary cyclic trace core: one must show, on the full
node-[181] ledger, that it yields an existing exit, a strictly smaller typed
residual with invariant preservation, or enough disjoint two-pole shells for
the conditional forest estimate.  Until that proof is supplied, node [181]
is not mathematically closed.
