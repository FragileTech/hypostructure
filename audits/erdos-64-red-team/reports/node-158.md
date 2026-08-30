<!-- red-team-audit
{
  "schema_version": 1,
  "proof": "erdos-gyarfas",
  "node": 158,
  "node_label": "joint window package realized\\\\in the labelled class?",
  "panel": "fig:proof-diagram-part-i",
  "contract_sha256": "5ba886e04540bfe5288d5ed6b93cfbaafef05856376c4d98b02853979077af88",
  "manuscript_sha256": "106a8205a1718fbf90e1686a107b2143b9edca574e2b0c11415e7f44aee2c0f9",
  "graph_sha256": "dc67fae178f947a9607c167e383d85919633341bdd423e4c4a45e4c317b3a765",
  "lean_audit_sha256": "50324ef5594d635a52d83aeb297f2ca3f3d30ef58de4ce3602816c7e78365b12",
  "verdict": "NO ISSUE FOUND",
  "audited_at": "2026-08-24T20:59:21Z"
}
-->

# Red-team audit: node [158]

## 1. Executive verdict

Verdict: **NO ISSUE FOUND**

Node [158] is an exhaustive decision on the exact counting predicate introduced in `def:window-realization-test`, not an unconditional assertion that the window code is realized. If \(N_{\rm win}:=2^{c_{13}p_{13}\log_2 n}\), the selected predicate is the existence of an assignment from the fixed labelled skeleton class with range of cardinality at least \(N_{\rm win}\). Every such range has size at most \(|\mathcal G_{n,m}|\), while, conversely, the identity assignment on the skeleton class has range exactly \(|\mathcal G_{n,m}|\). Thus the literal no predicate is \(N_{\rm win}>|\mathcal G_{n,m}|\), exactly the entry fact of [159]. The tempting counterexample obtained by fixing a noninjective response map changes the existential predicate and is non-applicable. The two outgoing arms are literal complements and retain the complete incoming ledger.

## 2. Exact node contract

### Incoming residual

There is one incoming edge, [21] → [158], and no merge or loop. The current object is a finite simple labelled graph \(G\) on \(n\) vertices and \(m\) edges, assumed to be the lexicographically selected minimal counterexample: \(\delta(G)\ge3\) and \(G\) has no cycle of power-of-two length. The selected path carries the no-Mersenne-return formulation, no proper minimum-degree-three core, edge-deletion criticality, independence of \(V_{\ge4}(G)\), the boundaried-piece degree fibres, context universality, replacement exclusion, and hereditary target-uncompressibility.

The no arm of [15] has supplied an induced \(P_{13}\), and [17] has fixed the deterministic maximal vertex-disjoint induced-\(P_{13}\) packing \(\mathcal P\), with \(p_{13}=|\mathcal P|\). The no arm of [19] supplies \(\sigma(G)\le C_{\rm sp}\sqrt n\), hence the near-cubic edge stratum used at [21]. Node [18] supplies the finite \(399\)-label algebra, and [21] supplies the certified barrier enumeration, the separated window-package count, and the fixed-\(m\) labelled skeleton class
\[
\mathcal G_{n,m}=\{H:V(H)=[n],\ |E(H)|=m\},
\qquad |\mathcal G_{n,m}|=\binom{\binom n2}{m}.
\]

In Lean, the literal incoming `ExactLedger` is
`[skeletonDominates, windowPackageSeparated, barrierEnumeration,
surplusAtOrBelow, localAlgebra, maximalPacking, uncompressible,
replacementExclusion, targetCompleteContextUniversality,
degreeProfileFibres, tightEndpoint, slackIndependent, noProperBaseline,
returnAvoidance, selection]`. This confirms both the selected branch and the absence of any sibling fact.

### Accumulated facts

1. [2], `def:counterexample`: \(\delta(G)\ge3\) and no \(C_{2^j}\).
2. [4], minimal selection: \(G\) is least in the declared lexicographic order.
3. [5]–[6], `lem:return-equivalence`: every oriented edge avoids Mersenne returns.
4. [8]–[10], `lem:no-proper-core` and `lem:deletion-critical`: no proper \(3\)-core, every edge has a degree-three endpoint, and \(V_{\ge4}(G)\) is independent.
5. [11]–[14], `lem:degree-profile-fibres`, `lem:context-universality`, `lem:replacement`, and `cor:uncompressible`: boundary fibres are retained and no proper target-complete replacement is available.
6. [15]–[17], `cor:p13-exists`: the fixed maximal packing \(\mathcal P\) is nonempty and is chosen canonically.
7. [18], `lem:labels`: the \(399\) legal labels and the relations \(C_s\) are available.
8. [19] no arm and `def:near-cubic-spine`: the current edge stratum is near cubic; the strict-surplus sibling is not imported.
9. [21], `lem:p13-window-package`: the fixed packing has its separated canonical multi-scale package with rate \(c_{13}=118.108581006\ldots\).
10. [21], `lem:skeleton-dominates`: every assignment on the skeleton class has range at most \(|\mathcal G_{n,m}|\), and the skeleton class itself has exactly that cardinality.

### Current predicate and exact claim

Put
\[
N_{\rm win}=2^{c_{13}p_{13}\log_2 n},
\qquad D=\mathcal G_{n,m}.
\]
The decision predicate is
\[
P:\quad \exists (S,f:D\to S),\quad |\operatorname{range}(f)|\ge N_{\rm win},
\]
where the state labels are the target-complete window-package states in the manuscript's named exact counting test. The formal implication audited at [158] is
\[
F(158)\Longrightarrow P\ \sqcup\ \neg P,
\]
with
\[
P\Longrightarrow N_{\rm win}\le |D|,
\qquad
\neg P\Longrightarrow N_{\rm win}>|D|.
\]
The second implication uses the identity assignment \(D\to D\): if \(N_{\rm win}\le|D|\), its range witnesses \(P\). Therefore \(\neg P\iff N_{\rm win}>|D|\). On the near-cubic stratum, taking logarithms and using
\(\log_2|D|=\tfrac32n\log_2n+o(n\log n)\) rewrites the strict inequality as
\(\theta=p_{13}/n>\theta_{\rm win}+o(1)\), where
\(\theta_{\rm win}=1.5/c_{13}\). The exact strict cardinal inequality, not the asymptotic shorthand, is the routed fact.

### Outgoing contracts

- **Yes, [158] → [22].** Predicate \(P\) is retained as `windowPackageRealized`, together with every incoming key. Node [22] canonically partitions \(\mathcal P=\mathcal P_{\rm hot}\sqcup\mathcal P_{\rm cold}\); its later live-hot comparison is entitled to read the retained realization fact, the separated package, and `skeletonDominates`.
- **No, [158] → [159].** Predicate \(\neg P\) is retained as `windowPackageUnrealized`. Together with `skeletonDominates`, it yields
  \(N_{\rm win}>|\mathcal G_{n,m}|\), published formally as `densePackingOverflow`. This is exactly node [159]'s entry contract before its own deficiency test [160].

The arms are \(P\) and its literal negation. No charge, deficit, packing datum, or target ledger item is deleted on either edge.

## 3. Sentence audit

| Sentence | Exact assertion | Facts used | Hidden obligation | Adversarial test | Status |
|---|---|---|---|---|---|
| S1 | The realization sentence is a branch test, not an assertion. | Diagram [158]; `def:window-realization-test` | Both truth values must be routed. | Inspect both live edges and their destination entries. | SUPPORTED |
| S2 | \(\mathcal P\) and \(\mathcal G_{n,m}\) are fixed canonical objects. | [17], [21]; deterministic tie breaking in `lem:skeleton-dominates` | Auxiliary choices must not multiply the domain. | Replace the packing by a noncanonical maximal packing. | EXCLUDED UPSTREAM |
| S3 | Realized means an assignment with range at least \(N_{\rm win}\). | `def:window-realization-test` | The test must be read as the named cardinal predicate, not as a prescribed noninjective map. | Force a constant designated response map while leaving other assignments available. | SUPPORTED |
| S4 | Node [158] decides \(P\) exhaustively. | Classical excluded middle; `Decision.run` | The no key must express exactly \(\neg P\). | Compare `windowPackageRealized` with `windowPackageUnrealized`. | SUPPORTED |
| S5 | The yes branch enters [22]. | Edge [158] → [22] | The realization fact and incoming package ledger must be retained. | Inspect the literal `ExactLedger` and later `windowPackageRealized` reads. | SUPPORTED |
| S6 | The no branch satisfies \(N_{\rm win}>|\mathcal G_{n,m}|\) and enters [159]. | S3; `lem:skeleton-dominates` | Converse cardinal witness and strict complement must both hold. | Use the identity assignment at equality and below budget. | SUPPORTED |
| S7 | The strict count is asymptotically \(\theta>\theta_{\rm win}+o(1)\). | Near-cubic edge count; binomial skeleton asymptotic | Do not replace the exact routing fact by the asymptotic formula at finite \(n\). | Test equality and bounded-\(n\) rounding. | SUPPORTED |

## 4. Counterexample attempts

### Smallest-parameter test

- **Explicit data:** Take the formally smallest package size \(p_{13}=0\). Then \(N_{\rm win}=1\), and any nonempty fixed edge stratum \(\mathcal G_{n,m}\) realizes it by a constant or identity assignment.
- **Hypotheses satisfied:** The cardinal decision itself is well-defined, and its yes arm is selected.
- **Accumulated facts violated:** The no arm of [15], `cor:p13-exists`, followed by the maximal packing at [17], forces \(p_{13}\ge1\) on the actual residual.
- **Applicability:** **NON-APPLICABLE TO THE NODE.** The earliest excluding fact is [15], `cor:p13-exists`; the test nevertheless confirms that the zero-package endpoint is not accidentally sent to [159].

### Parity or 2-adic test

- **Explicit data:** Use the power-of-two order \(n=16\), the cubic edge count \(m=24\), and \(p_{13}=1\). Numerically,
  \(\log_2N_{\rm win}=472.4343240\ldots\), whereas
  \(\log_2\binom{120}{24}=83.1688466\ldots\); hence the no arm is selected.
- **Hypotheses satisfied:** \(n\ge13\), \(p_{13}\le\lfloor n/13\rfloor\), and \(m=3n/2\) satisfy the node's finite numerical ranges.
- **Accumulated facts violated:** No parity, divisibility, or 2-adic fact is used by node [158]. The data do not construct a graph satisfying [2]–[21], so they are not claimed as an actual residual graph.
- **Applicability:** Applicable as a parity stress test of the cardinal predicate; it is routed to [159], not a counterexample. The modular checker does not apply because there is no congruence, orbit, or integer-lift inference at this node.

### Boundary or range test

- **Explicit data:** Abstract the comparison to \(N_{\rm win}=4\) and \(|\mathcal G_{n,m}|=4\). The identity assignment has range \(4\).
- **Hypotheses satisfied:** This is the equality endpoint of S3, with a finite nonempty domain and the full range available.
- **Accumulated facts violated:** None at the cardinal level; the numbers are a boundary model rather than parameters asserted to arise from a graph on the incoming residual.
- **Applicability:** Equality belongs to the yes arm because the definition uses \(\ge\); the no arm is the strict inequality \(N_{\rm win}>|\mathcal G_{n,m}|\). There is no uncovered equality case.

### Graph-realizability test

- **Explicit data:** Let a four-skeleton class have a *designated* canonical response map whose image is a single state, while two abstract target-complete package states exist. If realization meant “the designated map has range at least \(2\),” realization would fail although \(2\le4\), apparently defeating the edge to [159].
- **Hypotheses satisfied:** The example satisfies the skeleton upper bound and exhibits the strongest correlation/collision attack on an informal reading of “realized canonically.”
- **Accumulated facts violated:** It replaces the existential assignment in `def:window-realization-test` by a different, fixed-map predicate. Under the selected predicate, choose an assignment sending two skeletons to the two states (or use the formal identity assignment); then realization holds. It also supplies no graph satisfying the minimal-counterexample ledger [2]–[21].
- **Applicability:** **NON-APPLICABLE TO THE NODE.** The excluding statement is the exact predicate in `def:window-realization-test`, confirmed by `WindowPackageRealized` and the identity-range proof in `densePackingOverflowRow`.

### Branch-routing test

- **Explicit data:** At \(n=100,m=150\),
  \(\log_2|\mathcal G_{100,150}|=964.8321282\ldots\). For \(p_{13}=1\),
  \(\log_2N_{\rm win}=784.6964270\ldots\), so \(P\) holds and the route is [22]. For \(p_{13}=2\),
  \(\log_2N_{\rm win}=1569.3928540\ldots\), so \(\neg P\) holds and the route is [159].
- **Hypotheses satisfied:** Both choices obey \(p_{13}\le\lfloor100/13\rfloor\) and use the exact near-cubic edge stratum; each is a valid finite truth-table input to the decision.
- **Accumulated facts violated:** Neither numerical tuple is asserted to come from a minimal counterexample satisfying all graph invariants.
- **Applicability:** Both decision values have exactly one destination. The first retains realization for [22]; the second supplies the strict overflow required at [159].

## 5. Strongest valid counterexample

No candidate reaches the actual residual and falsifies node [158]. The strongest candidate is the four-skeleton, two-state example with a constant *designated* response map: it preserves the numerical capacity and exposes the only plausible semantic trap, but it changes the node's existential counting predicate. With the actual predicate an assignment of range two exists, so the example is on the yes arm. No candidate survived both the exact predicate and the full [2]–[21] graph ledger.

## 6. Local repair

### Corrected statement

No proof-source change required. A fully explicit equivalent wording would be: “Let \(N_{\rm win}=2^{c_{13}p_{13}\log_2n}\). Node [158] tests whether \(N_{\rm win}\le|\mathcal G_{n,m}|\), equivalently whether there exists an assignment on the labelled skeleton class whose range has at least \(N_{\rm win}\) state labels. The yes arm retains this realization fact and enters [22]; the no arm retains the strict complement \(N_{\rm win}>|\mathcal G_{n,m}|\) and enters [159].”

### Complete local proof

For any assignment \(f:\mathcal G_{n,m}\to S\), the elementary range bound gives \(|\operatorname{range}(f)|\le|\mathcal G_{n,m}|\). Hence realization implies \(N_{\rm win}\le|\mathcal G_{n,m}|\). Conversely, if \(N_{\rm win}\le|\mathcal G_{n,m}|\), take the state-label type to be the labelled skeleton class and take the identity assignment. Its range is the whole class, so it witnesses realization. Thus realization is equivalent to the weak cardinal inequality, and its literal negation is the strict reverse inequality. Excluded middle yields exactly the two decision arms. The fixed-\(m\) binomial asymptotic on the retained near-cubic stratum converts the strict reverse inequality to \(\theta>1.5/c_{13}+o(1)\), but [159] retains the exact finite inequality.

### Counterexample disposition

The zero-packing candidate is excluded at [15]. The equality candidate is in the yes arm. The power-of-two-order and \(n=100\) numerical candidates are routed by the strict comparison. The fixed constant-map candidate changes the existential predicate and is therefore non-applicable.

### Graph patch

No graph patch is required. The verified local routing remains
\[
[21]\longrightarrow[158]
\begin{cases}
N_{\rm win}\le|\mathcal G_{n,m}| &\longrightarrow [22],\\
N_{\rm win}>|\mathcal G_{n,m}| &\longrightarrow [159].
\end{cases}
\]
The [22] edge retains the complete [21] ledger and the realization key; the [159] edge retains the same ledger and the negated key, from which the exact overflow fact is derived.

### Downstream impact

None. The diagram, caption, detailed dependency row, dense-residual subsection, and `prop:p13-density` already use this two-arm interpretation. Lean's `selectedWindowPackageRealizationDichotomy` selects literal complements, and `densePackingOverflowRow` proves the [159] entry inequality with the identity range. No repeated theorem, table row, caption, analogue, or Lean contract requires alteration.

## 7. Regression audit

- Inspected the Part I diagram and caption at the occurrences of `[158]`, including both explicit edges [158] → [22] and [158] → [159].
- Inspected the Part XII entry node [159] and its caption, the detailed dependency-table row `[158]--[168]`, the entropy/skeleton table row for `def:window-realization-test`, and the dense-residual status paragraph.
- Inspected `def:target-rank`, `lem:independent-target-entropy`, `lem:skeleton-dominates`, `lem:state-count-comparison`, `lem:p13-window-package`, `def:window-realization-test`, `lem:dense-deficiency-routing`, `lem:dense-cold-pass`, and the first window-only part of `prop:p13-density`.
- Inspected the analogous branch-test discussion for the pair-code residual [178]–[180]; it does not alter node [158]'s predicate or routing.
- Inspected `web/tools/papers/erdos64.py`; its explicit continuation is [158] → [159], and the freshly extracted graph has `graph_drift: false`.
- Inspected the literal Lean contract `WindowPackageRealized`, its `Holds` clauses, the incoming `ExactLedger`, `selectedWindowPackageRealizationDichotomy`, `skeletonDominatesRow`, the [22] partition consumer, and `densePackingOverflowRow`. The decision arms are exact negations and the latter constructs the identity-range witness.
- Inspected `Assembly_node_audit.md` and `web/data/eg_node_audit.json` only as locators/status evidence, then verified their claims in the actual declarations. Formalization gaps downstream at other nodes were not promoted to a mathematical finding at [158].
- Search commands/patterns included `rg -n 'def:window-realization-test|lem:p13-window-package|lem:skeleton-dominates|lem:independent-target-entropy|lem:state-count-comparison|prop:p13-density|dense-packing residual|joint window package' to_formalize/erdos_64_proof.tex` and `rg -n 'WindowPackageRealized|windowPackageUnrealized|densePackingOverflow|selectedWindowPackageRealizationDichotomy' hypostructure proofs Assembly_node_audit.md web/data/eg_node_audit.json`. No second manuscript definition or contradictory outgoing edge was found.

## 8. Residual uncertainty

This audit does not re-prove the finite barrier computation or the graph-realizability/independence claims owned by [21], and it does not audit any downstream closure in [159]–[172]. The manuscript phrase “target-complete states ... realized canonically” does not separately formalize a prescribed graph-to-response map inside `def:window-realization-test`; this report follows the definition's immediately stated exact counting reading, corroborated by the identity-assignment implementation. If a future revision changes node [158] to test the image of a prescribed response map, the no-edge would need a new contract and this report's fingerprint should become stale. No proof source, Lean source, diagram, audit table, or coverage ledger was changed.
