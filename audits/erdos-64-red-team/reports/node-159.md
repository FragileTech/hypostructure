<!-- red-team-audit
{
  "schema_version": 1,
  "proof": "erdos-gyarfas",
  "node": 159,
  "node_label": "dense-packing residual: the no-edge of [158];\u005c\u005c\u005c(2^{c_{13}p_{13}\u005clog_2 n}\u005c) exceeds the labelled skeleton class, i.e.\u005c \u005c(\u005ctheta>\u005ctheta_{\u005crm win}\u005c)",
  "panel": "fig:proof-diagram-part-xii",
  "contract_sha256": "30795e32f110d92e3767b560936fd6d27c8017ed3269688b2060fba594d79173",
  "manuscript_sha256": "106a8205a1718fbf90e1686a107b2143b9edca574e2b0c11415e7f44aee2c0f9",
  "graph_sha256": "dc67fae178f947a9607c167e383d85919633341bdd423e4c4a45e4c317b3a765",
  "lean_audit_sha256": "50324ef5594d635a52d83aeb297f2ca3f3d30ef58de4ce3602816c7e78365b12",
  "verdict": "PROSE AMBIGUITY",
  "audited_at": "2026-08-24T20:59:54Z"
}
-->

# Red-team audit: node [159]

## 1. Executive verdict

Verdict: **PROSE AMBIGUITY**

Read semantically, node [158] asks whether the fixed package's target-complete states are canonically realized by labelled skeletons; the negation of that statement does not imply that the package demand exceeds the cardinality of the skeleton class, as node [159] asserts. Read instead as the bare cardinal test \(Q\le B\), where \(Q=2^{c_{13}p_{13}\log_2 n}\) and \(B=|\mathcal G_{n,m}|\), the no-arm is exactly \(Q>B\), and the node is valid. The manuscript uses both readings in the same definition. The implementation selects the latter reading by allowing an unconstrained state type and state map. The smallest proof-preserving correction is therefore to call [158] the exact package-budget feasibility test \(Q\le B\), not a semantic realization test.

## 2. Exact node contract

### Incoming residual

The object is a finite simple graph \(G\) chosen lexicographically minimal in \((|V(G)|,|E(G)|)\) among graphs with minimum degree at least \(3\) and no power-of-two cycle. Write \(n=|V(G)|\), \(m=|E(G)|\), let \(\mathcal P\) be the fixed canonical maximal vertex-disjoint induced-\(P_{13}\) packing, put \(p_{13}=|\mathcal P|\), and set \(\theta=p_{13}/n\). The selected incoming edge is uniquely the no-arm of [158]. On the semantic reading of `def:window-realization-test`, that arm carries

\[
\neg\operatorname{Real}_{\rm can}(\mathcal P),
\]

where \(\operatorname{Real}_{\rm can}(\mathcal P)\) means that a canonical graph-to-target-state assignment from \(\mathcal G_{n,m}\) realizes at least

\[
Q:=2^{c_{13}p_{13}\log_2 n}
\]

distinct target-complete package states. The skeleton budget is

\[
B:=|\mathcal G_{n,m}|=\binom{\binom n2}{m}.
\]

There is no merge and no loop at this node. The route tag “no from [158]” must be retained; facts from [158]'s yes-arm and the sibling hot/cold continuation are not incoming facts.

### Accumulated facts

The manuscript and live graph supply the following cumulative state.

1. Nodes [1]--[6]: \(G\) is the selected minimal counterexample; for every oriented edge \(e\), \(R_e(G)\cap\mathcal M=\varnothing\).
2. Nodes [8]--[10]: every proper subgraph has minimum degree at most \(2\); every edge has a degree-\(3\) endpoint; \(V_{\ge4}(G)\) is independent.
3. Nodes [11]--[14]: boundary-degree fibres are retained; a target-complete identification is context-universal; no proper support has a smaller replacement or a target-complete compression satisfying the replacement hypotheses.
4. Nodes [15]--[18]: \(G\) is not \(P_{13}\)-free; \(\mathcal P\) is the fixed maximal packing; its \(P_{13}\) labels belong to the \(399\)-label algebra with the declared relations \(C_s\).
5. The no-arm of [19] and node [21]: the selected branch has the near-cubic estimate \(m=\tfrac32n+O(\sqrt n)\), \(\sigma(G)=O(\sqrt n)\); the finite barrier enumeration gives \(c_{13}=118.108581006\ldots\); and the separated package supplies \((c_{13}-o(1))p_{13}\log_2 n\) independently target-testable coordinates.
6. `lem:skeleton-dominates`: every canonical graph-to-state map from \(\mathcal G_{n,m}\) has range at most \(B\), and the auxiliary packing, profile, and tie-breaking data add no independent choices.
7. Selected branch predicate from [158]: the canonical full package is not realized, under the semantic wording of the manuscript.

The literal Lean ledger just before [158] is

```text
[skeletonDominates, windowPackageSeparated, barrierEnumeration,
 surplusAtOrBelow, localAlgebra, maximalPacking, uncompressible,
 replacementExclusion, targetCompleteContextUniversality,
 degreeProfileFibres, tightEndpoint, slackIndependent,
 noProperBaseline, returnAvoidance, selection].
```

The no-arm appends `windowPackageUnrealized`. The [159] row then reads exactly `windowPackageUnrealized` and `skeletonDominates` and appends `densePackingOverflow`. No charge, deficit, or support carrier is transferred or discharged at [159].

### Current predicate and exact claim

The literal semantic implication presented by the prose is

\[
F(159)+\neg\operatorname{Real}_{\rm can}(\mathcal P)
\quad\Longrightarrow\quad
Q>B,
\]

followed by the asymptotic reading

\[
Q>B
\quad\Longleftrightarrow\quad
\theta>\theta_{\rm win}+o(1),
\qquad
\theta_{\rm win}=\frac{3}{2c_{13}}.
\]

Only the first implication is at issue. `lem:skeleton-dominates` proves \(\operatorname{Real}_{\rm can}(\mathcal P)\Rightarrow Q\le B\), not its converse. Consequently its contrapositive is \(Q>B\Rightarrow\neg\operatorname{Real}_{\rm can}(\mathcal P)\), the reverse of the implication consumed at [159]. If “realized” is defined instead to mean the bare predicate \(Q\le B\), the displayed claim is the literal negation and is valid.

### Outgoing contracts

The only graph edge is [159] \(\to\) [160]. It retains the complete incoming state, the no-arm tag, the canonical packing, and the asserted strict overflow \(Q>B\). Node [160] then decides the exact finite version of

\[
\tau(\theta)=\frac{15\theta}{1-13\theta}<\frac14,
\]

including the near-cubic \(O(\sqrt n)\) allowance. Its yes-arm supplies the deficiency cap required at [161] and the continuation to [25]; its no-arm retains the literal complement and enters the dense hot/cold pass at [162]. The immediate decision [160] can be formed without the overflow fact, but the later additive compression closure [171] consumes that strict overflow. Thus silently weakening [159] to mere non-realization would make the eventual [171] handoff ill-typed.

## 3. Sentence audit

| Sentence | Exact assertion | Facts used | Hidden obligation | Adversarial test | Status |
|---|---|---|---|---|---|
| S1 | The fixed objects are \(\mathcal P\) and \(\mathcal G_{n,m}\). | [17], `lem:skeleton-dominates`, canonical tie-breaking. | Both must be functions of the same selected graph and fixed \(n,m\). | Checked the manuscript definitions and the literal Lean object indices. | SUPPORTED |
| S2 | The package is “realized” if a canonical assignment of target-complete states to skeletons has range at least \(Q\). | `lem:p13-window-package`, `def:target-rank`, `lem:state-count-comparison`. | “Canonical” must select the actual target-state map; not every function from skeletons to an arbitrary type is such a map. | Replace the canonical map by a constant map while keeping \(Q\le B\). | AMBIGUOUS |
| S3 | This is “i.e.” the full package code being realized canonically. | S2. | Existential quantification over arbitrary assignments must be equivalent to realization of the fixed code. | A type with many arbitrary labels does not make those labels package states of the graphs. | AMBIGUOUS |
| S4 | Node [158] decides the predicate and its yes-arm goes to [22]. | Law of excluded middle; graph edge [158] \(\to\) [22]. | The no-arm must retain the literal negation. | Checked `Decision.run`: Lean does retain exact proposition/negation arms. | SUPPORTED |
| S5 | On the no-arm, \(Q>B\). | Claimed from S2 and `lem:skeleton-dominates`. | The converse \(Q\le B\Rightarrow\operatorname{Real}_{\rm can}\) is required. | Budget-feasible but collapsed canonical map: \(Q\le B\) and realized range \(<Q\). | AMBIGUOUS |
| S6 | The strict overflow is asymptotically \(\theta>\theta_{\rm win}+o(1)\). | Near-cubic budget and \(p_{13}=\theta n\). | The statement is asymptotic, not a pointwise equality; the \((c_{13}-o(1))\) package loss must be retained. | Tested equality and finite-\(n\) threshold cases. | SUPPORTED |
| S7 | The residual flows to [160]. | Diagram edge [159] \(\to\) [160]; `lem:dense-deficiency-routing`. | The strict overflow must remain available for later [171], although [160] itself does not consume it. | Traced the live ExactLedger through `densePackingOverflowRow` and the later compression theorem. | ROUTING ONLY |

The live Lean declaration `WindowPackageRealized` quantifies over an arbitrary type `State` and an arbitrary map `stateOf : Skeleton → State`, with no target-completeness or fixed-code predicate. Therefore \(Q\le B\) supplies a witness by taking `State = Skeleton` and `stateOf` to be the identity. `densePackingOverflowRow` is kernel-valid for that deliberately cardinal schema. This establishes implementation consistency with the bare-budget reading, but does not resolve the manuscript's stronger semantic wording.

## 4. Counterexample attempts

### Smallest-parameter test

- **Explicit data:** At the first numerical size permitting one \(P_{13}\) window, take \(n=13\), \(p_{13}=1\), and the near-cubic integer \(m=20\). Then \(\log_2 Q\approx437.054\), whereas \(\log_2\binom{78}{20}\approx60.780\), so \(Q>B\).
- **Hypotheses satisfied:** The integer parameters satisfy \(p_{13}\le n/13\), and the numerical overflow conclusion is true.
- **Accumulated facts violated:** No graph realizing the complete [2]--[21] state is supplied; in particular a \(13\)-vertex target-avoiding minimum-degree-\(3\) minimal counterexample is not constructed.
- **Applicability:** **NON-APPLICABLE TO THE NODE** as a graph candidate, excluded first by the unverified counterexample predicate at [2]. It is nevertheless a successful endpoint check: the smallest numerical packing does not expose the quantifier problem.

### Parity or 2-adic test

- **Explicit data:** Compare even \(n=100,m=150,p_{13}=1\) with odd \(n=101,m=152,p_{13}=1\). For \(n=100\), \(\log_2 Q\approx784.696<964.832\approx\log_2 B\); for \(n=101\), \(\log_2 Q\approx786.392<979.257\approx\log_2 B\). In either case a fixed canonical target-state map with image of size \(1\) is not package-realizing although \(Q<B\).
- **Hypotheses satisfied:** The numerical data are near-cubic, \(p_{13}>0\), and \(\theta<\theta_{\rm win}\). The same logical witness works for both parities; the node contains no modular division or 2-adic reduction.
- **Accumulated facts violated:** The state-map model is not accompanied by an actual graph satisfying [2], the replacement ledger, and the window-package graph-realizability requirements.
- **Applicability:** **NON-APPLICABLE TO THE NODE** as an actual graph, first because [2]'s target-avoiding counterexample is unverified. It survives the arithmetic abstraction and shows that parity cannot repair the reversed implication.

### Boundary or range test

- **Explicit data:** Let the skeleton class have cardinality \(B=4\), let the package demand be \(Q=4\), let four distinct target-complete package states exist abstractly, and let the only admissible canonical graph-to-state map have range \(1\).
- **Hypotheses satisfied:** Every canonical range is at most \(B\); \(Q\le B\); and the fixed package is not canonically realized because its realized range has cardinality \(1<Q\).
- **Accumulated facts violated:** This is a cardinal/state-map model, not a finite simple graph satisfying the accumulated graph predicates from [2]--[21].
- **Applicability:** **NON-APPLICABLE TO THE NODE** as a graph witness, first at [2]. It is applicable to the literal logical inference in `def:window-realization-test` and falsifies the strict conclusion at the equality boundary \(Q=B\).

### Graph-realizability test

- **Explicit data:** The smallest concrete cubic test graph \(K_4\) has \(n=4,m=6,\delta=3\), but it contains a \(4\)-cycle and has no induced \(P_{13}\); hence \(p_{13}=0\).
- **Hypotheses satisfied:** It is a finite simple graph with the minimum-degree condition and exact cubic edge count.
- **Accumulated facts violated:** It violates the target-avoidance half of [2] and the selected no-arm of [15] that produces the nonempty maximal \(P_{13}\) packing.
- **Applicability:** **NON-APPLICABLE TO THE NODE**, excluded first by node [2]. No actual graph realizing the stronger range-collapse candidate and the complete cumulative residual was found.

### Branch-routing test

- **Explicit data:** Partition the semantic possibilities into (A) \(\operatorname{Real}_{\rm can}\); (B) \(\neg\operatorname{Real}_{\rm can}\land Q>B\); and (C) \(\neg\operatorname{Real}_{\rm can}\land Q\le B\). The current graph sends A to [22] and sends the entire literal no-arm, B or C, to [159], but [159]'s asserted contract contains only B.
- **Hypotheses satisfied:** The three cases are exhaustive and disjoint. Case C satisfies `lem:skeleton-dominates` and the literal selected branch predicate.
- **Accumulated facts violated:** No accumulated manuscript lemma excludes C by proving \(Q\le B\Rightarrow\operatorname{Real}_{\rm can}\). Actual graph realization of C remains unproved.
- **Applicability:** Applicable to the source-level branch contract and is the strongest audit candidate. Under the implementation's cardinal-only definition, C is reclassified into A; under the manuscript's semantic wording, C reaches [159] but does not satisfy its claimed overflow payload.

## 5. Strongest valid counterexample

The strongest surviving candidate is case C from the branch-routing test: a fixed target-state map whose image has fewer than \(Q\) states even though the skeleton class has at least \(Q\) elements. It satisfies the no-realization predicate and the skeleton upper bound while falsifying \(Q>B\). This is a valid countermodel to the isolated semantic implication and is not excluded by any cited range theorem. It is not an actual residual graph: no finite simple graph satisfying the complete minimal-counterexample, packing, quotient, and target-avoidance state was constructed. That is why the finding is confined to the ambiguity between the semantic and cardinal readings rather than promoted to a graph counterexample.

## 6. Local repair

### Corrected statement

Let

\[
Q=2^{c_{13}p_{13}\log_2 n}
\quad\text{and}\quad
B=|\mathcal G_{n,m}|.
\]

Node [158] is the exact package-budget feasibility test \(Q\le B\). Its yes-arm continues to the hot/cold split [22]. Its no-arm is the dense-packing residual [159], on which \(Q>B\). Under the near-cubic estimate \(\log_2 B=\tfrac32n\log_2 n+o(n\log n)\), this strict inequality is equivalently \(\theta>\theta_{\rm win}+o(1)\), with \(\theta_{\rm win}=3/(2c_{13})\). This statement deliberately makes no assertion that a budget-feasible package is canonically graph-realized.

### Complete local proof

The integers \(Q\) and \(B\) are totally ordered. Node [158] decides \(Q\le B\). On its no-arm, \(\neg(Q\le B)\), hence \(B<Q\), which is the displayed inequality at [159]. On the near-cubic branch,

\[
\log_2B=\frac32n\log_2n+o(n\log n).
\]

Taking logarithms of \(Q>B\), substituting \(p_{13}=\theta n\), and dividing by \(n\log_2n>0\) gives

\[
c_{13}\theta>\frac32+o(1),
\]

or \(\theta>3/(2c_{13})+o(1)=\theta_{\rm win}+o(1)\). The yes-arm may still proceed to [22], because the hot/cold partition is defined from the fixed canonical packing and its own local realization tests; neither the manuscript definition of that partition nor the live `hotColdPartitionRow` requires semantic realization of the whole packing at [158].

### Counterexample disposition

The range-collapse candidate has \(Q\le B\), so the corrected [158] sends it to the yes-arm. Its small canonical image no longer contradicts [159], because [159] is reached only from the strict cardinal complement. Any claim that the whole package is graph-realized must then be proved where it is actually consumed, using the independent-target and hot/cold ledgers rather than the word “realized” at [158].

### Graph patch

No new node is needed:

```text
[21] -> [158]: decide Q <= |G_{n,m}|
[158] -> yes (Q <= |G_{n,m}|; retain fixed packing/package facts) -> [22]
[158] -> no  (Q >  |G_{n,m}|; retain complete incoming ledger) -> [159]
[159] -> retain strict overflow and near-cubic state -> [160]
```

The entry contract of [22] remains the fixed maximal packing, the label/barrier package, and the facts needed to define its canonical hot/cold partition. The entry contract of [160] remains the complete [159] ledger plus the strict package overflow and the exact quantities used by `DenseDeficiencyBelowStatement`. If the authors insist that [158] test semantic graph-realization instead, a third explicit residual \(\neg\operatorname{Real}_{\rm can}\land Q\le B\) is necessary; it cannot be sent to [160] as carrying the overflow fact or to any named closure without a new producer.

### Downstream impact

The repair preserves the strategy and all existing edges, but the phrases “joint window package realized” and “realization sentence” should be changed to “package budget feasible” in the Part I and Part XII node labels/captions, the detailed dependency table, `def:window-realization-test`, and `rem:dense-residual-status`. The strict fact consumed by `lem:blocked-graphs-compress` at [171] is unchanged. In Lean, `WindowPackageRealized` is already extensionally the cardinal test because the identity skeleton map is admissible; its name and documentation should be made explicit, or its proposition should be replaced directly by \(Q\le B\). If genuine target-complete realization is later required, it must have a separate predicate with the target-state type, fixed canonical map, and package-code condition encoded. The node-status tables in `Assembly_node_audit.md` and `web/data/eg_node_audit.json` should then describe the same reading.

## 7. Regression audit

The audit inspected these repeated uses and consumers:

- Part I edge [158] \(\to\) [159], Part XII node label and edge [159] \(\to\) [160], and both captions.
- Detailed dependency-table item 51 and the framework rows for `def:window-realization-test`, `lem:dense-deficiency-routing`, and `lem:blocked-graphs-compress`.
- `def:target-rank`, `lem:independent-target-entropy`, `lem:skeleton-dominates`, `lem:state-count-comparison`, `lem:p13-window-package`, `def:window-realization-test`, `rem:dense-residual-status`, `lem:blocked-graphs-compress`, and `prop:p13-density`.
- The live declarations `WindowPackageRealized`, `Holds .windowPackageRealized`, `Holds .windowPackageUnrealized`, `Holds .densePackingOverflow`, `densePackingOverflowRow`, `selectedWindowPackageRealizationDichotomy`, and the literal no-arm in `selectedNearCubicBranch`.
- The node [158]--[162] rows of `Assembly_node_audit.md` and the node [159]--[162] entries of `web/data/eg_node_audit.json`. These locators disagree about current formalization status, but neither status table is mathematical authority.
- The registered node-[158] predicate is the exact cardinal branch test. This report does not call that branch nonexhaustive; it flags only the manuscript's simultaneous semantic wording and supplies the supported cardinal wording as the repair.

The principal search was

```text
rg -n 'def:window-realization-test|dense-packing residual|densePackingOverflow|windowPackageUnrealized|WindowPackageRealized|word for word|same proof|analog' \
  to_formalize/erdos_64_proof.tex hypostructure proofs \
  Assembly_node_audit.md web/data/eg_node_audit.json
```

No “word for word,” “same proof,” or analogous manuscript use was found that independently transfers the [159] inference. The only material downstream use of its strict cardinal conclusion found by this search is the additive blocked-class compression at [171]; the deficiency decision [160] is arithmetically independent of the realization predicate.

## 8. Residual uncertainty

No actual minimal-counterexample graph realizing the range-collapse candidate was found, so this report does not assert that case C is graph-realizable. The manuscript does not specify a concrete canonical graph-to-package-state map in `def:window-realization-test`, leaving unresolved whether “assignment of target-complete states” was intended semantically or merely as shorthand for the cardinal inequality. The live Lean proof validates only the latter because its state type and map are unconstrained by target-completeness. The finite \(o(1)\) package loss and the pointwise meaning of the diagram's abbreviated \(\theta>\theta_{\rm win}\) were inspected only to the extent needed for this node; no new finite-\(n\) threshold was derived. No manuscript, diagram, Lean, implementation-audit, or coverage-ledger source was changed.
