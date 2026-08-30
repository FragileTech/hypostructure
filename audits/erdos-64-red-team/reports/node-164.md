<!-- red-team-audit
{
  "schema_version": 1,
  "proof": "erdos-gyarfas",
  "node": 164,
  "node_label": "all-cold comparison closes: \\(|\\mathcal G(R)|\\le|\\mathcal G_{n,m}|\\) by the remainder glue",
  "panel": "fig:proof-diagram-part-xii",
  "contract_sha256": "9cbf530cc461b7c6a07c8055a1d901893050c8b694c32c2a495541b4a0f1473c",
  "manuscript_sha256": "106a8205a1718fbf90e1686a107b2143b9edca574e2b0c11415e7f44aee2c0f9",
  "graph_sha256": "dc67fae178f947a9607c167e383d85919633341bdd423e4c4a45e4c317b3a765",
  "lean_audit_sha256": "50324ef5594d635a52d83aeb297f2ca3f3d30ef58de4ce3602816c7e78365b12",
  "verdict": "PROSE AMBIGUITY",
  "audited_at": "2026-08-24T21:15:51Z"
}
-->

# Red-team audit: node [164]

## 1. Executive verdict

Verdict: **PROSE AMBIGUITY**

The remainder-glue injection at node [164] is correct for the intended exact-edge class: retaining $e(H)=e(G[R])$ makes the glued graph an $n$-vertex, $m$-edge labelled skeleton, and its internal edges recover $H$. The ambiguity is that 'def:remainder-entropy', whose cardinality node [53] used, explicitly lists only subcubicity, $P_{13}$-freeness, absence of an internal $3$-core, and a deficiency cap. Its next sentence says only that candidates share the inherited vertex set, which does not fix their edge count or net-deficiency numerator. Node [164] then silently reads the same notation with an additional exact-edge constraint. Thus the intended closure is valid, but the manuscript must say that $\mathcal G(R)$ was the fixed-edge slice all along; otherwise the injection bounds a smaller class than the one counted at [53].

## 2. Exact node contract

### Incoming residual

The sole incoming edge is '[162] -- [53] active --> [164]'; node [164] is terminal and lies in no loop or strongly connected component. Work with the selected lexicographically minimal finite simple counterexample $G$, its fixed order $n$ and size $m$, and the deterministic maximal packing $\mathcal P$ of vertex-disjoint induced $P_{13}$'s. Put

\[
R=G-\bigcup_{P\in\mathcal P}V(P).
\]

The selected edge retains the hot/cold partition with
$\mathcal P_{\rm hot}=\varnothing$, the fixed remainder support $V(R)$, the fixed outer edge set (including every window--remainder incidence), and node [53]'s strict active comparison. On this all-cold arm the window factor is $1$, so the joint demand is exactly the cardinality denoted by $|\mathcal G(R)|$, and the active predicate is

\[
|\mathcal G_{n,m}|<|\mathcal G(R)|.
\tag{164-active}
\]

The intended incoming domain also retains the inherited internal edge count $m_R=e(G[R])$. Whether that equality is part of the earlier definition of $\mathcal G(R)$, rather than a new restriction introduced only in the closing lemma, is the ambiguity under audit.

### Accumulated facts

1. Nodes [1]--[6]: $G$ is a selected finite simple counterexample of minimum degree at least three, with no power-of-two cycle and the equivalent oriented-edge return-avoidance data.
2. Nodes [8]--[14]: $G$ has no proper internal $3$-core, every edge touches a degree-three vertex, high-degree vertices are independent, and the degree-profile, context-universality, replacement, and hereditary-uncompressibility ledgers are retained.
3. Nodes [15], [17], and [18]: $\mathcal P$ is the fixed maximal induced-$P_{13}$ packing; each component of $R$ is induced-$P_{13}$-free and has no internal $3$-core; the $399$-label window algebra is retained.
4. The no-arm of [19] and node [21]: the near-cubic surplus estimate, deterministic auxiliary choices, separated window package, and labelled skeleton budget are fixed on the same graph. In particular $\mathcal G_{n,m}$ is the set of all labelled simple graphs on the fixed $n$-vertex set with exactly $m$ edges.
5. Nodes [158]--[160]: the package-realization test failed, giving the dense residual, and the exact deficiency comparison took its complementary arm into the hot/cold pass.
6. The selected subarm of [162] retains $\mathcal P_{\rm hot}=\varnothing$, the exact [53] active fact (164-active), and no nonempty retained hot code.
7. The earlier remainder normalization supplies a branch-local vertex set, boundaried-piece part, window-freeness, empty internal $3$-core, and the current deficiency cap. The original graph also determines $m_R=e(G[R])$ and the outer edge set, so an exact-edge slice is available as accumulated data even though 'def:remainder-entropy' does not clearly include it in the quantified class.
8. For every simple graph $H$ on $V(R)$, the identity
   \[
   \defp(H)-\sigma(H)=3|R|-2e(H)
   \]
   shows that, after fixing $V(R)$, equality of the net-deficiency numerator is equivalent to equality of the edge count. Fixing the vertex set alone is not sufficient.

### Current predicate and exact claim

The intended class is

\[
\mathcal G_{m_R}(R)=\left\{H\text{ labelled on }V(R):
\begin{array}{l}
H\text{ satisfies the branch's remainder constraints},\\
e(H)=m_R
\end{array}\right\}.
\]

With the outer edge set $E_{\rm out}=E(G)\setminus E(G[R])$ fixed, define

\[
\Phi(H)=G[R:=H],\qquad
E(\Phi(H))=E_{\rm out}\cup E(H).
\]

The exact local claim is that $\Phi$ maps $\mathcal G_{m_R}(R)$ injectively into $\mathcal G_{n,m}$. It follows that

\[
|\mathcal G_{m_R}(R)|\le |\mathcal G_{n,m}|,
\]

contradicting (164-active), provided the $\mathcal G(R)$ counted by [53] is exactly $\mathcal G_{m_R}(R)$.

The literal earlier definition does not establish that proviso. It lists an upper deficiency cap, which permits multiple edge strata, and then attributes numerator equivalence to the common vertex set. The later phrase “read with its glue constraints” adds the missing equality but does not explain why the cardinality in [53] already referred to the narrowed class.

### Outgoing contracts

There are no outgoing edges. Node [164] must close the selected residual by producing the non-strict opposite

\[
|\mathcal G(R)|\le |\mathcal G_{n,m}|
\]

to [53]'s strict active fact. No target-avoidance or minimum-degree condition is required of the glued skeletons: the codomain is the full labelled $(n,m)$ skeleton class. The only landing conditions needed are simplicity, the fixed vertex set, and the fixed total edge count. The first two are automatic from the construction; the third is precisely why the exact internal edge-count constraint cannot be omitted.

## 3. Sentence audit

| Sentence | Exact assertion | Facts used | Hidden obligation | Adversarial test | Status |
|---|---|---|---|---|---|
| S1 | On the selected all-cold arm, node [53]'s joint demand reduces to $|\mathcal G(R)|$. | $\mathcal P_{\rm hot}=\varnothing$; definition of the joint package demand. | The obstruction/curvature coordinate must not be multiplied a second time. | Expand the empty-family factor and inspect 'jointPackageDemand'. | SUPPORTED |
| S2 | 'def:remainder-entropy' defines the same class later used by the glue lemma. | Branch-locality sentence; “read with its glue constraints.” | Its quantified candidates must already have $e(H)=e(G[R])$. | Put two different-edge graphs on the same inherited vertex set under the same upper cap. | AMBIGUOUS |
| S3 | A common inherited vertex set makes density comparison equivalent to comparison with the inherited numerator. | Fixed $V(R)$. | Fixed vertices do not fix $3|R|-2e(H)$; exact edges are additionally needed. | Compare $P_5$ and $C_5$. | FAILED AS WRITTEN |
| S4 | Every intended candidate glues to an element of $\mathcal G_{n,m}$. | Fixed outer edges; $e(H)=e(G[R])$; simplicity. | Outer and inner edge sets must be disjoint, with no loops or duplicate edges. | Filter edges by whether both ends lie in $V(R)$. | SUPPORTED |
| S5 | The glue map is injective. | Fixed support and outer edges. | Equality of glued graphs must recover the labelled internal edge set, not merely an isomorphism type. | Intersect the common labelled edge set with $\binom{V(R)}2$. | SUPPORTED |
| S6 | The all-cold obstruction sharpening is not an additional independent multiplicative factor. | Definition of the all-cold joint demand; `rem:closure-robust`; remainder states already realize the patterns. | The [53] predicate must be the same exact demand used in the closing row. | Compare `retainedCode` with `jointPackageDemand` and set the hot family empty. | SUPPORTED |
| S7 | The injection contradicts [53] active and terminates the branch. | S1, S4, S5; strict/non-strict complementary inequalities. | Domain identity from S2 is required. | Let [53] count a union of edge strata while the glue bounds only one stratum. | SUPPORTED ONLY UNDER THE INTENDED EXACT-EDGE READING |

## 4. Counterexample attempts

### Smallest-parameter test

- **Explicit data:** Take a one-vertex remainder support and inherited internal edge count $m_R=0$. The exact-edge remainder class has at most the single edgeless labelled graph, while the original graph itself witnesses that the fixed $\mathcal G_{n,m}$ skeleton class is nonempty.
- **Hypotheses satisfied:** Fixed vertex support, exact inherited edge count, simplicity, window-freeness, absence of an internal $3$-core, and every nonnegative deficiency cap admitting the candidate.
- **Accumulated facts violated:** The strict active comparison would require a nonempty one-element demand to exceed a nonempty skeleton class.
- **Applicability:** **NON-APPLICABLE TO THE NODE.** The earliest excluding predicate is `[53] active` on the incoming edge from [162]. This test confirms that no empty/singleton convention reverses the terminal inequality.

### Parity or 2-adic test

- **Explicit data:** Let $V(R)=\{1,2,3,4,5\}$, let $H=P_5$, take threshold $3$, edge count $m_R=4$, and deficiency cap $7$. Then $e(H)=4$ and
  \[
  \defp(H)-\sigma(H)=3\cdot5-2\cdot4=7,
  \]
  which is odd.
- **Hypotheses satisfied:** $P_5$ is subcubic, induced-$P_{13}$-free, has no internal $3$-core, meets the cap at equality, and lies in the exact edge-count slice. The glue still has exactly $m$ edges.
- **Accumulated facts violated:** No local glue hypothesis. This does not construct the complete ambient minimal counterexample or the [53] active inequality.
- **Applicability:** Applicable to the set-theoretic injection and it does not break it. The parity identity is integral and no division or orbit-lifting step occurs. The modular-orbit checker is therefore not relevant to this node.

### Boundary or range test

- **Explicit data:** Use the same $P_5$ with deficiency cap exactly $7$, so the upper-cap constraint is attained. Separately take the comparison boundary $D=B$, where $D=|\mathcal G_{m_R}(R)|$ and $B=|\mathcal G_{n,m}|$.
- **Hypotheses satisfied:** Equality at the deficiency cap is allowed by “at most,” and the glue proof uses no strictness there. Equality $D=B$ satisfies the injection's conclusion.
- **Accumulated facts violated:** The comparison boundary $D=B$ violates the strict [53] predicate $B<D$.
- **Applicability:** **NON-APPLICABLE TO THE NODE** as a surviving branch, first excluded by `[53] active`. It confirms that the terminal uses the correct strict/non-strict complement and has no endpoint gap.

### Graph-realizability test

- **Explicit data:** On the same five labelled vertices, take $H_0=P_5$ and $H_1=C_5$. At threshold $3$, $H_0$ has four edges and positive deficiency $7$, while $H_1$ has five edges and positive deficiency $5$. With cap $7$, both are subcubic, induced-$P_{13}$-free, have no internal $3$-core, and satisfy every constraint explicitly listed in 'def:remainder-entropy'.
- **Hypotheses satisfied:** Both candidates have the inherited vertex set and the four displayed prose constraints. They are actual labelled simple graphs, not abstract response records.
- **Accumulated facts violated:** If $e(G[R])=4$, then $H_1$ violates the intended inherited-edge constraint and its glue has $m+1$ edges. That constraint appears in 'lem:remainder-glue-injection', but not clearly in the earlier quantified definition whose cardinality [53] consumed.
- **Applicability:** Under the intended glue contract, **NON-APPLICABLE TO THE NODE**; the earliest excluding clause is node [164]'s requirement $e(H)=e(G[R])$. Under the literal four-clause reading of 'def:remainder-entropy', however, $H_1$ is applicable and proves that the proposed map from that larger class does not land in $\mathcal G_{n,m}$. This is the report's strongest ambiguity witness.

### Branch-routing test

- **Explicit data:** Take a hot/cold partition with one retained hot window, so $\mathcal P_{\rm hot}\ne\varnothing$, and suppose a joint package comparison is active.
- **Hypotheses satisfied:** Such data can belong to the ordinary retained-family entropy comparison, whose demand includes a nontrivial window factor.
- **Accumulated facts violated:** The incoming edge to [164] retains $\mathcal P_{\rm hot}=\varnothing$; a nonempty retained family belongs to the live-hot/ordinary [54] closure rather than the all-cold terminal.
- **Applicability:** **NON-APPLICABLE TO THE NODE.** The earliest excluding branch is `[162] -- [53] active --> [164]`, whose all-cold payload has empty hot family. On the actual edge, the demand reduces exactly to the remainder-state count and no outgoing residual remains after the bound.

## 5. Strongest valid counterexample

No graph satisfying the complete selected minimal-counterexample ledger and node [164]'s intended exact-edge incoming contract survives the glue injection. The strongest candidate is the pair $H_0=P_5$, $H_1=C_5$ on one labelled five-vertex support. It survives every constraint explicitly enumerated in 'def:remainder-entropy' under cap $7$, but its members occupy different edge strata. If the inherited remainder has four edges, gluing $C_5$ changes the global size from $m$ to $m+1$, so the literal larger class does not inject into the fixed $\mathcal G_{n,m}$ by the stated map. The candidate is excluded immediately once the intended equality $e(H)=e(G[R])$ is made part of the definition. It therefore demonstrates a quantifier/domain ambiguity, not a counterexample to the corrected node.

## 6. Local repair

### Corrected statement

For the fixed residual $R$ of the selected graph $G$, define $\mathcal G(R)$ to be the set of labelled simple graphs $H$ on the inherited vertex set $V(R)$ satisfying all retained remainder constraints and the exact equality

\[
e(H)=e(G[R]).
\]

Equivalently, because the vertex set is fixed, require

\[
\defp(H)-\sigma(H)
=3|R|-2e(H)
=3|R|-2e(G[R])
=\defp(G[R])-\sigma_R.
\]

The upper positive-deficiency or net-deficiency cap remains an additional constraint; it does not replace this equality. On the all-cold arm $\mathcal P_{\rm hot}=\varnothing$, the [53] joint demand is exactly this fixed-edge class's cardinality. The map $H\mapsto G[R:=H]$ injects it into $\mathcal G_{n,m}$, so [53] cannot be active.

### Complete local proof

Let $S=V(R)$, let $m_R=e(G[S])$, and let

\[
E_{\rm out}=\{e\in E(G):e\not\subseteq S\}.
\]

For $H\in\mathcal G(R)$, embed its labelled edge set into the fixed labels $S\subseteq V(G)$ and define

\[
E(\Phi(H))=E_{\rm out}\cup E(H).
\]

Every edge in $E_{\rm out}$ has an endpoint outside $S$, while every edge of $H$ has both endpoints in $S$; hence the two sets are disjoint. Both are loop-free, so their union is the edge set of a labelled simple graph on $V(G)$. Moreover

\[
|E_{\rm out}|=m-m_R,
\qquad
e(H)=m_R,
\]

and therefore $e(\Phi(H))=m$. Thus $\Phi(H)\in\mathcal G_{n,m}$.

If $\Phi(H_1)=\Phi(H_2)$, filter their common labelled edge set to the pairs whose two endpoints lie in $S$. The outer edges disappear and the filter returns exactly $E(H_i)$, so $E(H_1)=E(H_2)$. Labelled simple graphs are determined by their edge sets, hence $H_1=H_2$. Therefore $\Phi$ is injective and

\[
|\mathcal G(R)|\le|\mathcal G_{n,m}|.
\]

Since $\mathcal P_{\rm hot}=\varnothing$, the window term in the joint demand is $2^0=1$, so the [53] demand equals $|\mathcal G(R)|$. The displayed inequality contradicts the retained strict inequality $|\mathcal G_{n,m}|<|\mathcal G(R)|$, closing node [164]. No extra curvature factor is required: the current [53] demand counts that sharpening within the remainder-state coordinate rather than as an independent multiplier.

### Counterexample disposition

The $P_5/C_5$ pair is separated by the repaired exact-edge clause: only the member with $e(H)=m_R$ is counted. The cap-equality and odd-numerator tests remain in the class and glue correctly. A nonempty hot family is routed away at [162], while equality of the demand and budget is excluded by [53]'s strict active arm. Hence every attempted residual is either outside the repaired incoming predicate or contradicted by the injection.

### Graph patch

No new proof-flow edge is needed. Retain the terminal shape and clarify the sole incoming edge as

```text
[162] -- P_hot = empty; [53] active for the exact inherited-edge
         remainder class G_{e(G[R])}(R) --> [164]
[164] -- inject H |-> G[R:=H] into G_{n,m} --> closed
```

The box label may continue to state $|\mathcal G(R)|\le|\mathcal G_{n,m}|$, provided the exact-edge meaning of $\mathcal G(R)$ has been fixed at [49].

### Downstream impact

The smallest source repair is in 'def:remainder-entropy': add $e(H)=e(G[R])$ to its displayed list and replace the claim that a common vertex set alone fixes the numerator with the identity $3|R|-2e(H)$. The statement of 'lem:remainder-glue-injection', node [164], its diagram edge, the dependency row, and 'rem:dense-residual-status' then become literal consumers of the same class rather than later reinterpretations.

Every earlier high-/low-entropy use of $|\mathcal G(R)|$, especially 'prop:two-budget' and nodes [49]--[53], should be checked under the fixed-edge definition. This is the intended formal reading already implemented by 'RemainderClass', 'remainderStates', and 'remainderStateCount_le_skeletonBudget', so no Lean proof change is indicated by this local repair. A separate fidelity detail remains: Lean bounds the degree of every remainder vertex, whereas the manuscript says subcubicity only on the boundaried-piece part. That difference does not affect the glue injection, but the two classes should be aligned before treating their cardinalities as interchangeable throughout the entropy branch.

## 7. Regression audit

The audit inspected the following repeated uses and consumers:

- The Part XII diagram, its caption and summary, the incoming `[53] active` edge, the terminal node [164], the detailed dependency row for `def:all-cold-comparison`/`lem:remainder-glue-injection`, and `rem:dense-residual-status`.
- The full statements and proofs of `def:all-cold-comparison`, `lem:remainder-glue-injection`, `def:remainder-entropy`, `lem:skeleton-dominates`, `prop:two-budget`, `prop:entropy-high-theta`, and `rem:closure-robust`.
- The explicit glue is accepted; the remaining question is whether its exact-edge domain is the class counted by the live entropy definition.
- `Graph/RemainderEntropy.lean`: all five conjuncts of `RemainderClass`, the exact `edgeCount` parameter, `remainderStateCount`, and the integer entropy-rate predicates.
- `Graph/RemainderGlue.lean`: the labelled embeddings, outer/inner edge split, disjointness, loop-freeness, edge-count preservation, recovery by filtering, `glue_injective`, and `remainderStateCount_le_skeletonBudget`.
- `Strategy/SpineVocabulary.lean`: `remainderStates`, `retainedCode`, `jointPackageDemand`, `IsHotColdWindowPartition`, and the exact `entropyCapActive`/`entropyCapBound` predicates. The formal remainder count receives the object's inherited internal edge count.
- `Strategy/EntropyClosure.lean`: `entropyCapBoundRow`, including both its retained-family arm and its all-cold arm. The all-cold simplification removes the window factor and invokes the real remainder-glue theorem.
- The dense branch of `Assembly.lean`: the [53] decision and the unified sealed closing row are wired, although the all-cold case is an internal case of the row rather than a separately named node-[164] producer.
- `Assembly_node_audit.md` and `web/data/eg_node_audit.json` were used only as locators. Their recorded unresolved clause-by-clause comparison agrees with the present source check but was not treated as proof authority.

The principal searches were

```text
rg -n 'def:all-cold-comparison|lem:remainder-glue-injection|def:remainder-entropy|inherited edge count|inherited net-deficiency' to_formalize/erdos_64_proof.tex
rg -n 'RemainderClass|remainderStateCount|glue_injective|remainderStateCount_le_skeletonBudget' hypostructure proofs
rg -n 'jointPackageDemand|retainedCode|entropyCapBoundRow|entropyCapActive|allCold' hypostructure proofs
rg -n 'word for word|same proof|analog' to_formalize/erdos_64_proof.tex hypostructure proofs
```

No second manuscript definition explicitly adding the exact-edge equality before node [53] was found. No alternate outgoing route from [164], no second glue map with a larger domain, and no modular/divisibility inference used by this terminal were found. Occurrences of “analog” were unrelated API descriptions; no “word for word” or “same proof” shortcut supplies the missing domain equality.

## 8. Residual uncertainty

No complete minimum-degree-three, power-of-two-cycle-free graph realizing every incoming node-[164] fact was constructed; the $P_5/C_5$ pair is a concrete countermodel to the literal class identification, not to the corrected terminal. It remains possible that “constraints already imposed on the branch” was intended to include exact edge count despite its omission from the explicit list, but the following sentence's appeal to the common vertex set is mathematically insufficient to communicate that intent. Clause-by-clause manuscript/Lean fidelity also remains unresolved for “subcubicity on the boundaried-piece part” versus Lean's all-vertex degree bound and for the manuscript's terminology around positive versus net deficiency. These do not damage the fixed-edge glue theorem itself, but they can change the cardinality used earlier in the entropy split. This audit conditions on the selected all-cold '[53] active' payload from [162] and does not certify the production of that predecessor residual. No manuscript, diagram, Lean, implementation-audit, or coverage-ledger source was changed.
