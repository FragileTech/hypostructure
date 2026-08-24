<!-- red-team-audit
{
  "schema_version": 1,
  "proof": "erdos-gyarfas",
  "node": 167,
  "node_label": "symmetric strand pair: finite two-strand check on the closing lengths \\(2\\ell\\), \\(\\ell+d\\)",
  "panel": "fig:proof-diagram-part-xii",
  "contract_sha256": "96046c41db45058985b08785661063b41d318e3521ce83d9372b3ea5d53ed549",
  "manuscript_sha256": "106a8205a1718fbf90e1686a107b2143b9edca574e2b0c11415e7f44aee2c0f9",
  "graph_sha256": "dc67fae178f947a9607c167e383d85919633341bdd423e4c4a45e4c317b3a765",
  "lean_audit_sha256": "50324ef5594d635a52d83aeb297f2ca3f3d30ef58de4ce3602816c7e78365b12",
  "verdict": "PROSE AMBIGUITY",
  "audited_at": "2026-08-24T21:23:35Z"
}
-->

# Red-team audit: node [167]

## 1. Executive verdict

Verdict: **PROSE AMBIGUITY**

The two actual closing lengths at node [167] are correctly identified as $2\ell$ and $\ell+d$, and the displayed closed/survives edges are exhaustive when they retain the literal predicate
$2\ell\in\Pow\lor\ell+d\in\Pow$ and its negation. The stated survivor characterization is nevertheless false as written: the manuscript defines $\Pow=\{2^k:k\ge2\}=\{4,8,\ldots\}$, so $\ell=2$ satisfies $\ell\notin\Pow$ although $2\ell=4\in\Pow$. Thus $(\ell,d)=(2,12)$ meets the written survivor formula but is closed by its $4$-cycle. The immediately preceding criterion, the following excluded-length list, and the executable `DyadicallyClosed` filter all support the intended correction $2\ell\notin\Pow$ (equivalently, $\ell$ is not a positive power of two). This is a locally repairable notation error, not an uncaught residual or a counterexample to the corrected node.

## 2. Exact node contract

### Incoming residual

The sole incoming edge is `[163] -- yes --> [167]`. Work with the selected finite simple lexicographically minimal counterexample $G$: it has minimum degree at least three, no cycle whose length lies in $\Pow$, and the equivalent Mersenne-return avoidance. The no-arm of [158] supplies the dense-packing residual; the complementary arm of [160] has $\tau(\theta)\ge1/4$; and [162] has run the hot/cold and first-failure pass on that same residual.

The selected [163] arm carries a terminal (F5), neutral, equal-length cold bounded configuration. Its same-interface representatives $Q$ and $E$ have common length $\ell$, preserve the retained boundary-degree and target-response data, and the selected predicate says that $E$ is graph-realized as a genuine second strand rather than merely a canonical replacement piece. Consequently $Q$ and $E$ are simple outside strands with the same two window attachment vertices, equal length, and disjoint interiors. The attachment-coordinate distance along the induced $P_{13}$ window is $d$, with $0\le d\le12$ in the arithmetic table. On the genuine two-attachment realization used by the typed Lean vocabulary, the attachment vertices are distinct, hence $d>0$; node [168] is allowed also to discuss a one-endpoint self-return convention.

The cold branch is built from ambient-cubic packed windows and selected branch-excess incidences. This fact, rather than an arbitrary numerical configuration, is retained for the `survives` handoff to [168].

### Accumulated facts

1. Nodes [1]--[6]: $G$ is finite and simple, has minimum degree at least three, has no $\Pow$-cycle, and has no oriented-edge Mersenne return.
2. Nodes [8]--[14]: no proper subgraph has minimum degree three; the edge-criticality, independent high-degree set, boundary-profile, context-universality, replacement, and hereditary-uncompressibility facts remain available.
3. Nodes [15], [17], [18], and [21]: the deterministic maximal induced-$P_{13}$ packing, its window coordinates $0,\ldots,12$, the exact label algebra, and the finite window package are fixed.
4. Nodes [158]--[162]: the selected branch is the dense package-unrealized residual, it failed the strict $\tau<1/4$ test, and its hot/cold pass leaves the neutral terminal-configuration arm.
5. `def:cold-corridor-first-failure`, `def:cold-bounded-germ`, and the [157] neutral row retain a bounded terminal corridor, two boundary interfaces, the actual return-corridor strand $Q$, a same-interface equal-length representative $E$, and exact target-response equivalence.
6. The yes-arm of [163], `lem:neutral-germ-symmetry`, says that $E$ is an actual second strand of $G$. Thus the pair-cycle and the two strand/window cycles are graph-realized, not merely numerical response codes.
7. The target set is literally $\Pow=\{4,8,16,\ldots\}$. In particular $2\notin\Pow$, while $4\in\Pow$.
8. No ancestor gives the numerical upper bound $\ell\le40$: the cold first-failure bound is the unrelated constant $M_{\rm cold}=Q_{\rm cold}+30$. The first closure criterion is uniform in $\ell$, and the `survives` edge handles every complement, so the finite census is not allowed to become an implicit range restriction on routing.

### Current predicate and exact claim

Let $W_{ab}$ be the unique window subpath between the attachment vertices, of length $d$. The exact local implication is

\[
\begin{aligned}
&Q,E\text{ internally disjoint outside }a,b,\quad
|Q|=|E|=\ell,\quad |W_{ab}|=d \\
&\qquad\Longrightarrow
|Q\cup E|=2\ell,
\qquad |Q\cup W_{ab}|=|E\cup W_{ab}|=\ell+d.
\end{aligned}
\]

Therefore the decision predicate is

\[
P(\ell,d):=(2\ell\in\Pow)\lor(\ell+d\in\Pow).
\]

If $P(\ell,d)$ holds, one of these simple cycles is a target cycle and the branch goes to [155]. If it does not hold, the exact retained predicate is

\[
\neg P(\ell,d)
\iff 2\ell\notin\Pow\ \land\ \ell+d\notin\Pow,
\tag{167-survives}
\]

and the pair goes to [168]. Since $\Pow$ begins at $4$, the first conjunct is equivalent to

\[
\ell\notin\{2,4,8,16,\ldots\},
\]

not to $\ell\notin\Pow$.

For the formal arithmetic grid $0\le\ell\le40$, $0\le d\le12$, there are $41\cdot13=533$ configurations. Exactly $96$ satisfy $P$: $65$ have $\ell\in\{2,4,8,16,32\}$, and another $3+6+10+12=31$ have $\ell+d\in\{4,8,16,32\}$ without one of those five strand lengths. The survivor-length projection is consequently every length in $\{0,\ldots,40\}$ except $2,4,8,16,32$. The grid includes degenerate numerical lengths $0,1$; actual two-stub strands form a restricted, conservatively covered subfamily.

### Outgoing contracts

- `[167] -- closed --> [155]` retains the actual pair and the witness $2\ell\in\Pow\lor\ell+d\in\Pow$. The union of the corresponding simple paths supplies a $\Pow$-cycle in $G$, exactly the G1/[155] entry fact.
- `[167] -- survives --> [168]` must retain the literal complement (167-survives), the genuine pair, the ambient-cubic induced window, its attachment vertices, and the selected cold-incidence provenance. Node [168] then uses the two-distinct-stubs requirement to put a genuine pair at window endpoints and reruns the selection on interior stubs, retaining $9$ branch-excess units per window. Its entry argument is independent of the upper bound $\ell\le40$.

These predicates are complements. Replacing $2\ell\notin\Pow$ by the manuscript's $\ell\notin\Pow$ weakens the `survives` contract exactly at $\ell=2$.

## 3. Sentence audit

| Sentence | Exact assertion | Facts used | Hidden obligation | Adversarial test | Status |
|---|---|---|---|---|---|
| S1 | A symmetric pair consists of two internally disjoint outside strands of common edge length $\ell$ between window coordinates at distance $d$. | [163] yes-arm; neutral equal-length terminal configuration. | “Outside” must make the strand interiors disjoint from the window subpath, and both attachment stubs are included in $\ell$. | Try $\ell=0,1$ from the numerical list. | SUPPORTED for graph-realized strands; numerical census is broader |
| S2 | The pair support has cycles of lengths $2\ell$ and $\ell+d$. | S1; induced window gives a unique $a$--$b$ subpath. | The unions must be simple cycles, not closed walks. | Explicit theta support with two outside paths and the window path. | SUPPORTED |
| S3 | These are “exactly” all cycles in the bounded support. | S1; intended union-subgraph convention. | If “support” means an induced ambient support, cross-edges or chords must be excluded. | Add an ambient cross-edge between strand interiors. | AMBIGUOUS BUT INESSENTIAL; existence of the named cycles is sufficient |
| S4 | If $2\ell\in\Pow$ or $\ell+d\in\Pow$, the pair is a power-of-two hit and routes to [155]. | S2; target definition. | The numerical length must be realized by a simple cycle in $G$. | $(\ell,d)=(6,2)$ gives lengths $12$ and $8$. | SUPPORTED |
| S5 | Every $\ell\in\{2,4,8,16,\ldots\}$ closes through the pair cycle. | S2; $2\cdot2^j=2^{j+1}\in\Pow$ for $j\ge1$. | The list starts at $2$, one dyadic step below the target set. | $\ell=2$ gives the first target length $4$. | SUPPORTED |
| S6 | The arithmetic grid at order $13$ and bound $40$ has $533$ configurations and $96$ closed ones. | Definition of `configurations`/`DyadicallyClosed`; exact finite count. | Clarify that the grid includes numerical $\ell=0,1$ and all $d=0,\ldots,12$, not only graph-realizable pairs. | Direct enumeration and disjoint count $65+31$. | SUPPORTED AS AN ARITHMETIC CENSUS |
| S7 | Survivors are exactly $\ell\notin\Pow$ and $\ell+d\notin\Pow$. | Intended negation of S4. | Negation must retain $2\ell$, not replace it by membership of $\ell$ in a set beginning at $4$. | $(\ell,d)=(2,12)$ satisfies the written formula but has pair-cycle length $4$. | FAILED AS WRITTEN |
| S8 | Survivor lengths in the finite grid are all lengths except $2,4,8,16,32$. | Exact filter; projection to the $\ell$ coordinate. | “All lengths” is scoped to $0\le\ell\le40$. | Compute the projection of all $437$ survivors. | SUPPORTED and confirms the intended correction to S7 |
| P1 | Internal disjointness gives the $2\ell$ pair cycle and two $\ell+d$ strand/window cycles. | S1; elementary path union. | Common endpoints must be the only shared vertices. | Realize a theta graph with branch lengths $\ell,\ell,d$. | SUPPORTED |
| P2 | The target predicate gives the closing criterion. | P1; $\Pow$ convention. | Both alternatives and their literal complement must be retained. | Compare $P(2,12)$ with the written survivor shorthand. | SUPPORTED for the criterion; shorthand fails |
| P3 | The claimed enumeration is over $\ell\le40$, $0\le d\le12$. | `survivors 13 40`; list ranges. | The finite range must not silently exclude longer incoming strands. | $(\ell,d)=(41,12)$. | SUPPORTED as a scoped census; routing remains uniform |

## 4. Counterexample attempts

### Smallest-parameter test

- **Explicit data:** The executable grid begins with $(\ell,d)=(0,0)$. Its closing lengths are $0$ and $0$, so it survives the numerical predicate.
- **Hypotheses satisfied:** It satisfies $0\le\ell\le40$ and $0\le d\le12$ and is genuinely present in `configurations 13 40`.
- **Accumulated facts violated:** It is not an outside strand with both attachment stubs included; any such graph-realized strand has at least two edges. It also cannot be the genuine return-corridor/second-strand pair selected at [163].
- **Applicability:** **NON-APPLICABLE TO THE NODE.** The earliest excluding selected fact is the `[163] yes` genuine-second-strand payload, made explicit by the first premise of `lem:two-strand-check`. The test shows that $533$ is a count of an arithmetic superset rather than the exact number of graph-realizable pairs.

### Parity or 2-adic test

- **Explicit data:** Take $(\ell,d)=(6,2)$. Then $2\ell=12\notin\Pow$ but $\ell+d=8\in\Pow$. Also, in general, $2\ell\in\Pow$ iff $\ell=2^j$ for some $j\ge1$; multiplying by two lowers the allowed exponent threshold on $\ell$ from $2$ to $1$.
- **Hypotheses satisfied:** The parameters are inside the finite grid and can be realized by two equal internally disjoint paths between window coordinates at distance two.
- **Accumulated facts violated:** Such a realized pair in $G$ would contain an $8$-cycle and hence violate target avoidance from [2]/[5].
- **Applicability:** **NON-APPLICABLE TO THE ACTUAL RESIDUAL**, first excluded by node [2]'s no-$\Pow$-cycle predicate. It is correctly sent to [155]. The separate factor-two calculation exposes the only lost 2-adic endpoint: $\ell=2$ is below $\Pow$ but $2\ell$ is in $\Pow$.

### Boundary or range test

- **Explicit data:** At the stated boundary, $(\ell,d)=(40,12)$ has closing lengths $80$ and $52$, so it survives. Just outside the census, $(41,12)$ has closing lengths $82$ and $53$, so it also survives the exact predicate.
- **Hypotheses satisfied:** Both have a valid window gap $d=12$ and satisfy the uniform two-strand arithmetic. The first lies in `configurations 13 40`; the second deliberately does not.
- **Accumulated facts violated:** No local closing-length fact is violated. The manuscript does not derive $\ell\le40$ from $M_{\rm cold}=Q_{\rm cold}+30$, and no full ambient minimal counterexample realizing the length-$41$ pair is supplied here.
- **Applicability:** The length-$40$ case is an applicable finite survivor. A graph-realized length-$41$ case would be outside the census but still goes through the displayed `survives` edge to [168]. Thus the boundary does not produce an unassigned residual; it confirms that the finite count must remain descriptive rather than serve as the routing domain.

### Graph-realizability test

- **Explicit data:** Let $W=v_0\cdots v_{12}$ be an induced $P_{13}$, and add two internally vertex-disjoint outside paths $v_0-a_1-a_2-v_{12}$ and $v_0-b_1-b_2-v_{12}$. Add one external stub at each interior window vertex so that the window has the ambient-cubic local stub pattern. Here $(\ell,d)=(3,12)$, and the named cycles have lengths $6$ and $15$.
- **Hypotheses satisfied:** The graph is simple on the displayed support; the outside strand interiors are disjoint from one another and from $W$; both attachment vertices are window endpoints; and neither named cycle length lies in $\Pow$.
- **Accumulated facts violated:** The displayed support alone does not complete every outside stub or strand-internal degree to a finite minimum-degree-three graph, nor does it establish global target avoidance, minimality, the dense entropy predicates, or the canonical first-failure selection.
- **Applicability:** It is a graph-local realization of the `survives` handoff, not a complete actual-residual candidate. Even if such a pair occurred in the full residual, [168]'s endpoint/interior-stub argument is exactly its destination, so it does not falsify node [167].

### Branch-routing test

- **Explicit data:** Realize $(\ell,d)=(2,12)$ by the induced window $v_0\cdots v_{12}$ and two outside paths $v_0-a-v_{12}$ and $v_0-b-v_{12}$. The strand/window cycles have length $14$, while the pair cycle $v_0av_{12}bv_0$ has length $4$.
- **Hypotheses satisfied:** This is a simple symmetric pair with equal length, internally disjoint outside strands, endpoint attachments, a valid order-$13$ gap, and parameters inside the finite table. It satisfies the manuscript's written survivor shorthand because $2\notin\Pow$ and $14\notin\Pow$.
- **Accumulated facts violated:** Its $4$-cycle violates node [2]'s counterexample condition and node [5]'s return avoidance.
- **Applicability:** **NON-APPLICABLE TO THE ACTUAL RESIDUAL**, first excluded by [2]. It is nevertheless the decisive wording witness: the exact decision routes it `closed` to [155], whereas the printed survivor formula would also admit it to [168]. Replacing $\ell\notin\Pow$ by $2\ell\notin\Pow$ restores disjoint complementary arms.

## 5. Strongest valid counterexample

No candidate satisfies the complete minimal-counterexample residual and falsifies the corrected conclusion. The strongest local candidate is the explicit endpoint pair $(\ell,d)=(2,12)$. It satisfies every geometric premise of the two-strand lemma and the printed survivor formula, yet its two strands form a $4$-cycle. It is therefore a genuine counterexample to the literal survivor characterization, including the downstream shorthand at [168], but not to the node's intended decision: the immediately preceding $2\ell\in\Pow$ criterion routes it to [155], and the accumulated no-target fact means it cannot occur on the actual residual. This makes the finding a prose ambiguity with an unambiguous correction, not a valid local counterexample to the cumulative node.

## 6. Local repair

### Corrected statement

Let $Q$ and $E$ be two simple outside strands with common endpoints $a,b$ on a packed window, with interiors disjoint from each other and from the window, and with $|Q|=|E|=\ell$. Let $W_{ab}$ be the window subpath from $a$ to $b$ and put $d=|W_{ab}|$. Then $Q\cup E$ is a simple cycle of length $2\ell$, while $Q\cup W_{ab}$ and $E\cup W_{ab}$ are simple cycles of length $\ell+d$. Consequently the configuration routes to [155] when

\[
2\ell\in\Pow\quad\text{or}\quad\ell+d\in\Pow,
\]

and otherwise it routes to [168] carrying

\[
2\ell\notin\Pow\quad\text{and}\quad\ell+d\notin\Pow.
\]

Equivalently, the first survivor condition is
$\ell\notin\{2,4,8,16,\ldots\}$; it is not $\ell\notin\Pow$, because $\Pow$ starts at $4$. In the arithmetic census $0\le\ell\le40$, $0\le d\le12$, exactly $96$ of the $533$ numerical configurations close, and the survivor-length projection is $\{0,\ldots,40\}\setminus\{2,4,8,16,32\}$. Actual strands form the subfamily satisfying the graph-realizability restrictions, in particular $\ell\ge2$.

### Complete local proof

Because $Q$ and $E$ have the same distinct endpoints and disjoint interiors, traversing $Q$ from $a$ to $b$ and $E$ in reverse gives a simple cycle. Its edge sets are disjoint and each has $\ell$ edges, so its length is $2\ell$. Since each strand is outside the window except at $a,b$, adjoining the unique induced-window subpath $W_{ab}$ to either strand likewise gives a simple cycle of length $\ell+d$. No claim that these are all cycles of an induced ambient support is needed.

If either named length lies in $\Pow$, the corresponding simple cycle is a target cycle of $G$, which is the [155] contract. Otherwise De Morgan's law gives exactly (167-survives), which is the retained predicate for [168]. Finally,

\[
2\ell\in\Pow
\iff \exists k\ge2\ (2\ell=2^k)
\iff \exists j\ge1\ (\ell=2^j),
\]

so the excluded strand lengths begin with $2$.

For the finite count, the five pair-closed lengths $2,4,8,16,32$ contribute $5\cdot13=65$ configurations. Among the remaining lengths, segment closure at $4,8,16,32$ contributes respectively $3,6,10,12$ pairs: these are the possible $\ell$ in $[\max(0,p-12),p]$ after removing the pair-closed lengths. The sums are disjoint because $\ell+d$ has a unique value, so the total is $65+3+6+10+12=96$. If $\ell$ is not one of the five pair-closed lengths, $d=0$ already witnesses a surviving numerical configuration unless $\ell\in\Pow$; within $0\le\ell\le40$, those $\Pow$ values are already among the five. Hence the survivor-length projection is exactly the stated complement.

### Counterexample disposition

The $(2,12)$ candidate is caught by the repaired first arm because $2\ell=4\in\Pow$. The $(6,2)$ parity test is caught because $\ell+d=8\in\Pow$. The $(40,12)$ and possible $(41,12)$ cases satisfy the repaired complement and are routed to [168], so the census boundary does not strand them. The $(0,0)$ arithmetic configuration remains in the deliberately broad numerical list but is excluded from the graph-realized incoming domain by the two-stub strand premise.

### Graph patch

No new node or edge is required. The exact labels and retained payload should be

```text
[163] -- E is a genuine second strand; retain the ambient-cubic window,
         equal length ell, gap d, and selected cold-incidence provenance --> [167]
[167] -- 2 ell in Pow or ell+d in Pow; retain the realized simple cycle --> [155]
[167] -- 2 ell notin Pow and ell+d notin Pow; retain the genuine pair,
         ambient-cubic window, and selection provenance --> [168]
```

Node [168]'s endpoint-stub argument should consume the second literal predicate, not the weaker shorthand $\ell\notin\Pow$. The existing two outgoing edges remain exhaustive and disjoint.

### Downstream impact

The same correction is required in `lem:symmetric-pair-endpoint`, which repeats `($\ell\notin\Pow$, $\ell+d\notin\Pow$)`, and in the Assembly comment that calls the survivors `$\ell \notin Pow \land \ell+d \notin Pow$`. The Part XII box, dependency-table row, dense-residual summary, and node-[176] reference state only the two actual closing lengths or cite the lemma, so their mathematical wording remains valid once the lemma is corrected. The generated explorer JSON mirrors the manuscript and should be regenerated by its normal pipeline after a source repair.

`Graph/TwoStrandEnumeration.lean` defines survival correctly as the negation of `PowerOfTwoLength (length+gap) \lor PowerOfTwoLength (2*length)`, so its executable filter already rejects $\ell=2$. Its theorem `survives_length_not_powerOfTwo` proves only the weaker necessary condition $\ell\notin\Pow$; a faithful consumer should instead expose the exact two-closing-length equivalence and an instantiated theorem or checked count for `survivors 13 40`. The current node-[167] formalization remains absent: there is no live producer connecting `GenuineSecondStrandStatement` to a `TwoStrand.Configuration`, the `survivors 13 40` instantiation is not performed, and Assembly closes the arm through the unresolved `selectedGenuineSecondStrandCloses`. These are formalization gaps, separate from the paper's locally corrected mathematics.

## 7. Regression audit

The audit inspected:

- The Part XII node, both outgoing edges, caption, dense-residual summary row, detailed dependency rows for `lem:two-strand-check` and `lem:symmetric-pair-endpoint`, `rem:dense-residual-status`, and the node-[176] reuse.
- The complete statements and proofs of `def:cold-corridor-first-failure`, `def:cold-bounded-germ`, `lem:cold-germ-extraction`, `lem:cold-bounded-germ-trichotomy`, `def:cold-same-interface-table`, `lem:cold-same-interface-table`, `lem:dense-cold-pass`, `def:neutral-equal-length-germ`, `lem:neutral-germ-symmetry`, `lem:two-strand-check`, and the [168] destination lemma.
- The global definition $\Pow=\{2^k:k\ge2\}$ and the target/return algebra on the selected minimal counterexample.
- `Core/DyadicLength.lean`, confirming that `PowerOfTwoLength` requires exponent at least two; `Graph/TwoStrandEnumeration.lean`, including both closing-length definitions, the survivor filter, the generic list theorems, `three_zero_survives`, and the weaker length theorem; and `Graph/WindowStubStructure.lean`, confirming the destination's endpoint/interior stub facts.
- `Strategy/SpineVocabulary.lean`, including `twoStrandEnumerationBound`, `GenuineSecondStrandConfiguration`, `GenuineSecondStrandStatement`, and the literal selected-object target predicate; `ColdCorridorRows.lean` for the [163] dichotomy and stub row; both node-[167] call sites in `Assembly.lean`; and the node/fidelity locators in `Assembly_node_audit.md` and `web/data/eg_node_audit.json`.

The principal searches and checks were

```text
rg -n -F '\Pow' to_formalize/erdos_64_proof.tex
rg -n -F 'survivors 13 40' .
rg -n -F 'ℓ ∉ Pow' proofs hypostructure Assembly_node_audit.md web/data/eg_node_audit.json
rg -n 'two-strand|two strand|symmetric strand|TwoStrandEnumeration' to_formalize/erdos_64_proof.tex proofs hypostructure Assembly_node_audit.md web/data/eg_node_audit.json
```

and an exact enumeration of all $(\ell,d)\in\{0,\ldots,40\}\times\{0,\ldots,12\}$ returned `total=533`, `closed=96`, `survivors=437`, with survivor lengths precisely the displayed complement. No other manuscript formula asserting the correct survivor predicate was found; the exact predicate exists only in the preceding closing criterion and the Lean definition. No modular-orbit, divisibility, integer-lift, or central-coefficient argument occurs at this node, so the modular checker is not applicable.

## 8. Residual uncertainty

No complete minimum-degree-three, target-free minimal counterexample realizing the local $(3,12)$ or $(41,12)$ support was constructed; those tests establish graph-local realization or range behavior, not survival of the entire incoming ledger. The phrase “no other cycle lies in the bounded support” is secure only if support means the three-path union rather than the induced ambient support, but the repair removes that unnecessary assertion. The manuscript also does not identify a derivation of $\ell\le40$ from the cold first-failure bound; this does not create a node-[167] range gap because the exact predicate and the [168] destination are uniform in $\ell$, but any future formal consumer of the finite list must not assume that bound without proof. Finally, the actual Lean node is absent and its Assembly consumer is unresolved, so this audit does not establish formal wiring or kernel-checked coverage. It conditions on the [163] genuine-second-strand payload and checks [168] only as the required outgoing contract; it does not certify either neighboring node independently. No manuscript, diagram, Lean, implementation-audit, or coverage-ledger source was changed.
