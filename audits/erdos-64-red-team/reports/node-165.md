<!-- red-team-audit
{
  "schema_version": 1,
  "proof": "erdos-gyarfas",
  "node": 165,
  "node_label": "canonical replacement \\(E\\ne Q\\): swap \\(Q\\to E\\) gives a same-size counterexample",
  "panel": "fig:proof-diagram-part-xii",
  "contract_sha256": "9622b4ebb004b014736d2968f66caf1dd8ee5fd69b4df4b1a58bb092c8fb2919",
  "manuscript_sha256": "106a8205a1718fbf90e1686a107b2143b9edca574e2b0c11415e7f44aee2c0f9",
  "graph_sha256": "dc67fae178f947a9607c167e383d85919633341bdd423e4c4a45e4c317b3a765",
  "lean_audit_sha256": "50324ef5594d635a52d83aeb297f2ca3f3d30ef58de4ce3602816c7e78365b12",
  "verdict": "MISSING REPRESENTATIVE",
  "audited_at": "2026-08-24T21:16:57Z"
}
-->

# Red-team audit: node [165]

## 1. Executive verdict

Verdict: **MISSING REPRESENTATIVE**

Even granting that the canonical exchange (Q\to E) preserves simplicity, minimum degree, target avoidance, vertex count, and edge count, the resulting counterexample (G') is only tied with (G) in the minimality order actually selected at node [4], namely ((|V|,|E|)). Node [165] introduces a third coordinate (Phi) locally, but (Phi) is not defined earlier as a fixed well-founded graph measure, the manuscript's named canonical support decomposition is a different decomposition into remainder components, and no stability lemma proves that recomputing the canonical packing/decomposition after the exchange changes exactly one cell. A labelled canonical graph code would suffice; isomorphism invariance is not required. What is missing is the fixed graph-level order and the proof that this swap strictly decreases it. The Lean source confirms the distinction: it closes only a strictly smaller-vertex case and leaves the actual same-size case without a producer.

## 2. Exact node contract

### Incoming residual

The unique incoming edge is the `no` arm `[163] -> [165]`; node [165] is not a merge and is not in a loop. The ambient object is the selected finite simple graph (G), minimal among counterexamples in the lexicographic order

\[
(|V(G)|,|E(G)|),
\]

with minimum degree at least (3) and no power-of-two cycle. The route also carries the fixed maximal induced-(P_{13}) packing, the near-cubic dense-packing residual, the exact no-arm of the deficiency comparison, and the cold-pass data that produced a neutral equal-length terminal configuration.

Write that configuration as an owned gluing

\[
G=Q\oplus_TY,
\]

where (Q) is the actual corridor piece on a proper connected bounded support and (E) is its second same-interface representative. The selected no-arm of [163] says that the second representative is not a genuine second strand embedded disjointly in (G); the intended `lem:neutral-germ-symmetry` route therefore treats (E) as the canonical replacement determined by the retained cut-state. On the nontrivial subcase audited at [165], (E\ne Q) as a canonical boundaried piece.

The equal-length and neutrality facts are route-specific: (Q) and (E) have the same size, boundary-degree profile, baseline behavior, and target response against every compatible outside context. In particular the actual context (Y) cannot distinguish them. These facts are not facts from the sibling genuine-strand arm [167].

### Accumulated facts

The complete state relevant to this node consists of:

1. Nodes [1]--[6]: (G) is a selected counterexample; every oriented edge satisfies the retained Mersenne-return avoidance condition.
2. Node [4] specifically selects only lexicographic ((|V|,|E|))-minimality. No third tie-break occurs in its statement, diagram label, dependency table, or formal progress relation.
3. Nodes [8]--[14]: no proper minimum-degree-three subgraph exists; edge deletion is critical; high-degree vertices are independent; the boundary-degree fibre and all-context target response are retained; and replacement can contradict minimality only after an actual candidate is strictly smaller in the selected order.
4. Nodes [15]--[21]: the fixed maximal induced-(P_{13}) packing, finite label algebra, near-cubic branch, skeleton bound, and certified window constants are retained.
5. Nodes [158]--[163]: the dense-package route, exact deficiency complement, dense cold pass, and the neutral equal-length terminal configuration are retained. The [163] no-arm selects the canonical-replacement alternative rather than a graph-realized second strand.
6. `def:neutral-equal-length-germ`: exchanging (Q) and (E) is asserted to preserve vertex and edge counts, the boundary-degree profile, the baseline, and target response in every context.
7. The canonical local order on bounded pieces chooses (E) before (Q) when (E\ne Q). In Lean this is `CanonicalPiece.Precedes E Q`, a well-founded order parameterized by one fixed boundary interface and refining internal vertex count.

What is not accumulated is a graph-level measure (Phi), a decomposition of every counterexample into cells comparable in one common order, a proof that the current (Q) is one of those cells, or a theorem that the swap preserves every other cell when the canonical data of (G') are recomputed.

The live Lean `selection` fact uses `Graph.lexicographicProgress`, whose measure is exactly `(vertexCount, edgeCount)`. Its node-[165] closure consumes `coldCanonicalSwapSmaller`, an existential germ whose canonical representative has strictly fewer internal vertices. The same-size arm is `coldCanonicalSwapSameSize`; its intended consumer `selectedDenseSameSizeCanonicalSwap` is absent. Moreover that predicate merely says the canonical representative is not smaller in internal vertex count and does not publish a global (Phi)-decrease.

### Current predicate and exact claim

The manuscript claims the implication

\[
\begin{aligned}
F(165)&+E\ne Q+|E|=|Q|\\
&+\bigl(E\text{ and }Q\text{ have the same boundary, baseline, and target response}\bigr)\\
&\Longrightarrow
G':=E\oplus_TY\text{ is a counterexample with }\\
&\hspace{25mm}(|V(G')|,|E(G')|,\Phi(G'))
 < (|V(G)|,|E(G)|,\Phi(G)).
\end{aligned}
\]

The local swap data support the counterexample predicate and, as stated in the manuscript, equality of the first two coordinates. The unsupported part is the last strict inequality. The only definition of the minimal counterexample preceding [165] has two coordinates. The sentence at [165] calling (Phi(H)) “the multiset of the boundaried pieces of the canonical decomposition of (H)” is not a prior definition. The named `def:canonical-decomp` instead decomposes the (P_{13})-free remainder into connected components and assigns surplus units; it does not decompose the whole graph into the bounded cold germs used here.

Even if a suitable multiset is supplied, one must prove the stability identity

\[
\Phi(E\oplus_TY)=\Phi(Q\oplus_TY)-\{Q\}+\{E\}.
\]

The retained cut-state fixes the current support's boundary data, stubs, and window labels, but it does not by itself prove that the canonical packing, return corridors, tie-breaking choices, or all overlapping decomposition cells of the new graph are unchanged.

### Outgoing contracts

The only edge is `[165] -> [166]`. Node [166] concludes (Q=E) from the contradiction obtained on the (E\ne Q) subcase, and the graph then continues to the trivial neutral residual [169]. For this handoff to be valid, [165] must supply either:

- a counterexample (G') strictly smaller under node [4]'s actual order; or
- a graph-level, well-founded third-coordinate order fixed when (G) was selected, plus a proved strict decrease for this exact swap.

Producing a locally earlier canonical piece is insufficient. Without the global decrease, the nontrivial canonical-swap residual is not eligible for [166]'s equality conclusion and remains unassigned.

## 3. Sentence audit

| Sentence | Exact assertion | Facts used | Hidden obligation | Adversarial test | Status |
|---|---|---|---|---|---|
| S1 | Node [4] may be refined to minimize ((|V|,|E|,Phi)). | Finiteness of canonically labelled graphs at fixed (n,m). | (Phi) must be fixed, valued in a well-founded order, and part of the original selection; it need not be isomorphism-invariant. | Search every earlier minimality statement and the live progress type. | FAILED |
| S2 | (Phi(G)) is the multiset of pieces of the canonical decomposition of (G). | A claimed fixed canonical order on bounded pieces. | A unique whole-graph decomposition into comparable bounded cells must be defined. | Compare this phrase with `def:canonical-decomp`, which consists of remainder components. | FAILED |
| S3 | (E\ne Q) implies that the canonical (E) precedes (Q) locally. | Canonical least representative of the retained cut-state. | (Q) and (E) must be canonicalized over the same boundary and realize the same reading. | Inspect `CanonicalPiece.toCanonical_eq_or_precedes`. | SUPPORTED |
| S4 | The exchange preserves vertex count. | Equal length/internal size and the same boundary/context. | “Length” must count exactly the internal vertices used by gluing. | Evaluate the gluing vertex-count formula at equality. | SUPPORTED |
| S5 | The exchange preserves edge count. | The claim that (Q,E) are equal-length strands. | Equal internal size does not imply equal edge count for general boundaried pieces; the strand/path property must be retained. | Hold internal size fixed while varying an internal edge. | AMBIGUOUS |
| S6 | (G') has minimum degree at least (3). | Same boundary-degree profile; inherited baseline/proper-representative condition. | Every internal vertex of (E) must satisfy the baseline, not merely the boundary vertices. | Inspect `def:proper-quotient-representative` (d) and the cut-state reading. | SUPPORTED IF THE FULL REPRESENTATIVE CONTRACT IS RETAINED |
| S7 | (G') has no power-of-two cycle. | Context equivalence of (Q,E); (G) avoids target. | Equivalence must hold for the actual outside context (Y), including internal and crossing cycles. | Apply the all-context predicate to (Y). | SUPPORTED |
| S8 | Swapping one cell leaves the canonical decomposition and every other cell unchanged. | Retained stubs and window labels. | Canonical packing, corridor selection, overlapping supports, and tie-breaks must be stable in (G'). | Allow the replacement to create a new induced (P_{13}) or an earlier canonical corridor elsewhere. | FAILED |
| S9 | Consequently (Phi(G')<Phi(G)) in multiset order. | S2, S3, S8. | The pieces must lie in one common well-order and the exact one-cell replacement identity must hold. | Use a locally smaller replacement while another recomputed cell becomes larger. | FAILED |
| S10 | Earlier uses of minimality remain valid under the refinement. | Earlier comparisons strictly decrease (n) or (m). | The refinement must have been fixed before choosing (G). | Check [8], [9], bridgelessness, and replacement: all use strict first/second coordinates. | SUPPORTED CONDITIONALLY |
| S11 | Hence every canonical neutral configuration has (Q=E). | Contradiction on (E\ne Q). | The same-size nontrivial swap must be strictly smaller in the selected graph order. | Keep (G') tied in ((n,m)) and omit the unproved (Phi)-stability lemma. | FAILED |
| S12 | The live Lean closure formalizes this same-size argument. | `selectedCanonicalSwapCloses`. | Its premise and progress relation must include the equal-size canonical-order decrease. | Inspect the predicate and body. | FAILED |

## 4. Counterexample attempts

### Smallest-parameter test

- **Explicit data:** Let (T=\{x,y\}) and let (Q=x-a-b-y) and (E=x-c-d-y) be two length-(3) strands. Their union is a (6)-cycle, so neither the pair cycle nor either strand alone supplies a power-of-two cycle. Both strands have the same boundary degrees, vertex count, and edge count.
- **Hypotheses satisfied:** This is the smallest distinct embedded equal-length strand pair avoiding the (4)-cycle forced by two length-(2) strands. Exchanging the two embeddings is count-neutral.
- **Accumulated facts violated:** (E) is a genuine second strand of the ambient graph, so it selects the `yes` arm of node [163] and routes to [167], not node [165]. As a standalone (6)-cycle it also fails node [2]'s minimum-degree-three condition.
- **Applicability:** **NON-APPLICABLE TO THE NODE**, excluded first by the selected `no` arm of node [163]. It nevertheless confirms that a same-size exchange is invisible to node [4]'s two-coordinate order.

### Parity or 2-adic test

- **Explicit data:** Compare two internally disjoint strand pairs of common lengths (ell=3) and (ell=6). Their pair cycles have lengths (6) and (12), respectively, neither a power of two; the equality (|E|=|Q|) holds in both the odd- and even-length cases.
- **Hypotheses satisfied:** Equal vertex/edge counts and absence of a direct pair-cycle target are insensitive to the parity of (ell). Node [165] contains no division, modulus, or 2-adic projection that could turn equality into strict progress.
- **Accumulated facts violated:** Both examples use graph-realized second strands and therefore violate node [163]'s selected `no` predicate; no complete dense residual graph is supplied.
- **Applicability:** **NON-APPLICABLE TO THE NODE**, first excluded by node [163]. The test shows that parity supplies no missing tie-break for the canonical-replacement arm.

### Boundary or range test

- **Explicit data:** Work at the exact boundary

  \[
  |V(G')|=|V(G)|,qquad |E(G')|=|E(G)|.
  \]

  Assume all the node's local data, including (E\ne Q) and (E\prec Q) in the fixed-boundary canonical-piece order.
- **Hypotheses satisfied:** This is precisely the same-size subcase in the node label and `lem:refined-minimality-swap`; the swap is allowed to preserve baseline and target response.
- **Accumulated facts violated:** None. Node [4]'s relation compares only the two displayed counts, so neither graph is strictly smaller there. The missing (Phi) fact is a desired conclusion, not an accumulated hypothesis.
- **Applicability:** APPLICABLE TO THE LOCAL MINIMALITY OBLIGATION. It is the decisive equality case: the original minimality theorem cannot close it.

### Graph-realizability test

- **Explicit data:** Realize (Q,E) as the two length-(3) arcs of the simple (6)-cycle (x-a-b-y-d-c-x), and take the outside context to be the rest of that cycle. The swap preserves the complete graph up to relabelling and therefore preserves all graph counts and target status.
- **Hypotheses satisfied:** Simplicity, exact graph realization, equal boundary profiles, equal counts, and a non-power-of-two bounded cycle.
- **Accumulated facts violated:** The second strand is graph-realized, contradicting node [163]'s `no` branch; the cycle graph also has minimum degree (2), contradicting node [2].
- **Applicability:** **NON-APPLICABLE TO THE NODE**, first excluded at node [2] and independently at node [163]. No actual minimum-degree-three dense residual realizing a nonembedded canonical replacement was found.

### Branch-routing test

- **Explicit data:** Model the claimed multiset step abstractly. Let the current decomposition codes be (Phi(G)=\{a,q\}), with the local replacement code (e\prec q). After recomputing canonical data in the swapped graph, let another cell change from (a) to (b) with (q\prec b), so (Phi(G')=\{e,b\}) is not below (Phi(G)) in the multiset extension. All local cut-state data at (Q) remain unchanged.
- **Hypotheses satisfied:** The selected node-[165] facts constrain (e\prec q), the common interface, and the local swap. They do not constrain the recomputed second cell, the global canonical packing, or the decomposition of (G').
- **Accumulated facts violated:** No accumulated stability theorem is violated, because none is stated. This is an abstract decomposition model rather than a fully realized graph.
- **Applicability:** APPLICABLE TO THE CLAIMED LOCAL-TO-GLOBAL INFERENCE. It shows that local precedence alone does not imply the outgoing [166] contract. Actual graph realization remains unproved, so it is evidence of a missing strict-decrease construction rather than a graph counterexample.

The modular checker was not run. Node [165] has no modular-orbit inference; its only arithmetic is equality of finite vertex and edge counts and strictness of a proposed well-founded order.

## 5. Strongest valid counterexample

No actual graph satisfying the complete node-[165] residual was constructed. The strongest surviving candidate is the node's own same-size canonical-swap schema after every local preservation claim is granted: (G'=E\oplus_TY) is another counterexample with the same (n,m), and (E\prec Q) only in a local fixed-boundary order. This violates no accumulated fact, because node [4] did not select (G) using (Phi). The abstract two-cell routing test further shows why the missing decomposition-stability theorem is substantive: recomputation can erase the alleged one-cell multiset decrease. Thus the gap is not the construction of a target-safe graph (G'); it is the construction of (G') as a strictly smaller representative in a graph-level order to which minimality applies.

## 6. Local repair

### Corrected statement

Fix before node [4] a map on the manuscript's canonically labelled graph presentations

\[
\Phi:\{\text{finite simple graphs}\}\longrightarrow W
\]

into a well-founded ordered set (W), and select (G) lexicographically minimal in ((|V|,|E|,\Phi)). For every canonical-replacement configuration used at node [165], require a swap-stability lemma stating that if (G=Q\oplus_TY), (E) is the canonical least realization of the retained cut-state, (E\ne Q), and (E,Q) have equal vertex and edge counts, then

\[
\Phi(E\oplus_TY)<_W\Phi(Q\oplus_TY).
\]

Under these explicitly prior hypotheses, the canonical replacement produces a smaller counterexample and the nontrivial arm is empty. Without that lemma, retain the same-size canonical-swap residual rather than asserting (Q=E).

### Complete local proof

Let (G=Q\oplus_TY) satisfy the corrected node contract and put (G'=E\oplus_TY). The equal-count hypotheses give

\[
|V(G')|=|V(G)|,qquad |E(G')|=|E(G)|.
\]

The boundary-degree equality preserves the final degree of every boundary vertex. Vertices of (Y) are unchanged, and the representative's baseline clause gives minimum degree at least (3) at every internal vertex of (E). Hence (delta(G')\ge3). Context equivalence applied to the actual outside context (Y) gives

\[
G'\text{ has a power-of-two cycle}
\iff
G\text{ has a power-of-two cycle},
\]

so (G') avoids the target. It is therefore a counterexample.

Because (E) is the canonical least realization of the cut-state and (E\ne Q), the fixed-boundary canonical order gives (E\prec Q). The added swap-stability lemma converts this local relation into (Phi(G')<_W\Phi(G)). Thus

\[
(|V(G')|,|E(G')|,\Phi(G'))
<
(|V(G)|,|E(G)|,\Phi(G)),
\]

contradicting the corrected selection at node [4]. Consequently the canonical-replacement arm (E\ne Q) is empty and the surviving canonical case has (E=Q), as required at [166]. Every earlier minimality argument remains valid because it strictly decreases (|V|) or, at fixed (|V|), strictly decreases (|E|), so the third coordinate is never consulted there.

This proof is complete once the new swap-stability lemma is proved; merely defining a local order on pieces is not a substitute for that producer.

### Counterexample disposition

The equality-boundary candidate is caught only by the new third-coordinate decrease. The two graph-realized strand examples remain on node [163]'s yes-arm and continue to [167]. The abstract decomposition-instability candidate is excluded exactly by the new swap-stability lemma, which forbids any compensating change of other cells. If such a lemma cannot be established for the proposed (Phi), the candidate remains an open same-size residual and must not be sent to [166].

### Graph patch

The proof-flow shape can remain unchanged only after adding the missing producer:

```text
[4] -> select G minimal in (|V|, |E|, Phi), with Phi fixed and well-founded
[163] -- no genuine second strand; retain actual Q,E and cut-state --> [165]
[165] -- E != Q + equal counts + swap-stability gives Phi(G') < Phi(G)
      --> contradiction by refined minimality
[165] -- complement --> [166: Q = E]
[166] --> [169]
```

If `canonicalSwapGlobalDecrease` is not available, the honest routing is instead

```text
[165] -- E != Q, same (|V|,|E|), no certified Phi decrease
      --> open same-size canonical-swap residual
```

and there is no justified edge to [166]. The edge must retain the actual germ, its owned decomposition, (Q,E,Y), equal counts, all-context equivalence, baseline preservation, and the certified global decrease.

### Downstream impact

Node [4]'s label and minimality paragraph, the minimality row in the detailed dependency table, `def:proper-quotient-representative`, `lem:replacement`, `def:neutral-equal-length-germ`, `lem:neutral-germ-symmetry`, `lem:refined-minimality-swap`, the Part XII caption, and `rem:dense-residual-status` must all name the same order. Node [166]'s equality and the trivial residual [169]--[172] depend directly on the repair. The absorbed-configuration reuse at [176] also cites [165]--[168] and must receive the same global-decrease certificate.

In Lean, `Graph.lexicographicProgress` currently measures only `(vertexCount, edgeCount)`. `CanonicalPiece.Precedes` proves the local piece order but is not connected to a graph-level progress measure. A faithful implementation needs either an extended canonical `Progress` with the proved (Phi) coordinate or a separately sealed minimality fact whose `Smaller` relation includes that coordinate, plus a theorem constructing the global decrease for the exact gluing. `coldCanonicalSwapSameSize` must carry an actual neutral germ and equal-count representative, not merely the universal negation of a vertex-count decrease. The missing `selectedDenseSameSizeCanonicalSwap` producer should consume the global certificate; `selectedCanonicalSwapCloses` remains only the distinct strictly-smaller-vertex case. No proof or implementation source is changed by this report.

## 7. Regression audit

The audit inspected these repeated sources and consumers:

- node [4]'s diagram box, minimality paragraph, dependency-table row, and every early proof explicitly using vertex/edge lexicographic minimality;
- `lem:replacement`, `cor:uncompressible`, `def:proper-quotient-representative`, and `def:admissible-rank-quotient`;
- `def:cold-bounded-germ`, the terminal/repeated first-failure representatives, `def:neutral-equal-length-germ`, and `lem:neutral-germ-symmetry`;
- Part XII nodes [163], [165], [166], and [169], their edges and caption, the detailed dependency row, and `rem:dense-residual-status`;
- `def:canonical-decomp`, which is the only named canonical decomposition found in the manuscript and is a decomposition of the remainder into connected components rather than the asserted bounded-piece multiset;
- `Graph/CanonicalRealization.lean`: `CanonicalPiece.Precedes`, canonical least realization, cut-state reading, target/baseline swap theorems, and the strictly-smaller-vertex theorem;
- `Graph/Progress.lean`: the exact two-coordinate `lexicographicProgress`;
- `SpineVocabulary.lean`: `CanonicalNeutralConfigurationStatement`, `coldCanonicalSwapSmaller`, and `coldCanonicalSwapSameSize`;
- `ColdCorridorRows.lean`: `neutralGermSymmetryDichotomy` and `canonicalSwapSizeDichotomy`;
- `Assembly.lean`: `selectedCanonicalSwapCloses` and both calls to the absent `selectedDenseSameSizeCanonicalSwap`;
- the [165], [166], and [176] implementation-audit entries, used as locators rather than authority.

The principal searches were

```text
rg -n -F '\\Phi' to_formalize/erdos_64_proof.tex
rg -n 'lexicographically minimal|minimal counterexample|canonical decomposition|canonical order' to_formalize/erdos_64_proof.tex
rg -n 'canonical atom multiset|CanonicalPiece|Precedes|lexicographicProgress|coldCanonicalSwapSameSize|selectedDenseSameSizeCanonicalSwap' hypostructure proofs Assembly_node_audit.md web/data/eg_node_audit.json
rg -n 'word for word|same proof|analog' to_formalize/erdos_64_proof.tex hypostructure proofs
```

No earlier definition of the node-[165] graph measure (Phi), no proof of a one-cell decomposition update, and no “word for word,” “same proof,” or analogous same-size minimality argument was found. The other manuscript uses of the symbol (Phi_{\rm can}) concern the unrelated sparse-surplus blocker assignment and do not provide this graph tie-break.

## 8. Residual uncertainty

No complete minimum-degree-three, target-avoiding graph realizing the node-[165] nonembedded canonical replacement was constructed. It remains possible that the authors can define a labelled global graph code or a decorated-counterexample selection for which every allowed canonical swap is provably decreasing; no such construction was found in the manuscript or Lean source. The audit did not prove that a swap-stable decomposition is impossible, only that the stated retained cut-state does not establish it. The equal-edge-count inference is also secure only if the canonical representative remains a strand/path in the precise sense required by the node; the generic Lean canonical piece does not encode that constraint. No manuscript, diagram, Lean, implementation-audit, or coverage-ledger source was changed.
