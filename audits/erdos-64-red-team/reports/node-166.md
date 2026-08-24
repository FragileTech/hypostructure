<!-- red-team-audit
{
  "schema_version": 1,
  "proof": "erdos-gyarfas",
  "node": 166,
  "node_label": "refined lexicographic minimality: \\(Q=E\\)",
  "panel": "fig:proof-diagram-part-xii",
  "contract_sha256": "853a21e10d3eb6ba37cb82454014de0d7a23f2f8b1cb0d3265726da95b73fe4b",
  "manuscript_sha256": "106a8205a1718fbf90e1686a107b2143b9edca574e2b0c11415e7f44aee2c0f9",
  "graph_sha256": "dc67fae178f947a9607c167e383d85919633341bdd423e4c4a45e4c317b3a765",
  "lean_audit_sha256": "50324ef5594d635a52d83aeb297f2ca3f3d30ef58de4ce3602816c7e78365b12",
  "verdict": "MISSING REPRESENTATIVE",
  "audited_at": "2026-08-24T21:25:44Z"
}
-->

# Red-team audit: node [166]

## 1. Executive verdict

Verdict: **MISSING REPRESENTATIVE**

The equal-size exchange produces an actual counterexample (G') only at the same declared node-[4] measure ((|V|,|E|)).  The newly invoked third coordinate (Phi) is not defined at node [4], and the manuscript proves neither a fixed well-founded graph-level definition of (Phi) nor the asserted locality identity saying that recomputing the canonical decomposition after the swap changes exactly one multiset entry.  A tie-break on canonically labelled graph presentations would be sufficient; it need not be isomorphism-invariant.  Without that tie-break and locality proof, no replacement strictly smaller in the selected minimality order has been constructed.  The conclusion (Q=E), and hence the handoff to [169], does not follow from the complete incoming residual as written.

## 2. Exact node contract

### Incoming residual

The only immediate edge is [165] (	o) [166].  It carries the canonical-replacement arm of the neutral equal-length terminal configuration: (Q) is the return-corridor piece, (E) is the canonical replacement for the retained cut-state, (E\ne Q) as a boundaried piece, and exchanging (Q) for (E) gives a counterexample (G') with the same vertex and edge counts as (G).

### Accumulated facts

The cumulative route retains the following facts, not the union of sibling branches.

- [1]--[6]: (G) is a finite simple counterexample, so (delta(G)\ge3), it has no power-of-two cycle (equivalently the oriented-edge Mersenne returns are absent), and node [4] selected it lexicographically only by ((|V(G)|,|E(G)|)).
- [8]--[14]: no proper subgraph has minimum degree three; every edge has a degree-three endpoint; (V_{\ge4}(G)) is independent; boundary-degree profiles and context-universal target responses are retained; and a proper support has no genuinely smaller target-safe replacement in the declared node-[4] order.
- [15], [17]--[21]: (G) is on the induced-(P_{13}) side, with the fixed maximal disjoint induced-(P_{13}) packing, its 399-label window algebra and obstruction data, and the near-cubic/skeleton-budget data supplied before the dense branch.
- [158]--[160], [162]: the joint window package is not realized by the labelled skeleton class, so this is the dense-packing residual; the exact deficiency test did not take the (	au(\theta)<1/4) closure; and the dense hot/cold pass has removed its hit, target-defect, smaller-replacement, handoff, and all-cold alternatives.
- [163], [165]: the selected (F5) germ is terminal, equal-length and neutral.  The two pieces have the same boundary-degree profile and target response in every compatible context; the retained cut-state keeps the stubs and window labels; the selected arm is a canonical replacement rather than a genuine second strand; and the swap preserves ((|V|,|E|)), the baseline, and target avoidance.

No accumulated fact supplies a graph-level third minimality coordinate.  In particular, the later `def:canonical-decomp` is not an ancestor and decomposes the remainder (R) into connected components with surplus assignments, not (G) into the bounded boundaried pieces used in the asserted (Phi).

### Current predicate and exact claim

The operative sentences of `lem:refined-minimality-swap` are:

1. Refine node [4]'s selection to lexicographic order on ((|V|,|E|,\Phi)).
2. Define (Phi(G)) as the multiset of pieces in a canonical decomposition of (G), ordered by the order used for canonical representatives.
3. The neutral swap makes a counterexample (G') with the same ((|V|,|E|)).
4. Replacing (Q) by the preceding piece (E) changes only that entry of (Phi), hence (Phi(G')<Phi(G)).
5. Refined minimality contradicts the existence of (G').
6. Therefore every neutral configuration satisfies literal equality (Q=E), and [165] is empty.
7. All earlier minimality arguments remain valid because they strictly decrease one of the first two coordinates.

### Outgoing contracts

The sole outgoing edge is [166] (	o) [169].  Node [169] requires the trivial neutral-configuration residual: every selected corridor is terminal and neutral, is literally its own canonical representative (Q=E), and every packed window is blocked at every dyadic scale.  The counterexample condition supplies blockedness, but the incoming arm (E\ne Q) cannot satisfy the equality part unless node [166]'s strict-decrease contradiction is valid.

## 3. Sentence audit

| Sentence | Exact assertion | Facts used | Hidden obligation | Adversarial test | Status |
|---|---|---|---|---|---|
| 1 | Node [4] may be refined to ((|V|,|E|,\Phi)). | Node [4] selected a minimal counterexample. | The refined order must have been fixed at selection time, be well-founded, and admit a minimum among canonically labelled counterexamples. | Compare the source's two-coordinate selection at lines 428--434 and 1835--1838 with the first appearance of (Phi) at node [166]. | FAILED |
| 2 | A canonical decomposition of (G) gives a finite multiset (Phi(G)) in the representative order. | A canonical order on bounded pieces is mentioned. | The decomposition, occurrence multiplicities, multiset extension, and behavior under the selected labelled canonicalization must be defined. | Source-wide search finds no prior definition of this decomposition or of (Phi); the later `def:canonical-decomp` is a different remainder-component construction. | FAILED |
| 3 | Swapping (Q) for (E) yields a same-((n,m)) counterexample. | Neutrality, equal length, boundary profile, context response, and `def:proper-quotient-representative`(d). | (E) must be an actual simple proper representative at the selected interface, and gluing must preserve the baseline and target avoidance. | Glue against the actual complement; the stated neutral and proper-representative clauses provide exactly these properties. | SUPPORTED |
| 4 | (Phi(G')) is obtained by replacing exactly one entry (Q) by (E\prec Q). | Retained stubs/window labels and canonical precedence. | Recomputing the canonical decomposition must preserve every other piece and occurrence in the selected labelled presentation. | Let a second recomputed cell increase even though (E\prec Q) locally. | FAILED |
| 5 | The strict third-coordinate decrease contradicts minimality. | Sentences 1 and 4. | (G) must actually have been selected by the proved three-coordinate order. | In the declared order, (G') has exactly the same measure as (G). | FAILED |
| 6 | Every neutral configuration has literal (Q=E). | Claimed contradiction for every (E\ne Q) canonical arm. | The arm must be universal over all selected germs and every distinct labelled canonical representative must produce the proved global decrease. | Keep (E\ne Q) while omitting the graph-level decrease. | FAILED |
| 7 | Earlier minimality arguments remain valid after refinement. | Earlier swaps strictly decreased (n) or, at fixed (n), (m). | The refined selection and all earlier definitions must be restarted coherently. | A genuine decrease in either first coordinate remains a lexicographic decrease. | SUPPORTED |

## 4. Counterexample attempts

### Smallest-parameter test

- **Explicit data:** Let (T=\{x,y\}).  On internal carrier ({a,b}), take (Q) with edges (xa,ab,by) and (E) with edges (xb,ab,ay).  They are distinct fixed-carrier pieces, each a three-edge (x)-to-(y) path, with the same two internal vertices and boundary profile ((1,1)); the swap (a\leftrightarrow b) is a boundary-fixing isomorphism.
- **Hypotheses satisfied:** Equal vertex and edge counts, same boundary profile, and the same response for every isomorphism-invariant target.
- **Accumulated facts violated:** Each internal vertex has degree two.  This fails the ambient minimum-degree condition first retained at node [2] and the internal-degree clause of `def:proper-quotient-representative` used at [166].
- **Applicability:** **NON-APPLICABLE TO THE NODE**; node [2] excludes this smallest graph realization.

### Parity or 2-adic test

- **Explicit data:** Test equal-size abstract pairs with ((|V_{\rm int}|,|E|)=(3,6)), for which (v_2(|E|)=1), and ((4,8)), for which (v_2(|E|)=3).  In both cases impose (|V(E)|=|V(Q)|), (|E(E)|=|E(Q)|), and (E\prec Q).
- **Hypotheses satisfied:** The numerical equal-size branch of [165] is satisfied for both odd and even internal order and for different powers of two dividing the edge count.  In neither case does parity create a strict decrease in the pair ((|V|,|E|)).
- **Accumulated facts violated:** These are numerical records only; they do not supply actual boundaried pieces, a proper representative, or a retained cut-state, first required by node [11] and concretely by [165].
- **Applicability:** **NON-APPLICABLE TO THE NODE** as graph candidates; node [11]'s boundaried-piece requirement is the earliest unmet contract.  The test confirms that no parity or 2-adic refinement repairs the missing strict order.

### Boundary or range test

- **Explicit data:** Put the canonical representative exactly on the equality boundary (|V_{\rm int}(E)|=|V_{\rm int}(Q)|=3) and (|E(E)|=|E(Q)|=6), with (E\ne Q), (E\prec Q), the same interface (T), and the same boundary profile.
- **Hypotheses satisfied:** This is precisely the right-hand/equality case left after the strictly-smaller-size canonical swap; it also meets node [165]'s same-((n,m)) premise.
- **Accumulated facts violated:** None at the finite-state or boundaried-object level.  No complete ambient residual is asserted.
- **Applicability:** Applicable to the exact boundary of node [166]'s inference.  The declared node-[4] measure is equal there, so the missing third-coordinate construction is load-bearing.

### Graph-realizability test

- **Explicit data:** Let (T=\{x,y,z\}), with internal carrier ({a,b,c}).  Set
  [
  E(Q)=\{ab,bc,ca,xa,yb,zc\},\qquad
  E(E)=\{ab,bc,ca,xb,yc,za\}.
  ]
  Both are simple pieces with three internal vertices and six edges.  Each internal vertex has degree three, every boundary vertex has piece-degree one, and the only piece cycle is the triangle (abc).  The permutation (a\mapsto b\mapsto c\mapsto a), fixing (T), is a boundary-preserving isomorphism (Q\cong_T E), although (Q\ne E) as fixed-carrier graph records.
- **Hypotheses satisfied:** Equal counts, equal boundary-degree profile, internal degree at least three, no internal power-of-two cycle, and identical target response against every compatible context.  Whichever member of this finite presentation orbit is first in a label-sensitive canonical order may precede another.
- **Accumulated facts violated:** The pair alone does not exhibit an outside context whose glued graph satisfies the complete node-[2] counterexample condition, the dense-packing route, and the selected cold cut-state.  It therefore does not construct a full residual graph.
- **Applicability:** **NON-APPLICABLE TO THE NODE** as an actual residual counterexample because the earliest global requirement, node [2], has not been instantiated.  It is also not a counterexample to a label-sensitive tie-break: one presentation can precede another.  Its only force is to show that the manuscript must declare which presentation/order is being minimized.

### Branch-routing test

- **Explicit data:** Retain the incoming symbolic data of [165]: an actual neutral canonical replacement (E\ne Q), (G'=G[Q:=E]), ((|V(G')|,|E(G')|)=(|V(G)|,|E(G)|)), the same baseline, and no target cycle.  Do not add an unproved (Phi)-decrease.
- **Hypotheses satisfied:** This is the exact selected branch predicate and all locally stated preservation facts.
- **Accumulated facts violated:** None symbolically.  The data do not contradict the actual node-[4] minimality because its two coordinates are equal.
- **Applicability:** Applicable as an unclosed logical residual.  Routing it to [169] is ill-typed: [169] requires (Q=E), while this branch retains (E\ne Q).  It becomes an actual routing counterexample only if a complete ambient residual graph is supplied, which this audit does not claim.

## 5. Strongest valid counterexample

No candidate reaches the actual residual: no finite graph satisfying the complete node-[2] counterexample condition, all dense-packing facts, and the selected cold germ was constructed.  The strongest surviving candidate is the exact symbolic incoming state from the branch-routing test: an actual same-size target-safe swap with (E\ne Q), but no graph-level third coordinate or one-cell update theorem.  The abstract two-cell recomputation model from node [165] shows why local precedence alone does not supply the missing global decrease.  The triangle presentation test is weaker and is non-applicable even to a label-sensitive tie-break.  The surviving result is therefore a missing strict representative/decrease, not a claimed counterexample to the global theorem.

## 6. Local repair

### Corrected statement

At node [4], before any consequence of minimality is derived, put every counterexample into one fixed canonical labelled presentation and choose (G) lexicographically minimal by

[
  (|V(G)|,|E(G)|,\Psi(G)),
]

where (Psi) is a fully defined well-founded multiset code of a fixed finite decomposition of that labelled presentation.  Prove the following swap-locality property: whenever a marked decomposition occurrence (Q) is replaced by a context-equivalent canonical representative (E) with the same vertex and edge counts and unchanged retained interface data, canonicalizing the glued graph preserves every occurrence outside the mark and replaces (Q) by (E).  The canonical representative order is the same fixed well-order used inside (Psi).  Then every neutral equal-size canonical replacement with (E\ne Q) satisfies (Psi(G[Q:=E])<Psi(G)).  Consequently the nontrivial canonical-replacement arm is empty and the surviving labelled representative satisfies (Q=E).

### Complete local proof

Let (G=Q\oplus_TY) be the selected occurrence and let (G'=E\oplus_TY).  Neutrality gives equality of the target response against every compatible context, so the actual context (Y) gives a target cycle in (G') if and only if it gives one in (G).  The common boundary-degree profile, internal degree bound, and unchanged retained stubs give (delta(G')\ge3); equal internal vertex and edge counts give ((|V(G')|,|E(G')|)=(|V(G)|,|E(G)|)).  Hence (G') is a counterexample with the same first two coordinates.

Because (E) is the canonical least realization of the retained state and (E\ne Q) in the fixed labelled presentation, (E) strictly precedes (Q) in the declared piece order.  The swap-locality lemma identifies all other decomposition occurrences and replaces only (Q) by the strictly preceding (E); the multiset extension therefore gives (Psi(G')<Psi(G)).  Thus (G') is smaller in the three-coordinate order, contradicting the selection at [4].  Earlier minimality arguments remain valid because each already decreases (|V|), or decreases (|E|) at fixed (|V|), before the third coordinate is read.

This proof is complete once the stated construction and swap-locality lemma for (Psi) are supplied.  The present manuscript does not supply them; calling an unspecified later decomposition “canonical” cannot replace that obligation.

### Counterexample disposition

The triangle-with-boundary-leaves candidate is ordered by the same labelled canonical rule and therefore supplies no objection once that rule is fixed.  The abstract recomputation candidate is excluded exactly by the proved (Psi)-locality identity, which forbids compensating changes in other cells.  Until that measure and lemma exist, the equal-size canonical-replacement case must remain an explicit residual rather than being sent to [169].

### Graph patch

Replace the current unconditional chain

```text
[163] -> [165] (E != Q) -> [166] (refined minimality: Q = E) -> [169]
```

by the typed split

```text
[4] -> canonically label counterexamples and select by the declared (|V|, |E|, Psi) order
[163] -> [165] canonical replacement with an actual proper E
[165] -> (E != Q) -> [166]
[166] -> swap-locality gives Psi(G') < Psi(G) -> minimality contradiction
[165] -> complement (E = Q) -> [169]
```

The entry to [169] must retain: dense packing; every selected corridor terminal and neutral; every such corridor literally equal to its canonical representative in the fixed labelled presentation; the fixed packing and edge count; and blockedness at every dyadic scale.  If no swap-local (Psi) can be constructed, keep “equal-size, distinct, context-equivalent canonical replacement” as an open residual instead of routing it to [169].

### Downstream impact

- Define the fixed labelled (Psi) order before node [4] and cite its swap-locality theorem in the Part XII node [166]/[169] caption, dense-residual source-ledger rows, branch-table rows 51 and 53, and `rem:dense-residual-status`.
- Recheck `lem:window-system-realizability`, its zero-increment shortening, and `lem:serial-system-sumset`: their use of literal (Q=E) must refer to the same canonical labelled representatives and marked common subpath.
- Recheck the “identical to” use in `lem:pair-system-realizability` and therefore the pair-system continuation [178]--[180].
- Recheck node [176]'s reuse of `lem:refined-minimality-swap` for graph-realized (F5) configurations.
- In Lean, extend or replace `Graph.lexicographicProgress`, currently only ((\texttt{vertexCount},\texttt{edgeCount})); define the canonical labelled graph-level (Psi) and its swap-locality theorem; strengthen `.coldCanonicalSwapSameSize`, which currently records only failure of a strict size decrease; and replace the absent `selectedDenseSameSizeCanonicalSwap` producer with the actual proof.  Existing size-reducing `selectedCanonicalSwapCloses` is unaffected.

## 7. Regression audit

The source-wide manuscript search

```text
rg -n -C 3 'refined-minimality-swap|Node \[166\]|node \[166\]|Q=E|Phi\(G\)|canonical decomposition' to_formalize/erdos_64_proof.tex
```

inspected the following repeated uses:

- diagram labels and caption for [166] and [169] at lines 1145--1149;
- overview/branch-table row 51 and source-ledger row for `lem:refined-minimality-swap` at lines 1229 and 1555;
- `lem:pair-system-realizability` at lines 4943--4945, which imports node [166] to remove an intersection;
- the lemma and proof at lines 7477--7501;
- `rem:dense-residual-status` at line 7603 and node [176]'s absorbed-germ reuse at line 7669;
- the [169] entry contract at lines 7716--7718;
- `lem:window-system-realizability` at lines 7848--7851 and its zero-difference use at line 7873;
- removal of neutral cells in `lem:serial-system-sumset` at line 7914.

The same search found `def:canonical-decomp` only later, around line 9671.  Inspection showed that it consists of connected components of the remainder (R) plus surplus assignments; it is not the bounded-piece decomposition asserted at [166] and is not available on the incoming route.  A search for `\Phi(G)` found no independent definition or stability theorem beyond the three occurrences in `lem:refined-minimality-swap`.  The dossier's reverse-item-dependency search reports no declared reverse dependencies, so the textual uses above are the complete extra regression surface found by source search.

The Lean searches

```text
rg -n -uuu 'lexicographicProgress|CanonicalPiece\.Precedes|canonicalRepresentative_precedes|toCanonical_eq_or_precedes|coldCanonicalSwapSameSize|canonicalSwapSizeDichotomy|selectedDenseSameSizeCanonicalSwap' proofs hypostructure
rg -n 'lexicographicProgress|namespace CanonicalPiece|def Precedes|theorem.*precedes|toCanonical_eq_or_precedes|coldCanonicalSwapSmaller|coldCanonicalSwapSameSize|canonicalSwapSizeDichotomy' hypostructure/Hypostructure/Graph/{Progress.lean,CanonicalRealization.lean,Strategy/SpineVocabulary.lean}
```

confirmed that `Graph.lexicographicProgress` has only vertex and edge counts; `CanonicalPiece.Precedes` is a well-order on fixed-carrier presentations and is not installed as a graph progress coordinate; `.coldCanonicalSwapSameSize` is the non-smaller-size arm, not (Q=E); and `selectedDenseSameSizeCanonicalSwap` has no live source declaration, only Assembly call sites/frontier-stub evidence.  This absence is corroboration, not the basis of the manuscript verdict.

## 8. Residual uncertainty

No full graph satisfying the complete counterexample and dense-packing residual was found, so this report does not claim `VALID LOCAL COUNTEREXAMPLE` or failure of the global theorem.  It remains unproved whether a canonical labelled, swap-stable decomposition and well-founded (Psi) with the required one-entry replacement law can be constructed; the later remainder-component decomposition does not provide it.  It also remains to prove that the resulting literal equality is preserved for every downstream overlap-shortening operation with its marked stubs and common subpaths.  Lean was inspected only as contract evidence; no absent declaration was treated as a mathematical counterexample.
