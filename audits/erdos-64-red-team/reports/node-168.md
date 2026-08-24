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
  "verdict": "WRONG ROUTING DESTINATION",
  "audited_at": "2026-08-24T21:23:03Z"
}
-->

# Red-team audit: node [168]

## 1. Executive verdict

Verdict: **WRONG ROUTING DESTINATION**

The geometric half of node [168] is correct: in an ambient-cubic induced \(P_{13}\), each interior vertex has one external stub and each endpoint has two, so a genuine pair of internally disjoint strands with distinct attachment vertices must attach at the endpoints.  The routing conclusion does not follow for the selected family that reaches the node.  `def:cold-skeleton-excess` fixed the first two of all \(15\) stubs as transit stubs and fixed the other \(13\) as selected; it did not select only interior stubs.  Since there are only \(11\) interior stubs, the fixed \(13\)-set contains at least two endpoint stubs.  More decisively, the pair at [168] arose from the return corridor of a selected half-edge, so one of its strand stubs is selected by construction.  The conditional phrase “if the selected ... are taken among the interior stubs” silently replaces the retained selection and all corridors and extracted germs depending on it.  Thus the live `survives` residual of [167] fails [168]'s terminal contract.  The strategy can be repaired locally by filtering the original selected set to its at-least-nine interior stubs per ambient-cubic window before the candidate extraction and re-running the overlap extraction with \(9C\) in place of \(13C\).

## 2. Exact node contract

### Incoming residual

The only displayed incoming edge is `[167] -> [168]`, tagged `survives`.  The residual carries a selected lexicographically minimal finite simple graph \(G\) with \(\delta(G)\ge3\) and no cycle of power-of-two length, together with the retained edge-criticality, high-degree independence, context-universality, replacement, and hereditary uncompressibility facts from nodes [1]--[14].  It carries the fixed maximal packing \(\mathcal P\) of induced \(P_{13}\) windows and the near-cubic spine selected at [19]--[21].

On the Part-XII path, [158]'s no-arm retains the dense-packing overflow, [160]'s no-arm retains the exact deficiency comparison \(\tau(\theta)\ge1/4\), and [162] runs the cold linear extraction on that dense residual.  In particular, the incoming germ is not an arbitrary two-strand diagram.  It descends from a half-edge
\[
\epsilon\in\mathcal E_{\rm br}(P)
\]
selected at `def:cold-skeleton-excess`; \(Q\) is the canonical return corridor of \(\epsilon\), and the extracted first-failure support is a neutral, equal-length terminal configuration.  The yes-arm of [163] retains that its second representative \(E\) is graph-realized.  Hence \(Q,E\) are actual internally disjoint outside strands of common length \(\ell\), with the first edge of \(Q\) equal to the selected stub \(\epsilon\), between attachment coordinates of an ambient-cubic packed window at gap \(d\).

Node [167]'s selected `survives` edge retains the literal complement of its closing test:
\[
2\ell\notin\Pow,
\qquad
\ell+d\notin\Pow.
\]
The manuscript also summarizes this as \(\ell\notin\Pow\) and \(\ell+d\notin\Pow\), but the exact branch predicate needed here is the displayed condition on the two realized closing lengths.  The endpoint audit below does not depend on that notational compression.

### Accumulated facts

The node may use the following facts, and no later destination theorem as an unproved premise:

- `[2]`, `def:counterexample`: \(G\) is finite and simple, has minimum degree at least three, and avoids all accepted power-of-two cycle lengths.
- `[4]`--`[14]`: the selected minimality order, deletion criticality, independence of \(V_{\ge4}(G)\), exact boundary-degree data, context-universality, replacement, and target-uncompressibility are retained.
- `[17]`--`[21]`: \(\mathcal P\) is the fixed maximal disjoint induced-\(P_{13}\) packing on the near-cubic residual.
- `[159]`, `[160]` no, `[162]`: the current object is the dense residual on which the cold corridor construction and extraction have been executed.
- `def:cold-skeleton-excess`: every ambient-cubic cold window has \(15\) ordered external stubs; the first two in the global lexicographic order are transit stubs and the remaining \(13\) form the fixed set \(\mathcal E_{\rm br}(P)\).  All later cold counts and corridors use this set.
- `def:cold-corridor-first-failure` and `lem:cold-germ-extraction`: every candidate is indexed by its originating selected half-edge, and its return corridor begins with that half-edge.
- `[163]` yes: the neutral equal-length candidate has a graph-realized second strand.
- `[167]` survives: the two actual closing cycles have lengths \(2\ell\) and \(\ell+d\), neither accepted.
- `lem:cold-window-stub-excess`: an ambient-cubic induced \(P_{13}\) has exactly \(15\) external stubs.

No accumulated fact says that \(\mathcal E_{\rm br}(P)\) is contained in the interior stubs.  The opposite cardinality obstruction is immediate: \(|\mathcal E_{\rm br}(P)|=13>11\).

### Current predicate and exact claim

Write \(I(P)\) for the \(11\) stubs at the interior vertices of \(P\), and \(A(P)\) for its four endpoint stubs.  The valid local geometric implication is
\[
\text{ambient-cubic induced }P_{13}
+\text{ genuine symmetric pair with distinct attachments}
\Longrightarrow
\text{both attachments are endpoints and the pair uses }A(P).
\]

The node claims the stronger terminal implication
\[
F(168)+\text{[167] survivor}
\Longrightarrow
\text{the pair contains no selected branch-excess half-edge}.
\]
That is false for the retained selection.  Since \(\mathcal E_{\rm br}(P)\) is the complement of only two transit stubs,
\[
|\mathcal E_{\rm br}(P)\cap A(P)|\ge 4-2=2,
\qquad
|\mathcal E_{\rm br}(P)\cap I(P)|\ge13-4=9.
\]
Moreover, the particular \(Q\) reaching [168] begins with its selected indexing stub \(\epsilon\), so the incoming pair itself contains a selected half-edge regardless of the two inequalities.  The manuscript's conditional re-selection among interior stubs is a different state, not a conclusion about \(F(168)\).

### Outgoing contracts

Node [168] is drawn as terminal and has no outgoing edge.  Its intended terminal contract is that the [167] survivor is irrelevant to the extracted selected family because every selected originating stub is interior.  The actual incoming ledger supplies no such fact and supplies the contrary provenance fact that \(Q\) originates at selected \(\epsilon\).  Therefore the incoming survivor is left without a valid closure or a typed destination.

The nearest proof-preserving destination is not an existing terminal node applied to the same candidate.  One must first restrict the selected source family to
\[
\mathcal E_{\rm br}^{\rm int}(P):=
\mathcal E_{\rm br}(P)\cap I(P),
\qquad
|\mathcal E_{\rm br}^{\rm int}(P)|\ge9,
\]
then perform the first-failure candidate and vertex-disjoint extraction on that restricted indexing family.  Only germs carrying that retained interior-origin fact meet [168]'s endpoint-exclusion contract.

## 3. Sentence audit

| Sentence | Exact assertion | Facts used | Hidden obligation | Adversarial test | Status |
|---|---|---|---|---|---|
| S1 | Every interior vertex of an ambient-cubic induced \(P_{13}\) has one external stub. | Induced path; ambient degree \(3\). | The two path neighbours must be the only neighbours inside the window. | Count \(3-2=1\) at \(v_i\), \(1\le i\le11\). | SUPPORTED |
| S2 | Each path endpoint has two external stubs. | Induced path; ambient degree \(3\). | The endpoint has exactly one neighbour inside the window. | Count \(3-1=2\) at \(v_0,v_{12}\). | SUPPORTED |
| S3 | A genuine pair needs two distinct external stubs at each attachment. | Simplicity and internal disjointness of the two graph-realized strands. | The two strands may meet only at their attachment vertices and their first edges must differ. | Give both strands the same first edge; their first outside vertex is then an internal intersection. | SUPPORTED |
| S4 | With distinct attachment vertices, both attachments are the two endpoints and \(d=12\). | S1--S3; the incoming genuine witness has distinct left/right attachments. | Distinctness must be retained; a `gap = 0` census entry alone is not such a witness. | Test the formal witness's `left != right` field. | SUPPORTED |
| S5 | A window carries at most one genuine symmetric pair on its four endpoint stubs. | Endpoint stub count. | Stub count bounds edge-disjoint pairs, but does not by itself rule out several alternative pairs sharing initial stubs and branching later. | Build multiple outside routes sharing an endpoint edge before diverging. | AMBIGUOUS |
| S6 | The \(11\) interior stubs are single-stub attachments and cannot start a genuine pair. | S1 and S3. | The originating attachment of the candidate must be the vertex carrying its selected stub. | Track the first stub of \(Q\). | SUPPORTED |
| S7 | The selected branch-excess half-edges may now be “taken among” those \(11\) interior stubs. | Conditional wording in `lem:symmetric-pair-endpoint`. | The earlier canonical \(13\)-element selection, its corridors, first failures, and extracted family must be replaced or restricted explicitly. | Compare with the first-two-transit definition in `def:cold-skeleton-excess`. | FAILED |
| S8 | After two transit losses, nine interior selected stubs per window remain. | \(11-2=9\), or equivalently \(13-4=9\) as a lower bound. | This must be a proved lower bound for a retained interior subfamily, not a redefinition of the already consumed \(13\)-set. | Put both transit stubs in the interior: exactly nine interior stubs remain selected. | SUPPORTED AS A REPAIR, NOT IN THE CURRENT HANDOFF |
| S9 | No surviving symmetric pair occurs among the selected half-edges. | S6 plus the unstated interior-selection premise. | Every candidate reaching [163]--[168] must have been extracted from the restricted interior-origin family. | Use the actual selected indexing stub of \(Q\). | FAILED |
| S10 | `lem:cold-germ-extraction` survives automatically with \(9C\) in place of \(13C\). | The candidate-incidence and overlap proof. | Filter candidates by their originating interior stub before the greedy disjoint extraction and retain the origin map through every route. | Restrict only after a greedy extraction that may have chosen endpoint candidates. | AMBIGUOUS |
| S11 | The surviving edge of [167] terminates at [168]. | S7--S10. | The destination must close the literal retained pair, not a newly selected family. | Observe that incoming \(Q\) begins with selected \(\epsilon\). | FAILED |

## 4. Counterexample attempts

### Smallest-parameter test

- **Explicit data:** Let \(P=v_0v_1\cdots v_{12}\).  Attach two internally disjoint outside paths \(Q=v_0abv_{12}\) and \(E=v_0cdv_{12}\), so \(\ell=3\) and \(d=12\).  Their closing lengths are \(2\ell=6\) and \(\ell+d=15\).  Length \(2\) is closed by the pair cycle of length \(4\), so \(\ell=3\) is the smallest simple distinct-endpoint survivor.
- **Hypotheses satisfied:** The bounded support is simple; \(Q,E\) are equal-length and internally disjoint; each uses one of the two endpoint stubs at both endpoints; and neither \(6\) nor \(15\) is an accepted power of two.  Thus the datum passes the exact numerical `survives` predicate of [167].
- **Accumulated facts violated:** As a standalone whole graph, the internal vertices \(a,b,c,d\) and the uncompleted window interiors have degree below three.  No completion satisfying the full selected-minimal-counterexample and packing residual has been supplied.
- **Applicability:** **NON-APPLICABLE TO THE NODE** as a complete graph counterexample, first excluded by node [2]'s minimum-degree-three contract.  It is applicable to the local finite and routing subcontracts: it is the smallest graph-realized bounded support that [167] sends toward [168], and all four of its endpoint edges lie in the endpoint-stub set that the current \(13\)-selection cannot avoid.

### Parity or 2-adic test

- **Explicit data:** At the endpoint gap \(d=12\), test both \((\ell,d)=(3,12)\) and \((6,12)\).  The odd case closes lengths \((6,15)\); the even case closes lengths \((12,18)\).  None is a power of two.  Their 2-adic valuations are respectively \((1,0)\) and \((2,1)\), so neither parity forces a hit.
- **Hypotheses satisfied:** Both lengths lie below the manuscript's finite bound \(40\), both gaps satisfy \(0\le d\le12\), and both pairs satisfy the literal complement of [167]'s two closing tests.
- **Accumulated facts violated:** The arithmetic pairs alone do not provide the ambient graph, extracted germ, or selected-stub provenance required by [162]--[163].
- **Applicability:** **NON-APPLICABLE TO THE NODE** as full residual objects, first missing node [2]'s ambient graph contract.  They show that neither odd/even parity nor a retained 2-adic condition repairs node [168]; the obstruction is the selection handoff.

### Boundary or range test

- **Explicit data:** Use the exact boundary counts of one ambient-cubic \(P_{13}\): \(11\) interior stubs and \(4\) endpoint stubs.  Let \(T(P)\) be the two transit stubs and \(\mathcal E_{\rm br}(P)\) the other \(13\).  Then
  \[
  |\mathcal E_{\rm br}(P)\cap A(P)|=4-|T(P)\cap A(P)|\in\{2,3,4\},
  \]
  and
  \[
  |\mathcal E_{\rm br}(P)\cap I(P)|=11-|T(P)\cap I(P)|\in\{9,10,11\}.
  \]
- **Hypotheses satisfied:** This is exactly the selection and exact stub count already retained from `def:cold-skeleton-excess` and `lem:cold-window-stub-excess`; no choice of lexicographic ordering is assumed.
- **Accumulated facts violated:** None.
- **Applicability:** APPLICABLE TO THE NODE.  It disproves the unqualified identification of the selected \(13\)-set with interior stubs and proves the repair's sharp uniform lower bound of nine selected interior stubs.

### Graph-realizability test

- **Explicit data:** Use the simple subgraph on \(P=v_0\ldots v_{12}\) together with \(Q=v_0abv_{12}\) and \(E=v_0cdv_{12}\).  Give each \(v_i\), \(1\le i\le11\), one boundary edge leaving the displayed support; give \(a,b,c,d\) one additional boundary incidence for possible degree restoration.  Inside the displayed support the only cycles are \(Q\cup E\), of length \(6\), and each strand together with \(P\), of length \(15\).
- **Hypotheses satisfied:** It is an induced \(P_{13}\) window with the correct local ambient-cubic stub pattern, and it graph-realizes a genuine symmetric pair whose complete bounded-support cycle list avoids powers of two.  The endpoint attachments use all four endpoint stubs.
- **Accumulated facts violated:** The boundary incidences have not been completed to a finite graph of minimum degree three while preserving global power-of-two-cycle avoidance, the maximal packing, minimality, and every cold ledger exclusion.
- **Applicability:** **NON-APPLICABLE TO THE NODE** as a full graph, first not meeting node [2]'s complete ambient-graph requirement.  It confirms that the local endpoint geometry does not itself create a target cycle and that an endpoint survivor is graph-realizable as a bounded support.

### Branch-routing test

- **Explicit data:** Let \(\epsilon\in\mathcal E_{\rm br}(P)\) be the selected half-edge indexing the extracted neutral terminal germ, let \(Q\) be its return corridor, and take the [163] yes-arm and [167] `survives` arm.  By definition, \(\epsilon\) is the first boundary stub of \(Q\).  By [168]'s valid endpoint argument, if \(Q,E\) are a genuine pair then this attachment is an endpoint.
- **Hypotheses satisfied:** This is the literal provenance and all selected branch predicates of the incoming residual, rather than an independently invented graph.  It retains selectedness of \(\epsilon\), graph realization of \(E\), equal length, internal disjointness, endpoint attachment, and failure of both dyadic closing tests.
- **Accumulated facts violated:** None.  The only conflicting statement is the destination's new assertion that the same pair is not represented among selected half-edges.
- **Applicability:** APPLICABLE TO THE NODE'S ROUTING CONTRACT.  The live residual sent from [167] fails the terminal destination [168] because its strand \(Q\) contains the selected indexing half-edge \(\epsilon\).  No outgoing edge retains it.

The bundled modular checker was not run: node [168] makes no inference from an orbit modulo a factor of a modulus to an integer power in a finite central range.  The complete parity and finite-range obligations here are the explicit closing lengths \(2\ell,\ell+d\) and the exact finite stub counts above.

## 5. Strongest valid counterexample

No independent complete minimum-degree-three, power-of-two-cycle-free graph satisfying every minimality, packing, density, and cold-ledger condition was constructed.  The strongest candidate is nevertheless an exact incoming-residual schema, not an isolated simplification: take the graph-realized symmetric pair selected by [163] and surviving [167], together with its originating half-edge \(\epsilon\).  The accumulated corridor construction proves \(\epsilon\) is selected and lies on \(Q\); node [168]'s endpoint argument proves it is an endpoint stub.  Thus the same retained witness satisfies the source contract and fails the destination assertion “not a selected ... half-edge.”

The \((\ell,d)=(3,12)\) support is the smallest concrete realization of the local geometry and finite predicate.  The decisive failure does not depend on completing that support to a global counterexample: conditional on the incoming residual being inhabited, its own selected-origin witness contradicts the claimed terminal handoff.  This supports `WRONG ROUTING DESTINATION`, not `VALID LOCAL COUNTEREXAMPLE` to the theorem.

## 6. Local repair

### Corrected statement

Let \(P\) be an ambient-cubic packed induced \(P_{13}\), let \(I(P)\) be its interior stubs, and let \(\mathcal E_{\rm br}(P)\) be the selected set fixed in `def:cold-skeleton-excess`.  Every interior vertex has one external stub and each endpoint has two.  Hence a genuine symmetric pair with distinct attachment vertices attaches at the two endpoints and contains no stub of \(I(P)\).  The fixed selected set need not be interior: it satisfies
\[
|\mathcal E_{\rm br}(P)\cap I(P)|\ge9,
\]
and may contain two, three, or four endpoint stubs.  Define the retained interior source set
\[
\mathcal E_{\rm br}^{\rm int}(P)
:=\mathcal E_{\rm br}(P)\cap I(P).
\]
Restrict the first-failure candidate family to candidates indexed by \(\mathcal E_{\rm br}^{\rm int}:=\bigcup_P\mathcal E_{\rm br}^{\rm int}(P)\) before taking the greedy vertex-disjoint subfamily.  On the dense linear residual this gives
\[
N_{\rm conf}^{\rm int}\ge \frac{9C}{D_{\rm cold}}-o(n).
\]
No graph-realized genuine symmetric pair occurs in this restricted extracted family.  Therefore the [167] survivor is terminal only for the restricted interior-origin family; the original endpoint-origin survivor must be discarded when the restriction is made, not retroactively declared unselected.

### Complete local proof

Let \(P=v_0v_1\cdots v_{12}\).  Since \(P\) is induced and every vertex of \(P\) has ambient degree three, \(v_1,\ldots,v_{11}\) have two neighbours in \(P\) and one external stub each, while \(v_0,v_{12}\) have one neighbour in \(P\) and two external stubs each.  Thus \(|I(P)|=11\) and \(|A(P)|=4\).

The selected set \(\mathcal E_{\rm br}(P)\) has cardinality \(13\).  Removing all four endpoint stubs from it can remove at most four elements, so
\[
|\mathcal E_{\rm br}^{\rm int}(P)|
=|\mathcal E_{\rm br}(P)\cap I(P)|
\ge13-4=9.
\]
Equivalently, the two transit stubs can delete at most two of the \(11\) interior stubs.  Summing over the \(C-o(n)\) ambient-cubic cold windows gives at least \(9C-o(n)\) selected interior source incidences.

The corridor definition has already assigned a canonical return corridor and first failure to every member of \(\mathcal E_{\rm br}\).  Restrict that incidence family to \(\mathcal E_{\rm br}^{\rm int}\) before the greedy extraction.  Deleting candidates cannot increase support size or the number of candidate supports containing a fixed vertex, so the same bounds \(M_{\rm cold}\), \(B_{\rm cold}\), and \(D_{\rm cold}=M_{\rm cold}B_{\rm cold}+1\) remain valid.  After the same \(o(n)\) non-ambient-cubic and already transferred incidences are removed, the candidate intersection graph has at least \(9C-o(n)\) vertices and maximum degree at most \(M_{\rm cold}B_{\rm cold}\).  A greedy independent set therefore has size at least \(9C/D_{\rm cold}-o(n)\).

Now take a neutral candidate in this restricted extracted family and let \(\epsilon\in\mathcal E_{\rm br}^{\rm int}(P)\) be its originating half-edge.  The corridor strand \(Q\) begins with \(\epsilon\), so one attachment vertex of \(Q\) is the interior vertex carrying \(\epsilon\).  If the second representative \(E\) were a graph-realized strand internally disjoint from \(Q\), the first edges of \(Q\) and \(E\) at that attachment would be distinct external stubs.  But an interior vertex of \(P\) has exactly one external stub.  This is impossible.  Hence the genuine-pair yes-arm of [163], and therefore the survivor arm of [167], is empty for the restricted family.  Since \(C\) is linear on the dense residual and nine is positive, the quantitative extraction needed by the rest of the strategy is preserved.

### Counterexample disposition

The length-three endpoint pair is not declared “unselected” under the original \(13\)-stub ledger; it may contain selected endpoint stubs and an incoming instance necessarily contains its selected origin \(\epsilon\).  The repair removes endpoint-origin candidates when forming \(\mathcal E_{\rm br}^{\rm int}\).  The candidate then does not enter the repaired extraction.  Every retained candidate begins at a one-stub interior attachment, so it cannot realize two distinct strands there.  The standalone bounded support remains non-applicable as a global graph counterexample because no admissible degree-restoring target-safe completion was constructed.

### Graph patch

Replace the silent selection change at [168] by an explicit dense-branch refinement before candidate extraction:

```text
[162] dense cold linear residual
  -> retain the original E_br and define E_br^int = E_br ∩ {interior stubs}
  -> prove |E_br^int(P)| >= 9 for every ambient-cubic cold window
  -> restrict first-failure candidates to their retained originating epsilon in E_br^int
  -> [153-int] greedy extraction: N_conf^int >= 9C/D_cold - o(n)
  -> [154]--[157] and [163] on the interior-origin family
[163] graph-realized second strand
  -> [168] impossible: the selected interior attachment has only one stub
```

If the two-strand check [167] remains displayed, its incoming edge must retain `originating epsilon is an interior stub`; then [168] closes that edge directly before any finite survivor is relevant.  The destination entry facts are: the same literal graph and packing, membership of \(\epsilon\) in the original selected set, membership of \(\epsilon\) in \(I(P)\), the corridor/germ incidence indexed by \(\epsilon\), and the ambient-cubic stub equation at its attachment.  No unmarked loop or change of graph is needed.

### Downstream impact

The general \(13C\) cold-stub count may remain as a count of the original branch-excess set, but every closure that invokes endpoint exclusion must use the restricted \(9C\) candidate extraction.  In the manuscript this affects the “executed unchanged” wording in `lem:dense-cold-pass`, the proof and statement of `lem:symmetric-pair-endpoint`, the Part-XII node label and caption, the detailed dependency row, `rem:dense-residual-status`, and the reuse in `lem:absorbed-germ-fan-data`.  If the absorbed-configuration route cites [168] for endpoint exclusion, it too must filter before extraction or retain an independently proved interior-origin fact.

In Lean, `Graph/WindowStubStructure.lean` proves the endpoint/interior counts, but its `interior_stubs_le_asymmetric` theorem only counts all interior stubs; it does not connect them to the selected branch-excess set.  `K .coldWindowStubStructure` and `coldWindowStubStructureRow` likewise publish counts but no selected-set intersection or candidate-origin predicate.  The current `GenuineSecondStrandStatement` records a neutral graph-realized germ but deliberately omits the stronger endpoint, stub, and selection conclusions; the stronger `GenuineSecondStrandConfiguration` is not the ledger proposition consumed by Assembly.  A faithful implementation therefore needs an object-local fact for the restricted selected set, a producer of the \(9C\) restricted extraction retaining each germ's origin, and a node-[168] closure consuming that fact.  The existing human/JSON audit entry, which calls the implementation weaker and says endpoint exclusion is only a comment, should be synchronized after such a producer exists.  No proof, manuscript, diagram, Lean, or audit-source change is made by this report.

## 7. Regression audit

The audit used the searches

```text
rg -n 'symmetric-pair-endpoint|symmetric pair|symmetric-pair|selected interior|interior stubs|9C|13C|coldWindowStubStructure|GenuineSecondStrand|TwoStrandEnumeration|selectedGenuineSecondStrandCloses' to_formalize/erdos_64_proof.tex hypostructure/Hypostructure/Graph proofs/hypostructure_erdos_64_eg/HypostructureErdos64EG Assembly_node_audit.md web/data/eg_node_audit.json
rg -n 'word for word|same proof|verbatim|unchanged|analog' to_formalize/erdos_64_proof.tex
```

and inspected:

- `def:cold-skeleton-excess`, including the first-two-transit and remaining-\(13\) canonical selection;
- `lem:cold-window-stub-excess`, the exact \(15\)-stub count, and every displayed \(13C\) extraction formula in the cold ledger and quantitative closure;
- `def:cold-corridor-first-failure` and `lem:cold-germ-extraction`, including the selected-half-edge indexing, successor construction, candidate incidence, overlap bound, and greedy extraction order;
- `lem:dense-cold-pass`, `def:neutral-equal-length-germ`, `lem:neutral-germ-symmetry`, `lem:two-strand-check`, `lem:symmetric-pair-endpoint`, and `rem:dense-residual-status`;
- the Part-XI and Part-XII diagrams, captions, overview rows, and detailed dependency table entries for [152], [153], [162], [163], [167], and [168];
- the repeated endpoint-exclusion citation in `lem:absorbed-germ-fan-data`;
- `Graph/WindowStubStructure.lean`, including `exists_ends_externalNeighbours` and `interior_stubs_le_asymmetric`;
- `Graph/TwoStrandEnumeration.lean`, including `Configuration.Survives`, `three_zero_survives`, and the finite order/bound interfaces;
- `Strategy/SpineVocabulary.lean`'s `GenuineSecondStrandConfiguration`, weaker `GenuineSecondStrandStatement`, and `K .coldWindowStubStructure` schema;
- `Strategy/ColdCorridorRows.lean`'s `coldWindowStubStructureRow` and neutral-germ decision;
- every current Assembly occurrence of `selectedGenuineSecondStrandCloses` and the dense/absorbed consumers;
- the node-[168] entries in `Assembly_node_audit.md` and `web/data/eg_node_audit.json`.

The negative idiom search found `lem:dense-cold-pass`'s assertion that the cold pass runs “unchanged”; no separate “word for word,” “same proof,” or specifically analogous invocation repairs the selection handoff.  No other source establishes that the original selected \(13\)-set is interior or filters candidates by an interior originating stub.

## 8. Residual uncertainty

No complete ambient graph realizing the length-three endpoint pair while satisfying minimum degree three, global power-of-two-cycle avoidance, selected minimality, the maximal packing, the dense inequality, and every earlier cold exclusion was constructed.  The diagnosis instead uses the exact provenance of any residual that actually arrives: its corridor strand already has a selected originating stub.  It remains to prove in the manuscript's precise candidate data type that this origin map is retained through the first-failure and greedy extraction; the prose defines it, but the extracted-family notation does not expose a formal projection.

The sentence that a window carries “at most one” genuine pair was not proved by the stub count alone; alternative pairs may share initial endpoint stubs.  The repair does not use that assertion.  It also remains to audit whether all \(o(n)\) charge transfers commute with filtering before the greedy extraction; monotonicity preserves the overlap bound and the \(9C-o(n)\) lower bound provided discarded charges are still counted by originating incidence.  Finally, the live Lean files were under unrelated working-tree modification during this audit; the current checked audit says the node-[168] implementation is weaker, and the source inspection found no implemented restricted-selection producer.  The report makes no claim that resolving this local handoff settles other open nodes or the global theorem.
