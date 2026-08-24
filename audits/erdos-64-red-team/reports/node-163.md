<!-- red-team-audit
{
  "schema_version": 1,
  "proof": "erdos-gyarfas",
  "node": 163,
  "node_label": "neutral equal-length terminal configuration: second strand graph-realized?",
  "panel": "fig:proof-diagram-part-xii",
  "contract_sha256": "0154a0b5d09dbfe4558ac244f9384eb39edda286ee4b894b0c9dad3edaa0f432",
  "manuscript_sha256": "106a8205a1718fbf90e1686a107b2143b9edca574e2b0c11415e7f44aee2c0f9",
  "graph_sha256": "dc67fae178f947a9607c167e383d85919633341bdd423e4c4a45e4c317b3a765",
  "lean_audit_sha256": "50324ef5594d635a52d83aeb297f2ca3f3d30ef58de4ce3602816c7e78365b12",
  "verdict": "PROSE AMBIGUITY",
  "audited_at": "2026-08-24T21:16:19Z"
}
-->

# Red-team audit: node [163]

## 1. Executive verdict

Verdict: **PROSE AMBIGUITY**

The displayed question “second strand graph-realized?” has an exhaustive yes/no reading, but \`lem:neutral-germ-symmetry\` does not prove that reading. It instead classifies the representative by provenance—canonical cut-state representative or terminal completion strand—and calls the classes exclusive because the equality case \(E=Q\) is “trivial.” This conflates three independent predicates: provenance, ambient graph realization, and equality with \(Q\). In particular, the trivial neutral case \(E=Q\), which the manuscript explicitly retains at [166] and [169], satisfies neither of the lemma's stated kinds (“canonical ... different from \(Q\)” or “genuine second strand”). Conversely, a canonical representative can also be graph-realized, so provenance does not establish exclusivity. The intended route is recoverable: decide the literal internally-disjoint graph-realization predicate; on its negation use the retained terminal/repeated-state dichotomy to identify the canonical case, and then split \(E\ne Q\) from \(E=Q\). The live Lean decision asks the correct realization question, but its no-arm retains only a candidate family and a global negation, not the selected neutral equal-length germ needed for that proof.

## 2. Exact node contract

### Incoming residual

There is one incoming graph edge, \`[162] -> [163]\`, tagged \`[157] neutral row\`; there is no merge and no loop. The current object is the selected lexicographically minimal finite simple counterexample \(G\): it has minimum degree at least \(3\), contains no cycle of power-of-two length, and retains the boundary-profile, context-universality, replacement, and hereditary-uncompressibility ledger from [1]--[18]. The no-arm of [19] retains the near-cubic surplus bound, [21] retains the fixed maximal induced-\(P_{13}\) packing and finite label algebra, [158]--[159] retain the unrealized dense package, and the selected no-arm of [160] reaches the dense hot/cold pass [162].

The mathematically usable reading of the incoming tag must include an actual extracted bounded germ \(g\), not merely a nonempty family: its support is connected and proper; its interface consists of the two window attachment vertices; \(Q=g.\mathrm{piece}\) and \(E=g.\mathrm{canonical}\) have the same boundary-degree profile and baseline completion; \(g\) is neutral, so \(Q\) and \(E\) have the same target response in every compatible context; and

\[
\delta(g)=|E|-|Q|=0.
\]

It also retains the first-failure provenance from \`def:cold-corridor-first-failure\`: a terminal corridor supplies an ambiently realized second completion strand, while a repeated-state corridor supplies the canonical representative of the repeated cut-state. Node [163] must decide a predicate of this same \(g\); it may not choose a different germ on either arm.

There is a source-level inconsistency immediately upstream: \`lem:cold-same-interface-table\` says that no neutral equal-length row survives, while [162] explicitly sends a \`[157] neutral row\` here. For this node audit, the incoming edge is read as the intended carve-out described by \`def:neutral-equal-length-germ\`: a neutral row for which no already constructed smaller proper representative has closed the branch. Without that carve-out, the incoming residual is empty and the entire [163]--[172] continuation is vacuous.

### Accumulated facts

The cumulative facts relevant locally are:

1. [2], [4], [8]--[10]: \(G\) is a target-avoiding minimum-degree-\(3\) selected counterexample, every proper subgraph has minimum degree at most \(2\), and high-degree vertices are independent.
2. [11]--[14]: boundary-degree fibres and exact context responses are retained; replacement requires an actual boundaried graph preserving the profile, target safety, internal degree, and strict selected order; no such proper-support compression survives.
3. [15], [17], [18], [19], and [21]: the fixed maximal \(P_{13}\) packing, its labels, the near-cubic bound, and the finite window data are all on the same selected object.
4. [158]--[160]: the dense package is unrealized and the exact deficiency comparison selected the hot/cold continuation.
5. [162] and the cold first-failure data: after realizing, distinguishing, handoff, and length-changing cases are routed, the intended incoming object is an actual active neutral zero-increment germ with retained terminal-or-repeated provenance.
6. \`def:cold-bounded-germ\`: in the terminal provenance \(E\) is the second bounded completion strand; in the repeated-state provenance \(E\) is the canonical cut-state representative.
7. \`def:neutral-equal-length-germ\`: exchange preserves vertex and edge counts, boundary degree, baseline, and target response in every context. Its last sentence warns that an identification without graph-realizable rank reduction is only an abstract label identification.
8. \`def:proper-quotient-representative\` and \`def:admissible-rank-quotient\`: calling a quotient admissible for replacement requires an actual qualifying graph representative; context equivalence alone does not manufacture one.

The current Lean vocabulary usefully makes the literal yes predicate precise. \`SecondStrandGraphRealizedStatement data g\` requires a two-vertex interface and an injective embedding of \(E\) into \(G\), fixes the two boundary images to those of \(Q\), maps every edge of \(E\) into \(G\), and puts every internal vertex of \(E\) outside \`g.support\`. Thus its “graph-realized” witness already gives internal disjointness from \(Q\)'s support. However, \`CanonicalNeutralConfigurationStatement\` is only

~~~text
ColdGermCandidatesStatement data object ∧
  ¬ GenuineSecondStrandStatement data object
~~~

and does not retain an existential neutral zero-increment germ or identify its canonical representative.

### Current predicate and exact claim

For the selected incoming germ \(g\), let

\[
P(g):=\text{“\(E\) has an ambient embedding on the same two boundary images,
with its internal vertices disjoint from the support of \(Q\)”}.
\]

The diagram asks \(P(g)\). Its literal alternatives \(P(g)\) and \(\neg P(g)\) are complements. The manuscript lemma instead asserts

\[
\text{neutral, equal-length, terminal }g
\Longrightarrow
\bigl(E\text{ is canonical and }E\ne Q\bigr)
\mathbin{\dot\lor}
\bigl(E\text{ is a genuine second strand}\bigr).
\]

That displayed disjoint union is not established. \`def:cold-bounded-germ\` supplies a provenance disjunction, not a realization/equality disjunction. A canonical representative may admit an ambient internally-disjoint embedding, so it may satisfy the second predicate as well. At the other boundary, \(E=Q\) is canonical but fails the first stated kind and is not a genuine distinct second strand. The proof's assertion that equality is “not a proper configuration” cites no definition or accumulated exclusion and conflicts with [166]'s and [169]'s explicit use of the equality case.

### Outgoing contracts

The graph has two outgoing edges:

- \`yes\` to [167]. It must retain the same \(g\), its neutrality and zero increment, the two boundary attachments and window offsets, and an actual internally-disjoint embedding of \(E\). These data make \(Q\cup E\) a simple two-strand support, so [167] can test the closing lengths \(2\ell\) and \(\ell+d\).
- \`no\` to [165]. To justify the canonical-replacement route, it must retain the same \(g\), prove from \(\neg P(g)\) and the first-failure provenance that \(g\) is the repeated-state/canonical case, and then distinguish \(E\ne Q\) from \(E=Q\). The \(E\ne Q\) subcase reaches [165]'s refined-order swap; the equality subcase must bypass the assertion “\(E\ne Q\)” and enter the already drawn [166]/[169] trivial-neutral continuation.

As drawn, the no-edge is understandable only if [165] is read as the conditional sentence “if \(E\ne Q\), the swap contradicts refined minimality,” followed by [166]'s complementary equality conclusion. The lemma's own “exactly one” statement does not say this and instead deletes the equality case.

## 3. Sentence audit

| Sentence | Exact assertion | Facts used | Hidden obligation | Adversarial test | Status |
|---|---|---|---|---|---|
| S1 | A neutral equal-length configuration has two same-interface representatives with identical response in every context. | \`def:neutral-equal-length-germ\`; retained boundary profile. | The same actual germ and context universe must be used on both arms. | Hold \(g\) fixed and vary only whether \(E\) has an ambient disjoint embedding. | SUPPORTED |
| S2 | Exchange preserves vertex count, edge count, boundary degrees, baseline, and target response. | Equal length, retained cut-state, context equivalence. | Equal path length alone must not be substituted for equality of all edge/count/profile data. | Compare a same-length piece with an extra internal chord. | SUPPORTED BY DEFINITION, NOT BY LENGTH ALONE |
| S3 | Every neutral equal-length terminal configuration is exactly one of “canonical \(E\ne Q\)” or “genuine second strand.” | \`def:cold-bounded-germ\`. | Provenance must imply both exclusivity and the \(E\ne Q\) condition. | Take \(E=Q\), and separately take a canonical \(E\ne Q\) that embeds elsewhere in \(G\). | FAILED |
| S4 | \`def:cold-bounded-germ\` supplies the asserted two cases. | Terminal/repeated-state sentence of that definition. | “Terminal” in the premise must permit the repeated-state alternative used in the proof. | Read the definition literally: a terminal corridor already supplies two completion strands. | AMBIGUOUS |
| S5 | In the canonical case \(E\) is a piece that may replace \(Q\). | Retained cut-state; boundary profile; context response. | It must be an actual graph piece satisfying the replacement/refined-order hypotheses, not an abstract label quotient. | Apply \`def:admissible-rank-quotient\`'s no-representative clause. | AMBIGUOUS UNTIL PROVEN FROM PROVENANCE |
| S6 | In the terminal case \(E\) is a subgraph of \(G\). | \`def:cold-bounded-germ\`. | The realization must use the same boundary vertices and have interior disjoint from \(Q\). | Compare the prose “subgraph” with \`SecondStrandGraphRealizedStatement\`. | SUPPORTED ONLY UNDER THE STRONG REALIZATION READING |
| S7 | The two cases are exclusive because canonical \(E=Q\) is trivial and not proper. | No cited lemma. | Equality does not address overlap between a distinct canonical piece and a graph-realized strand; “proper configuration” must be defined and retained. | Use distinct canonical \(E\) with an ambient embedding, then use \(E=Q\). | FAILED |
| S8 | The no-edge satisfies [165]'s entry contract. | Negation of graph realization. | It must produce canonical provenance and handle equality separately. | A trivial neutral \(E=Q\) takes the no-edge but falsifies [165]'s node label. | AMBIGUOUS ROUTING |
| S9 | The yes-edge satisfies [167]'s entry contract. | Graph realization, neutral equality, window data. | Internal disjointness and two distinct boundary attachments are required for the cycles to be simple. | Inspect the exact Lean embedding predicate and the two-strand lemma. | SUPPORTED UNDER THE LITERAL LEAN PREDICATE |
| S10 | The live Lean no-arm expresses the manuscript's canonical case. | \`CanonicalNeutralConfigurationStatement\`; \`neutralGermSymmetryDichotomy\`. | Candidate-family existence plus \(\neg\exists g\,P(g)\) must select a neutral zero-increment canonical germ. | Let all candidates be distinguishing or length-changing. | FAILED AS A FORMAL HANDOFF |

## 4. Counterexample attempts

### Smallest-parameter test

- **Explicit data:** Let \(T=\{x,y\}\), let \(Q=x-a-y\) be a two-edge boundary path, and set \(E=Q\) as a boundaried piece. Give the pair the same retained boundary profile and cut-state record. Then \(|E|=|Q|\), every context has identical target response, and no distinct second strand exists.
- **Hypotheses satisfied:** Equal length, neutrality, same interface, same boundary degree, and the canonical equality boundary are literal. This is the smallest non-edge \(x\)-\(y\) corridor with an internal vertex.
- **Accumulated facts violated:** As a standalone ambient graph the internal vertex has degree \(2\), so it does not realize node [2]'s selected minimum-degree-\(3\) object; no dense packing or extracted-family witness is supplied.
- **Applicability:** **NON-APPLICABLE TO THE NODE** as an actual graph, excluded first by node [2]. As boundaried data it exposes the omitted equality case, which the manuscript itself later names at [166]/[169].

### Parity or 2-adic test

- **Explicit data:** On the genuine-strand arm take \(\ell=3\) and window gap \(d=2\). The two closing lengths are \(2\ell=6\) and \(\ell+d=5\), neither a power of two. At the adjacent even value \(\ell=4\), the pair cycle has length \(8\), a target hit.
- **Hypotheses satisfied:** The arithmetic uses the exact two-strand formulas with \(0\le d\le12\), checks both odd and even strand lengths, and performs no invalid modular division.
- **Accumulated facts violated:** No actual \(P_{13}\)-window graph with the full selected residual is constructed. The \(\ell=4\) instance would violate node [2]'s target avoidance as soon as the graph-realized pair exists.
- **Applicability:** The \(\ell=4\) candidate is **NON-APPLICABLE TO THE NODE**, excluded first by node [2]. The \((\ell,d)=(3,2)\) arithmetic is applicable to [167]'s surviving numerical table but neither proves nor refutes node [163]'s realization split.

### Boundary or range test

- **Explicit data:** Set \(E=Q\) in an incoming neutral zero-increment germ. The literal “genuine second strand” predicate is false because there is no distinct second strand; the “canonical replacement piece different from \(Q\)” predicate is also false.
- **Hypotheses satisfied:** This is the equality boundary of the fixed canonical order. It preserves all counts, profiles, baseline facts, and context responses, and it is exactly the conclusion stated at [166] and the premise named at [169].
- **Accumulated facts violated:** No cited accumulated fact excludes equality. The proof's phrase “not a proper configuration” is unsupported, and properness of the support \(X\subsetneq G\) does not imply \(E\ne Q\).
- **Applicability:** APPLICABLE TO THE SOURCE-LEVEL CONTRACT. It falsifies the lemma's stated exhaustive classification. It does not refute the intended overall strategy because the later graph already contains the correct equality destination.

### Graph-realizability test

- **Explicit data:** Let \(Q=x-a-b-y\) and \(E=x-c-d-y\) be two internally disjoint three-edge paths. Their union is the simple \(6\)-cycle \(x-a-b-y-d-c-x\). With a window path of length \(d_0=2\), the strand/window cycles each have length \(5\).
- **Hypotheses satisfied:** \(Q\) and \(E\) are distinct, same-length, use the same two attachments, and are internally disjoint; the locally visible cycles have lengths \(6\) and \(5\), so the bounded support itself has no power-of-two cycle.
- **Accumulated facts violated:** The four internal vertices have degree \(2\) in this test graph, violating node [2]. Degree-restoring attachments preserving the full exact response profile, target avoidance, maximal \(P_{13}\) packing, and dense residual were not constructed.
- **Applicability:** **NON-APPLICABLE TO THE NODE**, excluded first by node [2]. It confirms that the strengthened graph-realization predicate is sufficient to form the simple cycles consumed by [167].

### Branch-routing test

- **Explicit data:** Consider two abstract incoming germs. Candidate A has repeated-state provenance, \(E\ne Q\), and an ambient internally-disjoint embedding of \(E\) on the same boundary. Candidate B has repeated-state provenance and \(E=Q\). Both are neutral and have zero increment.
- **Hypotheses satisfied:** Both respect the stated cold-bounded provenance and neutral/equal-length data. A shows that “canonical” and “graph-realized” are not exclusive predicates; B is the manuscript's later trivial-neutral residual.
- **Accumulated facts violated:** No complete graph satisfying all upstream selected-counterexample facts is supplied. No accumulated logical clause forbids either overlap or equality; an actual realization may be eliminated only after all graph constraints are imposed.
- **Applicability:** APPLICABLE TO THE TYPED LOCAL ROUTING. Under the literal question, A deterministically takes the yes-edge despite also being canonical; B takes the no-edge and must bypass the assertion \(E\ne Q\). Therefore provenance cannot replace the \(P/\neg P\) decision, and the no-arm needs the explicit equality split.

## 5. Strongest valid counterexample

No finite simple graph satisfying the complete minimum-degree, target-avoidance, dense-packing, selected-minimality, and extracted-cold-family residual was constructed. The strongest source-level candidate is the equality boundary \(E=Q\). It satisfies the full neutral/equal-length boundaried contract, violates no stated upstream condition, and is not speculative: [166] explicitly concludes \(Q=E\), while [169] is labelled the “trivial neutral-configuration residual” with \(Q=E\). Nevertheless it belongs to neither kind in \`lem:neutral-germ-symmetry\`. Thus it is a direct counterexample to the lemma's “exactly one” wording, but not to the intended proof strategy, because an existing downstream destination handles it once the no-arm is stated as a conditional canonical route rather than as \(E\ne Q\) itself.

Candidate A from the branch-routing test is the strongest exclusivity stress test: canonical provenance is compatible with graph realization unless the definition declares the alternatives as tagged constructors or proves a no-embedding theorem. It shows why the proof's equality sentence cannot establish exclusivity.

## 6. Local repair

### Corrected statement

Let \(g\) be the actual active neutral zero-increment germ retained from [162], with representatives \(Q\) and \(E\) and its terminal-or-repeated first-failure provenance. Decide the literal predicate \(P(g)\) that \(E\) embeds in \(G\) on the same two boundary vertices with internal vertices disjoint from \(Q\)'s support.

If \(P(g)\), then \(Q,E\) are a genuine symmetric strand pair and the same \(g\) enters [167]. If \(\neg P(g)\), the terminal provenance is impossible, because its second completion strand supplies \(P(g)\); therefore the repeated-state provenance holds and \(E\) is the actual canonical cut-state representative. In this canonical arm, decide \(E=Q\). If \(E\ne Q\), enter [165]. If \(E=Q\), enter [166]/[169] directly. Do not call provenance alternatives exclusive, and either replace “terminal configuration” in the premise by “terminal-or-repeated cold first-failure configuration” or prove that the repeated-state case is included in the term “terminal” used here.

### Complete local proof

Fix the incoming germ \(g\). Classical excluded middle gives \(P(g)\lor\neg P(g)\), so the principal branch is exhaustive and disjoint by construction.

Assume \(P(g)\). The embedding agrees with \`g.pieceIntoAmbient\` on the two boundary vertices, maps every edge of \(E\) to an edge of \(G\), and sends the internal vertices of \(E\) outside \`g.support\`, which contains the interior of \(Q\). Hence \(Q\) and \(E\) are internally disjoint and meet at the same two attachments. Incoming neutrality and \(\delta(g)=0\) give equal length and identical target response. Retained offsets give \(0\le d\le12\), and the bounded exchange constant gives the finite strand-length range. These are exactly the geometric inputs of [167]; no claim about canonical provenance is needed on this arm.

Assume \(\neg P(g)\). Read the retained first-failure provenance. Its terminal disjunct includes a graph-realized second completion strand on the same interface and therefore implies \(P(g)\), a contradiction. The repeated-state disjunct must hold, and it identifies \(E\) with the canonical representative of \(Q\)'s retained cut-state. This supplies an actual boundaried graph piece with the same boundary profile and context response; it is not obtained merely by identifying labels.

Now apply equality decidability to the canonical pieces. If \(E\ne Q\), canonical minimality gives that \(E\) precedes \(Q\) in the fixed canonical order. Incoming equal length and exchange equivalence preserve \((|V|,|E|)\), the baseline, and target avoidance, while replacing the one canonical-decomposition atom strictly decreases \(\Phi\). This is the conditional [165] argument and yields [166]'s conclusion that the case cannot occur in the selected graph. If \(E=Q\), no strict decrease is available and none should be claimed; this is exactly the trivial neutral residual of [166]/[169]. The three final cases \(P(g)\), \(\neg P(g)\land E\ne Q\), and \(\neg P(g)\land E=Q\) are disjoint and exhaustive.

### Counterexample disposition

The \(E=Q\) boundary candidate is no longer deleted by the symmetry lemma. It takes \(\neg P(g)\), is recognized as the repeated-state canonical case, and then takes the equality edge directly to [166]/[169]. A distinct canonical representative that is also ambiently graph-realized takes \(P(g)\) and goes to [167]; this is harmless because [167] needs the geometric witness, not noncanonical provenance. The local \(6\)-cycle example is still excluded as a full residual by minimum degree but correctly illustrates the yes contract.

### Graph patch

Use the already intended literal question and expose the equality subdecision:

~~~text
[162] -- exists an actual active neutral zero-increment germ g --> [163]
[163] -- yes: P(g), internally-disjoint ambient realization --> [167]
[163] -- no: not P(g); repeated-state provenance, E canonical --> [163a]
[163a] -- no: E != Q --> [165]
[163a] -- yes: E = Q --> [166] / [169]
~~~

Alternatively [165] may remain on the no-edge if its label and statement are changed to the conditional “canonical case: if \(E\ne Q\), refined minimality contradicts selection; hence \(E=Q\),” making [165]--[166] one implication rather than asserting \(E\ne Q\) at entry.

### Downstream impact

The proof-flow node label can remain the literal graph-realization question, but \`lem:neutral-germ-symmetry\`, the Part XII caption/overview, the [165] node label, and the detailed dependency row must agree on the equality subcase. Node [167] should consume an explicit internally-disjoint embedding and the same germ. Nodes [166] and [169] must receive \(E=Q\) rather than derive it after an edge whose contract already asserted \(E\ne Q\). The absorbed F5 reuse at [176] must retain the same repaired trichotomy.

In Lean, the yes predicate already includes the needed embedding and zero increment. The no fact should be strengthened from \`ColdGermCandidatesStatement ∧ ¬ GenuineSecondStrandStatement\` to an existential selected germ \(g\) with \`ActiveColdGermStatement\`, \`g.Neutral\`, \`g.increment = 0\`, \`¬ SecondStrandGraphRealizedStatement data g\`, and the repeated-state equality identifying \`g.canonical\` with \`germCanonicalRepresentative data g\`. The subsequent equality/canonical-order decision must be about that same \(g\). These are recommendations only; no proof, diagram, Lean, or audit source is changed here.

## 7. Regression audit

The audit inspected every direct and repeated source use found for node [163]:

- \`to_formalize/erdos_64_proof.tex\`: the Part XII node and edges; dependency rows at lines 1229 and 1554; \`def:cold-bounded-germ\`; \`def:cold-corridor-first-failure\`; \`lem:cold-same-interface-table\`; \`lem:dense-cold-pass\`; \`def:neutral-equal-length-germ\`; \`lem:neutral-germ-symmetry\`; \`lem:refined-minimality-swap\`; \`lem:two-strand-check\`; \`lem:symmetric-pair-endpoint\`; the [169] trivial residual; and the dense-residual closing summary.
- The proof-flow JSON and generator text for nodes [162], [163], [165]--[169]. The only incoming edge is \`[162] -> [163]\`; the outgoing edges are the no-edge to [165] and yes-edge to [167]. The graph already continues [165] to [166] and [166] to [169].
- \`Graph/ColdCorridor.lean\`: \`BoundedGerm\`, \`Neutral\`, \`increment\`, \`TableRow\`, \`TerminalColdResidual\`, and the terminal/repeated provenance retained by the corridor state.
- \`Graph/CanonicalRealization.lean\`: \`CanonicalPiece\`, \`cutStateRepresentative\`, \`cutStateRepresentative_size_le\`, \`glue_swap_target_iff\`, \`glue_swap_baseline\`, and \`toCanonical_eq_or_precedes\`.
- \`Strategy/SpineVocabulary.lean\`: \`SecondStrandGraphRealizedStatement\`, \`ColdCorridorStateStatement\`, \`ColdGermCandidatesStatement\`, \`ActiveColdGermStatement\`, \`germCanonicalRepresentative\`, \`GenuineSecondStrandStatement\`, and \`CanonicalNeutralConfigurationStatement\`.
- \`Strategy/ColdCorridorRows.lean\`: \`coldSameInterfaceTableRow\`, \`coldBranchClosedRow\`, \`neutralGermSymmetryDichotomy\`, and \`canonicalSwapSizeDichotomy\`.
- Both live Assembly call sites, in \`selectedAbsorbedGermResidual\` and the dense \`.right\` arm of \`selectedNearCubicBranch\`. Both call the same decision and then route no to the canonical swap size decision and yes to the two-strand frontier.
- \`Assembly_node_audit.md\` and \`EG_LEAN_COMPLIANCE_REMAINING.md\` were inspected only as locators. Their status rows disagree because the latter is stale; neither status assertion was used as mathematical evidence. The current code, not either status label, was audited.
- The repeated absorbed-germ use at [176], whose statement cites \`lem:neutral-germ-symmetry\` together with [165]--[168], was found and checked as a downstream regression candidate.

The principal searches were:

~~~text
rg -n 'def:neutral-equal-length-germ|lem:neutral-germ-symmetry|neutral equal-length terminal|second strand graph-realized' to_formalize web
rg -n 'SecondStrandGraphRealizedStatement|GenuineSecondStrandStatement|CanonicalNeutralConfigurationStatement|germCanonicalRepresentative' hypostructure
rg -n 'neutralGermSymmetryDichotomy|coldCanonicalNeutralConfiguration|coldGenuineSecondStrand' hypostructure proofs
rg -n 'word for word|verbatim|unchanged|same proof' to_formalize/erdos_64_proof.tex
~~~

The dossier's reverse item-dependency search reports no additional direct dependent item for \`def:neutral-equal-length-germ\`. No second manuscript definition of the realization predicate was found; its precise internal-disjointness content presently appears only in Lean.

## 8. Residual uncertainty

No complete graph realizing the full node-[163] residual was found, so the report does not claim a counterexample to the Erdős--Gyárfás theorem or a \`VALID LOCAL COUNTEREXAMPLE\`. The manuscript does not formally define “genuine,” “proper configuration,” or graph realization at this node, leaving open whether the authors intended distinctness and internal disjointness as part of those words. It also does not prove in this section that the retained first-failure provenance is tied to the same neutral germ selected on the incoming edge; that witness retention is essential to the repaired no-arm. Finally, the downstream refined \((|V|,|E|,\Phi)\) minimality and two-strand consumers have independent proof obligations not decided by this node audit. No manuscript, diagram, Lean, implementation-audit, or coverage-ledger source was changed.
