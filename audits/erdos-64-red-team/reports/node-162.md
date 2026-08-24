<!-- red-team-audit
{
  "schema_version": 1,
  "proof": "erdos-gyarfas",
  "node": 162,
  "node_label": "dense hot/cold pass: run [22]--[24] and [145]--[157] on the dense residual; [23], [149], [155], [156], [157] close as before; bounded arm of [153] and [146]/[160] arms return to [25]",
  "panel": "fig:proof-diagram-part-xii",
  "contract_sha256": "69233163d8593ddd9ce6a86dc2ee5d3ed5602c3969b35a452923aafc5a928511",
  "manuscript_sha256": "106a8205a1718fbf90e1686a107b2143b9edca574e2b0c11415e7f44aee2c0f9",
  "graph_sha256": "dc67fae178f947a9607c167e383d85919633341bdd423e4c4a45e4c317b3a765",
  "lean_audit_sha256": "50324ef5594d635a52d83aeb297f2ca3f3d30ef58de4ce3602816c7e78365b12",
  "verdict": "PROSE AMBIGUITY",
  "audited_at": "2026-08-24T21:08:28Z"
}
-->

# Red-team audit: node [162]

## 1. Executive verdict

Verdict: **PROSE AMBIGUITY**

Node [162] gives incompatible contracts for the equal-length cold row. Its box says that [157] “closes as before,” while its only non-entropy outgoing edge is explicitly labelled `[157] neutral row` and leads to [163]. The source makes the intended correction identifiable: `def:admissible-rank-quotient` says that a context-equivalent identification without a smaller graph representative is only an abstract label symmetry, and `def:neutral-equal-length-germ` sends exactly that symmetry to [163]. Thus [162] is valid only when “the [157] closure” means the realizing, distinguishing, handoff, and explicitly represented compression rows, with the neutral non-admissible complement retained as an actual extracted germ. The present Lean route is weaker still: its no-second-strand arm retains only a nonempty candidate family and the absence of a genuine second strand, not the existence of any neutral zero-increment germ. The smallest proof-preserving repair is to state the carve-out and strengthen the [163] edge contract; no new proof branch is needed.

## 2. Exact node contract

### Incoming residual

The unique incoming edge is the `no` arm `[160] -> [162]`; there is no merge and no loop. Work with the selected lexicographically minimal finite simple graph (G) of minimum degree at least (3) having no power-of-two cycle. Let (n=|V(G)|), let (mathcal P) be the fixed canonical maximal vertex-disjoint induced-(P_{13}) packing, put (p_{13}=|mathcal P|), and write (	heta=p_{13}/n).

The edge retains node [159]'s dense-package overflow as an incoming fact and the literal complement of node [160]'s exact deficiency comparison. In manuscript notation this complement is the finite-with-allowances version of

\[
\tau(\theta)=\frac{15\theta}{1-13\theta}\ge \frac14.
\]

This audit treats those predicates as the selected incoming state and does not use any conclusion from a different audit of [159]. The node then re-runs the fixed packing's hot/cold classification and must restrict every use of the cold lemmas to the surviving-cold subbranch: no target cycle, target-defective quotient, unpaid exit-(4), untransferred Type B/route-8 handoff, or previously constructed compression remains active. If one of those outcomes occurs during the pass, its data must be transferred to the named destination rather than erased.

### Accumulated facts

The complete common state available before the local pass is:

1. Nodes [1]--[6]: (G) is a selected minimal counterexample, and every oriented edge has the retained return-avoidance condition.
2. Nodes [8]--[10]: no proper subgraph has minimum degree (3); every edge has a degree-(3) endpoint; and (V_{\ge4}(G)) is independent.
3. Nodes [11]--[14]: boundary-degree fibres are fixed; target-completeness is universal over compatible contexts; replacement requires an actual qualifying smaller graph; and no proper support has such a target-complete compression.
4. Nodes [15], [17], and [18]: (G) is not induced-(P_{13})-free, (mathcal P) is the fixed maximal packing, and its (399)-label algebra and relations (C_s) are retained.
5. The selected no-arm of [19] and node [21]: the near-cubic surplus estimate, skeleton bound, separated package, and certified (c_{13}) enumeration are retained.
6. Nodes [158]--[160]: the selected dense-package predicate and the exact at-or-above deficiency predicate are retained on the same object.
7. On each internal cold-pass route, [22]/[145] supplies the hot/cold partition; [146] tests the route-8 rate; [148] tests live-hot overflow; [150] supplies cold mass; [151] and [152] supply ambient-cubic and branch-excess bounds; and [153] makes the exact finite linear/bounded split. The linear arm supplies actual return corridors, first failures, and a positive extracted family of bounded germs.
8. On that linear arm, realizing germs are excluded by target avoidance, distinguishing germs are transferred to the target-defect ledger, declared handoffs are transferred to their Type B or route-8 ledgers, and a silent length-changing germ has an explicit shorter representative. None of these facts implies that an equal-length neutral identification has a strictly smaller graph representative.

The literal Lean ledger before the dense decision contains the common keys

```text
[densePackingOverflow, windowPackageUnrealized, skeletonDominates,
 windowPackageSeparated, barrierEnumeration, surplusAtOrBelow,
 localAlgebra, maximalPacking, uncompressible, replacementExclusion,
 targetCompleteContextUniversality, degreeProfileFibres, tightEndpoint,
 slackIndependent, noProperBaseline, returnAvoidance, selection].
```

The implementation then appends `hotColdPartition` and the selected deficiency arm, followed on the cold linear route by `coldGermCandidates`, the trichotomy/table facts, and `coldBranchClosed`. These facts are useful contract evidence, but they do not themselves retain an existential neutral equal-length member of the extracted family.

### Current predicate and exact claim

The intended implication is a case split:

\[
F(162)+\neg\mathrm{DenseDeficiencyBelow}
\Longrightarrow
\begin{cases}
\text{one of the already named hot/cold closures or routed ledgers},\\
\text{an actual neutral equal-length extracted germ for [163]},\\
\text{or the active all-cold entropy comparison for [164]}.
\end{cases}
\]

On the linear cold arm, the [163] alternative must have the existential payload

\[
\exists g\in\mathcal F_{\rm ext},\qquad
g\text{ is nonrealizing and nondistinguishing},\quad
\delta(g)=0,
\]

together with its proper connected bounded support, the two actual same-interface representatives (Q,E), their common boundary-degree profile and baseline, and their context equivalence. This is the object on which [163] can ask whether (E) is graph-realized as a genuine second strand.

The printed claim “[157] closes as before” contradicts that payload. `lem:cold-same-interface-table` claims that every equal-length row closes by compression, but its proof obtains no smaller representative; `def:admissible-rank-quotient` instead says that without one the identification is non-admissible and reduces no graph-realizable rank. Node [163] is precisely the intended residual of that failure.

### Outgoing contracts

- `[162] -> [163]`, labelled `[157] neutral row`, must retain an actual germ (g\in\mathcal F_{\rm ext}), (delta(g)=0), nonrealization, nondistinguishability, no already declared handoff, the two same-interface representatives, and all boundary/baseline/context data. Node [163] then decides whether that same germ has a graph-realized second strand.
- `[162] -> [164]`, labelled `[53] active`, must retain (mathcal P_{\rm hot}=\varnothing), the active remainder entropy comparison, the fixed glue data, inherited edge count and net-deficiency numerator, and the skeleton class required by `lem:remainder-glue-injection`.
- Realizing, distinguishing, handoff, route-8, and explicit-compression outcomes are not residuals for [163] or [164]. They must terminate or reach their already named ledgers with their witnesses and charge intact. The bounded arm of [153] retains the exact density cap and returns to [24]/[25] as stated.

The current Lean predicate for the no-second-strand arm is only

```text
ColdGermCandidatesStatement data object ∧
  ¬ GenuineSecondStrandStatement data object
```

so it does not meet the first outgoing contract: all candidates could be distinguishing or length-changing, making the second conjunct true without any neutral equal-length germ.

## 3. Sentence audit

| Sentence | Exact assertion | Facts used | Hidden obligation | Adversarial test | Status |
|---|---|---|---|---|---|
| S1 | On the dense (	au\ge1/4) arm, [22] and [145]--[157] can be executed unchanged. | Fixed packing, near-cubic state, return avoidance, replacement ledger. | Every cold lemma requiring `def:surviving-cold-branch` must either receive its exclusions or route a newly active exit. | Compare the graph ancestry with the six clauses of `def:surviving-cold-branch`. | AMBIGUOUS |
| S2 | The pass does not consume the density sentence. | The listed inputs to first-failure routing and the literal Lean rows. | No later internal closure may silently read `densityCap`. | Traced the dense linear route through the literal ledger. | SUPPORTED |
| S3 | Live-hot overflow, route-8, bounded-mass, target-hit, target-defect, handoff, and explicit compression outcomes are handled as on the spine. | [23], [146]--[157], surviving-cold routing. | A routed defect or handoff is not itself a contradiction; its witness and charge must reach the named ledger. | Inspected F1--F5 and G1--G3 destination contracts. | ROUTING ONLY |
| S4 | The boundaried pieces of (R) are induced-(P_{13})-free and subcubic, hence bounded diameter. | Maximal packing; removal of high-degree candidate supports. | Subcubicity is proved for remaining candidate supports, not stated for every whole remainder component. | Let a return corridor pass a degree-(ge4) vertex; it should trigger F4 rather than become terminal. | AMBIGUOUS |
| S5 | Every surviving return corridor is in the terminal F5 subcase. | S4. | Long corridors with repeated states are F5-repeat, not terminal; the proof must not discard them. | Take a corridor longer than (Q_{\rm cold}) with its first repeated cut state. | AMBIGUOUS |
| S6 | The only nonrefuted cold outcome is a neutral equal-length terminal configuration. | Positive extracted family; target avoidance; defect/handoff routing; length-changing compression. | One must select an actual member and retain neutrality and (delta=0) after eliminating all other cases. | Use a one-element extracted family and exhaust its realizing/distinguishing/increment cases. | SUPPORTED WITH MISSING EXPLICIT PAYLOAD |
| S7 | “[157] closes as before.” | `lem:cold-same-interface-table`. | A neutral equal-length row needs an actual smaller representative before replacement can close it. | Keep T1--T4 and context equivalence but no graph-realizable rank reduction. | FAILED |
| S8 | The [157] neutral row survives to [163]. | Part XII edge; `def:neutral-equal-length-germ`. | This is the complement of S7 and requires the actual retained germ. | Compare the edge label with the [157] terminal label and theorem. | SUPPORTED AS THE INTENDED READING |
| S9 | The only other residual is the active all-cold comparison. | Hot/cold partition and [53] comparison. | The branch must retain (mathcal P_{\rm hot}=\varnothing) and the remainder glue class. | Read `def:all-cold-comparison` and `lem:remainder-glue-injection`. | SUPPORTED |
| S10 | Lean's no-genuine-strand branch realizes the [163] contract. | `ColdGermCandidatesStatement`; negation of `GenuineSecondStrandStatement`. | Nonempty candidates plus absence of a genuine strand must imply existence of a neutral zero-increment candidate. | Make the sole candidate target-distinguishing with increment (-1). | FAILED |

## 4. Counterexample attempts

### Smallest-parameter test

- **Explicit data:** Let the bounded interface be (T=\{x,y\}), and take two distinct internally disjoint (x)-(y) strands (Q=x-a-b-y) and (E=x-c-d-y), each of length (3). Their union is a (6)-cycle, not a power-of-two cycle. Give them the same boundary-degree vector, cold offsets, and exact target-response record.
- **Hypotheses satisfied:** The support is bounded and proper in an abstract ambient object; (|Q|=|E|), so (delta=0); swapping the strands preserves every path-completion length and hence the power-of-two response against those contexts.
- **Accumulated facts violated:** As a standalone graph the four internal vertices have degree (2), so it fails node [2]'s ambient minimum-degree-three condition; no full maximal-packing or dense-residual realization is supplied.
- **Applicability:** **NON-APPLICABLE TO THE NODE** as an actual graph, first excluded by node [2]. It is a smallest concrete demonstration that equal length and context equivalence do not create a strictly smaller representative and therefore cannot justify the phrase “[157] closes.”

### Parity or 2-adic test

- **Explicit data:** Take the short-return length (ell=17). Its full thirteen-offset smear is ([17,29]), which contains no power of two. Repeat the test at (ell=18), whose smear ([18,30]) also contains no power of two. Thus both odd and even starting parities reach the exceptional finite table rather than G1.
- **Hypotheses satisfied:** Every offset (0,\ldots,12) has been checked in the integers; no reduction modulo an odd factor is used and no 2-adic compatibility is omitted.
- **Accumulated facts violated:** The length datum alone does not construct a minimum-degree-three, target-avoiding graph satisfying nodes [2]--[160], nor an actual extracted corridor row of that graph.
- **Applicability:** **NON-APPLICABLE TO THE NODE** as a graph candidate, first for lack of node [2]'s selected counterexample. It confirms that parity cannot remove all neutral/exceptional table inputs before [162].

### Boundary or range test

- **Explicit data:** Let (g) be an actual T1--T4 bounded-germ record with (delta(g)=0), no realizing completion, no declared handoff, and no compatible context distinguishing (Q) from (E). Do not assume a strictly smaller proper representative. This is the exact equality boundary between the length-changing trichotomy and the same-interface table.
- **Hypotheses satisfied:** Bounded support, the same interface and boundary-degree profile, equal length, exact context equivalence, and the selected neutral complements. By `def:admissible-rank-quotient`, the identification is merely abstract when no smaller representative exists.
- **Accumulated facts violated:** None at the exact response-profile level. No complete graph realizing the entire cumulative residual was constructed, but the missing smaller representative is not an accumulated hypothesis.
- **Applicability:** APPLICABLE TO THE LOCAL CONTRACT. It is the branch that the outgoing edge calls `[157] neutral row`; it falsifies the unqualified “[157] closes” clause and is correctly assigned to [163] under the intended reading.

### Graph-realizability test

- **Explicit data:** Realize the smallest-parameter strands as the simple (6)-cycle (x-a-b-y-d-c-x). For any additional (x)-(y) path of length (s), either strand creates the same cycle length (s+3), so the pair is graph-level context-equivalent for path completions.
- **Hypotheses satisfied:** Two genuine, distinct, internally disjoint equal-length strands; a simple bounded support; no power-of-two cycle inside that support; and a graph-realized second strand.
- **Accumulated facts violated:** The internal vertices have degree (2), violating node [2]. Adding degree-restoring attachments without creating a power-of-two cycle or changing the retained packing and response profile was not established.
- **Applicability:** **NON-APPLICABLE TO THE NODE**, excluded first by node [2]. No actual minimal-counterexample graph satisfying the complete node-[162] residual was found.

### Branch-routing test

- **Explicit data:** At the manuscript level, select a neutral (delta=0) row with no smaller representative. At the Lean-schema level, separately take a one-element extracted family (mathcal F=\{g\}) whose sole germ has (delta(g)=-1), is nonrealizing and target-distinguishing, and has no graph-realized second strand.
- **Hypotheses satisfied:** The manuscript row satisfies the `[157] neutral row` source predicate. The Lean family satisfies `ColdGermCandidatesStatement` and the negation of `GenuineSecondStrandStatement`; a distinguishing negative-increment germ is compatible with `coldGermRouted` and with `coldBranchClosed`, whose terminal-family predicate requires *nondistinguishing* length-changing germs.
- **Accumulated facts violated:** No full graph model of the one-element Lean schema is supplied. The manuscript neutral row violates no logical upstream exclusion; it simply lacks the conclusion's smaller-representative witness.
- **Applicability:** The manuscript row is APPLICABLE TO THE NODE'S SOURCE-LEVEL ROUTING and must go to [163], not immediate [157] compression. The one-element family is **NON-APPLICABLE TO THE NODE** as a concrete graph, first because node [2]'s full graph predicate is unverified, but it is an exact countermodel to the current Lean [163] entry predicate: that predicate can be true while no neutral germ exists.

The modular checker was not run because [162] makes no inference from an orbit modulo a factor of an increment to an integer in a finite arithmetic progression. The relevant equality and smear endpoints were checked directly above.

## 5. Strongest valid counterexample

No finite simple graph satisfying the complete minimal-counterexample, dense-packing, exact-deficiency, packing, and cold-ledger state was constructed. The strongest source-level candidate is the neutral equality-boundary row: an actual extracted bounded configuration with (delta=0), no hit, no handoff, context-equivalent representatives, and no strictly smaller graph representative. It violates no response-profile or minimality fact. Rather, minimality is inapplicable until the representative exists. This candidate does not refute the intended node-[162] route because [163] is exactly where it belongs; it refutes the simultaneous claim that [157] already closes it. The strongest formal candidate is the one-element distinguishing family, which shows that the present Lean no-second-strand predicate does not even certify the neutral-row premise of [163].

## 6. Local repair

### Corrected statement

On the dense-packing residual with the exact complement of node [160]'s deficiency comparison, run the hot/cold split and the cold first-failure pass using the retained packing, near-cubic, return, and replacement facts. The live-hot overflow, route-8, bounded-mass, target-hit, target-defect, declared handoff, and explicitly represented compression cases retain their existing destinations. On the linear arm, choose a member of the positive extracted germ family. If every closing or routed case is excluded and the chosen germ is equal-length, retain that actual neutral germ and route it to [163]. In particular, [157] closes only those neutral table rows for which an explicit strictly smaller proper representative is available; a neutral row with no such representative is an abstract symmetry and is the [163] residual. Independently, if (mathcal P_{\rm hot}=\varnothing) and the remainder comparison [53] is active, retain its glue data and route it to [164]. These are the only two nonclosed outcomes.

### Complete local proof

Run the exact decisions in their displayed order. A live-hot overflow is closed by the package-to-skeleton comparison. On the complementary hot cap, decide the route-8 inequality; its strict arm enters the already proved route-8 response-support closure. If the cold-mass comparison is bounded, `densityBudgetRow` supplies the exact density cap and the route returns to [24]/[25]. Thus only the linear cold-mass arm remains.

On that arm, the retained branch-excess inequality and extraction theorem give a positive finite disjoint family (mathcal F_{\rm ext}) of actual bounded first-failure germs. Choose (g\inmathcal F_{\rm ext}). If (g) is realizing, its live completion is a power-of-two cycle and [155] closes. If (g) first enters a declared Type B or route-8 interface, transfer its retained interface and charge to that ledger. If a compatible context distinguishes its two representatives, context-universality supplies the target-defect route [156].

Suppose none of those cases holds. Then (g) is neutral. If (delta(g)\ne0), orient (Q,E) so the shorter one is the replacement. It has the same boundary-degree profile and target response in every context, and gluing it into the actual complement strictly decreases the selected graph; replacement and hereditary uncompressibility close this case. Hence every still-live (g) has (delta(g)=0).

Now decide whether this equal-length neutral identification has an explicit strictly smaller representative satisfying all clauses of `def:proper-quotient-representative`. On the yes arm, replacement closes it. On the no arm, `def:admissible-rank-quotient` says the identification reduces no graph-realizable rank; no contradiction follows. Retain (g), its extracted-family membership, support, two representatives, boundary profile, baseline, equality of lengths, and context equivalence. This is exactly `def:neutral-equal-length-germ`, so route it to [163]. The positivity of (mathcal F_{\rm ext}) ensures that the residual is existential rather than an empty verbal case.

The entropy comparison is independent of that local choice. If its hot family is empty and [53] remains active, retain the remainder class and glue constraints and route to [164]. Otherwise the realized hot-family comparison is among the already handled hot/cold outcomes. Consequently the only nonclosed residuals are the typed neutral witness at [163] and the typed all-cold comparison at [164].

### Counterexample disposition

The neutral equality-boundary candidate is no longer asserted to compress. If an explicit smaller representative is found, it is closed by replacement; otherwise it is retained at [163], where a distinct canonical piece is handled by the refined same-size order and a genuine second strand is handled by the two-strand/endpoint route. The one-element distinguishing Lean family is sent to the target-defect ledger and cannot satisfy the repaired [163] predicate because it has no neutral zero-increment member.

### Graph patch

Keep the two displayed destinations but repair the predicates and the elided routes:

```text
[160] -- exact no-arm --> [162]
[162] -- live-hot / route-8 / bounded-mass --> existing [23], [147], [24]/[25] routes
[162] -- realizing F5/G1 --> [155]
[162] -- distinguishing F2/G2 or declared handoff --> [156] / exact retained ledger
[162] -- neutral length-changing or neutral + explicit smaller representative --> [157 compression]
[162] -- exists g in the actual extracted family:
         Neutral(g) and increment(g)=0 and no smaller representative --> [163]
[162] -- P_hot = empty and [53] active, with remainder glue data --> [164]
```

Relabel the first displayed edge from `[157] neutral row` to `neutral equal-length F5 row not closed at [157]`, or redefine [157] as the table decision rather than a terminal compression. Delete “[157] close as before” from the [162] node label. Every routed edge must retain its actual witness and charge.

### Downstream impact

The Part XI caption, `lem:cold-same-interface-table`, `lem:cold-increment-arithmetic` case (d), `thm:cold-branch-quantitative-closure`, the Part XII node label/edge, the detailed dependency rows, and `rem:dense-residual-status` must use the same neutral-row carve-out. Nodes [163]--[172] keep their intended strategy but must receive an actual selected neutral germ, so their statements cannot be satisfied vacuously.

In Lean, introduce a semantic key such as

```text
∃ g, ActiveColdGermStatement data object g ∧
  g.Neutral ∧ g.increment = 0
```

and require it at `neutralGermSymmetryDichotomy`. Strengthen `CanonicalNeutralConfigurationStatement` from `ColdGermCandidatesStatement ∧ ¬ GenuineSecondStrandStatement` to this existential neutral fact plus the literal no-genuine predicate, tied to the selected germ or formulated as an exhaustive existential split. `TableRow.admissible` currently assumes the missing strict-decrease witness and therefore represents only the closable subtable; its documentation, `coldSameInterfaceTableRow`, `coldBranchClosedRow`, and the node-[162] assembly route must not use it to erase the non-admissible neutral complement. The implementation-audit tables should be synchronized after the proof contracts are repaired. No such source change is made in this report.

## 7. Regression audit

The audit inspected the following repeated uses and consumers:

- Part XI nodes [145]--[157], its caption, the finite-table definition, `lem:cold-same-interface-table`, `lem:cold-increment-arithmetic`, and `thm:cold-branch-quantitative-closure`.
- Part XII nodes [159]--[172], both outgoing edges of [162], its caption, `def:neutral-equal-length-germ`, `lem:neutral-germ-symmetry`, `lem:refined-minimality-swap`, `lem:two-strand-check`, `lem:symmetric-pair-endpoint`, `def:all-cold-comparison`, and `lem:remainder-glue-injection`.
- The detailed dependency entries for the hot/cold and dense-packing blocks, `rem:dense-residual-status`, and the small-order repair [173]--[177]. The exact [153] split avoids a new finite-(n) gap at [162]; the small-order repair concerns the separate [56]/[173] collision route.
- `Graph/ColdCorridor.lean`: `BoundedGerm`, `TableRow`, `row_closed`, `selfReturn_closed`, `TerminalColdResidual`, and `noTerminalColdResidual_of_routing`.
- `Strategy/SpineVocabulary.lean`: `ColdGermCandidatesStatement`, `ActiveColdGermStatement`, `GenuineSecondStrandStatement`, and `CanonicalNeutralConfigurationStatement`.
- `Strategy/ColdCorridorRows.lean`: the exact [153] decision, germ extraction/trichotomy, same-interface table, `coldBranchClosedRow`, and `neutralGermSymmetryDichotomy`.
- The dense `.right` arm of `selectedNearCubicBranch` in `Assembly.lean`, including its literal ledger and comments admitting that no object is yet available for the node-[163] arms.
- The relevant human and JSON implementation-audit rows. They were used only as locators; their status assertions were not treated as mathematical authority.

The principal searches were

```text
rg -n 'lem:dense-cold-pass|neutral equal-length|only outcome not refuted|lem:cold-same-interface-table|thm:cold-branch-quantitative-closure|small-order' to_formalize/erdos_64_proof.tex
rg -n 'coldBranchClosedRow|coldSameInterfaceTableRow|neutralGermSymmetry|CanonicalNeutralConfigurationStatement|GenuineSecondStrandStatement|ColdGermCandidatesStatement' hypostructure proofs
rg -n 'word for word|same proof|analog' to_formalize/erdos_64_proof.tex hypostructure proofs
```

No additional “word for word,” “same proof,” or analogous invocation of `lem:dense-cold-pass` was found. The absorbed-germ route [176] cites both the table and nodes [165]--[168], so it must be checked after the same neutral contract is repaired, but it is not an incoming fact at [162].

## 8. Residual uncertainty

No complete minimum-degree-three, power-of-two-cycle-free graph realizing the neutral row and every dense node-[162] input was constructed, so this report does not claim a valid local graph counterexample. The manuscript does not enumerate the finite same-interface table, leaving open whether an additional row-specific fact could construct a smaller representative, although no such fact is stated or retained. The assertion that every relevant boundaried piece of (R) is subcubic was not found as a standalone producer; the first-failure F4 route can handle a high-degree encounter, but the proof should say so. It also remains to verify, after strengthening the [163] entry, that the same selected germ is preserved through the canonical-piece/genuine-strand split and every later node [165]--[172]. No manuscript, diagram, Lean, implementation-audit, or coverage-ledger source was changed.
