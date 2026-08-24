<!-- red-team-audit
{
  "schema_version": 1,
  "proof": "erdos-gyarfas",
  "node": 157,
  "node_label": "G3 or same-interface\\\\table: compression",
  "panel": "fig:proof-diagram-part-xi",
  "contract_sha256": "49dc67d480c930dd9c513fef7fb02d7232affa7fa331283adc56dfce6d25d24e",
  "manuscript_sha256": "106a8205a1718fbf90e1686a107b2143b9edca574e2b0c11415e7f44aee2c0f9",
  "graph_sha256": "dc67fae178f947a9607c167e383d85919633341bdd423e4c4a45e4c317b3a765",
  "lean_audit_sha256": "50324ef5594d635a52d83aeb297f2ca3f3d30ef58de4ce3602816c7e78365b12",
  "verdict": "MISSING REPRESENTATIVE",
  "audited_at": "2026-08-24T21:00:52Z"
}
-->

# Red-team audit: node [157]

## 1. Executive verdict

Verdict: **MISSING REPRESENTATIVE**

The length-changing G3 part of node [157] is supported: one of its two same-interface representatives is strictly shorter, so that representative is an explicit candidate for the replacement lemma.  The finite-table part is not.  For a neutral equal-length row, 
`def:cold-same-interface-table` records only the boundary profile, stubs and offsets, exact response profile, and completion truth values.  Neither those data nor target-completeness construct a strictly smaller graph representative satisfying `def:proper-quotient-representative`.  The proof's appeal to `def:admissible-rank-quotient` reverses its logical direction: that definition says a proper-support quotient *without* a smaller graph representative is not an admissible rank reduction; it does not make every neutral identification admissible or supply a representative.  Thus the terminal compression assertion is missing precisely the witness required by `lem:replacement`.  This is a local gap, not a claimed counterexample to the whole theorem.

## 2. Exact node contract

### Incoming residual

The live edge is `[154] -> [157]`, tagged `G3/finite`.  It carries a lexicographically minimal finite simple graph (G) with (delta(G)ge 3) and no power-of-two cycle; the edge-rooted return avoidance, no-proper-(3)-core condition, edge-deletion criticality, independence of (V_{\ge4}(G)), boundary-degree fibres, context-universality, replacement lemma, and hereditary target-uncompressibility have all been retained.  It also carries the fixed maximal induced-(P_{13}) packing, the (399)-label algebra, the near-cubic spine, node [158]'s selected realization arm, and node [22]'s hot/cold partition.

On the selected cold path, `[146]` has retained the literal no-predicate (	heta\ge 1/78); `[148]` has retained failure of the live-hot closure; `[150]` has established (C\ge(\theta-\theta_{\rm win})n-o(n)); `[151]` has removed only the (o(n)) non-ambient-cubic windows; `[152]` has established (b(\mathfrak S_{\rm cold})\ge 13C-o(n)); and the selected `linear` arm of `[153]` carries a positive extracted family of actual first-failure bounded configurations together with the corridor, bounded-support, overlap, and charge data.  G1 realizations, G2 target defects, previously declared Type B/route-8 handoffs, and already constructed proper-support compressions are excluded or transferred by the surviving-cold ledger.

The `G3/finite` tag is a tagged union, not an intersection:

1. **Length-changing G3:** an extracted bounded configuration has (delta\ne0), is not realizing, and no compatible context distinguishes its representatives.  After orienting the pair, the shorter representative is explicit.
2. **Finite-table:** the extracted configuration has (delta=0), or is one of the short self-return exceptions.  A table row retains (T1) the two boundary vertices and boundary-degree profile, (T2) terminal stubs and offsets, (T3) the exact declared response profile, and (T4) completion truth values.  The row may be realizing, handed off, distinguishing, or neutral.  No incoming fact says that a neutral equal-length row has a strictly smaller graph representative.

### Accumulated facts

The manuscript facts available at this node are:

- `[1]`--`[6]`: (G) is a selected minimal counterexample and every oriented edge avoids the Mersenne return set.
- `[8]`--`[14]`: no proper subgraph has minimum degree three; every edge meets a degree-three vertex; (V_{\ge4}(G)) is independent; all quotient comparisons remain in one boundary-degree fibre; target-completeness is universal over compatible contexts; and only an *actual* strictly smaller, at-most-as-obstructing representative can invoke replacement and hereditary uncompressibility.
- `[15]`--`[22]` and `[158]`: the fixed maximal induced-(P_{13}) packing, label algebra, near-cubic spine, joint-package realization predicate, and selected hot/cold comparison.
- `[145]`--`[153]`: the selected threshold and entropy complements, cold mass, ambient-cubic reduction, (13C-o(n)) branch-excess supply, the exact linear branch, return corridors, first failures, and a positive disjoint bounded-configuration family.
- `[154]`: the G1/G2/G3 split for length-changing configurations, plus the finite (delta=0)/short-return case; G1 is forbidden, G2 is transferred to the defect ledger, and a silent length-changing pair has an explicit shorter member.
- The retained exclusion ledger: no target cycle, no live target defect, no unpaid exit-(4) peel, no untransferred Type B or route-8 handoff, and no already constructed nontrivial target-complete compression.

The literal Lean input ledger at `Assembly.lean:938` retains, in order, `coldGermRealized`, `coldGermDistinguished`, `coldGermSilent`, `coldGermRouted`, `coldGermCandidates`, `coldExchangeBound`, `coldGermExtraction`, `coldCorridorState`, the four first-failure routing facts, `coldFailureRouting`, `coldReturnCorridors`, `bridgeless`, `coldMassLinear`, `coldStubExcess`, `coldAmbientCubic`, `coldMass`, `coldHotEntropyCap`, `coldRoute8AtOrAbove`, `barrierCap`, `hotColdPartition`, `windowPackageRealized`, `skeletonDominates`, `windowPackageSeparated`, `barrierEnumeration`, `surplusAtOrBelow`, `localAlgebra`, `maximalPacking`, `uncompressible`, `replacementExclusion`, `targetCompleteContextUniversality`, `degreeProfileFibres`, `tightEndpoint`, `slackIndependent`, `noProperBaseline`, `returnAvoidance`, and `selection`.  Lean is only contract evidence here: its `TableRow.admissible` field already assumes the missing strict-decrease witness and therefore narrows the manuscript's T1--T4 row class.

### Current predicate and exact claim

The exact intended implication is:

> accumulated cold residual + selected `G3/finite` tag + an actual extracted row/configuration  
> (Longrightarrow) a power-of-two cycle, a target-defective quotient, a previously declared Type B/route-8 handoff, or a nontrivial target-complete compression of a proper support.

For length-changing G3, the implication is valid because (delta\ne0) supplies a strictly shorter representative.  For a finite-table row, realizing, handoff, and distinguishing are valid routes.  The remaining assertion is the unsupported implication



\[
\begin{aligned}
&|E|=|Q|,\quad \mathbf d_\partial(E)=\mathbf d_\partial(Q),\\
&E\text{ and }Q\text{ have identical target response in every context}
\\[-2mm]
&\hspace{35mm}\Longrightarrow
\exists X'\text{ strictly smaller satisfying all five clauses of } 
\texttt{def:proper-quotient-representative}.
\end{aligned}
\]

That implication is neither a definition nor a proved result.

### Outgoing contracts

The live graph marks [157] terminal and gives it no outgoing edge.  Internally the claimed closures have these contracts:

- realizing row (	o) [155]/target cycle: an actual simple power-of-two cycle in (G);
- distinguishing row (	o) [156]/defect ledger: same boundary-degree fibre plus a compatible context separating target truth;
- handoff row (	o) an already existing Type B or route-8 ledger: the first declared handoff interface and transferred charge are retained;
- neutral row (	o) compression: an explicit (T)-boundaried (X') with no larger obstruction profile, identical boundary degrees, no internal target cycle, internal minimum degree at least three, the same quotient relations, and strict decrease in the selected minimality order.

The first three contracts are met.  The neutral row provides context equivalence but not the final compression contract, so the terminal node is not exhaustive as implemented mathematically.

## 3. Sentence audit

| Sentence | Exact assertion | Facts used | Hidden obligation | Adversarial test | Status |
|---|---|---|---|---|---|
| S1 | Every same-interface table row routes to target, defect, handoff, or proper-support compression. | Table definition; surviving-cold exclusions. | The four outcomes must cover neutral equal-length rows, and compression needs an actual smaller graph. | Set (delta=0), no realization, no handoff, no distinguishing. | FAILED |
| S2 | Equal-length configurations and short exceptional self-returns cannot be terminal. | S1; short-return filter. | Every exceptional row must satisfy one destination contract. | Use (ell=17), whose smear ([17,29]) has no power of two, and leave the row neutral. | FAILED |
| S3 | A realizing row gives a power-of-two cycle in (G). | Definition of realizing; selected counterexample. | The completion must be graph-realized and simple. | Read the table row's actual compatible completion. | SUPPORTED |
| S4 | First contact with a declared Type B or route-8 interface transfers the charge. | First-failure routing; retained handoff ledgers. | The interface and charge must be the previously declared ones. | Require the first declared contact rather than an arbitrary named support. | ROUTING ONLY |
| S5 | For a nonrealizing, nonhandoff row, a distinguishing context makes the identification non-target-complete. | `lem:context-universality`; fixed boundary-degree fibre. | The context must be compatible with the same interface/profile. | Choose the context witnessing different target truth. | SUPPORTED |
| S6 | Such a defect belongs to the sparse-exit or exit-(4) ledger. | Surviving-cold branch and first-failure location. | The route must retain the defect witness and load. | Compare the destination facts in `[156]`. | ROUTING ONLY |
| S7 | Neutrality means equal boundary profile and equal target response in every compatible context. | Table T1--T4; negation of distinguishing. | Universal context quantifier, not only the actual complement. | Test an arbitrary (T)-boundaried context. | SUPPORTED |
| S8 | Being a first-failure row makes the quotient delete at least one declared branch-excess coordinate while retaining target-response coordinates. | First-failure definition; exact response profile. | Coordinate deletion must be a rank-reducing quotient of the stated exact labelled family. | Identify two labels with equal values but retain their graph pieces. | AMBIGUOUS |
| S9 | By `def:admissible-rank-quotient`, that quotient is admissible only when it has a strictly smaller proper representative. | Definition of admissible rank quotient. | One must first prove this table identification is an admissible graph-realizable rank reduction, or separately construct the representative. | Use a neutral equality of labels with no smaller graph representative. | FAILED |
| S10 | The smaller representative satisfies `lem:replacement` and is forbidden by `cor:uncompressible`. | Replacement and uncompressibility. | Existence plus all five representative clauses, especially internal minimum degree and strict decrease. | Inspect the proof for (X'); none is named. | FAILED |
| S11 | Hence no neutral row survives. | S7--S10. | S9--S10 must be established. | Compare node [163], which explicitly retains a neutral equal-length symmetry. | FAILED |

## 4. Counterexample attempts

### Smallest-parameter test

- **Explicit data:** Take interface (T=\{x,y\}) and two internally disjoint simple (x)-(y) strands (Q=xab y) and (E=xcd y), each of length (3).  They are the smallest distinct equal-length simple strands whose union is a (6)-cycle rather than the forbidden (4)-cycle produced by two length-(2) strands.  Give both the same two-entry boundary-degree record, offsets (0,0), and identical exact response value determined by length (3).
- **Hypotheses satisfied:** (delta=|E|-|Q|=0); the support and record are finite; every outside (x)-(y) completion has the same length when glued to (Q) or (E), so the target truth values agree; the bounded support itself has no power-of-two cycle.
- **Accumulated facts violated:** As a standalone (6)-cycle, the internal vertices have degree (2), violating node [2]'s ambient minimum-degree-three condition and the baseline required of a replacement representative.
- **Applicability:** **NON-APPLICABLE TO THE NODE** as a graph counterexample, first excluded at node [2].  It nevertheless shows that equal length and context equivalence do not themselves produce strict decrease.

### Parity or 2-adic test

- **Explicit data:** Use the short-return boundary value (ell=17).  The full offset smear is ([17,29]), which misses (4,8,16,32).  Equivalently, the parity mix in the interval contains no integer of (2)-adic odd part (1) that is itself a power of two.  The row therefore reaches the exceptional finite table rather than G1.
- **Hypotheses satisfied:** This is exactly one of `lem:cold-short-self-return-filter`'s surviving lengths; all thirteen offsets (0,ldots,12) have been checked, so no 2-adic projection or omitted residue is involved.
- **Accumulated facts violated:** No complete minimum-degree-three, target-avoiding ambient realization with the retained packing and first-failure state has been supplied by this arithmetic datum alone.
- **Applicability:** **NON-APPLICABLE TO THE NODE** as a full graph candidate; the earliest missing requirement is node [2]'s ambient graph contract.  The test confirms that the short-return filter legitimately hands (ell=17) to the table and that arithmetic does not close its neutral row.

### Boundary or range test

- **Explicit data:** Take an actual table record with boundary (T=\{x,y\}), equal boundary-degree vector ((d_x,d_y)), two equal-length representatives (|Q|=|E|=3), equal offsets, identical declared response profile, no first handoff, and identical target truth in every compatible context.  This is the endpoint (delta=0), not a strict inequality limit.
- **Hypotheses satisfied:** T1--T4, boundedness, equal length, nonrealization, nonhandoff, and neutrality.  The quotient can delete a label/branch-excess coordinate while preserving target truth.
- **Accumulated facts violated:** None at the exact response-quotient level.  What is absent is not an upstream exclusion but the conclusion's required object: a strictly smaller graph representative satisfying `def:proper-quotient-representative` (a)--(e).
- **Applicability:** APPLICABLE TO THE LOCAL MISSING-REPRESENTATIVE OBLIGATION.  It is not claimed as a realized counterexample graph; it is the strongest abstract residual allowed by the stated table definition.

### Graph-realizability test

- **Explicit data:** Realize the previous two strands as the (6)-cycle (x-a-b-y-d-c-x).  The two length-(3) routes are genuine, internally disjoint, equal-length, and form no power-of-two cycle.  For every added outside (x)-(y) path of length (s), both replacements test the same length (s+3).
- **Hypotheses satisfied:** Simple-graph realization of the two strands, exact same-interface equality, graph-level context equivalence for path completions, and target avoidance inside the bounded support.
- **Accumulated facts violated:** The four internal vertices have degree (2), so the ambient graph fails node [2].  Adding arbitrary degree-restoring attachments is not permitted because it must preserve all target-avoidance and packing facts.
- **Applicability:** **NON-APPLICABLE TO THE NODE**, first excluded by node [2].  No complete graph-realized minimal-counterexample candidate was found.

### Branch-routing test

- **Explicit data:** Start with a finite-table row (R) on the actual extracted family, and select the literal complement of the first three tests: `not realizing`, `no declared handoff`, and `no compatible context distinguishes`.  Retain (delta(R)=0) and T1--T4, but do not add an (X') not present in the row data.
- **Hypotheses satisfied:** This is exactly the neutral branch of the table classification and is compatible with the selected `G3/finite` edge.  Target-completeness and the fixed boundary-degree fibre hold.
- **Accumulated facts violated:** None.  Hereditary uncompressibility excludes a compression only after one exists; it does not exclude an abstract neutral symmetry.  `def:admissible-rank-quotient` classifies the identification as non-admissible when no smaller representative exists.
- **Applicability:** APPLICABLE TO THE NODE'S ROUTING CONTRACT.  The row satisfies the source predicate but fails the claimed compression destination's strict-representative entry condition.  This is the report's decisive missing-witness candidate.

The bundled modular checker was not run: node [157] contains no inference from an orbit modulo a factor of (g) to an integer in (L+R+g\mathbb Z).  The only arithmetic consumed here is the already exact finite smear filter.

## 5. Strongest valid counterexample

No valid graph counterexample satisfying the complete minimal-counterexample residual was constructed.  The strongest surviving candidate is the neutral equal-length table-row schema in the branch-routing test: an actual extracted T1--T4 row with (delta=0), no hit, no handoff, and context-equivalent representatives, but no strictly smaller graph representative.  It violates no accumulated logical fact.  It is a witness to a missing construction, not a counterexample to the global theorem.  The manuscript itself confirms that this is a live mathematical shape at `def:neutral-equal-length-germ`: it calls the identification an abstract label symmetry that reduces no graph-realizable rank and routes it through nodes [163], [165], and [167], rather than through immediate compression.

## 6. Local repair

### Corrected statement

Every length-changing silent cold bounded configuration is closed by replacing its longer representative with its explicitly shorter context-equivalent representative.  Every equal-length table row or short exceptional self-return is routed as follows.  A realizing row gives a power-of-two cycle; a row first meeting a declared Type B or route-8 interface transfers its charge to that retained ledger; and a row distinguished by a compatible context gives a target-defective quotient.  A remaining neutral row gives a target-complete proper-support compression only if an explicit strictly smaller representative satisfying `def:proper-quotient-representative` (a)--(e) is constructed.  If no such representative is available, the identification is merely an abstract label symmetry and must be routed to the neutral equal-length symmetry split of nodes [163], [165], and [167].

### Complete local proof

For a length-changing silent configuration, orient the representatives so that (E) is shorter than (Q).  The first-failure record gives the same two boundary vertices and degree profile, and silence gives equal target response against every compatible context.  The explicit shorter strand is graph-realized in the bounded configuration and preserves the baseline.  Gluing it into the actual complement therefore gives an at-most-as-obstructing graph with the same boundary degrees and strictly fewer vertices; `lem:replacement` and `cor:uncompressible` exclude it.

Now let (R) be an equal-length or short-exception table row arising from the extracted family.  If (R) is realizing, its displayed live completion is a power-of-two cycle.  If its first declared interface is a Type B or route-8 handoff, transfer the row's charge and full interface data to that existing ledger.  Otherwise, if a compatible context distinguishes (Q) and (E), `lem:context-universality` makes their identification target-defective and routes it to the appropriate defect ledger.

The only remaining case is neutral: (Q) and (E) have the same boundary profile, equal size, and identical target response in all compatible contexts.  Decide whether the quotient has a strictly smaller proper representative (X') satisfying clauses (a)--(e) of `def:proper-quotient-representative`.  On the yes arm, (X') satisfies all hypotheses of `lem:replacement`, so hereditary uncompressibility closes the arm.  On the no arm, `def:admissible-rank-quotient` says precisely that the identification is not an admissible rank reduction; no contradiction follows.  Retain the actual row, its candidate-family membership, equality of lengths, same boundary profile, baseline, and context equivalence, and route it to the existing neutral symmetry decision.  If (E) is a distinct canonical piece, use the refined same-size order of `lem:refined-minimality-swap`; if (E) is a genuine second strand, use `lem:two-strand-check` and `lem:symmetric-pair-endpoint`.  These are the existing proof mechanisms for the equal-length case and require no invented compression.

### Counterexample disposition

The length-(3) two-strand abstraction is not sent to compression merely because its response labels agree.  If an explicit smaller representative exists, it is caught by the corrected compression arm.  Otherwise it is a neutral symmetry: a distinct canonical piece is handled by refined same-size minimality, and a graph-realized second strand is handled by the two-strand/endpoint route.  The standalone (6)-cycle remains non-applicable because it fails the minimum-degree-three entry contract.

### Graph patch

Replace the terminal collapse by the following typed routing:

```text
[154] -> length-changing silent, explicit shorter representative -> [157 compression]
[154] -> delta = 0 or exceptional short return -> [157 table test]
[157 table test] -> realizing -> [155]
[157 table test] -> distinguishing or declared handoff -> [156 / retained handoff ledger]
[157 table test] -> neutral + explicit strictly smaller proper representative -> [157 compression]
[157 table test] -> neutral + no such representative -> [163 neutral symmetry split]
[163] -> distinct canonical same-size piece -> [165] -> [166]
[163] -> genuine second strand -> [167] -> [155] or [168]
```

The entry to [163] must retain: membership in the actual `[153]` extracted family (or the actual short-self-return row), proper connected bounded support, (delta=0), the same two interfaces and boundary-degree profile, the baseline for the exchanged graph, absence of realization/handoff/distinguishing, and context equivalence.  If [163] is kept textually restricted to the dense residual, introduce the same decision locally at [157] or generalize [163]'s entry theorem to the common cold-row contract; do not import the dense-packing predicate onto the node-[157] path.

### Downstream impact

`lem:cold-increment-arithmetic` case (d), rows 12 and 16 of `tab:cold-branch-ledger`, and `thm:cold-branch-quantitative-closure` must stop saying that every (delta=0) row immediately compresses; they must retain and route the neutral complement.  `lem:dense-cold-pass`, `def:neutral-equal-length-germ`, `lem:neutral-germ-symmetry`, `lem:refined-minimality-swap`, `lem:two-strand-check`, and `lem:symmetric-pair-endpoint` already contain the intended symmetry route, though their dense-only hypotheses must be checked before reuse on the node-[157] residual.  `lem:absorbed-germ-fan-data` already cites both the table and the neutral-symmetry chain and should be synchronized with the corrected split.

In Lean, `Graph.ColdCorridor.TableRow.admissible` currently stores the strict-decrease conclusion as an input field, so `row_closed` proves only the narrowed statement.  The manuscript's T1--T4 row should instead be represented without that field; explicit representative existence should be a branch predicate or a produced fact.  `coldSameInterfaceTableRow`, the `K .coldSameInterfaceTable` schema, the terminal-row predicates, the node [163] decision, `Assembly_node_audit.md`, and `web/data/eg_node_audit.json` then need synchronized contracts.  No such source change is made by this audit.

## 7. Regression audit

The search

```text
rg -n 'lem:cold-same-interface-table|def:cold-same-interface-table|coldSameInterfaceTable|TableRow|neutral equal-length|equal-length terminal' to_formalize/erdos_64_proof.tex hypostructure proofs Assembly_node_audit.md web/data/eg_node_audit.json
```

found and the audit inspected:

- the diagram caption, detailed dependency row, implementation ledger row, and cold-branch summary for `[145]`--`[157]`;
- `lem:cold-increment-arithmetic` case (d), the cold residual table, and both uses in `thm:cold-branch-quantitative-closure`;
- the dense-pass reuse and the explicit neutral symmetry route `def:neutral-equal-length-germ`, `lem:neutral-germ-symmetry`, `lem:refined-minimality-swap`, `lem:two-strand-check`, and `lem:symmetric-pair-endpoint`;
- the absorbed-configuration reuse in `lem:absorbed-germ-fan-data`;
- `Graph/ColdCorridor.lean`'s `Record`, `BoundedGerm`, strengthened `TableRow.admissible`, `row_closed`, `selfReturn_closed`, and terminal-residual consumers;
- `Strategy/SpineVocabulary.lean`'s `K .coldSameInterfaceTable` proposition and node-[163] vocabulary;
- `Strategy/ColdCorridorRows.lean`'s `coldSameInterfaceTableRow` and neutral-germ consumer;
- the node-[157] and node-[163] assembly declarations and every additional assembly use of `coldSameInterfaceTableRow`;
- the human and JSON audit rows, including the existing claim that the Lean row is faithful.

No `word for word`, `same proof`, or `analog` occurrence tied specifically to `lem:cold-same-interface-table` was found.  The dense and absorbed uses named above are the repeated mathematical uses requiring synchronization.

## 8. Residual uncertainty

No complete minimum-degree-three, power-of-two-cycle-free graph realizing the neutral row and every upstream packing/ledger condition was constructed; doing so would amount to a genuine local counterexample rather than the missing-witness diagnosis made here.  The manuscript does not enumerate the finite table, so it remains uninspected whether some separate finite property of every actual row could construct the missing representative.  The proposed reuse of nodes [163]--[168] also needs a source-level check that their dense-residual wording can be generalized without consuming the dense-packing predicate and that the endpoint-stub selection is compatible with node [152]'s present lexicographic stub selection.  No claim about the global theorem follows from this audit.
