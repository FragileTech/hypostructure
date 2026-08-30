<!-- red-team-audit
{
  "schema_version": 1,
  "proof": "erdos-gyarfas",
  "node": 171,
  "node_label": "compression closure:\\(|\\mathcal B(\\mathcal P)|<1\\)",
  "panel": "fig:proof-diagram-part-xii",
  "contract_sha256": "51d4320ec24dbce202a19fca9e466686e723ff272620b458724ddb1a1987c32f",
  "manuscript_sha256": "106a8205a1718fbf90e1686a107b2143b9edca574e2b0c11415e7f44aee2c0f9",
  "graph_sha256": "dc67fae178f947a9607c167e383d85919633341bdd423e4c4a45e4c317b3a765",
  "lean_audit_sha256": "50324ef5594d635a52d83aeb297f2ca3f3d30ef58de4ce3602816c7e78365b12",
  "verdict": "WRONG ROUTING DESTINATION",
  "audited_at": "2026-08-24T21:29:14Z"
}
-->

# Red-team audit: node [171]

## 1. Executive verdict

Verdict: **WRONG ROUTING DESTINATION**

The final arithmetic of node [171] would be valid if the additive branch supplied the cardinal inequality \(|\mathcal B(\mathcal P)|2^K\le|\mathcal G_{n,m}|\), where \(K=(c_{13}-o(1))p_{13}\log_2 n\).  It does not.  Node [170] bounds the number of barrier-*state values* in each conditional range by \(F_{a,b}\) out of \(W_{a,b}\).  An injective code by outside edges and surviving states yields only \(|\mathcal B|\le D\prod F_c\), where \(D\) counts outside-edge records.  The claimed relative bound additionally requires the unproved fiberwise baseline \(D\prod W_c\le|\mathcal G_{n,m}|\), or an equivalent switching injection \(\mathcal B\times\prod A_c\hookrightarrow\mathcal G_{n,m}\times\prod F_c\).  The proof instead bounds \(D\) by \(|\mathcal G_{n,m}|\), adds the positive state-code cost, and then subtracts the nonexistent \(\log W\) baseline.  Conditional range size alone does not control how many graphs lie over each state.  Therefore the yes-residual of [170] does not meet [171]'s compression entry contract, and the terminal routing is unsupported.  This is a local entropy-handoff gap, not a claimed graph counterexample to the theorem.

## 2. Exact node contract

### Incoming residual

The sole live edge is `[170] -> [171]`, tagged `yes`.  The common residual carries the selected finite simple graph \(G\) with \(n\) labelled vertices, \(m\) edges, minimum degree at least three, and no cycle of accepted power-of-two length.  The retained ancestry includes the selected minimality facts, edge-deletion criticality, high-degree independence, context-universality, replacement, and hereditary uncompressibility of nodes [1]--[14], as well as the fixed maximal vertex-disjoint induced-\(P_{13}\) packing \(\mathcal P\) and its canonical window positions from [17]--[18].

The edge at [19]--[21] has supplied the near-cubic spine, so
\[
m=\frac32n+O(\sqrt n),
\qquad
|\mathcal G_{n,m}|=\binom{\binom n2}{m},
\qquad
\log_2|\mathcal G_{n,m}|le\frac32n\log_2n+o(n\log n).
\]
On the Part-XII path, [158]'s no-arm has retained the exact dense-package overflow [159].  Writing
\[
K:=\operatorname{windowPackageBits}(G)\,p_{13},
\]
its exact finite form is
\[
2^K>|\mathcal G_{n,m}|.
\]
The no-arm of [160] and the dense cold pass [162] lead through the canonical neutral branch [163], the canonical-replacement route [165], and the refined tie-break [166] to [169].  At [169], every retained corridor is terminal and neutral with \(Q=E\); the object's labelled skeleton belongs to the fixed blocked class \(\mathcal B(\mathcal P)\).  Thus
\[
G\in\mathcal B(\mathcal P),
\qquad
|mathcal B(\mathcal P)|\ge1.
\]

For each exposure coordinate \(c\) (packed window, separated scale, and certified barrier row), let \(A_c\) be its a-priori state set of size \(W_c\), and let \(F_c\) denote the allowed blocked-state bound.  The [170] yes-arm says that, after fixing the outside-edge record and every earlier exposed state, the set of *values* assumed by the next state has cardinality at most \(F_c\); equivalently, the conditional restrictions of the state ranges multiply.  It retains no injection realizing all \(W_c\) states over each outside record and no cardinal comparison between the uncompressed outside-record code and the ambient graph class.

### Accumulated facts

The facts available at [171] are:

- `[2]`: \(G\) is an actual minimum-degree-three graph avoiding the target.
- `[17]`: \(\mathcal P\) is fixed and maximal, and its window positions are canonical data of \(G\).
- `[19]`--`[21]`, `def:near-cubic-spine`, `lem:near-cubic-budget`, and `lem:skeleton-dominates`: the ambient labelled graph budget is the fixed-\(m\) skeleton count with leading coefficient \(3/2\).
- `[159]`: the exact package size \(2^K\) is strictly larger than the skeleton budget.
- `[169]`, `def:blocked-class`: the object's skeleton is a member of \(\mathcal B(\mathcal P)\), whose graphs have the fixed vertex set, fixed edge count, minimum degree at least three, every packed window induced at its fixed position, and no accepted cycle through a packed window.
- `[170]` yes, `lem:scale-additivity`: in each conditioned prefix, at most \(F_c\) state values occur among the \(W_c\) a-priori labels.
- `lem:p13-window-package`: the unrestricted package globally realizes independently target-testable states and has aggregate rate \(c_{13}\).  This gives a global state lower bound, not a fiberwise completion of every outside-edge record.

No ancestor proves either of the two missing coding facts:

1. the map from a blocked graph to its outside-edge record and all barrier states is injective, up to a quantified subexponential internal-window-ordering overhead; and
2. if \(D\) is the number of admissible outside-edge records, then
   \[
   D\prod_c W_c\le|\mathcal G_{n,m}|\,2^{o(n\log n)}.
   \]

The second fact is the essential one.  Global independent target-testability does not imply it after conditioning on an arbitrary outside record.

### Current predicate and exact claim

Node [171] claims
\[
F(171)+\bigl(\text{each conditional state range has size at most }F_c\bigr)
\Longrightarrow
|\mathcal B(\mathcal P)|
\le |\mathcal G_{n,m}|\prod_c\frac{F_c}{W_c}.
\]
Since the certified products satisfy
\[
\prod_c\frac{W_c}{F_c}
\ge 2^K,
\]
the desired consequence is
\[
|\mathcal B(\mathcal P)|2^K\le|\mathcal G_{n,m}|.
\]
Together with \(2^K>|\mathcal G_{n,m}|\) and \(|\mathcal B|\ge1\), that would be a contradiction.

The stated conditional range bound only gives the following.  Let \(D\) be the number of first-coordinate outside records in the proposed code.  If the full code is injective, expose its states in the canonical order.  For each fixed outside record there are at most \(\prod_c F_c\) full state strings, hence
\[
|\mathcal B(\mathcal P)|\le D\prod_c F_c.
\]
The manuscript supplies only the crude \(D\le|\mathcal G_{n,m}|\) (and even describes an unnecessary window-placement factor).  This yields
\[
|\mathcal B(\mathcal P)|\le|\mathcal G_{n,m}|\prod_c F_c,
\]
not the claimed division by \(\prod_c W_c\).  The missing implication is exactly
\[
D\prod_c W_c\le|\mathcal G_{n,m}|,
\]
which would say that every a-priori state string can be represented injectively, fiber by fiber, inside the ambient graph budget.

### Outgoing contracts

Node [171] is terminal and has no outgoing edge.  Its terminal contract requires three ingredients on the same fixed residual:

1. \(G\in\mathcal B(\mathcal P)\), so \(|\mathcal B|\ge1\);
2. the exact dense inequality \(2^K>|\mathcal G_{n,m}|\); and
3. a proved compression inequality \(|\mathcal B|2^K\le|\mathcal G_{n,m}|\).

The first two are retained.  The third is not a consequence of the [170] yes-predicate as stated.  The residual therefore cannot terminate at [171] unless a fiberwise baseline/switching theorem is added.  Failure of that theorem is not automatically the [170] no-arm: a coordinate may have only \(F_c\) state values while the graph fibres over those values are highly nonuniform.  Such concentration is not, without another lemma, a minimal overlap obstruction satisfying [172]'s entry contract.

## 3. Sentence audit

| Sentence | Exact assertion | Facts used | Hidden obligation | Adversarial test | Status |
|---|---|---|---|---|---|
| S1 | Record the outside edges and the fixed window positions. | Definition of \(\mathcal B(\mathcal P)\); canonical packing. | The phrase “fixed positions” must mean there is one position record, not a fresh choice per graph. | Count placements of \(p=\Theta(n)\) unordered \(13\)-sets if they are not fixed. | AMBIGUOUS |
| S2 | The number of first-stage records is at most \(|\mathcal G_{n,m}|\) times a placement factor absorbed in the error. | Skeleton budget. | If positions vary, their logarithm can be \(\Theta(p\log n)\), not \(o(n\log n)\); if positions are fixed, the factor is exactly one. | Compare fixed packing with \(n^{13p}\) ordered placements. | FAILED AS WRITTEN; REPAIRABLE BY FIXED POSITIONS |
| S3 | Given a prefix, a barrier state costs at most \(\log_2F_c=\log_2W_c-\gamma_c\) bits. | [170] conditional state-range bound. | The code must enumerate the actually allowed value set canonically, and the bound is on values rather than graph multiplicities. | Put arbitrarily many graphs over one allowed value. | SUPPORTED ONLY FOR THE STATE STRING |
| S4 | Outside edges, positions, and all barrier states determine \(H\). | Claimed encoding. | Internal window edges/path order and incidences must be reconstructible, or separately encoded with quantified overhead. | Use two induced path orders on the same \(13\)-vertex position and the same outside edges. | AMBIGUOUS |
| S5 | Summing the \(\gamma_c\) savings makes the code \(\sum_c\gamma_c\) bits shorter than \(\log_2|\mathcal G_{n,m}|\). | S1--S4; [170]. | The uncompressed code with \(W_c\) choices at every coordinate must itself fit the ambient graph budget fiberwise. | Take one outside record, one allowed state, and an unused a-priori state. | FAILED |
| S6 | Therefore \(|\mathcal B|\le|\mathcal G|\prod_c(F_c/W_c)\). | S5. | Requires \(D\prod W_c\le|\mathcal G|\), not merely \(D\le|\mathcal G|\). | Write both inequalities symbolically and cancel no unjustified factor. | FAILED |
| S7 | The aggregate ratio is \(2^{-(c_{13}-o(1))p_{13}\log_2n}\). | Certified \(W/F\) products; separated scales. | Floors, omitted end scales, and fixed finite ordering overhead must be included in the same exact \(K\). | Use the exact package integer `windowPackageBits * p`. | SUPPORTED AT THE DECLARED RATE |
| S8 | The near-cubic budget has leading term \((3/2)n\log_2n\). | [19]--[21]; `lem:near-cubic-budget`. | The bound must apply to the same fixed \(n,m\) class. | Retain the literal fixed-edge-count ledger. | SUPPORTED |
| S9 | On the dense residual the exponent is negative, so \(|\mathcal B|<1\). | S6--S8; [159]. | Use the exact strict inequality rather than compare unrelated \(o(1)\) terms. | Substitute \(2^K>|\mathcal G|\). | SUPPORTED IF S6 IS SUPPLIED |
| S10 | A finite class of cardinality below one is empty, contradicting \(G\in\mathcal B\). | [169]; integrality. | Membership and the cardinal inequality must concern the same fixed packing. | Use \(|\mathcal B|\ge1\). | SUPPORTED |
| S11 | Hence [171] is terminal. | S5--S10. | The missing fiberwise baseline must be proved or its failure routed. | Concentrate every graph of a prefix on one allowed state. | FAILED |

## 4. Counterexample attempts

### Smallest-parameter test

- **Explicit data:** Use one exposure coordinate, a two-element a-priori state set \(A=\{0,1\}\) (\(W=2\)), and one allowed state \(F=\{0\}\) (\(F=1\)).  Let the ambient combinatorial class be \(\mathcal G=\{g\}\), the blocked class be \(\mathcal B=\{g\}\), the outside-record set be \(D=\{d\}\), and encode \(g\mapsto(d,0)\).
- **Hypotheses satisfied:** The code is injective; every conditional state range has cardinality \(1=F\), so the local relative state-range bound is \(F/W=1/2\); \(\mathcal B\) is nonempty; and the analogue of the dense inequality is \(2^1>1=|\mathcal G|\).
- **Accumulated facts violated:** This is a finite coding model, not a labelled minimum-degree-three graph class with an induced-\(P_{13}\) packing, the selected minimality facts, and the Part-XII residual.
- **Applicability:** **NON-APPLICABLE TO THE NODE** as an actual graph counterexample, first failing node [2]'s graph contract.  It is a valid counterexample to the exact entropy inference used at [171]: the claimed bound says \(1\le1/2\), while the proved prefix bound says only \(1\le1\).

### Parity or 2-adic test

- **Explicit data:** Compare odd package exponent \(K=1\) with the preceding model to even exponent \(K=2\): take two binary coordinates, one allowed value at each prefix, \(|\mathcal G|=3\), and \(|\mathcal B|=1\).  Then \(2^K=4>3\), but the desired compression inequality would be \(1\le3/4\).
- **Hypotheses satisfied:** In both parity cases the dense comparison is strict and every conditional state-value range has the asserted relative size \(1/2\).  There is no division by an odd part and no modular lift; the quantities are exact powers of two.
- **Accumulated facts violated:** Neither finite model supplies the graph, packing, near-cubic edge count, or neutral corridor ledger required at [169].
- **Applicability:** **NON-APPLICABLE TO THE NODE** as a full residual, first failing node [2].  The test shows that parity and 2-adic compatibility are irrelevant: the missing factor is an entropy baseline, not an exponent congruence.

### Boundary or range test

- **Explicit data:** Take the smallest strict dense boundary \(2^K=|\mathcal G|+1\), for example \(K=2\), \(|\mathcal G|=3\), and \(|\mathcal B|=1\).  If \(|\mathcal B|2^K\le|\mathcal G|\) were available, it would read \(4\le3\) and close.  At equality \(2^K=|\mathcal G|\), it would only give \(|\mathcal B|\le1\), so strictness is necessary.
- **Hypotheses satisfied:** The exact inequality pattern matches [159] and tests its sharp endpoint without asymptotic notation.
- **Accumulated facts violated:** The cardinal values are not exhibited as a fixed-\(m\) labelled graph class with the current packing.
- **Applicability:** **NON-APPLICABLE TO THE NODE** as a graph instance, first failing node [2].  It confirms that the final integer step has no range error: once the missing compression inequality is proved, the exact strict [159] predicate suffices.

### Graph-realizability test

- **Explicit data:** Let \(G=K_4\), \(n=4\), \(m=6\), and take the empty packing \(\mathcal P=\varnothing\).  Then \(G\) has minimum degree three and only cycles of length three, so it avoids all accepted powers \(4,8,16,\ldots\).  It belongs to the corresponding blocked class, and the barrier exposure is empty and hence additive.
- **Hypotheses satisfied:** This is an actual finite simple minimum-degree-three target-avoiding graph; its labelled skeleton is a blocked-class member, and the proposed outside/state code is trivially injective.
- **Accumulated facts violated:** \(K_4\) is induced-\(P_{13}\)-free and the packing has \(p_{13}=0\), so it is first excluded by the selected no-arm of node [15] and cannot satisfy the dense overflow [159].
- **Applicability:** **NON-APPLICABLE TO THE NODE**, first excluded at node [15].  It verifies that nonempty blocked classes and additive/vacuous state ranges are possible in the graph category; the dense packing condition, not blockedness alone, is essential.

### Branch-routing test

- **Explicit data:** Let \(D\) be the set of outside-edge records of the actual blocked class and order the state coordinates as at [170].  Retain exactly the yes-predicate: each prefix has at most \(F_c\) next-state values.  Do not add a realization of all \(W_c\) states over each \(d\in D\).  Then injectivity gives \(|\mathcal B|\le D\prod F_c\), while the [171] destination requires \(|\mathcal B|\prod W_c\le|\mathcal G|\prod F_c\).
- **Hypotheses satisfied:** This is the literal information carried by the manuscript's [170] yes-arm.  It preserves the same fixed blocked class, outside records, exposure order, and conditional state sets.
- **Accumulated facts violated:** None.  `lem:p13-window-package` supplies global target-complete states but not the missing conditional inequality \(D\prod W_c\le|\mathcal G|\).  `lem:skeleton-dominates` gives only that canonical data do not outnumber graphs, not a product of a separate outside record with every a-priori state.
- **Applicability:** APPLICABLE TO THE NODE'S ROUTING CONTRACT.  The [170] yes-residual lacks a required entry fact for [171], and concentration of graph fibres over allowed values is neither excluded nor routed to [172].

The modular-hit checker was not run.  Node [171] contains no passage from a doubling orbit modulo a divisor to an integer power in a finite coefficient range; its powers of two are exact cardinal multipliers.  The parity and strict-boundary tests above exhaust the relevant exponent edge cases.

## 5. Strongest valid counterexample

No complete graph satisfying every minimal-counterexample, packing, dense-residual, neutral-corridor, and additive-state condition was constructed.  The strongest surviving candidate is the exact conditional-code schema in the branch-routing test.  It violates no stated [170] yes-fact: all graphs over a fixed prefix may concentrate on one of the at-most-\(F_c\) state values with arbitrarily unequal multiplicity.  The one-coordinate model \(W=2,F=1,D=1,|\mathcal G|=|\mathcal B|=1\) is the smallest explicit witness that state-range shrinkage and code injectivity do not imply a relative graph-count shrinkage.

For the actual residual, [169] itself supplies the decisive nonemptiness witness \(G\in\mathcal B(\mathcal P)\).  What is missing is not a candidate graph but a map that turns each blocked graph together with each a-priori state choice into enough distinct ambient graphs (or a comparably strong fiberwise counting argument).  Therefore this report diagnoses an invalid destination handoff rather than a valid graph counterexample to the theorem.

## 6. Local repair

### Corrected statement

Let \(C\) be the ordered set of barrier exposure coordinates, let \(A_c\) be the a-priori state set at coordinate \(c\) with \(|A_c|=W_c\), and let \(F_c\) be the maximum allowed next-state count on the blocked additive branch.  Let \(D\) be the set of outside-edge records for the fixed packing positions.  Assume:

1. the code
   \[
   \operatorname{Enc}:\mathcal B(\mathcal P)\longrightarrow
   D\times\prod_{c\in C}A_c
   \]
   is injective, up to an explicitly bounded factor \(2^{o(n\log n)}\);
2. in every nonempty prefix fibre of this code, at most \(F_c\) next-state values occur;
3. the uncompressed baseline is realized fiberwise:
   \[
   |D|\prod_{c\in C}W_c
   \le |\mathcal G^{\delta\ge3}_{n,m}|\,2^{o(n\log n)}.
   \]

Then
\[
|\mathcal B(\mathcal P)|
\le |\mathcal G^{\delta\ge3}_{n,m}|
  \prod_{c\in C}\frac{F_c}{W_c}\,2^{o(n\log n)}.
\]
If the products and errors are packaged by the exact integer \(K\) on the [159] residual so that
\[
|\mathcal B(\mathcal P)|2^K
\le |\mathcal G^{\delta\ge3}_{n,m}|
\le|\mathcal G_{n,m}|<2^K,
\]
then \(\mathcal B(\mathcal P)=\varnothing\), contradicting \(G\in\mathcal B(\mathcal P)\).

An equivalent and often cleaner replacement for assumptions 1--3 is one explicit injection
\[
\Psi:\mathcal B(\mathcal P)\times\prod_{c\in C}A_c
\hookrightarrow
\mathcal G^{\delta\ge3}_{n,m}\times\prod_{c\in C}S_c,
\qquad |S_c|\le F_c,
\]
constructed by barrier switching while preserving the fixed vertex set, edge count, minimum degree, induced windows, and previously exposed states.

### Complete local proof

Fix an outside record \(d\in D\).  Expose the coordinates in the canonical order.  At the first coordinate there are at most \(F_{c_1}\) values among blocked codewords over \(d\).  For each such value, the second coordinate has at most \(F_{c_2}\) values, and so on.  Induction on the number of coordinates gives at most
\[
\prod_{c\in C}F_c
\]
complete blocked state strings over \(d\).  Injectivity of \(\operatorname{Enc}\), with its stated overhead, therefore gives
\[
|\mathcal B(\mathcal P)|
\le |D|\prod_{c\in C}F_c\,2^{o(n\log n)}.
\]

The baseline hypothesis gives
\[
|D|le
|\mathcal G^{\delta\ge3}_{n,m}|
\left(\prod_{c\in C}W_c\right)^{-1}
2^{o(n\log n)}.
\]
Substitution yields
\[
|\mathcal B(\mathcal P)|
\le |\mathcal G^{\delta\ge3}_{n,m}|
\prod_{c\in C}\frac{F_c}{W_c}
2^{o(n\log n)},
\]
after combining the two subleading errors.  In the exact finite formulation, choose \(K\) no larger than the certified logarithmic product after all floors and overheads.  Then
\[
|\mathcal B(\mathcal P)|2^K
\le |\mathcal G^{\delta\ge3}_{n,m}|.
\]
The near-cubic class injects into \(\mathcal G_{n,m}\), so the right side is at most \(|\mathcal G_{n,m}|\).  Node [159] retains the strict reverse inequality \(|\mathcal G_{n,m}|<2^K\).  If \(|\mathcal B|\ge1\), multiplication gives \(2^K\le|\mathcal B|2^K\le|\mathcal G_{n,m}|<2^K\), impossible.  Hence \(|\mathcal B|=0\), contradicting the retained member \(G\).

This proves the corrected compression statement completely once the baseline or switching injection is supplied.  It also isolates the missing mathematical task: `lem:scale-additivity`'s state-range bound alone proves assumption 2, not assumption 3.

### Counterexample disposition

The one-coordinate coding model is rejected by the corrected statement because it fails the baseline: \(|D|W=2>|\mathcal G|=1\).  The even two-coordinate model similarly has \(|D|W^2=4>|\mathcal G|=3\).  They are not sent to a target-cycle or modular-arithmetic branch; they identify failure of the barrier recoding baseline.  The \(K_4\) graph remains excluded upstream by node [15] and, with \(p=0\), does not satisfy the dense inequality.

### Graph patch

The smallest typed patch is:

```text
[170] yes: every conditional state-value range has size at most F_c
  -> [170a] barrier code injective, with explicit internal-window overhead
  -> [170b] uncompressed fiber baseline D * product(W_c) <= |G_near-cubic|
  -> [171] product count and exact dense contradiction
```

If [170b] is not uniform, insert a decision:

```text
[170b] fiberwise baseline/switching succeeds?
  yes -> [171]
  no  -> retain a minimal support-dependence witness
       -> [172] only after proving that witness is a connected barrier-overlap
          obstruction with every entry fact required by window-system realizability
```

The no-arm cannot be labelled [172] merely as the logical negation of a conjunction.  It must retain the fixed scale, outside record, first failing exposure coordinate, two graph codewords or unrealizable a-priori states witnessing the baseline failure, connected minimal support, and the completion-support overlap needed by `lem:barrier-failure-overlap`.

### Downstream impact

The Part-XII diagram label and caption, the `[169]--[172]` overview row, the detailed dependency entry calling [171] “the exact entropy step,” `rem:entropy-lives-here`, the proof summary near the start of the manuscript, and `prop:p13-density` all consume this compression and must cite the new baseline/switching lemma.  `rem:blocked-class-checks` does not prove it: part (a) explains why minimum degree matters, and part (b) is only a consistency example below the threshold.

In Lean, `Graph.BarrierSystem.ConditionalFibre` is explicitly a set of *state values*, not a fibre of blocked graph members.  `blockedEncodingRank_injective` proves only that the exposure order has no duplicate ranks; it is not injectivity of `blockedBarrierCode`.  `BlockedScaleAdditivityStatement` currently bundles the desired global cardinal inequality as its second conjunct.  Consequently `blockedClassCompressionCloses` kernel-checks by unpacking the very inequality node [171] is supposed to derive.  The fact schema should be split into conditional range additivity, code injectivity, the uncompressed baseline, and the derived saving.  The comments naming `selectedBlockedBarrierCodeInjectivity` and `selectedBlockedBarrierBaseline` need actual object-local producers.  The complement key for [172] must negate only the conditional-additivity predicate or carry an independently constructed overlap witness, rather than negate a conjunction containing [171]'s conclusion.  The human and JSON audit rows already identify this weaker/circular implementation and should be synchronized after the mathematical producers exist.  No proof, manuscript, diagram, Lean, or audit-source change is made by this report.

## 7. Regression audit

The audit used the searches

```text
rg -n 'lem:blocked-graphs-compress|blockedClassCompressionCloses|BlockedScaleAdditivityStatement|blockedScaleAdditive|blockedBarrierCode|ConditionalFibre|blocked class|blocked-class|compression closure|scale additivity|scale-additivity|uncompressed baseline|CodeInjectivity' to_formalize/erdos_64_proof.tex hypostructure/Hypostructure/Graph proofs/hypostructure_erdos_64_eg/HypostructureErdos64EG Assembly_node_audit.md web/data/eg_node_audit.json
rg -n 'barrier.*inject|inject.*barrier|uncompressed|baseline.*barrier|recod|switch.*barrier|blocked.*inject' to_formalize/erdos_64_proof.tex hypostructure/Hypostructure/Graph proofs/hypostructure_erdos_64_eg/HypostructureErdos64EG
rg -n 'word for word|same proof|verbatim|unchanged|analog' to_formalize/erdos_64_proof.tex
```

and inspected:

- the Part-XII TikZ node, incoming `yes` edge, terminal shape, caption, overview block, and detailed dependency rows for [169]--[172];
- `def:target-rank`, `lem:independent-target-entropy`, `lem:skeleton-dominates`, `lem:state-count-comparison`, and the full statement and proof of `lem:p13-window-package`;
- `def:window-realization-test` and the exact [159] dense overflow retained on this path;
- the full `def:blocked-class`, including fixed packing positions, minimum degree, window presence, blockedness, and current-object membership;
- `def:barrier-overlap-system`, `lem:barrier-failure-overlap`, and the statement/proof of `lem:scale-additivity` defining the [170] yes-predicate;
- every sentence of `lem:blocked-graphs-compress`, both checks in `rem:blocked-class-checks`, `rem:entropy-lives-here`, and the downstream use in `prop:p13-density` and the introductory proof summary;
- `Graph/BlockedClass.lean`'s exact subtype, current-object member, and cardinal domination theorem;
- `Graph/BarrierOverlapSystem.lean`'s `outsideEdges`, `code`, and value-set definition of `ConditionalFibre`;
- `Strategy/SpineVocabulary.lean`'s `blockedBarrierCode`, state counts, exposure rank, `BlockedScaleAdditivityStatement`, and `Holds` clauses;
- `Strategy/BlockedCompressionRows.lean`'s decision and `blockedClassCompressionCloses` proof;
- the literal `selectedScaleAdditivityDichotomy` consumer in Assembly and every reference to the proposed injectivity/baseline producers;
- the [169]--[172] rows in `Assembly_node_audit.md` and `web/data/eg_node_audit.json`.
- The report accepts the stated injective code. Its narrower objection is that the proof never charges the uncompressed `W_c` ranges against the ambient budget before subtracting them.

No manuscript or Lean theorem proving a fiberwise uncompressed barrier baseline, an injection of the displayed product type, or even injectivity of `blockedBarrierCode` was found.  The idiom search found no separate “word for word,” “same proof,” or analogous compression argument that supplies it.  The only relevant `verbatim` occurrence is a Lean comment claiming fidelity for `BlockedScaleAdditivityStatement`; its actual type includes the desired saving as an assumption.

## 8. Residual uncertainty

No actual dense blocked graph satisfying every accumulated condition was constructed.  It remains possible that the trivial-neutral fact \(Q=E\), together with a more detailed barrier-switching construction, yields the missing fiberwise baseline or the direct injection \(\Psi\); no such construction appears in the inspected sources.  Conversely, failure of a switching construction may produce a support-dependence object that can be routed to [172], but the necessary implication to a minimal connected completion-support overlap is also unproved here.

The exact internal-window reconstruction cost is unresolved.  Because the packing positions are fixed, there is no global placement cost, but a finitary path-order/orientation record may still be needed for injectivity; it would be \(O(p)\) bits and therefore subleading, provided it is stated and counted.  The report does not re-audit the arithmetic correctness of [172] or the earlier claims that the residual reaches [169].  It also does not claim that the missing entropy map cannot exist—only that [171]'s current incoming contract and proof do not establish it.
