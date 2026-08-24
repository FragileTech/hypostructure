<!-- red-team-audit
{
  "schema_version": 1,
  "proof": "erdos-gyarfas",
  "node": 161,
  "node_label": "negative-net-charge collision:\\\\continue at [25] with the deficiency cap in place of [24]",
  "panel": "fig:proof-diagram-part-xii",
  "contract_sha256": "8a2a5d2f658252e3fd12ef3466806446998870c028b24bf5de20f35bb277b4fb",
  "manuscript_sha256": "106a8205a1718fbf90e1686a107b2143b9edca574e2b0c11415e7f44aee2c0f9",
  "graph_sha256": "dc67fae178f947a9607c167e383d85919633341bdd423e4c4a45e4c317b3a765",
  "lean_audit_sha256": "50324ef5594d635a52d83aeb297f2ca3f3d30ef58de4ce3602816c7e78365b12",
  "verdict": "MISSING RANGE OR DIVISIBILITY CHECK",
  "audited_at": "2026-08-24T21:09:22Z"
}
-->

# Red-team audit: node [161]

## 1. Executive verdict

Verdict: **MISSING RANGE OR DIVISIBILITY CHECK**

Node [161] correctly turns the exact yes-arm of [160] into the strict net-deficiency cap and may therefore enter Residual A at [25]. It does not, however, justify the stronger claim in \(\cref{lem:dense-deficiency-routing}\) that the Type A/Type B continuation closes “exactly as the spine.” The downstream no-two-support route-8 contradiction [120]–[122] needs the stricter exact form of \(\tau<3/13\), while [160] supplies only the exact form of \(\tau<1/4\). The nonempty interval \(3/13\le\tau<1/4\), equivalently \(1/78\le\theta<1/73\) before finite allowances, is explicitly row 2 of the manuscript's cold-branch ledger and is assigned there to the hot/cold pass. The proof and graph omit that range check at [161].

## 2. Exact node contract

### Incoming residual

The sole incoming edge is the yes-arm [160] → [161]. There is no merge, loop, or strongly connected component. The current object is the selected finite simple minimal counterexample \(G\), with \(n=|V(G)|\), minimum degree at least three, no power-of-two cycle, the no-return formulation, no proper internal \(3\)-core, edge-deletion criticality, independent high-degree vertices, retained context/replacement/uncompressibility facts, and the deterministic maximal packing \(\mathcal P\) of vertex-disjoint induced \(P_{13}\)'s. Write
\[
p=|\mathcal P|,\qquad R=G-\bigcup_{P\in\mathcal P}V(P),\qquad |R|=n-13p.
\]

The path is the near-cubic arm of [19], so
\(\sigma(G)\le T(n):=C_{\rm sp}\lceil\sqrt n\rceil\). Node [158] has taken its no-arm and [159] retains the exact strict package overflow
\[
2^{c_{13}p\log_2n}>|\mathcal G_{n,m}|.
\]
Node [160] has taken the strict yes-arm of the exact [56] comparison. At the manuscript's registered values this is
\[
4\bigl(15p+T(n)\bigr)<|R|.
\tag{160}
\]
The asymptotic shorthand is \(\tau(\theta)<1/4\), where
\(\theta=p/n\) and \(\tau(\theta)=15\theta/(1-13\theta)\), but the retained fact is (160).

### Accumulated facts

1. [1]–[6]: \(G\) is the selected minimal counterexample, \(\delta(G)\ge3\), and every oriented edge avoids the Mersenne-return formulation of a power-of-two cycle.
2. [8]–[14]: \(G\) is bridgeless, has no proper minimum-degree-three core, every edge has a degree-three endpoint, \(V_{\ge4}(G)\) is independent, and the degree-fibre, context-universality, replacement-exclusion, and hereditary-uncompressibility ledgers are retained.
3. [15]–[17]: an induced \(P_{13}\) exists and \(\mathcal P\) is a fixed maximum-cardinality packing; hence every component of \(R\) is induced-\(P_{13}\)-free and has empty internal \(3\)-core.
4. [18]–[19]: the \(399\)-label algebra is available and \(\sigma(G)\le T(n)\) on the near-cubic branch.
5. [21]: the separated window package and labelled skeleton bound are retained.
6. [158]–[159]: the package-realization test failed, so the exact package demand strictly exceeds the skeleton class.
7. [160] yes: the exact strict inequality (160) holds for the fixed maximum packing.
8. The surplus-aware stub inequality gives
   \[
   \defp(R)-\sigma_R\le15p+\sigma_W-\sigma_R\le15p+T(n).
   \]

No [24] density-cap fact is on this route. In particular, nothing accumulated at [161] implies the stronger route-8 carrier rate \(\tau<3/13\).

### Current predicate and exact claim

The valid local consequence of (160) and the stub inequality is
\[
4\bigl(\defp(R)-\sigma_R\bigr)
\le4\bigl(15p+T(n)\bigr)<|R|,
\]
so
\[
\defp(R)-\sigma_R<\frac14|R|.
\tag{161-cap}
\]
The exact net-charge identity over the canonical connected support decomposition \(R=\bigsqcup_iX_i\) is
\[
\sum_i\No(X_i)=\defp(R)-\sigma_R-\frac14|R|<0.
\]
Consequently some connected admissible support \(X_i\) has \(\No(X_i)<0\). This part uses strict negativity only; it does not require the fixed linear margin appearing in the separately stated asymptotic proposition.

The overbroad claim attached to the node is that (161-cap) can replace [24] throughout the later spine and close the Type A and Type B continuations. That claim has an additional hidden premise: the route-8 no-two-support arm uses, at [120]–[122],
\[
\tau<\frac3{13}
\]
in its exact finite form. The inequality \(\tau<1/4\) does not imply it.

### Outgoing contracts

The extracted proof-flow graph has one continuation:

- **[161] → [25]:** “deficiency cap in place of [24]: enters Residual A in Part II.”

The destination's immediate entry contract is met. From (160),
\(|R|>60p\), hence \(n=13p+|R|<\tfrac{73}{60}|R|\), so \(R\) is a linear-sized remainder. Maximality of \(\mathcal P\) gives componentwise induced-\(P_{13}\)-freeness and empty internal \(3\)-core. The cap (161-cap) can be retained on this edge.

What is not met is the advertised complete continuation contract after Type A reaches route 8. The [120] private-carrier inequality is not a consequence of (161-cap). The route therefore needs a second exact decision before the proof may claim that all of the [161] residual is closed by the ordinary spine.

## 3. Sentence audit

| Sentence | Exact assertion | Facts used | Hidden obligation | Adversarial test | Status |
|---|---|---|---|---|---|
| S1 | The [160] yes-arm produces the strict deficiency cap (161-cap). | Exact comparison (160); surplus-aware stub bound; \(\sigma_W\le\sigma(G)\le T(n)\) | Natural-number subtraction and the surplus signs must not reverse the inequality. | Clear denominators and test the strict boundary. | SUPPORTED |
| S2 | Negative total charge localizes to a connected admissible support. | (161-cap); exact component identity in \(\cref{lem:netcharge-superadd}\) | The support decomposition must be disjoint and exact on deficiency, surplus, and vertex count. | Give every component nonnegative charge while keeping the sum negative. | SUPPORTED |
| S3 | The residual may enter [25]. | (160); maximal packing [17] | \(R\) must be large and componentwise \(P_{13}\)-free. | Use \(|R|\le60p\) or add an induced \(P_{13}\) inside \(R\). | SUPPORTED |
| S4 | The deficiency cap can stand in place of [24] for every later consumer. | \(\cref{lem:dense-deficiency-routing}\), proof sentence “nothing else” | Every descendant that formerly used [24] must require no stronger rate. | Inspect the route-8 private-support bound [120]. | FAILED |
| S5 | Nodes [57]–[64] apply verbatim. | (161-cap); net-charge identity | The statement must be limited to collision, localization, and the Type A/Type B split, not terminal closure. | Stop at the entries [63] and [64]. | SUPPORTED AS A LOCAL PREFIX |
| S6 | The Type A/Type B continuations close exactly as on the density-capped spine. | Claimed use of the same cap through [56] | Route 8 additionally needs exact \(\tau<3/13\). | Choose \(3/13\le\tau<1/4\). | FAILED |
| S7 | All dense residuals with \(\tau<1/4\) are closed by [160]–[161]. | Detailed dependency rows and dense-residual status paragraph | The delicate density interval must already be assigned. | Compare with row 2 of \(\cref{tab:cold-branch-ledger}\). | FAILED |

## 4. Counterexample attempts

### Smallest-parameter test

- **Explicit data:** Ignore the finite allowance and take \(p=1\), \(n=75\), \(|R|=62\), \(T=0\). Then \(\tau=15/62<1/4\) but \(\tau>3/13\).
- **Hypotheses satisfied:** The packing/remainder identity \(n=13p+|R|\), positivity, and the two rational comparisons hold.
- **Accumulated facts violated:** The registered near-cubic allowance is \(T(n)=C_{\rm sp}\lceil\sqrt n\rceil>0\). The exact [160] inequality would require \(60+4T<62\), which fails for the actual positive allowance.
- **Applicability:** **NON-APPLICABLE TO THE NODE.** The earliest excluding node is [160], whose yes-arm is the exact comparison with the \(\sqrt n\) allowance, not the allowance-free ratio.

### Parity or 2-adic test

- **Explicit data:** Let \(S=C_{\rm sp}\), \(q=S+1\), \(k=1200q^2+1\), \(p=k\), \(n=75k\), and \(|R|=62k\). Then \(p,n\) are odd and \(|R|\) is even. Moreover \(\lceil\sqrt{75k}\rceil\le301q\), so
  \[
  4S\lceil\sqrt n\rceil\le1204Sq<2k=|R|-60p.
  \]
  Thus the exact [160] inequality holds, while \(15p/|R|=15/62\ge3/13\).
- **Hypotheses satisfied:** The exact finite deficiency comparison, the packing/remainder cardinality identity, strict \(\tau<1/4\), and failure of the route-8 threshold.
- **Accumulated facts violated:** None at the arithmetic or parity level. The tuple does not itself construct a graph satisfying the complete minimal-counterexample ledger or prove the independent package-overflow fact [159].
- **Applicability:** Applicable to the node's exact numerical implication. It shows that parity and 2-adic compatibility do not remove the missing interval; graph realization remains a separate obligation.

### Boundary or range test

- **Explicit data:** Let \(S=C_{\rm sp}\), \(q=S+1\), \(p=78q^2\), \(n=6084q^2=(78q)^2\), \(|R|=5070q^2=65p\), and \(T=S\lceil\sqrt n\rceil=78Sq\). Then
  \[
  4(15p+T)<|R|
  \]
  because the allowance contribution \(312Sq\) is smaller than the base margin \(390q^2\). But
  \[
  \frac{15p}{|R|}=\frac3{13},
  \]
  exactly the strict route-8 boundary.
- **Hypotheses satisfied:** The exact [160] yes-predicate and the exact cardinality identity.
- **Accumulated facts violated:** None numerically; an actual graph and [159]'s exact package overflow are not constructed by the tuple.
- **Applicability:** Applicable as the finite boundary model. The strict \(1/4\) decision includes it, whereas the strict \(3/13\) route-8 decision rejects it.

### Graph-realizability test

- **Explicit data:** Take \(G=K_4\) and the empty \(P_{13}\)-packing, so \(n=4\), \(p=0\), and \(R=G\). It is a finite simple bridgeless graph of minimum degree three and has negative allowance-free net charge.
- **Hypotheses satisfied:** Basic simplicity, connectivity, minimum degree, and the formal \(p=0\) remainder identity.
- **Accumulated facts violated:** \(K_4\) contains a cycle of length \(4\), violating the counterexample predicate at [2]/[5]; it also violates [15]'s induced-\(P_{13}\) branch and cannot satisfy [159]'s dense package overflow.
- **Applicability:** **NON-APPLICABLE TO THE NODE.** The earliest excluding fact is [2], the absence of power-of-two cycles.

### Branch-routing test

- **Explicit data:** Let \(S=C_{\rm sp}\), choose \(q=M(S+1)\) with \(M\ge1\), and set
  \[
  p=1200q^2,\qquad n=90000q^2=(300q)^2,\qquad |R|=74400q^2,\qquad T=300Sq.
  \]
  Then
  \[
  4(15p+T)
  =72000q^2+1200Sq
  <74400q^2=|R|,
  \]
  so [160] routes to [161]. Nevertheless
  \[
  \tau=\frac{15p}{|R|}=\frac{15}{62},
  \qquad
  \frac3{13}<\frac{15}{62}<\frac14
  \]
  because \(3\cdot62=186<195=15\cdot13\) and \(15\cdot4=60<62\). More directly, the exact route-8 left side already contains \(13\cdot15p=195p\), while \(3|R|=186p\), so the exact route-8 inequality fails even before its positive allowance terms are added.
- **Hypotheses satisfied:** The exact [160] yes-predicate, the retained deficiency cap, a linear remainder, and the exact failure of the later route-8 rate. The [159] package overflow can be retained independently; asymptotically \(\theta=1/75>\theta_{\rm win}\), so this range is compatible with the dense branch rather than excluded by it.
- **Accumulated facts violated:** No numerical accumulated fact. No concrete minimal-counterexample graph realizing all structural ledgers is supplied.
- **Applicability:** Applicable to the branch implication being audited. The current graph sends it only through [161] → [25], but row 2 of the manuscript's own cold ledger says this rate-failure interval must run the hot/cold pass.

## 5. Strongest valid counterexample

The branch-routing family with \(\theta=1/75\) is the strongest candidate. It satisfies the exact finite [160] inequality including \(C_{\rm sp}\lceil\sqrt n\rceil\), produces the strict net-deficiency cap, remains within the dense asymptotic range of [159], and fails the exact route-8 rate before allowance terms are counted. Thus it survives every numerical fact used at [161] and refutes the claimed implication “\(\tau<1/4\), therefore the ordinary Type A/Type B spine closes.” No concrete graph satisfying the complete minimal-counterexample ledger was constructed, so the candidate is not asserted to disprove the theorem; it establishes the missing range implication and matches the manuscript's already acknowledged delicate interval.

## 6. Local repair

### Corrected statement

On the dense-packing residual, the exact yes-arm of [160] supplies
\(\defp(R)-\sigma_R<|R|/4\). Hence the residual enters [25], the negative charge localizes at [58]–[64], and the Type A/Type B split is available. Before claiming terminal closure, decide the exact route-8 carrier inequality used at [120]. If that inequality holds, continue through [25] with the deficiency cap and the route-8 rate in place of [24]. If it fails, including the range \(3/13\le\tau<1/4\) up to exact allowances, send the retained dense residual through the hot/cold pass [162], whose proof does not use the \(\tau\ge1/4\) sentence.

### Complete local proof

Let \(T=C_{\rm sp}\lceil\sqrt n\rceil\). The [160] yes-arm gives
\[
4(15p+T)<|R|.
\]
The exact stub ledger gives
\[
\defp(R)-\sigma_R
\le15p+\sigma_W-\sigma_R
\le15p+\sigma_W
\le15p+\sigma(G)
\le15p+T.
\]
Multiplication by four proves (161-cap), so the exact net-charge component identity has negative total. One connected admissible component therefore has negative charge. Also \(|R|>60p\), and maximality of the \(P_{13}\)-packing gives the full [25] structural entry.

Now decide the exact [120] carrier predicate. It and its negation are literal complements. On the yes-arm, the retained rate is precisely the additional fact used by the private-support upper bound; the remaining Type A/Type B continuation can therefore use the same inequalities as the ordinary spine. On the no-arm, no contradiction follows from (161-cap): the arithmetic family in Section 5 realizes this logical combination. Instead retain the packing, dense overflow, near-cubic surplus bound, hot/cold data when formed, deficiency cap, and route-8 failure, and run the hot/cold pass. The proof of \(\cref{lem:dense-cold-pass}\) explicitly lists only facts of the current residual and says that the density sentence is not among them; row 2 of \(\cref{tab:cold-branch-ledger}\) assigns this exact interval to rows 4–16. The two exact carrier arms are exhaustive, so no range remains unassigned.

### Counterexample disposition

The smallest allowance-free tuple is excluded by [160]. The equality tuple at \(\tau=3/13\) and the interior \(\theta=1/75\) family are caught by the new exact route-8 decision and sent to [162], rather than being claimed closed by [120]–[122]. The \(K_4\) construction is excluded at [2]. No parity case requires a separate route.

### Graph patch

The smallest proof-flow patch is

    [160] -- yes: exact net-deficiency comparison --> [161]
    [161] -- exact route-8 carrier inequality holds --> [25]
    [161] -- exact route-8 carrier inequality fails --> [162]
    [160] -- no: net-deficiency comparison fails --> [162]

The [25] edge retains the complete [161] ledger plus both the strict deficiency cap and the exact route-8 rate. The new [162] edge retains the complete dense-packing ledger, the [161] deficiency cap, and the exact rate failure; [162]'s hot/cold proof is valid on this stronger residual because it does not consume the sign of the \(1/4\) comparison.

### Downstream impact

The Part XII node [161], its outgoing continuation, panel caption/summary, detailed dependency-table rows for [158]–[168] and \(\cref{lem:dense-deficiency-routing}\), the lemma's statement and proof, and \(\cref{rem:dense-residual-status}\) must distinguish negative-charge localization from terminal route-8 closure. The cold quantitative ledger already has the correct case split and needs no mathematical change.

The live Lean control flow in selectedNearCubicBranch already exposes the missing premise: on the [160] yes-history it runs route8RateDichotomy before selectedSpineToLargeBudget, and only its left arm reaches denseNetDeficiencyCapRow and selectedNetChargeContinuation. This is evidence for the proposed graph patch, not a formal repair of the manuscript: the rate-failure continuation is absent from the displayed DAG, and the empty-cold subarm ends at the open producer selectedRouteEightBudgetEdge. The node-audit table and web audit currently calling [161] fully faithful should be revised after the proof source is repaired.

## 7. Regression audit

- Inspected the Part XII diagram node [161], the sole continuation [161] → [25], the panel caption and summary, and the route-alternative union at destination [25].
- Inspected the detailed dependency block for [158]–[168], the table row for \(\cref{lem:dense-deficiency-routing}\), the full statement and proof of that lemma, and \(\cref{rem:dense-residual-status}\).
- Inspected \(\cref{tab:cold-branch-ledger}\) and \(\cref{thm:cold-branch-quantitative-closure}\). Their rows 1–3 explicitly separate \(\theta<1/78\), \(1/78\le\theta<1/73\), and \(\theta\ge1/73\); the middle range is routed to the hot/cold branch.
- Inspected the route-8 diagram [110]–[124], especially [120]–[122], and the accompanying caption. The no-two-support contradiction explicitly ends with \(\tau<3/13\), not merely \(\tau<1/4\).
- Inspected the exact collision repair [173]–[177], \(\cref{lem:exact-collision-test}\), \(\cref{prop:negative-net-charge}\), and \(\cref{lem:netcharge-superadd}\). The exact charge localization itself needs only strict negativity and does not remove the later route-8 interval.
- Inspected DenseDeficiencyBelowStatement, denseNetDeficiencyCapRow, the netDeficiencyCap contract, route8RateDichotomy, selectedSpineToLargeBudget, selectedNetChargeContinuation, selectedRouteEightRateFailure, and the [160] branch inside selectedNearCubicBranch. The formal branch explicitly comments that \(\tau<1/4\) does not decide \(\tau<3/13\).
- Inspected Assembly_node_audit.md and web/data/eg_node_audit.json as locators, then checked the cited source declarations. Their “faithful” classification for [161] does not account for the later [120] consumer.
- Search patterns included: “dense-deficiency-routing”, “deficiency cap in place”, “[161]”, “tab:cold-branch-ledger”, “3/13”, “route8RateDichotomy”, “denseNetDeficiencyCapRow”, and “selectedRouteEightRateFailure” across to_formalize/erdos_64_proof.tex, hypostructure, proofs, Assembly_node_audit.md, and web/data/eg_node_audit.json.
- Negative searches found no second manuscript lemma proving \(\tau<3/13\) from the [160] yes-arm and no displayed graph edge assigning the [161] rate-failure complement to [162].

## 8. Residual uncertainty

No actual minimal-counterexample graph realizing the arithmetic family was found; constructing one would exceed the local audit and, if all theorem hypotheses held, contradict the target result. The exact finite package overflow [159] was retained as an incoming branch fact rather than independently proved for a concrete member of the symbolic family, although its fixed ratio \(\theta=1/75>\theta_{\rm win}\) lies in the manuscript's asymptotic dense regime. This audit verified that \(\cref{lem:dense-cold-pass}\) declares the \(1/4\)-density sentence unused, but it did not re-prove every closure inside [162]. The all-hot exact rate-failure corner represented by selectedRouteEightBudgetEdge remains an open formal producer and may require a more refined destination than [162]; that downstream implementation uncertainty does not restore the missing implication at [161]. No manuscript, proof-flow, Lean, audit-source, or coverage-ledger file was changed.
