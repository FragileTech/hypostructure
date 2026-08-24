<!-- red-team-audit
{
  "schema_version": 1,
  "proof": "erdos-gyarfas",
  "node": 160,
  "node_label": "\\(\\tau(\\theta)<1/4\\)?\\\\(exact [56] comparison)",
  "panel": "fig:proof-diagram-part-xii",
  "contract_sha256": "16f59fb0a67908e4f293708183b205d1ee9bca82d74758980eb91db68ea7c461",
  "manuscript_sha256": "106a8205a1718fbf90e1686a107b2143b9edca574e2b0c11415e7f44aee2c0f9",
  "graph_sha256": "dc67fae178f947a9607c167e383d85919633341bdd423e4c4a45e4c317b3a765",
  "lean_audit_sha256": "50324ef5594d635a52d83aeb297f2ca3f3d30ef58de4ce3602816c7e78365b12",
  "verdict": "WRONG ROUTING DESTINATION",
  "audited_at": "2026-08-24T21:07:05Z"
}
-->

# Red-team audit: node [160]

## 1. Executive verdict

Verdict: **WRONG ROUTING DESTINATION**

Node [160]'s exact strict comparison and its complement form a valid exhaustive decision, and the yes-arm does supply the \(1/4\) net-deficiency cap. The error is its direct yes-edge to [161] with the promise that the whole [25]--[64] Type A/Type B continuation closes. That continuation's route-8 no-two-support case needs the strictly stronger private-carrier inequality \(\tau<3/13\), whereas [160] assumes only \(\tau<1/4\). The manuscript itself retains \(1/78\le\theta<1/73\), equivalently \(3/13\le\tau<1/4\), as a delicate interval to be sent through the hot/cold pass. Thus this interval satisfies [160]'s yes predicate but fails [161]'s advertised destination contract. The live Lean assembly independently inserts the missing route8RateDichotomy; the proof-flow graph and lem:dense-deficiency-routing do not.

## 2. Exact node contract

### Incoming residual

The current object is the selected lexicographically minimal finite simple counterexample \(G\), with \(n=|V(G)|\), minimum degree at least \(3\), no power-of-two cycle, and the complete replacement/context ledger from [1]--[18]. The no-arm of [19] supplies the near-cubic bound \(\sigma(G)\le C_{\rm sp}\lceil\sqrt n\rceil\). Node [21] supplies the finite \(P_{13}\)-window enumeration and skeleton comparison. Let \(\mathcal P\) be the fixed canonical maximal vertex-disjoint induced-\(P_{13}\) packing, let \(p=|\mathcal P|\), and let \(R=G-\bigcup_{P\in\mathcal P}V(P)\), so

\[
|R|=n-13p.
\]

The selected incoming route is uniquely [158]'s no-arm through [159]. Its entry payload is the strict dense-package overflow

\[
2^{c_{13}p\log_2 n}>|\mathcal G_{n,m}|,
\]

with its asymptotic density reading \(\theta=p/n>\theta_{\rm win}+o(1)\). There is no merge and no loop. The hot/cold split [22] is not a manuscript ancestor of [160]; the Lean implementation computes the same current-object partition before the decision so it is available to both arms, but no sibling branch conclusion is imported.

### Accumulated facts

The cumulative contract at [160] contains:

1. [1]--[6]: \(G\) is the selected counterexample and every oriented edge avoids a Mersenne return.
2. [8]--[14]: every proper subgraph has minimum degree at most \(2\), \(V_{\ge4}(G)\) is independent, boundary-degree profiles and context universality are retained, and no permitted smaller target-complete replacement or compression exists.
3. [15]--[18]: \(G\) contains induced \(P_{13}\)'s; \(\mathcal P\) is fixed and maximal; the \(399\)-label algebra and its declared relations are available.
4. The no-arm of [19]: the same selected graph is on the near-cubic side, with surplus allowance \(T(n):=C_{\rm sp}\lceil\sqrt n\rceil\).
5. [21]: the exact finite enumeration, separated window package, and labelled skeleton bound are retained.
6. [158] no and [159]: the exact package-budget overflow is retained on the dense-packing residual.

The literal Lean ledger immediately before the decision consists of the original selected-counterexample keys together with barrierEnumeration, windowPackageSeparated, skeletonDominates, windowPackageUnrealized, densePackingOverflow, and the current-object hotColdPartition. The decision appends exactly one of denseDeficiencyBelow and denseDeficiencyAtOrAbove, while retaining every earlier fact.

### Current predicate and exact claim

At the registered values \(\delta=3\), window order \(13\), and discharge scale \(4\), DenseDeficiencyBelowStatement is

\[
4(39p+T(n))<96p+(n-13p),
\]

equivalently

\[
N:\qquad 4(15p+T(n))<|R|,
\qquad\text{or}\qquad
73p+4T(n)<n.
\]

This is the exact finite sufficient version of \(\tau(\theta)<1/4\), where

\[
\tau(\theta)=\frac{15\theta}{1-13\theta}.
\]

The decision is \(N\) versus \(\neg N\); these predicates are literal complements. On \(N\), node [29]'s supply estimate gives

\[
4(\defp(R)-\sigma_R)
\le 4\defp(R)
\le 4(15p+T(n))
<|R|,
\]

so the negative-net-charge localization is valid. What \(N\) does not imply is the exact route-8 private-carrier rate. Asymptotically that second rate is

\[
\tau(\theta)<\frac3{13}
\quad\Longleftrightarrow\quad
\theta<\frac1{78},
\]

and its exact Lean form is the separately decided Graph.Route8Census.Rate, not DenseDeficiencyBelowStatement.

### Outgoing contracts

The graph has two outgoing edges:

- yes, \(N\), to [161], whose stated contract is a negative-net-charge collision followed by [25] and closure of the Type A and Type B continuations with the deficiency cap in place of [24];
- no, \(\neg N\), to [162], which reruns the dense hot/cold pass.

The no-edge is a legitimate complement handoff, although its destination should be stated using the exact predicate rather than only the simplified phrase \(\tau\ge1/4\). The yes-edge is overbroad. In the Type A route-8 continuation, nodes [120]--[122] use

\[
12\left(\frac14-\tau\right)>\tau,
\]

equivalently \(\tau<3/13\). Therefore [161]'s advertised complete continuation needs both the \(1/4\) net cap and the route-8 rate. The selected edge supplies only the first.

## 3. Sentence audit

| Sentence | Exact assertion | Facts used | Hidden obligation | Adversarial test | Status |
|---|---|---|---|---|---|
| S1 | Node [160] decides the exact finite version of \(\tau(\theta)<1/4\). | Fixed \(p,n\), [19]'s \(T(n)\), DenseDeficiencyBelowStatement. | The allowance must be retained before clearing denominators. | Expanded the registered coefficients to \(73p+4T(n)<n\). | SUPPORTED |
| S2 | The two outgoing predicates are exhaustive. | Holds .denseDeficiencyAtOrAbove is the negation of DenseDeficiencyBelowStatement; Decision.run. | No equality case may be discarded. | Set \(73p+4T(n)=n\); equality goes to the no-arm. | SUPPORTED |
| S3 | The yes-arm supplies \(\defp(R)-\sigma_R<|R|/4\). | [29]'s supply bound and \(\sigma_R\ge0\). | The strict inequality must survive the upper-bound substitution. | Checked the complete chain \(4(\defp-\sigma_R)\le4(15p+T)<|R|\). | SUPPORTED |
| S4 | Negative total charge localizes to a connected admissible support. | lem:netcharge-superadd, prop:negative-net-charge. | Additivity and assigned surplus must refer to the same \(R\). | Traced the fixed packing and remainder through the exact ledger. | SUPPORTED |
| S5 | With that cap, [57]--[64] and the Type A/Type B continuations close exactly as on the spine. | lem:dense-deficiency-routing. | The Type A route-8 reduction additionally needs \(\tau<3/13\). | Chose \(\theta=1/75\), for which \(3/13<15/62<1/4\). | FAILED |
| S6 | Every \(\tau<1/4\) dense residual belongs on the [161] edge. | Part XII edge [160] \(\to\) [161]. | The manuscript's own delicate interval \(1/78\le\theta<1/73\) must instead reach the hot/cold pass. | Compared the edge with rows 1--3 of tab:cold-branch-ledger. | WRONG DESTINATION |
| S7 | The formal implementation faithfully consumes the yes-arm. | selectedNearCubicBranch. | It must not silently assume the route-8 rate from the \(1/4\) cap. | The code explicitly runs route8RateDichotomy and sends its failure to selectedRouteEightRateFailure. | IMPLEMENTATION REPAIRS GRAPH |

## 4. Counterexample attempts

### Smallest-parameter test

- **Explicit data:** Suppress the allowance and take \(p=1,n=74\). Then \(|R|=61\), \(73p<n\), and \(\tau=15/61<1/4\), but \(15/61>3/13\).
- **Hypotheses satisfied:** This is the smallest integer coefficient test in the delicate range \(73p<n\le78p\); it passes the allowance-free \(1/4\) comparison and fails the route-8 rate.
- **Accumulated facts violated:** The exact node uses the positive registered allowance \(T(74)\), not \(T=0\), and no graph satisfying [2]--[21] is supplied.
- **Applicability:** **NON-APPLICABLE TO THE NODE** as an exact residual, excluded first by node [160]'s exact parenthetical comparison. It identifies the threshold mismatch but is not the surviving candidate.

### Parity or 2-adic test

- **Explicit data:** Let \(n=75q\) and \(p=q\), with \(q\) chosen arbitrarily large and either odd or even. Then \(\theta=1/75\) and \(\tau=15/62\). Writing \(T(n)=C_{\rm sp}\lceil\sqrt n\rceil\), the exact yes predicate holds for all sufficiently large \(q\), because \(73q+4C_{\rm sp}\lceil\sqrt{75q}\rceil<75q\). The route-8 leading inequality fails with a linear margin: \(13(15q)>3(62q)\).
- **Hypotheses satisfied:** Both parities occur; the strict \(1/4\) comparison, the dense inequality \(\theta>\theta_{\rm win}\), and failure of the \(3/13\) route-8 rate coexist for sufficiently large \(q\). No division by an even quantity or 2-adic cancellation is used.
- **Accumulated facts violated:** None of the scalar branch constraints is violated. The family specifies parameter data, not an actual graph satisfying the target-avoidance, minimality, and replacement facts [2]--[21].
- **Applicability:** Applicable to the claimed implication between the selected branch predicate and its destination contract. It shows the gap persists for both parities and after the exact \(O(\sqrt n)\) allowance is restored.

### Boundary or range test

- **Explicit data:** For the fixed object quantities \(p,n,T(n)\), compare \(n=73p+4T(n)\) with \(n=73p+4T(n)+1\). Equality is \(\neg N\); increasing \(n\) by one enters \(N\). Separately, the asymptotic route-8 boundary is \(n=78p\).
- **Hypotheses satisfied:** These are the exact strict/equality cases for the two different cleared comparisons.
- **Accumulated facts violated:** No actual graph with the prescribed tied values is constructed; the equality test is an arithmetic model of the object quantities.
- **Applicability:** Applicable to exhaustiveness. It finds no missing equality case at [160], but confirms that the \(73p\) and \(78p\) boundaries cannot be identified or covered by the same yes-edge.

### Graph-realizability test

- **Explicit data:** The smallest cubic test graph \(K_4\) has \(n=4\), \(m=6\), and minimum degree \(3\), but it contains a \(4\)-cycle and has no induced \(P_{13}\), hence \(p=0\).
- **Hypotheses satisfied:** It is a finite simple cubic graph, so the basic degree and near-cubic arithmetic are concrete.
- **Accumulated facts violated:** It violates the target-avoidance predicate at [2] and never reaches the induced-\(P_{13}\) packing branch [15]--[17].
- **Applicability:** **NON-APPLICABLE TO THE NODE**, excluded first by node [2]. No actual minimal-counterexample graph realizing the \(1/75\) parameter profile was found.

### Branch-routing test

- **Explicit data:** Use the sufficiently large family \(n=75q,p=q\). It lies above \(\theta_{\rm win}=0.01270017798\ldots\), satisfies the exact [160] yes predicate for large \(q\), and has

  \[
  \frac3{13}<\frac{15}{62}<\frac14.
  \]

  Thus it enters the drawn yes-edge [160] \(\to\) [161] but fails the private-carrier inequality used when the Type A continuation reaches route 8.
- **Hypotheses satisfied:** The dense-overflow density regime, exact net-deficiency test, and the manuscript's declared delicate interval are mutually compatible. tab:cold-branch-ledger explicitly retains this interval and routes it through rows 4--16.
- **Accumulated facts violated:** Actual graph realization of the scalar family is not established, but no cited accumulated fact excludes the interval; the manuscript treats it as a live residual class.
- **Applicability:** Applicable to the source-level typed handoff. The current yes destination lacks a required fact, while the existing hot/cold destination [162] is the manuscript's stated handler for precisely this interval.

## 5. Strongest valid counterexample

The strongest candidate is the exact large-\(q\) branch profile \(n=75q,p=q\). It survives every numerical fact available at [160]: it is dense relative to \(\theta_{\rm win}\), the \(O(\sqrt n)\) allowance is eventually dominated by the linear \(1/4\)-margin, and so the exact yes predicate holds. Nevertheless \(\tau=15/62>3/13\), so the no-two-support route-8 collision used by the advertised Type A continuation is unavailable. The manuscript itself certifies the relevance of this profile by retaining the whole interval \(1/78\le\theta<1/73\) and assigning it to the hot/cold branch. No actual finite graph satisfying the complete minimal-counterexample residual was constructed, so this is a valid counterexample to the local routing implication, not a counterexample to the theorem.

## 6. Local repair

### Corrected statement

Let

\[
N:\quad 4(15p+T(n))<|R|
\]

be node [160]'s exact net-deficiency comparison, and let \(Q_8\) be the exact route-8 private-carrier rate

\[
13|\partial R|+12F\,T(n)<3|R|,
\]

with the same registered bridge-mass factor \(F\) and current packing. Node [160] decides \(N\). On \(\neg N\), enter the exact dense hot/cold pass. On \(N\), first decide \(Q_8\). The arm \(N\land Q_8\) enters [161] and then [25], carrying both the \(1/4\) net cap and the route-8 rate. The arm \(N\land\neg Q_8\) is the exact delicate-density residual and enters [162], not [161].

### Complete local proof

If \(N\) holds, the external-incidence supply gives

\[
4(\defp(R)-\sigma_R)
\le 4(15p+T(n))<|R|.
\]

Hence total net charge is negative and lem:netcharge-superadd selects a negative connected admissible support. Every use of the \(1/4\) cap through the initial [25]--[64] localization is therefore justified. If \(Q_8\) also holds, the private-support upper bound and route-8 burden have the strict margin used at [120]--[122]; the Type A route-8 continuation closes, while the other Type A and Type B outcomes retain their existing destinations. Thus \(N\land Q_8\) satisfies the full [161] contract.

If \(N\land\neg Q_8\), negative charge still localizes, but the route-8 no-two-support contradiction is unavailable. This is not a contradiction: asymptotically it includes \(3/13\le\tau<1/4\), exactly row 2 of tab:cold-branch-ledger. thm:cold-branch-quantitative-closure sends that row through the live-hot comparison, cold-mass extraction, and G1/G2/G3 or finite same-interface outcomes. Hence it belongs at [162]. If \(\neg N\), the same hot/cold pass is the already drawn destination and does not require the failed \(1/4\) sentence; its proof explicitly lists only current-residual structural facts. The three routed predicates \(\neg N\), \(N\land\neg Q_8\), and \(N\land Q_8\) are disjoint and exhaustive.

### Counterexample disposition

For \(n=75q,p=q\) and large \(q\), \(N\) holds but \(Q_8\) fails. The repaired subdecision therefore sends the candidate to [162], agreeing with the manuscript's delicate-density ledger. It no longer reaches [161] without the private-carrier fact.

### Graph patch

Insert one local decision between [160]'s yes-arm and [161]:

~~~text
[159] -> [160]: retain the complete dense residual
[160] -- no:  not N --> [162]
[160] -- yes: N --> [160a]: exact route-8 private-carrier rate Q8?
[160a] -- yes: Q8 --> [161]
    entry facts: complete [160] ledger + N + Q8
[160a] -- no: not Q8 --> [162]
    entry facts: complete [160] ledger + N + not Q8
~~~

Node [160a] may reuse the exact rate decision already represented in Lean by route8RateDichotomy. It should not be collapsed into [160], because \(N\) and \(Q_8\) have different thresholds and different consumers.

### Downstream impact

lem:dense-deficiency-routing must restrict its promise of complete Type A/Type B closure to \(N\land Q_8\); under \(N\) alone it may assert only the net-cap localization. lem:dense-cold-pass and the Part XII caption/table row must explicitly accept the additional \(N\land\neg Q_8\) incoming alternative, matching case 2 of tab:cold-branch-ledger. The [161] entry contract gains \(Q_8\); [162] gains the tagged exact-rate-failure alternative while retaining all earlier facts. The large-budget and route-8 results themselves need no mathematical change. The live Lean assembly already performs route8RateDichotomy before calling denseNetDeficiencyCapRow/selectedNetChargeContinuation, so its control flow should be documented as node [160a] rather than as an unnumbered repair. The node-status rows for [160]--[162] should be updated to audit the cross-node destination contract, not only the individual producers.

## 7. Regression audit

The audit inspected every indexed occurrence of lem:dense-deficiency-routing: the Part XII diagram and caption, detailed dependency-table item 51, the source lemma and proof, the theorem-dependency ledger row, and rem:dense-residual-status. It also inspected def:cold-window-ledger, rows 1--3 and the closure proof of tab:cold-branch-ledger, nodes [120]--[122] in Part IX, thm:large-budget-route8-only, and rem:route8-carrier-margin. The latter states explicitly that the tight reduction requires \(\tau_{\rm win}<3/13\).

On the formal side, the audit inspected DenseDeficiencyBelowStatement, its two Holds clauses, the inline Decision.run at [160], denseNetDeficiencyCapRow, route8RateDichotomy, the yes-arm and failure-arm calls inside selectedNearCubicBranch, and selectedRouteEightRateFailure. The code comments explicitly say that the dense arm's \(\tau<1/4\) does not decide the route-8 rate and identify the same delicate interval. The implementation-audit rows [160]--[162] and the corresponding explorer entries were read as locators; their producer-local “faithful” labels do not check the missing graph edge.

Searches included:

~~~text
rg -n 'lem:dense-deficiency-routing|lem:dense-cold-pass|delicate density interval|3/13|1/78|route8-carrier-margin|exactly as the spine|verbatim' \
  to_formalize/erdos_64_proof.tex hypostructure proofs Assembly_node_audit.md web/data/eg_node_audit.json

rg -n 'DenseDeficiencyBelowStatement|denseDeficiencyBelow|denseDeficiencyAtOrAbove|route8RateDichotomy|selectedRouteEightRateFailure|denseNetDeficiencyCapRow' \
  hypostructure proofs
~~~

No manuscript edge or local subdecision was found that sends \(N\land\neg Q_8\) from [160]'s yes-arm to [162]. No second use was found that validly derives the \(3/13\) rate from the \(1/4\) cap.

## 8. Residual uncertainty

No concrete minimal counterexample graph realizes the \(n=75q,p=q\) profile; its force is as an unexcluded branch state and as a counterexample to the asserted numerical implication. The exact finite correspondence between every Graph.Route8Census.Rate term and the manuscript's asymptotic \(\tau<3/13\) was inspected through its defining formula and producer comments, not re-proved from the entire route-8 census library. The downstream completeness of [162], including its separately listed open Lean producers, is outside this single-node audit. No manuscript, proof-flow diagram, Lean source, implementation-audit source, or coverage ledger was changed.
