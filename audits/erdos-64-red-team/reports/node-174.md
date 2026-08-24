<!-- red-team-audit
{
  "schema_version": 1,
  "proof": "erdos-gyarfas",
  "node": 174,
  "node_label": "absorbed-configuration residual:\\\\the exact collision fails and the selected cold corridors were charged to high-degree vertices",
  "panel": "fig:proof-diagram-part-v",
  "contract_sha256": "b062789ebc53dfb1f15a0fa96b51688c1a51a7ab16cbb17467b1b96661ae583a",
  "manuscript_sha256": "106a8205a1718fbf90e1686a107b2143b9edca574e2b0c11415e7f44aee2c0f9",
  "graph_sha256": "dc67fae178f947a9607c167e383d85919633341bdd423e4c4a45e4c317b3a765",
  "lean_audit_sha256": "50324ef5594d635a52d83aeb297f2ca3f3d30ef58de4ce3602816c7e78365b12",
  "verdict": "MISSING RANGE OR DIVISIBILITY CHECK",
  "audited_at": "2026-08-24T21:39:03Z"
}
-->

# Red-team audit: node [174]

## 1. Executive verdict

Verdict: **MISSING RANGE OR DIVISIBILITY CHECK**

The no-arm of [173] does rearrange exactly to
\[
73C\ge n-73|\mathcal P_{\rm hot}|-4(\sigma_W-\sigma_R).
\]
It does not follow, without a positive lower bound for the numerator, that (C>0), much less that there are linearly many cold windows or an actual selected cold corridor.  The finite boundary data
\[
n=77,quad |\mathcal P_{\rm hot}|=1,quad C=0,quad
\sigma_W=1,quad \sigma_R=0,quad |R|=64,quad \defp(R)=16
\]
satisfy the exact stub ceiling and make the strict collision fail by equality, while the displayed lower bound says only (0\ge0).  They also satisfy the route-[146] boundary (p_{13}/n>1/78), the near-cubic surplus scale, and the bounded-arm inequality vacuously.  Thus the small-order repair has silently reused the sufficiently-large-(n) positivity that it was meant to eliminate.  Before [175], the proof needs an exact nonempty-eligible-corridor decision; its empty complement must go to a separately proved finite budget-edge residual.  This is a local finite-range gap, not an actual target-free graph counterexample.

## 2. Exact node contract

### Incoming residual

The sole immediate edge is `[173] -- no --> [174]`.  The selected object is the same finite simple graph (G), chosen as a lexicographically minimal counterexample at [4], with minimum degree at least three, no cycle of power-of-two length, no proper minimum-degree-three core, independent (V_{\ge4}(G)), the replacement/context-universality facts of [11]--[14], and a fixed maximal vertex-disjoint induced-(P_{13}) packing
\[
\mathcal P=\mathcal P_{\rm hot}\sqcup\mathcal P_{\rm cold},
\qquad
p_{13}=H+C,
\]
where (H=|\mathcal P_{\rm hot}|) and (C=|\mathcal P_{\rm cold}|).  Write (W=\bigcup_{P\in\mathcal P}V(P)), (R=G-W), (sigma_W=\sigma(W)), and (sigma_R=\sigma(R)).  The exact identities retained at [173] are
\[
|R|=n-13p_{13},
\qquad
\defp(R)\le e(R,W)\le15p_{13}+\sigma_W.
\]

On the ordinary spine route, the only live edge to [24] is the bounded arm of [153], so that tagged residual also carries
\[
13C\le(13+B_{\rm cold})\sigma(G)
\]
in the exact Lean normalization.  This is an upper bound on cold mass, not a positive lower bound and not a witness that a selected corridor exists.  The graph ancestry extractor also lists the dense [159]--[161] route.  On the manuscript's [160]-yes route, [161] already supplies the exact negative-net-charge comparison, so the [173]-no arm is empty there; this does not supply `coldMassBounded` as an untagged common premise.

Node [173]'s selected branch predicate is the literal complement of the strict collision:
\[
15(H+C)+\sigma_W-\sigma_R
\ge \frac14\bigl(n-13(H+C)\bigr).
\]
Equivalently, the failure witness has nonnegative net charge,
\[
4\bigl(\defp(R)-\sigma_R\bigr)\ge |R|.
\]

### Accumulated facts

The facts usable at [174] are:

- `[2]`, `[4]`--`[14]`: the selected actual counterexample, target avoidance, minimality, high-degree independence, context universality, replacement, and hereditary uncompressibility.
- `[17]`, `[25]`--`[29]`: the maximal induced-(P_{13}) packing, its remainder, (|R|+13p_{13}=n), and the exact incidence ceiling (defp(R)\le e(R,W)\le15p_{13}+\sigma_W).
- `[19]`: the near-cubic route, in particular (sigma(G)) is bounded by the registered (C_{\rm sp}\lceil\sqrt n\rceil), but that finite bound can dominate the small linear margin.
- `[22]`: the actual hot/cold partition and (p_{13}=H+C).
- `[146] -- no`, on the ordinary cold route: (p_{13}/n\ge1/78).
- `[148] -- no`: the live-hot code does not overflow the exact skeleton budget.  Its asymptotic consequence is (H\le\theta_{\rm win}n+o(n)); no exact positive value of (n-73H-4(\sigma_W-\sigma_R)) is retained.
- `[153] -- bounded`, on the ordinary route: (13C\le(13+B_{\rm cold})\sigma(G)), followed by the finite density slack at [24].  This permits (C=0).
- `[55]`--`[57]`: the large-budget residual and the object-exact decision at [173].
- `[173] -- no`: the failed strict collision, hence only the weak cleared inequality at [174].

No ancestor supplies any of
\[
n-73H-4(\sigma_W-\sigma_R)>0,
\qquad C>0,
\qquad
\mathcal E_{\rm eligible}\ne\varnothing,
\]
where (mathcal E_{\rm eligible}) is the set of selected branch-excess half-edges of ambient-cubic cold windows that actually leave the cold-window union.

### Current predicate and exact claim

The valid arithmetic implication is
\[
\begin{aligned}
&4\bigl(15(H+C)+\sigma_W-\sigma_R\bigr)
   \ge n-13(H+C)\\
&\hspace{3em}\Longrightarrow
73C\ge n-73H-4(\sigma_W-\sigma_R).
\end{aligned}
\]
The manuscript then claims three stronger conclusions:

1. the residual carries linearly many cold windows;
2. it lies on the bounded arm of [153], whose loss consists of selected corridors charged to high-degree vertices; and
3. it can pass unconditionally to [175], which chooses and classifies a selected corridor.

Conclusion 1 needs a uniform positive margin after the exact hot and surplus errors are subtracted.  Conclusion 2 is route-tagged rather than an arithmetic consequence of failure, and the diagram label overstates it: [175] still has to decide whether a corridor meets a high-degree vertex.  Conclusion 3 needs existence of an eligible selected corridor.  None follows from the displayed inequality at finite order.

The Lean fact `absorbedConfigurationResidual` accurately stores only the subtraction-free inequality
\[
n+4\sigma_R\le73(H+C)+4\sigma_W.
\]
Its vocabulary comment calls this “linearly many,” but the proposition contains neither (C>0) nor a corridor witness.  `absorbedGermDichotomy` tests whether the candidate-germ finset has positive cardinality; when it is empty, its all-heavy alternative is a universal statement over the empty eligible-stub type.  That vacuity is not a Type B representative.

### Outgoing contracts

The displayed edge `[174] --> [175]` has no predicate.  Its intended destination contract needs an actual selected branch-excess half-edge (epsilon) of an ambient-cubic cold window, its return corridor, and its first-failure support (J).  Node [175] then splits:

- (J\cap V_{\ge4}(G)=\varnothing): retain the actual subcubic germ and route it to [176];
- (J\cap V_{\ge4}(G)\ne\varnothing): retain an actual (z\in J\cap V_{\ge4}(G)), its cubic neighbours, and the two corridor tails, and route it to [177]/Type B [65].

If (mathcal E_{\rm eligible}=\varnothing), neither destination receives a representative.  A universal “every selected corridor is heavy” is then true but supplies no centre (z).  The outgoing contract therefore needs an explicit nonemptiness branch before [175].

## 3. Sentence audit

| Sentence | Exact assertion | Facts used | Hidden obligation | Adversarial test | Status |
|---|---|---|---|---|---|
| S1 | The collision is the exact displayed strict inequality on the current object. | [29], (|R|=n-13p), hot/cold split. | The packing and both surplus terms must be those of the same object. | Substitute (n=77,p=1,sigma_W=1,sigma_R=0). | SUPPORTED |
| S2 | [173] decides the strict inequality. | Decidability of an integer inequality. | The no-arm must retain the literal weak reverse inequality, including equality. | Equality (16=|R|/4). | SUPPORTED |
| S3 | Failure rearranges to (C\ge(n-73H-4(\sigma_W-\sigma_R))/73). | S2 and (p=H+C). | The rational display must be read as the cleared integer inequality; it does not imply a positive integer. | Numerator (0). | SUPPORTED AS A WEAK BOUND |
| S4 | “So” the residual has linearly many cold windows. | S3, asymptotic hot cap, near-cubic surplus. | Need an explicit positive margin, or a finite threshold proving the numerator is at least (73). | (n=77,H=1,C=0,sigma_W-sigma_R=1). | FAILED |
| S5 | The residual lies on [153]'s bounded arm. | Ordinary [153]-bounded route. | This must be retained as a route tag, not inferred from S3 or asserted on the dense merge. | Compare the [153] and [161] predecessor histories. | AMBIGUOUS |
| S6 | Its cold mass was charged as configuration-extraction loss. | `coldMassBounded`. | A scalar upper bound does not identify an actual discarded half-edge or prove all loss is high-degree. | (C=0) makes the scalar bound vacuous. | FAILED |
| S7 | The stub supply and support-size identities are exact. | `lem:stub-positive`, induced path has 12 internal edges. | Boundary incidence and surplus must not be replaced by (o(n)). | (defp=e=16=15p+sigma_W). | SUPPORTED |
| S8 | Failure of the strict collision is an integer fact of the object. | S1--S2. | Equality must stay on the failure arm. | Cleared equality (4\cdot16=64). | SUPPORTED |
| S9 | The bounded arm's only content is the extraction loss. | [153]-bounded prose. | Must exclude (C=0), non-ambient-cubic-only cold mass, and every other finite slack source, or split them. | Empty cold family. | FAILED |
| S10 | Node label: the selected cold corridors “were charged to high-degree vertices.” | S6. | Requires actual selected corridors and actual high-degree witnesses; otherwise [175]'s no-arm is incoherent. | (mathcal E_{\rm eligible}=\varnothing). | FAILED |
| S11 | Unconditional edge [174] to [175]. | S4--S6. | Destination needs an actual (epsilon), corridor, and (J). | Empty eligible set. | FAILED |

## 4. Counterexample attempts

### Smallest-parameter test

- **Explicit data:** At the arithmetic level take (n=13), (H=1), (C=0), (sigma_W=sigma_R=0), and (p_{13}=1).  Then (15<0) is false and the cleared conclusion is (0\ge13-73=-60).
- **Hypotheses satisfied:** The packing/cardinality identities and the literal no-arm of the strict collision are satisfied; the inferred cold lower bound is nonpositive.
- **Accumulated facts violated:** An actual 13-vertex minimum-degree-three graph cannot have all 13 vertices induce a (P_{13}): the two path endpoints would have degree one.  This violates the combination of node [2]'s minimum-degree condition and node [17]'s window interpretation.
- **Applicability:** **NON-APPLICABLE TO THE NODE.**  The earliest exclusion is node [2], (delta(G)\ge3), once the node-[17] window spans the whole graph.  The test nevertheless shows that the algebra itself contains no positivity mechanism.

### Parity or 2-adic test

- **Explicit data:** Take (n=78), (H=1), (C=0), (sigma_W=2), and (sigma_R=0).  Then (4(15+2)=68\ge65=n-13), while (73C=0\ge78-73-8=-3).
- **Hypotheses satisfied:** The strict quarter comparison is cleared exactly and its failure does not require divisibility of (|R|=65) by four.  The packing density is exactly (1/78), hence lies on the no-arm of the strict test (	heta<1/78).
- **Accumulated facts violated:** No scalar ancestor is violated.  No actual target-free graph, canonical hot classification, or maximal packing realizing these numbers was constructed.
- **Applicability:** Applicable to the exact arithmetic contract.  It rules out a parity repair: the problem is the sign/range of the numerator, not a lost factor of two or four.

### Boundary or range test

- **Explicit data:** Take
  [
  n=77, H=1, C=0, p=1, |R|=64,
   sigma_W=1, sigma_R=0, defp(R)=e(R,W)=16.
  ]
- **Hypotheses satisfied:** The exact supply is tight, (defp=e=15p+sigma_W=16); the collision is the equality (15+1=64/4), so its strict form fails; (	heta=1/77>1/78); (sigma(G)=1=O(\sqrt n)); and the [153]-bounded inequality holds because (C=0).  The derived display is exactly (73C\ge77-73-4=0).
- **Accumulated facts violated:** The numerical data do not themselves provide an actual minimal target-free graph or certify that the unique chosen window is the canonical maximal packing and is live-hot.
- **Applicability:** This is the strongest arithmetic residual.  No incoming scalar or branch inequality listed in the manuscript excludes it.  It falsifies the finite-order inference (\text{failure}\Rightarrow C>0) at the equality boundary.

### Graph-realizability test

- **Explicit data:** Let (R) start as the cubic prism (C_{32}\square K_2) on vertices (u_{i,b}) ((i\in\mathbb Z/32\mathbb Z), (b\in\{0,1\})).  Delete the eight rungs (u_{i,0}u_{i,1}) for (0\le i<8).  Add an induced path (v_0\ldots v_{12}), and join its 16 external stubs to the 16 endpoints of the deleted rungs: two stubs from each endpoint (v_0,v_{12}), one from every internal (v_i), and one extra from (v_6).  The resulting simple graph has (n=77), minimum degree three, one degree-four window vertex, (sigma_W=1), (sigma_R=0), and for the displayed window (defp(R)=e(R,W)=16).
- **Hypotheses satisfied:** The path is induced, every vertex has ambient degree at least three, (V_{\ge4}) is independent, and the exact node-[174] equality data are graph-realized for this selected window.
- **Accumulated facts violated:** The undeleted rungs at indices 8 and 9 together with the two layer edges give a 4-cycle.  Thus node [2]'s target-avoidance condition fails.  The displayed one-window packing was also not proved maximal.
- **Applicability:** **NON-APPLICABLE TO THE NODE.**  The earliest excluding fact is node [2], “no (C_{2^j}).”  This test shows that simplicity, degrees, induced-window geometry, high-degree independence, and the exact charge equality do not themselves force cold nonemptiness.

### Branch-routing test

- **Explicit data:** On the ordinary route retain the [153]-bounded tag and the boundary data (n=77,H=1,C=0,sigma_W=1,sigma_R=0).  Then the [173]-no predicate holds but the eligible selected-cold-stub set is empty.
- **Hypotheses satisfied:** All displayed scalar facts on the [153]-bounded route, including (	heta\ge1/78), the near-cubic surplus bound, the bounded cold-mass inequality, exact stub supply, and the failed collision, are mutually consistent.
- **Accumulated facts violated:** No manuscript branch fact asserts (C>0) or an eligible corridor.  In the current Lean application, `selectedNetChargeContinuation` additionally requires `K .route8Rate`; together with exact boundary demand that stronger hidden ledger would rule out the failed quarter collision.  That formal dead-arm restriction is not an ancestor predicate of the displayed [173] node and therefore does not repair the manuscript edge.
- **Applicability:** Applicable to the proof-flow contract.  The unconditional edge `[174] -> [175]` loses the empty-eligible-set residual.  Treating “every selected corridor meets a heavy centre” as true on the empty set still fails to supply the actual (z) required by [177]/[65].

## 5. Strongest valid counterexample

The strongest candidate is the finite boundary package
\[
(n,H,C,\sigma_W,\sigma_R,|R|,\defp,e)=(77,1,0,1,0,64,16,16).
\]
It survives every explicit scalar equality and inequality used at node [174], including the route-[146] boundary, the near-cubic scale, the [153]-bounded upper bound, exact incidence supply, and the literal [173]-no predicate.  It makes the alleged positive cold mass equal to zero.  The prism construction realizes all of those local degree/support numbers in a simple graph, but that graph has a 4-cycle and hence does not reach the actual minimal-counterexample residual.  No actual graph satisfying the full target-avoidance and maximal/canonical packing contract was found.  The surviving candidate is therefore a valid witness to the missing finite-range implication and destination precondition, not a `VALID LOCAL COUNTEREXAMPLE` to the theorem.

## 6. Local repair

### Corrected statement

Replace node [174]'s operative claim by:

> On the no-arm of [173], at its failure witness packing,
>
> \[
> 73C\ge n-73|\mathcal P_{\rm hot}|-4(\sigma_W-\sigma_R).
> \]
>
> This inequality alone asserts neither (C>0) nor the existence of a selected cold corridor.  Retain `coldMassBounded` only on incoming routes that actually passed through the bounded arm of [153].  Let (mathcal E_{\rm eligible}) be the finite set of selected branch-excess half-edges of ambient-cubic cold windows whose outside endpoint leaves the cold-window union.  Decide exactly whether (mathcal E_{\rm eligible}) is empty.  If it is nonempty, choose (epsilon\in\mathcal E_{\rm eligible}), retain its return corridor and first-failure support, and continue to [175].  If it is empty, continue to the exact finite budget-edge residual; do not route a vacuous all-heavy assertion to Type B.

If the manuscript wants to retain “linearly many,” state it separately under an explicit margin, for example
\[
n-73H-4(\sigma_W-\sigma_R)\ge73\kappa n
\]
for a fixed (kappa>0), which gives (C\ge\kappa n).  The complementary finite-margin branch must still be assigned.

### Complete local proof

The no-arm of [173] is
\[
4\bigl(15(H+C)+\sigma_W-\sigma_R\bigr)
\ge n-13(H+C).
\]
Move the (60H+60C) terms to the right-hand support identity and collect the packing terms:
\[
60H+60C+4\sigma_W-4\sigma_R
\ge n-13H-13C,
\]
hence
\[
73C\ge n-73H-4(\sigma_W-\sigma_R).
\]
No division, rounding, or positivity has been used.  If the right-hand side is at least (73\kappa n), division by the positive integer 73 yields (C\ge\kappa n).  If it is merely positive, integrality yields (C\ge1).  If it is nonpositive, it yields no cold window; the (n=77) boundary package realizes equality.

Now form the literal finite set (mathcal E_{\rm eligible}).  By decidable equality of the finite graph, exactly one of
\[
\mathcal E_{\rm eligible}=\varnothing,
\qquad
\exists\epsilon\in\mathcal E_{\rm eligible}
\]
holds.  On the second arm, choose such an (epsilon).  Bridgelessness and the already defined corridor construction give its actual return corridor and first-failure support (J); only then does [175]'s exhaustive split (J\cap V_{\ge4}=\varnothing) versus (J\cap V_{\ge4}\ne\varnothing) apply.  On the first arm there is no representative to classify, so its exact budget/surplus data must be consumed by a separate closure.  This establishes every claimed implication without reinstating a sufficient-order assumption.

### Counterexample disposition

The (n=77) candidate lands on the corrected empty arm because (C=0) implies (mathcal E_{\rm eligible}=\varnothing).  It is no longer mislabeled as carrying linear cold mass or sent to [175].  The concrete prism graph remains excluded at node [2] by its 4-cycle; the abstract finite equality package becomes an explicit test case for the budget-edge producer.

### Graph patch

Replace the unconditional edge by the exact split

```text
[173] -- no --> [174: exact cleared inequality; retain route tag]
[174] -- Eligible != empty --> [175]
[174] -- Eligible = empty --> exact finite budget-edge residual
```

The first edge to [175] must retain the same graph and packing, one actual (epsilon\in\mathcal E_{\rm eligible}), its cold window, return corridor, first-failure state, and support (J), plus high-degree independence.  The empty edge must retain (H,C,sigma_W,sigma_R), exact collision failure, exact skeleton/hot budget data, the route tag, and the literal equality (mathcal E_{\rm eligible}=\varnothing).  It may reuse the repository's named `selectedRouteEightBudgetEdge` obligation only after a theorem proves that this exact empty-eligible residual satisfies that obligation; cold-family emptiness alone is not equivalent to eligible-set emptiness.

### Downstream impact

Synchronize the Part-V node [174] label, caption, panel summary, detailed dependency row, `lem:exact-collision-test`, `rem:no-sufficient-order`, and every “linearly many cold windows” description.  `lem:absorbed-germ-fan-data` and [175]--[177] must consume a nonempty actual incidence rather than a universal statement over a possibly empty type.  In Lean, strengthen the entry to `selectedAbsorbedGermResidual` with the actual eligible representative or insert the exact decision before it; do not let `absorbedGermDichotomy`'s empty candidate family become vacuous `absorbedGermFanData`.  `absorbedConfigurationResidualRow` may keep its correct cleared inequality, but its comment and audit row must stop calling that inequality a linear count.  The hidden `route8Rate` prerequisite of `selectedNetChargeContinuation` should either be represented as an actual proof-flow predecessor (making [174] unreachable on that formal lane) or removed from the manuscript-node implementation; it must not silently certify the displayed [174] branch.

## 7. Regression audit

The audit inspected:

- the Part-I, Part-IV, Part-V, Part-XI, and Part-XII diagrams, especially the unique bounded return `[153] -> [24]`, the dense return [161], and `[173] -> [174] -> [175]`;
- the full statements and proofs of `lem:exact-collision-test`, `lem:absorbed-germ-fan-data`, `lem:hot-failure-cold-mass`, `lem:cold-window-stub-excess`, `lem:cold-germ-extraction`, `thm:cold-branch-quantitative-closure`, `lem:dense-deficiency-routing`, and `lem:dense-cold-pass`;
- the cold quantitative ledger, the dependency table, the Part-V caption/summary, and `rem:no-sufficient-order`;
- `ColdMassLinearStatement`, `ColdMassBoundedStatement`, `coldMassDichotomy`, `ExactCollisionFails`, `AbsorbedConfigurationResidual`, `AbsorbedGermSplitStatement`, `AbsorbedGermFanDataStatement`, `absorbedConfigurationResidualRow`, `absorbedGermDichotomy`, `selectedAbsorbedGermResidual`, `selectedNetChargeContinuation`, and the separate `coldFamilyDichotomy`/`selectedRouteEightBudgetEdge` lane;
- `Assembly_node_audit.md` and `web/data/eg_node_audit.json` as locators, followed by the cited source declarations.  Their current [174] fidelity note records the cleared inequality but does not check positivity or the empty eligible family.

Search patterns included

```text
rg -n 'exact-collision-test|absorbed-configuration|absorbed-germ-fan-data|coldMassBounded|ColdMassBoundedStatement|absorbedConfigurationResidual|absorbedGermDichotomy|coldFamilyDichotomy|route8Rate' to_formalize/erdos_64_proof.tex hypostructure proofs Assembly_node_audit.md web/data/eg_node_audit.json
```

Negative searches found no manuscript inequality proving
\[
n-73H-4(\sigma_W-\sigma_R)>0
\]
at every finite object reaching [174], no decision that the eligible selected-corridor set is nonempty before [175], and no graph edge assigning its empty complement.  The only explicit empty-cold decision is on the separate route-8 rate-failure lane, and its budget-edge consumer is still a named obligation rather than a proof of the node-[174] complement.

## 8. Residual uncertainty

No actual minimum-degree-three, power-of-two-cycle-free graph realizing the (n=77) equality package and every canonical hot/maximal-packing condition was found; constructing one would amount to a theorem-level counterexample search and is not needed to expose the invalid finite implication.  The exact live-hot classification of the explicit prism window was not evaluated because the graph is already excluded at node [2].  I did not re-audit the mathematical closure of the proposed empty budget-edge residual or the downstream [175]--[177] fan construction; both are separate node obligations.  Concurrent source work has left the human Lean audit noting a first downstream owner failure at [175], but this report does not rely on that failure.  No manuscript, proof-flow, Lean, diagram, audit-source, or coverage-ledger file was changed.
