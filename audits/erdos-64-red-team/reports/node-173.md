<!-- red-team-audit
{
  "schema_version": 1,
  "proof": "erdos-gyarfas",
  "node": 173,
  "node_label": "exact collision\\\\test holds?",
  "panel": "fig:proof-diagram-part-v",
  "contract_sha256": "fbaa029562894b303e501f2ed03d83edc7873f0d02566215699cb15f408066d3",
  "manuscript_sha256": "106a8205a1718fbf90e1686a107b2143b9edca574e2b0c11415e7f44aee2c0f9",
  "graph_sha256": "dc67fae178f947a9607c167e383d85919633341bdd423e4c4a45e4c317b3a765",
  "lean_audit_sha256": "50324ef5594d635a52d83aeb297f2ca3f3d30ef58de4ce3602816c7e78365b12",
  "verdict": "MISSING RANGE OR DIVISIBILITY CHECK",
  "audited_at": "2026-08-24T21:41:35Z"
}
-->

# Red-team audit: node [173]

## 1. Executive verdict

Verdict: **MISSING RANGE OR DIVISIBILITY CHECK**

Node [173] correctly decides an exact integer inequality, and failure correctly rearranges to
\[
73C\ge n-73|\mathcal P_{\rm hot}|-4(\sigma_W-\sigma_R).
\]
The next sentence does not follow for all finite orders: unless the numerator is proved positive by a fixed linear amount, this lower bound need not give even one cold window, much less linearly many. At the equality boundary it permits (C=0), while [174] and [175] are described as a residual of selected cold corridors. The literal Lean decision is exhaustive, but its no arm retains only a nonnegative-net-charge witness and the rearranged inequality; it does not retain (C>0). The implementation then enters the cold-corridor continuation without the `coldFamilyPositive` split that it uses for an analogous rate-failure residual. The smallest repair is to keep the exact decision, split its no arm on (C>0), send only the positive arm to [174], and route (C=0) to a separate exact all-hot/budget-edge or finite-order check.

## 2. Exact node contract

### Incoming residual

The displayed node has the single incoming edge `[57] -> [173]`; it is not a merge or loop. The current object is the selected finite simple lexicographically minimal counterexample (G): (delta(G)\ge3), no power-of-two cycle, the equivalent edge-rooted return avoidance, no proper minimum-degree-three subgraph, edge criticality, independence of (V_{\ge4}(G)), and the retained boundary-profile, context-universality, replacement, and hereditary-uncompressibility facts of [1]--[14]. It carries a fixed maximal vertex-disjoint induced-(P_{13}) packing (mathcal P), its remainder (R), the exact hot/cold partition
\[
\mathcal P=\mathcal P_{\rm hot}\sqcup\mathcal P_{\rm cold},
\qquad p_{13}=|\mathcal P|=|\mathcal P_{\rm hot}|+C,
\qquad C=|\mathcal P_{\rm cold}|,
\]
and the exact surplus split (sigma(G)=\sigma_W+\sigma_R).

Every route reaching the live Lean owner `selectedNetChargeContinuation` has the common keys `route8Rate`, `surplusAtOrBelow`, `netDeficiencyCap`, `stubSupply`, `boundaryDemand`, `maximalPacking`, `largeBudgetResidual`, `hotColdPartition`, and `slackIndependent`; earlier keys remain in the append-only ledger. The graph-theoretic predecessor cone includes tagged variants: the ordinary bounded arm of [153] carries `coldMassBounded` and the density cap, while the dense [159]--[161] and route-8 variants carry their own exact cap predicates. Those route-specific facts must not be unioned. In particular, the signature of `selectedNetChargeContinuation` does not require `coldMassLinear`, `coldMassBounded`, or `coldFamilyPositive`.

For a maximal packing, the exact identities used locally are
\[
|R|=n-13p_{13},
\qquad
\defp(R)\le e(R,W)\le15p_{13}+\sigma_W.
\tag{173-supply}
\]
The manuscript formulates the tested upper-bound collision as
\[
15p_{13}+\sigma_W-\sigma_R<\frac14(n-13p_{13}).
\tag{173-U}
\]
Lean refines the decision to the actual net charge: `netChargeCap` says every maximal packing has
\[
\defp(R)-\sigma_R<\frac14|R|,
\tag{173-D}
\]
and `exactCollisionFails` is its literal negation at some maximal packing. Since (173-supply) makes (173-U) imply (173-D), the Lean yes arm is weaker and its no arm is stronger than the manuscript's surrogate split; that refinement itself is sound.

### Accumulated facts

1. Nodes [1]--[14] provide the selected counterexample, target safety, criticality, high-degree independence, and the replacement ledger.
2. Nodes [15]--[29] provide the maximal induced-(P_{13}) packing, componentwise (P_{13})-free remainder with empty internal (3)-core, positive deficiency, and the exact external-incidence supply (173-supply).
3. Nodes [30]--[56] and their selected route provide the large-budget residual and a conditional or exact net-deficiency cap. The density-cap version is conditional on `SufficientlyLargeForNetCap`; node [173] is explicitly intended to handle its finite complement.
4. Node [22] fixes the canonical hot/cold partition. Its entropy comparison bounds the hot code against the exact skeleton budget, but the proof of `lem:exact-collision-test` supplies no finite-order inequality showing
   \[
   n-73|\mathcal P_{\rm hot}|-4(\sigma_W-\sigma_R)>0
   \]
   or a fixed positive multiple of (n).
5. On the ordinary path returning from [153], `coldMassBounded` is an upper bound of the form
   \[
   bC\le(b+B_{\rm cold})\sigma(G).
   \]
   It is satisfied when (C=0) and therefore supplies no missing positivity.
6. `coldFamilyPositive`, the exact fact (0<C), exists in the Lean vocabulary and is selected before the analogous absorbed-germ continuation in `selectedRouteEightRateFailure`; it is not selected at node [173].

### Current predicate and exact claim

Let
\[
U:=15p_{13}+\sigma_W-\sigma_R,
\qquad r:=|R|=n-13p_{13}.
\]
The publication-level node decides (U<r/4). Its yes arm establishes negative total net charge because (defp(R)-\sigma_R\le U), and it may continue at [58]. Its no arm establishes (4U\ge r). Substitution of (p_{13}=|\mathcal P_{\rm hot}|+C) gives exactly
\[
73C\ge N,
\qquad
N:=n-73|\mathcal P_{\rm hot}|-4(\sigma_W-\sigma_R).
\tag{173-N}
\]
This is an exact integer conclusion. It yields (C>0) only if (N>0), and it yields (C\ge\varepsilon n) only if (N\ge73\varepsilon n). Neither range fact is proved in the lemma. If (N\le0), (173-N) is vacuous; if (N=0), it permits (C=0).

The live formal decision instead applies excluded middle to (173-D). On the no arm, `exactCollisionFails` stores a maximal packing whose remainder has nonnegative net charge. `absorbedConfigurationResidualRow` combines that witness with `boundaryDemand` and `hotColdPartition` to publish the subtraction-free inequality
\[
n+4\sigma_R\le73\bigl(|\mathcal P_{\rm hot}|+|\mathcal P_{\rm cold}|\bigr)+4\sigma_W.
\tag{173-L}
\]
This is equivalent to (173-N) at the registered values, but it also contains no (C>0) clause.

### Outgoing contracts

- `[173] -- yes --> [58]`: retain the chosen maximal packing and strict negative net charge. Node [58]'s net-charge localization consumes precisely this sign fact, so the yes route is correctly typed. In Lean, `netChargeCap` supplies the strict sign for every maximal packing.
- `[173] -- no --> [174]`: the diagram and caption describe an absorbed-configuration residual in which selected cold corridors were charged to high-degree vertices. For [175], one must at least retain a nonempty cold family, a selected branch-excess half-edge/corridor, its first-failure support, and the prior bounded-arm charge. The literal no key and (173-L) provide none of these existential facts. The implementation runs cold-return, first-failure, and absorbed-germ rows anyway; when (C=0), their universal statements are vacuous. That does not establish the manuscript's claimed cold residual.

Thus the yes/no test is logically exhaustive, but the inference from its no predicate to the cold destination omits the finite positivity range of (173-N).

## 3. Sentence audit

| Sentence | Exact assertion | Facts used | Hidden obligation | Adversarial test | Status |
|---|---|---|---|---|---|
| S1 | The asymptotic allowances are exact quantities carried by the residual. | Surplus split, hot/cold ledger, skeleton budget. | Replacing bounds by exact quantities must still leave an exact closing alternative for every finite value. | Set the cold count to zero at the collision boundary. | SUPPORTED AS DATA, NOT AS CLOSURE |
| S2 | Node [173] decides (U<r/4) on the current object. | Finiteness and decidability of integer comparison. | The arms must be literal complements and retain the witness packing. | Compare (4U<r) with (4U\ge r). | SUPPORTED |
| S3 | If (U<r/4), nodes [58]--[64] follow without an order condition. | (defp(R)-\sigma_R\le U); net-charge localization. | Strictness must be preserved. | Test (4U=r-1). | SUPPORTED |
| S4 | Failure rearranges to (173-N). | (4U\ge r), (p_{13}=H+C), (r=n-13p_{13}). | Natural-number subtraction should be avoided when the numerator is negative. | Derive the subtraction-free form (n+4\sigma_R\le73(H+C)+4\sigma_W). | SUPPORTED |
| S5 | The lower bound (173-N) means the residual has linearly many cold windows. | S4 and the exact hot entropy comparison. | Prove (N\ge\varepsilon n>0) uniformly at every finite order. | Use (N=0) and (C=0). | FAILED |
| S6 | The no residual lies on [153]'s bounded arm. | Directed ancestry on the ordinary return path. | Every route to [173] must carry `coldMassBounded`, or the route tag must be preserved. | Inspect the polymorphic Lean call sites, including dense and route-8 arms. | AMBIGUOUS / NOT COMMON TO ALL CALLS |
| S7 | The bounded arm's only content is configuration-extraction loss. | `coldMassBounded`; cold extraction ledger. | A loss bound is not an existence statement for a cold corridor. | Take (C=0). | FAILED AS DESTINATION ENTRY |
| P1 | The stub supply is exact. | Induced windows have (12) internal edges; (delta(G)\ge3). | Cross-window incidences must not be undercounted. | Count every leaving window incidence. | SUPPORTED |
| P2 | The hot comparison and cold count are exact object data. | Canonical hot/cold partition. | Exactness alone must imply a positive margin if “linearly many” is claimed. | Equality (n=73H+4(\sigma_W-\sigma_R)). | FAILED TO SUPPLY THE MARGIN |
| P3 | Therefore the collision is an integer inequality. | P1--P2. | Fractions are cleared with the correct strict boundary. | Compare (4U=r). | SUPPORTED |
| P4 | Failure rearranges to the displayed cold lower bound. | P3. | No division before sign/positivity is required. | Use the subtraction-free inequality. | SUPPORTED |
| P5 | [153]'s linear arm is closed, so the state is on the bounded arm. | Purported prior [153] route. | This must be an inherited tagged fact, not a theorem-order import; bounded must also imply a usable cold object. | Inspect the graph and literal call signature. | AMBIGUOUS AND INSUFFICIENT |
| P6 | Hence the residual carries the configuration-extraction loss used at [174]. | P5. | The no arm must produce (C>0) and selected cold corridors, not just an upper bound on cold mass. | Empty cold family. | FAILED |
| L1 | `exactCollisionDichotomy` records exact complements. | Decidability; `not_negativeNetCharge_iff`. | The same maximal packing data must be retained. | Expand both `Holds` clauses. | SUPPORTED |
| L2 | `absorbedConfigurationResidualRow` proves the exact arithmetic consequence. | `exactCollisionFails`, `boundaryDemand`, `hotColdPartition`. | The row must not claim more than (173-L). | Inspect its produced proposition. | SUPPORTED |
| L3 | The no arm is ready for cold-corridor analysis. | L2. | Require `coldFamilyPositive` or an explicit eligible half-edge. | Compare with `selectedRouteEightRateFailure`, which performs that split. | FAILED |

## 4. Counterexample attempts

### Smallest-parameter test

- **Explicit data:** At the numerical interface take one packed window: (n=80), (p_{13}=|\mathcal P_{\rm hot}|=1), (C=0), (sigma_W=2), (sigma_R=0), (|R|=67), and (defp(R)=17). Then (173-supply) is tight, (U=17), and (4U=68\ge67=|R|), so the exact collision fails. The displayed lower bound is (C\ge(80-73-8)/73=-1/73), which gives no cold window.
- **Hypotheses satisfied:** The packing identity, surplus split, exact stub upper bound, integer net-charge failure, and empty cold bounded-arm inequality all hold numerically.
- **Accumulated facts violated:** No actual (80)-vertex minimal target-free graph, exact hot package realization, or complete large-budget ledger has been constructed.
- **Applicability:** **NON-APPLICABLE TO THE NODE** as a complete graph, first at node [2]'s target-free counterexample requirement. It is the smallest one-window arithmetic model of the omitted positivity check.

### Parity or 2-adic test

- **Explicit data:** The preceding choice has degree-sum baseline plus surplus (3n+\sigma(G)=3\cdot80+2=242), which is even. Thus handshaking parity does not eliminate it. Changing only to (sigma_W=3) would give an odd degree sum (243) and is rejected; the new data are a separate failed candidate. The node uses only multiplication by (4=2^2), and the exact comparison is (4U\ge|R|), so there is no hidden division or odd-part projection.
- **Hypotheses satisfied:** The (n=80,sigma(G)=2) numerical state passes the necessary degree-sum parity and the exact cleared comparison.
- **Accumulated facts violated:** Necessary parity is not graph realization; the window, remainder, target avoidance, and all earlier ledgers remain unverified.
- **Applicability:** **NON-APPLICABLE TO THE NODE** as an actual graph, first at node [2]. The test shows that a basic parity check does not restore the missing positive cold mass. The bundled modular checker is not applicable because node [173] contains no orbit or congruence inference.

### Boundary or range test

- **Explicit data:** Take (n=146), (p_{13}=|\mathcal P_{\rm hot}|=2), (C=0), and (sigma_W=sigma_R=0). Then (|R|=120), (U=30), and (4U=120=|R|). The strict yes inequality fails exactly at equality, while (173-N) says only (73C\ge0), attained by (C=0).
- **Hypotheses satisfied:** All displayed integer identities, the strict/non-strict complement, handshaking parity for a cubic numerical model, and the exact stub/net-charge equality.
- **Accumulated facts violated:** No (146)-vertex target-free minimal graph with maximal packing number two and the required realized hot code is supplied.
- **Applicability:** **NON-APPLICABLE TO THE NODE** as a graph, first at node [2], but directly applicable to the arithmetic implication S5. It proves that the equality boundary is not a positive-cold residual.

### Graph-realizability test

- **Explicit data:** Try to realize the equality model with two disjoint induced (P_{13}) windows in an otherwise cubic (146)-vertex graph. The windows have (30) external stubs in total; attach them to a (120)-vertex remainder whose positive deficiency is exactly (30). This realizes the local degree and incidence counts with (C=0) if both windows are hot.
- **Hypotheses satisfied:** The attempted incidence object is parity-compatible, has the exact (15)-stub count per cubic induced window, and realizes the local equality (defp(R)=30=|R|/4).
- **Accumulated facts violated:** Simplicity, maximality of the packing, componentwise (P_{13})-freeness, absence of an internal (3)-core, all target-return exclusions, minimality, and exact hot-code realization were not simultaneously verified. Any complete graph satisfying the theorem's hypotheses would also have to evade the theorem's conclusion.
- **Applicability:** **NON-APPLICABLE TO THE NODE**, first at node [2]'s target-free counterexample predicate. The test nevertheless shows no local degree or parity mechanism forces (C>0).

### Branch-routing test

- **Explicit data:** Use the exact proposition-level state
  \[
  C=0,\qquad \exists\mathcal P\text{ maximal with }\No(R)\ge0.
  \]
  This satisfies `exactCollisionFails`. `absorbedConfigurationResidualRow` then proves (173-L), but the set of eligible selected cold stubs is empty. The live control flow calls `selectedAbsorbedGermResidual` directly. By contrast, `selectedRouteEightRateFailure` first runs `coldFamilyDichotomy` and sends only its (C>0) arm to the same continuation.
- **Hypotheses satisfied:** This is a consistent assignment to the exact node-[173] no predicate, the hot/cold partition, and the arithmetic output contract; neither `exactCollisionFails` nor `absorbedConfigurationResidual` asserts (C>0).
- **Accumulated facts violated:** A concrete selected counterexample realizing this formal state is not exhibited. On route variants where an unconditional exact cap already proves negative net charge, this no arm is unreachable; the density-cap finite complement is the live vulnerable variant.
- **Applicability:** Applicable to the proposition-to-destination handoff. The no fact does not satisfy [174]'s prose entry as a nonempty selected-corridor residual. This is the strongest surviving candidate and isolates the missing range test without treating a routed failure as a theorem contradiction.

## 5. Strongest valid counterexample

No concrete finite graph satisfying the complete selected minimal-counterexample ledger was constructed. The strongest candidate is the exact formal handoff state (C=0\land\mathsf{exactCollisionFails}). It survives the literal node-[173] no predicate and the arithmetic row producing (173-L), because both permit an empty cold family. The equality instance (n=146), (p_{13}=H=2), (sigma_W=sigma_R=0), (|R|=120), and (defp(R)=30) makes the omission transparent: the strict collision fails, yet (73C\ge0) is sharp at (C=0). The candidate is therefore a valid counterexample to the claimed arithmetic implication “failure (Rightarrow) linearly many cold windows” and to the current payload expected by the cold-corridor destination. It is not claimed to be a graph counterexample to the global theorem.

## 6. Local repair

### Corrected statement

On the large-budget residual, decide the exact comparison
\[
\defp(R)-\sigma_R<\frac14|R|
\]
for the fixed maximal packing (or, equivalently for the stronger sufficient yes test, decide (173-U)). If it holds, retain strict negative net charge and continue at [58]. If it fails, retain the witness packing and the exact subtraction-free consequence
\[
n+4\sigma_R\le73\bigl(|\mathcal P_{\rm hot}|+C\bigr)+4\sigma_W.
\]
Then decide (C>0). On the positive arm, retain a cold window and its selected branch-excess incidences and continue to [174]. On the empty arm, retain (C=0) and the exact all-hot budget-edge inequality; do not describe this state as an absorbed cold-configuration residual. Close it by a separately proved exact skeleton-budget comparison or by an explicit finite-order table.

The phrase “linearly many cold windows” may be used only after proving an explicit margin (N\ge73\varepsilon n) in (173-N).

### Complete local proof

The actual net charge is an integer, so excluded middle gives either (4(\defp(R)-\sigma_R)<|R|) or its non-strict complement, expressed without signed natural subtraction as (|R|+4\sigma_R\le4\defp(R)). In the first case, the canonical support decomposition of `lem:netcharge-superadd` localizes a connected negative support exactly as at [58]--[61].

In the second case, (173-supply) gives
\[
|R|+4\sigma_R
 \le4\defp(R)
 \le60p_{13}+4\sigma_W.
\]
Using (|R|+13p_{13}=n) yields
\[
n+4\sigma_R\le73p_{13}+4\sigma_W
=73(H+C)+4\sigma_W,
\]
which is (173-L) and hence (173-N). No positivity conclusion has been used.

Now decide the finite integer predicate (0<C). If true, choose a cold window from the nonempty finite family. Its induced (P_{13}) degree count supplies its external stubs, and the existing cold-corridor construction may be run with an actual selected cold incidence; the positive fact is retained into [174]. If false, (C=0) by natural-number trichotomy. The exact inequality becomes (n+4\sigma_R\le73H+4\sigma_W); it is the complete all-hot residual. Since this local proof has no theorem showing that residual impossible, it must be routed rather than silently closed. This proves an exhaustive, correctly typed local split using only facts available at node [173].

### Counterexample disposition

The (n=80) and equality (n=146) arithmetic candidates take the (C=0) subarm and are no longer mislabeled as cold-corridor residuals. A state with (C>0) reaches [174] with an actual cold witness. A later proof that the exact hot-code and skeleton inequalities force (N\ge73\varepsilon n) may collapse the split on the range where that estimate holds, but it must send the remaining finite orders to the all-hot exact comparison or a verified finite table.

### Graph patch

The minimal routing patch is

```text
[57] --> [173] exact net-charge collision?
[173] -- yes: strict negative net charge --> [58]
[173] -- no: witness packing and exact inequality --> [173a] C > 0?
[173a] -- yes: retain cold window, selected incidence, bounded-charge tag --> [174]
[173a] -- no: C = 0, all-hot exact budget-edge residual --> exact budget comparison / finite table
```

The positive edge must carry `coldFamilyPositive` and the route-specific [153] bounded-arm tag if [174] consumes it. The empty edge must not enter [174]. The analogous `coldFamilyDichotomy` already exists in the formal code, but its current empty-arm endpoint `selectedRouteEightBudgetEdge` is an open frontier placeholder and has a different incoming rate-failure fact; it is evidence for the shape of the patch, not yet a proof of the new empty-arm closure.

### Downstream impact

`lem:exact-collision-test`, the Part V box/caption, the structural-exhaustion summary row, dependency row [173]/[174], and `rem:no-sufficient-order` must distinguish the exact inequality from the additional positive-margin claim. Node [174]'s label should mention a positive cold family only on the new positive arm. `lem:absorbed-germ-fan-data` can retain its per-selected-half-edge dichotomy once entry supplies an actual cold witness; its universal clauses alone cannot certify nonemptiness.

In Lean, `exactCollisionDichotomy` may remain as the exact sign decision. After its right arm, run `coldFamilyDichotomy`; require `K .coldFamilyPositive` in `selectedAbsorbedGermResidual` and in the manifest producing the nonvacuous [174] entry. The `C=0` arm needs a dedicated all-hot exact-budget proposition and a proved producer; it must not be discharged by an absent frontier stub. `absorbedConfigurationResidualRow` may continue to publish (173-L), but its comment and fidelity status must not call that inequality a positive cold lower bound without a sign premise. The audit table and JSON sidecar currently mark [173] faithful/complete and should be reconsidered after the source repair.

The same positivity distinction appears in the route-8 rate-failure control flow, which already splits `coldFamilyPositive` from `coldFamilyEmpty`. No other occurrence was found that proves the missing finite-order margin for node [173].

## 7. Regression audit

The audit inspected:

- The complete Part V diagram, both node-[173] edges, its caption, the proof summary, and the dependency-table rows for [173]--[177].
- The full statement and proof of `lem:exact-collision-test`, `lem:absorbed-germ-fan-data`, `lem:stub-positive`, the surplus split, `lem:netcharge-superadd`, `cor:global-window-join-pressure`, and `prop:negative-net-charge`.
- The hot/cold definitions and the full quantitative cold branch: `def:cold-window-ledger`, `lem:hot-failure-cold-mass`, `def:cold-skeleton-excess`, `lem:cold-window-stub-excess`, node [153]'s linear/bounded split, and `thm:cold-branch-quantitative-closure`.
- The dense-packing variants [158]--[162] to distinguish common from route-specific facts. In particular, the manuscript's dense-deficiency route claims an exact cap, while the polymorphic Lean owner also accepts the finite density-cap complement.
- `SpineVocabulary.lean`: `netDeficiencyCap`, `netChargeCap`, `exactCollisionFails`, `absorbedConfigurationResidual`, `ColdMassLinearStatement`, `ColdMassBoundedStatement`, and the `coldFamilyPositive`/`coldFamilyEmpty` keys.
- `SpineRows.lean`: all three node-[56] cap producers, `exactCollisionDichotomy`, and `absorbedConfigurationResidualRow`. The latter proves only (173-L).
- `Assembly.lean`: every call to `selectedNetChargeContinuation`, the direct right-arm call to `selectedAbsorbedGermResidual`, and the contrasting `selectedRouteEightRateFailure` branch, which performs `coldFamilyDichotomy` first.
- `ColdCorridorRows.lean`: the literal complement decision (0<C) versus (C=0).
- The implementation status table and JSON locator. Their statement that the complaint belongs only to [174] does not supply the missing positivity premise on the [173] edge.
- The review postmortem's cumulative-ledger and routed-residual warnings. This report does not demand a global hot-window independence statement, import a sibling fact, or call the exact failure itself a contradiction; it checks whether the routed payload meets its stated destination.

The principal searches were

```text
rg -n -F -e '[173]' -e 'exact collision' -e 'absorbed-configuration' -e 'configuration-extraction loss' to_formalize/erdos_64_proof.tex
rg -n -F -e 'exactCollisionDichotomy' -e 'absorbedConfigurationResidualRow' -e 'exactCollisionFails' -e 'absorbedConfigurationResidual' hypostructure proofs Assembly_node_audit.md web/data/eg_node_audit.json
rg -n -F -e 'coldMassLinear' -e 'coldMassBounded' -e 'coldFamilyPositive' -e 'coldFamilyEmpty' hypostructure proofs
rg -n -F -e 'linearly many cold' -e 'small-order repair' -e 'No sufficient-order condition' to_formalize/erdos_64_proof.tex erdos_64_conversation_mistakes.md
```

No proof of (N>0) for all finite incoming objects, no `coldFamilyPositive` premise on node [173]'s no edge, and no closed all-hot exact-budget destination for that edge were found.

## 8. Residual uncertainty

No actual minimal counterexample realizing the (C=0) arithmetic boundary and every accumulated node-[173] fact was constructed. The exact hot-code comparison and skeleton cardinality were not exhaustively computed for each finite (n), so a future finite theorem could exclude some or all numerical models; no such theorem is currently cited or consumed at this node. The report did not independently audit the mathematical closure of [174]--[177], only their entry requirements, and the all-hot budget-edge continuation visible in Lean remains an open frontier producer. Route-specific histories reaching the polymorphic Lean owner are large; this audit checked the declared common requirements and representative call sites but did not reproduce every full type index in the report. No manuscript, proof-flow diagram, Lean source, implementation-audit source, or coverage ledger was changed.
