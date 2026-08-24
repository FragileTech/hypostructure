<!-- red-team-audit
{
  "schema_version": 1,
  "proof": "erdos-gyarfas",
  "node": 170,
  "node_label": "conditional savings additive at every fixed scale?",
  "panel": "fig:proof-diagram-part-xii",
  "contract_sha256": "51614570d5f6467a0f948ac7786f02cb48187d158041efa9396079c17509a1db",
  "manuscript_sha256": "106a8205a1718fbf90e1686a107b2143b9edca574e2b0c11415e7f44aee2c0f9",
  "graph_sha256": "dc67fae178f947a9607c167e383d85919633341bdd423e4c4a45e4c317b3a765",
  "lean_audit_sha256": "50324ef5594d635a52d83aeb297f2ca3f3d30ef58de4ce3602816c7e78365b12",
  "verdict": "PROSE AMBIGUITY",
  "audited_at": "2026-08-24T22:08:02Z"
}
-->

# Red-team audit: node [170]

## 1. Executive verdict

Verdict: **PROSE AMBIGUITY**

The manuscript's intended decision is exhaustive and correctly routed when its conditional-fibre predicate is read in the prefix-exposure sense used in the proof and in `def:barrier-overlap-system`: either every relevant nonempty prefix fibre admits the $F_{a,b}$ bound, or a minimal failed family is passed to [172].  The lemma statement also says that one conditions on “the barrier states of the other windows,” which can instead mean conditioning on all remaining coordinates.  That stronger-looking pointwise condition does not imply the product estimate: an even-parity code has singleton all-other conditionals but exponentially many joint states.  The proof's canonical exposure order identifies the intended correction, so this is a prose ambiguity rather than a nonexhaustive mathematical branch.  Separately, the current Lean proposition bundles the downstream [171] inequality into the decision and its negation does not produce an overlap obstruction; that is a formal-fidelity defect, not the paper-level verdict.

## 2. Exact node contract

### Incoming residual

The sole displayed incoming edge is `[169] -> [170]`; there is no merge and no loop. The residual carries the selected finite simple lexicographically minimal counterexample $G$, with minimum degree at least three, no power-of-two cycle, the equivalent return-avoidance fact, and the retained edge-criticality, high-degree independence, boundary-profile, context-universality, replacement, and hereditary-uncompressibility ledgers from [1]--[14]. It also retains the fixed maximal induced-$P_{13}$ packing $\mathcal P$, the exact barrier table and $399$-label algebra, the near-cubic spine, and the separated multi-scale window package from [15]--[21].

On the selected Part-XII path, [158]'s no arm supplies the exact dense overflow

\[
Q:=2^{(c_{13}-o(1))p_{13}\log_2 n}>|\mathcal G_{n,m}|,
\tag{170-dense}
\]

[160]--[162] run the dense hot/cold continuation, and [163]--[169] leave the trivial neutral residual: every selected corridor is terminal and neutral, $Q=E$, and every packed window is blocked at every dyadic scale. Thus $G\in\mathcal B(\mathcal P)$, where the blocked class has the fixed labelled vertex set, edge count, window positions, minimum-degree condition, and no target cycle through a window.

For one separated scale and barrier $(a,b)$, fix the outside-edge record and all earlier exposed barrier data. Let $\mathcal S(\mathcal U)$ be the joint states of a window subfamily $\mathcal U$ realized in that nonempty conditional fibre. The intended node-[170] predicate is the conditional product property, not unconditional independence of all windows.

The literal Lean entry to `selectedScaleAdditivityDichotomy` requires only the retained keys `blockedClassMember` and `densePackingOverflow`. The first says that the object's labelled skeleton is a blocked-class member and also stores a class-cardinality upper bound; the decision owner reads that key into `_blocked` and discards it. Every earlier ledger key is structurally retained by `Decision.run`.

### Accumulated facts

1. Nodes [1]--[14] supply the selected-counterexample, target-avoidance, boundary, replacement, and uncompressibility facts.
2. Nodes [15]--[21] supply the canonical packing, the $91$ barrier rows, the values $W_{a,b}$ and $F_{a,b}$, the separated scales, and the fixed encoding order.
3. Node [159] retains (170-dense), and the near-cubic skeleton class is bounded by the same skeleton budget $|\mathcal G_{n,m}|$.
4. Node [169] retains $G\in\mathcal B(\mathcal P)$, so $|\mathcal B(\mathcal P)|\ge1$.
5. `def:barrier-overlap-system` defines failure locally in a fixed nonempty conditional fibre: a nonempty family is obstructed when no exposure ordering keeps every next conditional state set at size at most $F_{a,b}$; a minimal obstruction has every proper nonempty subfamily orderable.
6. `lem:barrier-failure-overlap` is the intended bridge from failure of this product property to a minimal obstruction with connected overlap support. It does not accept failure of a downstream cardinal inequality as a premise.
7. The manuscript's phrases “the other windows” and “every conditional fibre” must be read with the exposure order fixed in `def:barrier-overlap-system` and the proof. Conditioning on all future coordinates is not a substitute for the prefix/decision-tree fibre used by the product bound.
8. In Lean, write
   \[
   A:=\forall(H_0,c),\quad |\operatorname{ConditionalFibre}(H_0,c)|\le F,
   \]
   and
   \[
   B:=|\mathcal B(\mathcal P)|\,Q
      \le |\mathcal G^{\delta\ge3}_{n,m}|.
   \]
   The current `BlockedScaleAdditivityStatement` is exactly $A\land B$, while `blockedBarrierOverlap` is exactly $\neg(A\land B)$.

### Current predicate and exact claim

The publication-level decision needed at [170] is

\[
\mathsf{Add}:=
\left\{
\begin{array}{l}
\text{for every fixed scale, barrier, outside record, earlier-scale prefix,}\
\text{and nonempty window subfamily, there is an exposure ordering in which}\
\text{every next conditional state set has cardinality at most }F_{a,b}
\end{array}
\right\}.
\]

The exact alternatives are $\mathsf{Add}$ and $\neg\mathsf{Add}$. On the first arm, multiplying the conditional cardinalities gives the barrier-state product saving; [171] must then combine that saving with its separate code injectivity and uncompressed-baseline arguments. On the second arm, finiteness permits choosing a nonempty obstruction $\mathcal U$ minimal by cardinality; `lem:barrier-failure-overlap` localizes it and [172] consumes the resulting connected support after the alternatives of `lem:window-system-realizability` have been applied.

The current formal proposition is not equivalent. Moreover, $B$ is false on every assumed incoming formal residual. If $B$ held, blocked-class nonemptiness would give

\[
Q\le |\mathcal B(\mathcal P)|Q
 \le |\mathcal G^{\delta\ge3}_{n,m}|
 \le |\mathcal G_{n,m}|,
\]

contradicting (170-dense). Hence $\neg(A\land B)$ is automatic and carries no information about $A$.

### Outgoing contracts

- `[170] -- yes --> [171]` must retain $\mathsf{Add}$, the same blocked class and encoding data, $G\in\mathcal B(\mathcal P)$, and the dense overflow. Node [171] must itself prove code injectivity, the correct baseline count, the compression inequality $B$, and then $|\mathcal B(\mathcal P)|<1$. The current Lean yes arm instead assumes $B$ as part of its node-[170] fact and `blockedClassCompressionCloses` reads it directly.
- `[170] -- no --> [172]` must retain a fixed scale and barrier, a nonempty conditional fibre, a cardinality-minimal nonempty $\mathcal U$ for which no exposure order works, its canonical completion supports, and the connected-overlap conclusion. After local uncrossing, only the scale-spanning serial-system alternative enters the increment arithmetic. The current Lean no arm retains only $\neg(A\land B)$, has no $\mathcal U$ or support, and calls the absent `selectedBarrierOverlapSerialSystem`.

The diagram's yes/no labels are logically exhaustive only for one predicate. They are not validator-compatible handoffs when the implemented predicate includes [171]'s conclusion.

## 3. Sentence audit

| Sentence | Exact assertion | Facts used | Hidden obligation | Adversarial test | Status |
|---|---|---|---|---|---|
| S1 | There are $L=\lfloor\log_2n\rfloor-O(1)$ separated scales from the window package. | [21], `lem:p13-window-package`. | The finite lost end scales must remain in the stated $O(1)$. | Test the first and last retained scales. | INHERITED BRANCH FACT |
| S2 | A barrier state is the label triple together with its deterministic edge-rooted completion. | Label algebra; canonical tie-breaking. | The state and completion support must be functions of the same graph and prefix. | Compare the TeX definition with `BarrierSystem.barrierState`. | SUPPORTED |
| S3 | The conditional state set has relative size at most $F_{a,b}/W_{a,b}$ on the additive arm. | Certified finite barrier row; current conditional fibre. | This is a branch predicate, and the conditioning must be the prefix used in the exposure product. | Use a fibre of size $F_{a,b}$ and one of size $F_{a,b}+1$. | SUPPORTED AS A DECISION PREDICATE |
| S4 | These conditional savings add over barriers, scales, and windows. | S3; exposure order; chain rule for finite cardinalities. | Each coordinate must be charged once and every nonempty prefix fibre must satisfy the bound. | Multiply the successive conditional bounds. | SUPPORTED ON THE INTENDED YES ARM |
| S5 | Otherwise the current graph is closed by the serial-system route. | Negation of the product property; `lem:barrier-failure-overlap`; local uncrossing. | The no arm must supply failed prefix additivity, not failure of a later compression inequality. | Compare the manuscript predicate with the live $A\land B$ proposition. | SUPPORTED FOR THE MANUSCRIPT; FAILED IN LEAN FIDELITY |
| P1 | The one-window finite fraction is exactly $F_{a,b}/W_{a,b}$. | `app:curv-code`; blockedness at the tested scale. | Numerator and denominator must refer to the same barrier row and conditioned a-priori range. | For $(1,1)$, inspect $W=543958$, $F=111286$. | SUPPORTED |
| P2 | Separation of dyadic scales makes their completion supports disjoint. | Scale selection. | Numerical scale separation alone does not imply spatial disjointness; the proof must use prefix conditioning when supports meet. | Reuse an outside path in two scale completions. | AMBIGUOUS BUT NOT NEEDED UNDER THE CONDITIONAL-FIBRE DECISION |
| P3 | If every conditional fibre satisfies the bound, multiplying fibre sizes gives the saving. | Finite exposure chain rule. | “Every” must quantify over the actual prefix fibres, not all-coordinate conditionals. | An $F$-regular relation has small full conditionals but a large joint class. | SUPPORTED UNDER THE PREFIX READING |
| P4 | Failure supplies a finite family for which no exposure order works. | Definition of $\mathsf{Add}$; finiteness. | Failure of one fixed order does not imply failure of every order. | Two disjoint $F$-sized blocks: one order fails, the reverse succeeds. | SUPPORTED ONLY FOR THE NO-ORDER PREDICATE |
| P5 | A minimal failed family has connected overlap support. | `lem:barrier-failure-overlap`. | Disconnected components must factor in the current conditional fibre. | Concatenate the componentwise admissible orders. | SUPPORTED BY THE ATTACHED LOCALIZATION LEMMA |
| P6 | The connected obstruction enters [172]. | `lem:window-system-realizability` alternatives (i)--(v). | The selected output must be an actual scale-spanning serial system after cases (i)--(iv) are closed. | Inspect the destination's required objects. | ROUTING ONLY; NOT PRODUCED IN LEAN |
| L1 | Lean's `blockedScaleAdditive` states only node [170]'s predicate. | `Holds`; `BlockedScaleAdditivityStatement`. | [171]'s cardinal conclusion must not be bundled. | Expand the conjunction. | FAILED |
| L2 | Lean's no key is a failed-additivity fact fit for [172]. | `Holds .blockedBarrierOverlap`. | $\neg(A\land B)$ must imply $\neg A$ and expose an obstruction witness. | Incoming facts force $\neg B$. | FAILED |

## 4. Counterexample attempts

### Smallest-parameter test

- **Explicit data:** Take one fixed barrier coordinate in a nonempty conditional fibre with exactly one realized state. Every certified $F_{a,b}$ is positive (otherwise the displayed logarithmic rate would be undefined), so $1\le F_{a,b}$ and the intended additivity test passes.
- **Hypotheses satisfied:** Nonempty fibre, one window coordinate, fixed outside record, and the exact non-strict conditional bound.
- **Accumulated facts violated:** This abstract one-coordinate fibre is not by itself a labelled graph satisfying the complete minimal-counterexample, dense-overflow, and trivial-neutral ledger.
- **Applicability:** **NON-APPLICABLE TO THE NODE** as a complete graph, first because node [1]/[2]'s selected graph and target-avoidance data have not been realized. It is nevertheless the smallest exact model showing that $A$ can hold while a separately false $B$ must not send the state to [172].

### Parity or 2-adic test

- **Explicit data:** To test the arithmetic destination rather than silently treat it as a contradiction, take $g=32=2^5$, $L=17$, residues $r=0,\ldots,12$, $C_{\rm sys}=1$, and $T_r=20$. The bundled checker reports raw odd-part hits modulo $u=1$ for every exponent, but no 2-adically compatible residue and no valid full-modulus hit.
- **Hypotheses satisfied:** Thirteen consecutive residue candidates, nonempty central coefficient ranges, and the even-modulus/odd-part shape mentioned by the destination theorem.
- **Accumulated facts violated:** It is not the scale-spanning spectrum produced by `lem:window-system-realizability`; in particular it does not supply the full compatible doubling orbit required by the actual destination entry. It is also not a graph-realized cycle spectrum.
- **Applicability:** **NON-APPLICABLE TO THE NODE.** Node [170] performs no modular inference, and the earliest excluding destination fact is `[172] scale-spanning serial system`. The test confirms that the no edge must carry the full serial-system witness; a bare negation such as $\neg(A\land B)$ cannot authorize arithmetic closure.

### Boundary or range test

- **Explicit data:** At a fixed row, let a nonempty prefix fibre have exactly $F_{a,b}$ states; it belongs to the yes arm because the bound is non-strict. With one window and $F_{a,b}+1$ states, the yes predicate fails, and the singleton window family itself is a minimal obstruction.
- **Hypotheses satisfied:** Both tests use the exact finite barrier range and the equality boundary of the displayed $\le F_{a,b}$ condition.
- **Accumulated facts violated:** No full blocked graph realizing either abstract fibre is constructed.
- **Applicability:** The equality case validates the intended yes boundary, while the $F+1$ singleton validates the intended no destination at finite-state level. Neither is an actual residual graph, so each is **NON-APPLICABLE TO THE NODE** as a graph, first at node [1]/[2]. In the live formal decision, both are routed no whenever $B$ fails, erasing this required distinction.

### Graph-realizability test

- **Explicit data:** Place two induced $P_{13}$ windows in a finite labelled support and let their canonical barrier completions share an outside path segment. Changing the shared segment can correlate the two label triples, giving the geometric overlap that `def:barrier-overlap-system` is designed to record.
- **Hypotheses satisfied:** The root windows can be vertex-disjoint while their completion supports meet outside their interiors; the overlap support is connected and can be minimized inside the finite support.
- **Accumulated facts violated:** The local support has not been completed to a finite graph of minimum degree at least three with no power-of-two cycle, the dense package overflow, every trivial-neutral corridor fact, and the fixed canonical completion choices.
- **Applicability:** **NON-APPLICABLE TO THE NODE** as an actual residual, first at node [2]'s counterexample predicate. It shows that the no branch needs concrete completion-support data; the proposition $\neg(A\land B)$ contains none.

### Branch-routing test

- **Explicit data:** Let $A$ be true on an incoming residual and use the retained facts $G\in\mathcal B(\mathcal P)$ and $Q>|\mathcal G_{n,m}|$. Then $|\mathcal B(\mathcal P)|\ge1$ and the near-cubic class is bounded by $|\mathcal G_{n,m}|$, so the formal second conjunct $B$ is false. Thus `scaleAdditivityDichotomy` returns the `blockedBarrierOverlap` arm because $\neg(A\land B)$, despite $A$.
- **Hypotheses satisfied:** This is the exact proposition-level state of the live `ExactLedger`: blocked membership and dense overflow are both required at the call site, and $A$ is the manuscript's legitimate yes predicate.
- **Accumulated facts violated:** No source-level accumulated fact says $A$ is false. A concrete minimal-counterexample graph on the additive arm is not exhibited; the proof itself is conditional on such a residual.
- **Applicability:** Applicable to the live Lean handoff contract: the resulting fact does not meet [172]'s entry predicate $\neg A$ and carries no minimal obstruction.  It is **NON-APPLICABLE TO THE NODE** as a paper counterexample because the manuscript decision is the prefix-exposure property $A$ alone.  It records a formal-fidelity regression and does not determine the mathematical verdict.

## 5. Strongest valid counterexample

No candidate reaches the complete residual and falsifies the intended prefix-exposure decision.  The strongest isolated prose counterexample is the even-parity code
\[
\mathcal S=\{x\in\{0,1\}^t:\textstyle\sum_i x_i\equiv0\pmod2\},
\qquad W=2,\quad F=1.
\]
After all other coordinates are fixed, the remaining coordinate has exactly one possible value, yet $|\mathcal S|=2^{t-1}$; thus the all-other reading does not yield the claimed product saving.  Under the intended prefix reading the first exposed coordinate has two possibilities, so the example takes the no arm and is routed to the overlap analysis.  The live-ledger state $A\land\neg B$ remains a separate counterexample to the Lean proposition-to-destination implication, but it is not a counterexample to the manuscript node.

## 6. Local repair

### Corrected statement

Fix a separated scale $2^j$, a barrier $(a,b)$, the outside-edge record, all earlier-scale states, and a nonempty current conditional fibre. Exactly one of the following holds.

1. Every nonempty window subfamily admits an exposure ordering such that, after conditioning on the previously exposed states, the next window has at most $F_{a,b}$ possible barrier states. Then the conditional savings $\gamma_{a,b}=\log_2(W_{a,b}/F_{a,b})$ multiply over that fibre. Applying this at every barrier and separated scale gives the additive fact passed to [171].
2. Some nonempty window family admits no such ordering. Choose it minimal by cardinality. It is a barrier overlap obstruction; its overlap support is connected by `lem:barrier-failure-overlap`, and this explicit object is passed to the structural alternatives leading to [172].

The compression inequality for $\mathcal B(\mathcal P)$ is not part of either decision predicate; it is the conclusion to be derived at [171].

### Complete local proof

All relevant window families and state sets are finite. Apply excluded middle to the ordering property in item 1. If it holds, expose the windows in the supplied order. For each realized prefix, the next coordinate has at most $F_{a,b}$ choices. Induction on the family size multiplies these bounds, and repeating the same conditional argument in the fixed barrier/scale encoding order yields the additive product fact. This proves only the node-[170] yes payload; code injectivity and the uncompressed baseline remain obligations of [171].

If the ordering property fails, the finite set of failing nonempty window families is nonempty. Choose a member $\mathcal U$ of least cardinality. By construction no ordering of $\mathcal U$ satisfies the conditional bound, while every proper nonempty subfamily does, so $\mathcal U$ is a minimal barrier overlap obstruction exactly as defined. If its overlap support were disconnected, minimality supplies an admissible order inside each connected component and disjoint declared supports allow those component orders to be concatenated, contradicting failure. Hence the support is connected. The object $\mathcal U$, its fibre, and its completion supports—not merely a negated proposition—satisfy the structural entry to the [172] route.

### Counterexample disposition

The parity-code candidate fails item 1 at its first prefix and therefore takes item 2; it no longer masquerades as an additive family merely because every all-other conditional is a singleton.  The live $A\land\neg B$ candidate takes item 1 after the formal proposition is repaired and reaches [171], where deriving $B$ is a separate obligation.  A fibre of size $F_{a,b}+1$ with no alternative exposure ordering takes item 2 and carries its minimal support. The even-modulus arithmetic test is not admitted until item 2 has been converted into the full scale-spanning serial spectrum; it cannot be inferred from the decision's negation alone.

### Graph patch

No new displayed branch is needed. The existing graph should carry these exact predicates:

```text
[169] -- blocked-class member; dense overflow; trivial neutral residual --> [170]
[170] -- Add: every relevant conditional fibre admits the F_{a,b}
         exposure bound; retain blocked member and dense overflow --> [171]
[170] -- not Add: publish a minimal nonempty no-order obstruction,
         its fixed fibre and connected completion support --> [172]
```

The [172] edge may internally close the nonserial alternatives before passing the scale-spanning serial witness to its arithmetic component. It must not consume a bare failure of [171]'s cardinal conclusion.

### Downstream impact

In the manuscript, `lem:scale-additivity` should say “previously exposed windows” or state the admissible-order property explicitly; this removes the possible all-other-windows reading. `lem:barrier-failure-overlap` already names the required no-order obstruction. The Part XII node label, its two edges, caption, summary row, and dependency-table row can remain after their edge payloads are made explicit. `lem:blocked-graphs-compress` must continue to prove—rather than assume—the encoding injectivity, uncompressed baseline, and resulting cardinal inequality.

In Lean, `BlockedScaleAdditivityStatement` must contain only the conditional-fibre/exposure property. Its current second conjunct belongs to a node-[171] theorem. `Holds .blockedBarrierOverlap` should be an existential obstruction statement with the fixed scale, barrier, conditional fibre, minimal family, and support data, or a producer immediately after the literal $\neg\mathsf{Add}$ decision should construct that object. `scaleAdditivityDichotomy` must read the blocked-class input for that construction rather than discard it as `_blocked`. `blockedClassCompressionCloses` must derive its saving inequality from separately proved code injectivity and baseline facts. The absent `selectedBarrierOverlapSerialSystem` must consume the obstruction object, not $\neg(A\land B)$. `BarrierOverlapSystem.lean` currently defines the state and `ConditionalFibre` but no obstruction or uncrossing object; the graph-free `SerialSystemArithmetic.lean` does not fill that gap.

The pair-overlap branch [178]--[180] uses the analogous “no exposure order works” language and should be checked when its own implementation is built, but no source occurrence was found that reuses the erroneous `BlockedScaleAdditivityStatement` conjunction outside [170]--[172]. The node-status table and JSON sidecar should be synchronized only after the live declarations are repaired.

## 7. Regression audit

The audit inspected:

- The Part XII decision box, both yes/no edges, caption, structural-exhaustion summary row, detailed dependency rows, and the complete statements and proofs of `def:blocked-class`, `def:barrier-overlap-system`, `lem:barrier-failure-overlap`, `lem:scale-additivity`, and the outgoing [171]/[172] entry material.
- The accumulated `lem:p13-window-package`, cold first-failure, neutral/trivial-residual, near-cubic, and dense-overflow statements needed to reconstruct the selected path.
- The exact finite $(1,1)$ counts $W=543958$, $F=111286$, the $91$-barrier aggregate, and the appendix computation of $c_{13}$.
- `Graph/BarrierOverlapSystem.lean`: completion supports, deterministic barrier states, outside-edge code, and the literal prefix-ranked `ConditionalFibre`.
- `Strategy/SpineVocabulary.lean`: `blockedClassAt`, encoding coordinates/rank, `blockedBarrierCode`, `BlockedScaleAdditivityStatement`, and the two `Holds` clauses. The second conjunct is exactly the [171] compression inequality.
- `Strategy/BlockedCompressionRows.lean`: `scaleAdditivityDichotomy` reads and discards `_blocked`, decides the conjunction, and publishes its exact negation; `blockedClassCompressionCloses` destructures the same key and consumes the bundled inequality.
- `Assembly.lean`: `selectedScaleAdditivityDichotomy` requires blocked membership and dense overflow, routes the no key directly to the absent `selectedBarrierOverlapSerialSystem`, and contains no intermediate obstruction producer.
- `Graph/SerialSystemArithmetic.lean` and the [172] manuscript contract only to verify the no-edge entry data. The modular checker on `/tmp/eg-node-170-modular.json` found raw odd-part hits but no compatible full-modulus hit; the candidate was rejected because it lacks the destination's scale-spanning witness.
- The analogous pair-overlap definitions and nodes [178]--[180]. They explicitly require a minimal no-order obstruction and do not justify weakening the node-[170] no payload.
- The review postmortem entries E03, E04, E09--E12. This report respects their corrections: it does not demand global independence, treat nonadditivity as omitted, claim the outside code already determines the graph, or use a raw modular congruence as a counterexample.

The principal searches were

```text
rg -n 'node \[170\]|conditional savings|scale-additivity|barrier overlap' to_formalize/erdos_64_proof.tex
rg -n 'BlockedScaleAdditivityStatement|blockedBarrierOverlap|blockedScaleAdditive|scaleAdditivityDichotomy|ConditionalFibre' hypostructure proofs Assembly_node_audit.md web/data/eg_node_audit.json
rg -n 'no ordering|exposure order|pair overlap obstruction|pair-failure' to_formalize/erdos_64_proof.tex
rg -n '170|conditional fibre|blocked class|odd part' erdos_64_conversation_mistakes.md EG_LEAN_COMPLIANCE_REMAINING.md
```

No second live producer of a barrier overlap object, no alternate no-arm predicate implying $\neg A$, and no call site that repairs the conjunction before [172] were found.

## 8. Residual uncertainty

No actual finite minimal counterexample realizing every node-[169] fact was constructed, and no candidate refutes the intended prefix-exposure dichotomy. The manuscript alternates between conditioning on “the other windows,” a canonical exposure order, and existence of an admissible order; the repair states the no-order prefix version because that is the literal premise of `def:barrier-overlap-system`.  A formal implementation must choose the same decision-tree formulation and prove the equivalence used by the product count. The current Lean $A\land B$ predicate remains a genuine fidelity mismatch, but missing or mismatched formal plumbing is not evidence that the corrected paper statement is false. This audit did not independently prove [171]'s full blocked-code baseline or [172]'s uncrossing and arithmetic closure; it checked them only as outgoing contracts. No manuscript, diagram, Lean, implementation-audit, or coverage-ledger source was changed.
