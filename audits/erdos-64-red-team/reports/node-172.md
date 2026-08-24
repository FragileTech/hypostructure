<!-- red-team-audit
{
  "schema_version": 1,
  "proof": "erdos-gyarfas",
  "node": 172,
  "node_label": "fixed-scale overlap system:\\\\serial realization and increment arithmetic close",
  "panel": "fig:proof-diagram-part-xii",
  "contract_sha256": "986ac18d8cae76a3d56ed6c4d0fd866bd38adb182a3fc522222966da6e1b66b7",
  "manuscript_sha256": "106a8205a1718fbf90e1686a107b2143b9edca574e2b0c11415e7f44aee2c0f9",
  "graph_sha256": "dc67fae178f947a9607c167e383d85919633341bdd423e4c4a45e4c317b3a765",
  "lean_audit_sha256": "50324ef5594d635a52d83aeb297f2ca3f3d30ef58de4ce3602816c7e78365b12",
  "verdict": "MISSING RANGE OR DIVISIBILITY CHECK",
  "audited_at": "2026-08-24T21:35:43Z"
}
-->

# Red-team audit: node [172]

## 1. Executive verdict

Verdict: **MISSING RANGE OR DIVISIBILITY CHECK**

Node [172] does not justify its terminal arithmetic closure.  From
\[
2^k\equiv L+r\pmod{u},\qquad g=2^a u,quad u\text{ odd},
\]
the proof infers that (2^k) is one of the realized central lengths
(L+r+tg).  This omits two independent requirements: (2^a\mid L+r), with the corresponding normalized congruence modulo (u), and the exact bound
(C_{\rm sys}\le t\le T_r-C_{\rm sys}).  Scale-spanning only puts the minimum and maximum spectra on opposite sides of the tested power; it does not move a congruent power into a particular central coset.  Consequently a raw odd-part hit can be neither a realized target nor an orbit-avoidance case, so the stated two-way closure leaves an arithmetic residual unproved.  This is a local defect in [172], not a counterexample to the full graph theorem.

## 2. Exact node contract

### Incoming residual

The only immediate edge is `[170] --no--> [172]`.  It carries the selected finite simple graph (G), its fixed maximal vertex-disjoint induced-(P_{13}) packing (mathcal P), the fixed outside-edge record and earlier barrier-state prefix, and a fixed separated scale (2^j) and barrier ((a,b)) at which the conditional state saving does not add.  On the intended manuscript path, `lem:barrier-failure-overlap` chooses a minimal connected overlap obstruction in that conditional fibre.  `lem:window-system-realizability` eliminates its alternatives (i)--(iv) by the already retained target, G2, G3, Type B, and route-8 exits, leaving alternative (v): a scale-spanning serial window system whose increments are at most

\[
D_{\rm sys}=2M_{\rm cold}+26
\]

and for which every displayed choice is an actual simple cycle of the same (G).

The manuscript's logical no-arm is the failure of the local conditional-additivity predicate.  The current Lean key is weaker evidence, not an additional manuscript fact: it records the negation of a conjunction that also includes [171]'s cardinal conclusion and carries no obstruction object.  The node's mathematical audit therefore uses the intended manuscript witness and records the Lean mismatch only in the regression audit.

### Accumulated facts

The retained path facts are:

- `[1]`, `[2]`: (G) is a finite simple graph with minimum degree at least three and no cycle of accepted power-of-two length.
- `[4]`--`[14]`: (G) is the selected lexicographically minimal counterexample; target response is context-universal; any actual smaller proper target-complete representative is forbidden by replacement and hereditary uncompressibility.
- `[15]`, `[17]`, `[18]`: (G) contains the fixed maximal induced-(P_{13}) packing with its label algebra and offsets (0,\ldots,12).
- `[19]`, `[21]`: the near-cubic spine and finite window package have been supplied.
- `[158] --no--> [159]`, `[160] --no--> [162]`: the dense package overflow persists through the dense hot/cold branch.
- `[163]`, `[165]`, `[166]`: the selected neutral germ is in the canonical equal-size case and the refined tie-break leaves the trivial (Q=E) residual.
- `[169]`: every selected corridor is terminal, neutral, and its own canonical representative; the selected graph belongs to the fixed blocked class and every packed window is blocked at every tested scale.
- `[170] --no--> [172]`: at a fixed scale and barrier, the conditional saving fails; on the intended paper route this produces the minimal connected overlap obstruction just described.
- `lem:window-system-realizability` (v): after prior closures, the obstruction is a scale-spanning serial system; its cells have disjoint interiors and every spectrum choice closes an actual simple cycle of (G).
- `lem:serial-system-sumset`: for the gcd (g) of the frequent increments and a residue set (mathcal R), the actual simple-cycle spectrum contains
  \[
  L+r+tg,qquad r\in\mathcal R,quad C_{\rm sys}\le t\le T_r-C_{\rm sys},
  \]
  with (|\mathcal R|\ge\min\{13,g\}).  Empty end ranges go to the bounded cold table.
- `def:serial-window-system`: even after any bounded number of end-cell deletions, the shortest and longest realizable cycle lengths, with the available offsets, lie on opposite sides of the tested (2^j).

No accumulated fact says that every residue coset crosses (2^j), that an odd-part hit is (2)-adically compatible, or that the integer lift lies in its residue-dependent central interval.

### Current predicate and exact claim

Write (g=2^a u) with (u) odd.  Node [172] claims:

1. if the doubling orbit modulo (u) meets the projection of (mathcal R), then the central realized spectrum contains a power (2^k);
2. if that orbit avoids the projected residues, the odd-part route residue is a periodic response class routed to G2, G3, or the declared route-8 trace interface;
3. for odd (g), the cardinal inequality (operatorname{ord}_g(2)>g-|\mathcal R|) forces the first case; and for even (g), the same reasoning applies modulo (u) after the transient (k<a).

For a chosen integer representative (r), the actual direct-hit predicate is instead

\[
\exists k,t:quad 2^k=L+r+tg,qquad
C_{\rm sys}\le t\le T_r-C_{\rm sys}.
\]

For (k\ge a), this equality requires

\[
2^a\mid L+r,qquad
2^{k-a}\equiv\frac{L+r}{2^a}\pmod u,qquad
t=\frac{2^k-L-r}{g}\in[C_{\rm sys},T_r-C_{\rm sys}].
\]

Raw intersection after projecting (L+r) modulo (u) is insufficient.  Even when (a=0), a full-modulus congruence says only that (t) is an integer, not that it is central.

### Outgoing contracts

Node [172] is terminal and has no drawn outgoing edge.  Its terminal contract is therefore stronger than production of a serial system: every serial alternative must either realize a power-of-two cycle in (G), supply the complete entry data for G2, construct an actual smaller proper representative for G3, reach the declared route-8 trace interface with its indexed support data, or enter the bounded finite table.  A raw odd-part hit with no exact central lift meets none of these destination contracts.  It is incorrectly classified as case (a), while case (b) requires raw avoidance and is false for the same input.

## 3. Sentence audit

| Sentence | Exact assertion | Facts used | Hidden obligation | Adversarial test | Status |
|---|---|---|---|---|---|
| S1 | Failure of the fixed-scale product saving yields a minimal connected barrier overlap obstruction. | `[170]` no; `def:barrier-overlap-system`; `lem:barrier-failure-overlap`. | The no-predicate must be exactly failure of conditional additivity and must retain the fixed scale, barrier, conditional fibre, and completion supports. | Compare the manuscript no-arm with Lean's negation of a larger conjunction. | SUPPORTED IN THE MANUSCRIPT; ABSENT IN LEAN |
| S2 | After alternatives (i)--(iv), uncrossing yields a scale-spanning serial system with bounded increments and actual simple-cycle realizations. | `lem:window-system-realizability`; (Q=E); prior G1/G2/G3/handoff closures. | All earlier alternatives must preserve the same support and destination entry facts. | Follow a branching or cyclic intersection support through the stated secondary minimality. | SUPPORTED AS THE INCOMING CONTRACT FOR THE ARITHMETIC TEST |
| S3 | The serial spectrum contains every (L+r+tg) in the residue-dependent central range. | `lem:serial-system-sumset`; actual-cycle clause. | The representative (r), its rare submultiset, and its own (T_r) must stay paired. | Give different residues different upper ranges. | SUPPORTED AS STATED |
| S4 | Scale-spanning puts a congruent power into the central coefficient interval after bounded scales are put in the cold table. | Scale-spanning; S3. | Min/max straddling must imply that the *same residue coset* has a central representative at the power. | Use (g=31,L=0,mathcal R=\{0,\ldots,12\},C=10,T_r=30): the spectrum straddles (512), but (512\bmod31=16\). | FAILED |
| S5 | If the orbit modulo the odd part (u) meets (mathcal R), the central spectrum contains (2^k). | S3; modular orbit. | Need (2^a\mid L+r), the normalized congruence, an exact integer (t), and the central bounds on (t). | Use (g=48,L=1,r\in\{0,\ldots,12\}): raw hits modulo (3) exist, but (16\nmid L+r) for every (r). | FAILED |
| S6 | If the projected orbit avoids (mathcal R), the odd-part residue transported along interfaces is well-defined. | System increments generate route-length differences. | The response must retain the full phase relevant to target equality, not only its odd projection. | Two routes congruent modulo (u) but different modulo (2^a) have different power-of-two compatibility. | FAILED AS A TARGET-RESPONSE INVARIANT |
| S7 | A context-visible repeated response gives G2. | Context universality. | The two actual response supports and a distinguishing compatible context must be exhibited. | Retain only a residue number with no response-support pair. | CONDITIONAL; ROUTING DATA NOT CONSTRUCTED BY ARITHMETIC ALONE |
| S8 | A context-invisible response gives G3. | Replacement; hereditary uncompressibility. | Equal residues do not themselves construct an actual smaller proper graph representative with the same boundary-degree profile. | Delete between abstract equal residues and check simplicity, degrees, properness, and exact target response. | CONDITIONAL; REPRESENTATIVE MUST BE CONSTRUCTED |
| S9 | A minimal response support reaching a trace interface is already route 8. | Declared route-8 carrier interface. | It must carry the indexed basin, essential incidences, private-support data, and deletion witnesses required downstream. | Compare a bare modular trace with `def:typeA-route8-carriers`. | ROUTING ONLY; ENTRY FACTS MUST BE RETAINED |
| S10 | For odd (g), (operatorname{ord}_g(2)>g-|\mathcal R|) forces a modular intersection. | Orbit cardinality; (|\mathcal R|) bound. | (2) must be a unit modulo (g), and intersection is only modular, not a central realization. | Separate the pigeonhole conclusion from the coefficient interval. | SUPPORTED ONLY AS A MODULAR INTERSECTION |
| S11 | For (g=2^a u), the odd-(u) assertion applies after (k<a). | Factorization of (g). | Must restrict to (r) with (2^a\mid L+r) and divide the congruence by (2^a). | Run the exact checker on (g=48,L=1). | FAILED |
| S12 | Hence a scale-spanning serial window system is impossible and [172] closes. | S4--S11. | Every no-exact-hit case must be sent to a destination with its entry data. | A raw odd-part hit with no compatible central lift is neither the stated hit nor avoidance case. | FAILED |

## 4. Counterexample attempts

### Smallest-parameter test

- **Explicit data:** Take (g=1), (L=20), (mathcal R=\{0\}), (C_{\rm sys}=1), and (T_0=20).  The displayed central spectrum is the integer interval (21,\ldots,39), which straddles and contains (2^5=32).
- **Hypotheses satisfied:** The central range is nonempty, (|\mathcal R|=\min\{13,g\}=1), and the direct-hit equation holds with (t=12).  This tests the degenerate odd modulus for which an order formula should be separated from the elementary interval argument.
- **Accumulated facts violated:** No actual selected minimum-degree-three graph or node-[170] overlap obstruction is supplied.
- **Applicability:** **NON-APPLICABLE TO THE NODE** as a graph counterexample, first missing node [2]'s selected-graph contract.  It is a successful smallest-modulus sanity check: once the exact coefficient range is imposed, there is no arithmetic counterexample at (g=1).

### Parity or 2-adic test

- **Explicit data:** Give the modular checker (g=48=2^4\cdot3), (L=1), (k=4,\ldots,20), (C_{\rm sys}=1), and residues (r=0,\ldots,12), each with (T_r=100).  The checker reports many `raw_odd_part_hits`, `compatible_residues: []`, no full-modulus lifts, and `has_valid_direct_hit: false`.
- **Hypotheses satisfied:** The modulus is a bounded positive system increment; the residue set has the required thirteen consecutive members; every central range is nonempty; and the doubling orbit modulo the odd part (3) meets the projected residues.
- **Accumulated facts violated:** These arithmetic data alone do not construct the selected graph, the minimal fixed-scale overlap obstruction, or the graph-realizable serial system required by nodes [2], [170], and `lem:window-system-realizability`.
- **Applicability:** **NON-APPLICABLE TO THE NODE** as a complete graph residual, first missing node [2].  It is directly applicable to and falsifies S5/S11: for (k\ge4), every power is divisible by (16), whereas (L+r=1,\ldots,13) is never divisible by (16).

### Boundary or range test

- **Explicit data:** Give the checker (g=31), (L=0), (k=0,\ldots,12), (C_{\rm sys}=10), and (r=0,\ldots,12) with (T_r=30).  The central spectrum consists of (r+31t) for (10\le t\le20), lies between (310) and (632), and therefore straddles (512).  The orbit has full congruence hits at residues (1,2,4,8), but their lift coefficients are respectively below (10) or above (20); the checker reports no valid direct hit.  In particular, (512\equiv16\pmod{31}), outside the displayed residue set.
- **Hypotheses satisfied:** Here (g) is odd, the full-modulus and odd-part congruences agree, all residue ranges are nonempty, (|\mathcal R|=13), and the central union straddles a tested power.
- **Accumulated facts violated:** The data are a spectrum rather than a selected graph serial system, so they first omit node [2]'s graph contract.
- **Applicability:** **NON-APPLICABLE TO THE NODE** as a full graph counterexample, first missing node [2].  It is a valid counterexample to S4: scale straddling and modular intersection do not put a lift inside the finite central range.

### Graph-realizability test

- **Explicit data:** Fix an end-deletion bound (B) and (C=C_{\rm sys}).  Choose (N> B(D_{\rm sys}+1)), (q=2C+2N\ge2D_{\rm sys}^2), an even (j\ge4) so large that (L=2^j-15-48(C+N)>8), and (q) serial cells.  At each cell use two internally disjoint paths whose lengths differ by (48); use closing paths supplying offsets (0,\ldots,12).  The resulting cycle spectrum contains
  \[
  L+r+48t,qquad 0\le r\le12,quad0\le t\le q.
  \]
  It remains scale-spanning after at most (B) end-cell deletions by the (N)-cell slack.  Yet (L\equiv1\pmod{48}), so every displayed length is congruent to one of (1,\ldots,13pmod{48}), while every power (2^k) with (k\ge4) is (16) or (32pmod{48}); the smaller powers lie below (L).  The raw orbit modulo (3) does meet the projected residues.
- **Hypotheses satisfied:** This is an explicit serial graph support with disjoint cell interiors, bounded increment (48\le D_{\rm sys}), at least the required frequency, thirteen offsets, robust scale-spanning, and actual simple cycles for every selected cell path and closing offset.  It realizes the strongest arithmetic countercandidate, including the local graph-realizability clause of the serial-system definition.
- **Accumulated facts violated:** Internal vertices on the long cell and closing paths have degree two.  The support is not exhibited inside a selected minimum-degree-three graph satisfying the dense packing, blocked-class, minimality, and node-[170] obstruction facts.
- **Applicability:** **NON-APPLICABLE TO THE NODE** as an actual cumulative residual, first excluded by node [2]'s minimum-degree-three selected-graph condition.  It shows that the local serial-system and scale-spanning hypotheses themselves do not repair the missing (2)-adic check.

### Branch-routing test

- **Explicit data:** Reuse (g=48,L=1,mathcal R=\{0,\ldots,12\}) and any nonempty central ranges containing many coefficients.  The projected orbit modulo (3) meets (mathcal R), but no residue is compatible modulo (16).
- **Hypotheses satisfied:** The exact predicate written in [172](a), “the doubling orbit modulo the odd part of (g) meets one of the realizable residues,” is true.  The exact predicate written in [172](b), projected avoidance, is false.
- **Accumulated facts violated:** As in the parity test, no complete selected graph residual is supplied.
- **Applicability:** **NON-APPLICABLE TO THE NODE** as a whole-graph counterexample, first missing node [2].  It is fully applicable to the outgoing partition: the input is sent to the direct-hit arm, whose target conclusion is false, and cannot enter the avoidance arm.  Thus the missing compatibility condition also creates an unassigned corrected residual.

## 5. Strongest valid counterexample

No candidate constructed here reaches the complete node-[172] residual: in particular, no minimum-degree-three, target-avoiding, dense blocked graph carrying the prescribed node-[170] minimal overlap obstruction was found.  The strongest candidate is the parametric (g=48) serial graph support in the graph-realizability test.  It satisfies every local combinatorial and arithmetic hypothesis immediately used by [172]—bounded and frequent increment, thirteen offsets, actual simple-cycle realizations, and scale-spanning after bounded end deletions—while a raw odd-part hit exists and no power of two is in its spectrum.  Its degree-two internal vertices are the earliest reason it is not a counterexample to the cumulative graph residual.  It nevertheless refutes the exact arithmetic inference because minimum degree is not used in, and cannot supply, the omitted congruence and range conditions.

## 6. Local repair

### Corrected statement

Let (g=2^a u) with (u) odd, and choose an integer representative for every (r\in\mathcal R) together with its associated upper coefficient (T_r).  Define

\[
\mathcal R_a=\{r\in\mathcal R:2^a\mid L+r\},
\qquad
\widetilde{\mathcal R}_a=
\left\{\frac{L+r}{2^a}\bmod u:r\in\mathcal R_a\right\}.
\]

The direct target case holds exactly when there are (r\in\mathcal R_a), (k\ge a), and an integer (t) such that

\[
2^{k-a}\equiv\frac{L+r}{2^a}\pmod u,
\qquad
t=\frac{2^k-L-r}{g},
\qquad
C_{\rm sys}\le t\le T_r-C_{\rm sys}.
\]

The finitely many exponents (k<a), empty central ranges, and lifts meeting only an end interval are checked in the bounded cold table.  If there is no exact central hit, retain the full phase modulo (g), the relevant cut state and boundary-degree profile, the two truncated distances to the central-range ends, and any declared trace incidence.  A context-distinguished equal full-phase pair routes to G2; a context-indistinguishable pair routes to G3 only after deletion of the intervening serial segment has been exhibited as an actual smaller proper representative; a pair meeting a declared trace interface routes with the complete route-8 carrier data.  If no such pair occurs, the number of interfaces is bounded by the finite full-state count and the system is a cold-table row.  A raw odd-part hit or no-hit is not itself terminal.

### Complete local proof

For (k\ge a), suppose first that (2^k=L+r+tg).  Reducing modulo (2^a) gives (2^a\mid L+r).  Dividing the equality by (2^a) and reducing modulo (u) gives the normalized congruence.  Solving the equality gives the displayed formula for (t), and membership in the sumset supplied by `lem:serial-system-sumset` gives its two central bounds.

Conversely, take (r,k,t) satisfying the corrected direct-hit predicate.  The normalized congruence says (u\mid 2^{k-a}-(L+r)/2^a).  Multiplying by (2^a) gives (g\mid2^k-L-r), so the displayed (t) is an integer and (2^k=L+r+tg).  Its central bounds let `lem:serial-system-sumset` realize (2^k) as an actual simple cycle of (G), contradicting node [2].  This proves precisely the direct target arm.  The cases (k<a) and the two end intervals contain only a bounded number of exponent/coefficient patterns because (g,D_{\rm sys},C_{\rm sys}) are fixed; they are legitimate finite-table inputs, not implicit central lifts.

Assume now that no exact central hit exists.  Transport along each ordered interface the route length modulo the full (g), not merely modulo (u), together with the already finite cold cut state, boundary-degree profile, truncated central-end availability, and declared-interface flag.  System increments change route lengths by multiples represented in the system ledger, so this full state is well-defined for the same corridor choice data.  There are only finitely many such states, with a bound depending on (D_{\rm sys}) and the registered cold table.  If the interface list is longer than that bound, two interfaces have equal full state.  Their intervening interiors are disjoint by serial realizability.  If a compatible outside context distinguishes deleting that interval from retaining it, the two actual supports are a target-defective pair and `lem:context-universality` supplies G2.  If no context distinguishes them, the equal boundary profile and full target phase make deletion target-complete; deleting a nonempty serial interval gives the required actual proper smaller support, so `lem:replacement` and `cor:uncompressible` supply G3.  If the minimal repeated support meets a declared trace interface, retain its indexed incidences and send it instead through the declared route-8 carrier reduction.  If there is no repeat, the interface count is bounded and the complete support belongs to the finite cold table.  These predicates exhaust the no-exact-hit branch without calling projected avoidance a contradiction.

### Counterexample disposition

For the (g=48,L=1) candidates, (mathcal R_a) is empty because no (L+r\in\{1,\ldots,13\}) is divisible by (16).  They therefore do not enter the repaired direct-hit arm.  Their complete phase is retained and they proceed to the full-phase repeat/G2/G3/trace/finite-table decision.  For the (g=31) range candidate, the congruences give integer lifts but every lift fails one of the exact central inequalities, so it receives the same no-exact-hit treatment.  The (g=1) sanity test remains a direct hit.

### Graph patch

Replace the terminal shortcut by the following typed subdiamond:

```text
[170] no
  -- retain fixed scale, barrier, outside prefix, failing fibre,
     minimal connected overlap support --> [172a] serial uncrossing

[172a] cases (i)--(iv) --> [155] / [156] / [157] / declared handoff
[172a] case (v), with actual serial system and residue-specific ranges --> [172b]

[172b] exact compatible central lift H(g,L,r,k,t)?
  yes --> [155] G1, carrying the actual simple cycle of length 2^k
  no  --> [172c] full-phase response decision

[172c] bounded/transient/end-supported --> finite cold table [157]
[172c] context-distinguished repeat --> G2 [156], carrying both supports and context
[172c] context-equivalent proper deletion --> G3 [157], carrying the actual representative
[172c] declared trace support --> route 8, carrying its indexed carrier/incident data
```

Node [172] may remain terminal only after each last destination has discharged its own entry contract.  The [170] Lean decision must separately negate the local conditional-additivity predicate and append the fixed witness data; it must not use the present bare negation of a conjunction containing [171]'s conclusion.

### Downstream impact

The statement and proof of `lem:system-increment-arithmetic`, the Part-XII [172] terminal label and caption, the [169]--[172] overview row, detailed dependency row 53, `lem:scale-additivity`, and every later assertion that the nonadditive branch is closed must use the exact-hit/full-phase split.  `lem:cold-increment-arithmetic` contains the same unbounded congruence-to-attainability inference and the same unnormalized even-modulus reduction.  `lem:pair-system-increment-arithmetic` says its proof is “word for word” the [172] proof, so node [180], the Part-X caption, overview row 54, and its dependency row require the identical repair.  Any final density or closure theorem consuming [170]--[172], including `prop:p13-density` and the introductory proof summary, must wait for the repaired destinations.

The Lean `SerialSystemArithmetic.Spectrum.exists_pow_realized` proves a narrower sound theorem only after assuming a *full doubling orbit* lies inside the central range.  That is strictly stronger than the manuscript's scale-spanning min/max condition and covers only the stated unit/order criterion; it neither proves the even-(g) projection nor constructs the graph spectrum.  A faithful Lean repair must represent the residue-specific (T_r), exact lift predicate, finite end cases, and full-phase routing, then connect `Realized` to the selected graph.  `selectedBarrierOverlapSerialSystem` and its obstruction producer remain absent independently of this arithmetic repair.

## 7. Regression audit

The audit used the live node dossier and inspected the following searches:

```text
rg -n 'lem:system-increment-arithmetic|system-increment|serial-system-sumset|scale-spanning serial|odd part|periodic response class' to_formalize/erdos_64_proof.tex hypostructure/Hypostructure/Graph proofs/hypostructure_erdos_64_eg/HypostructureErdos64EG Assembly_node_audit.md web/data/eg_node_audit.json
rg -n 'lem:pair-system-increment-arithmetic|lem:cold-increment-arithmetic' to_formalize/erdos_64_proof.tex audits/erdos-64-red-team
rg -n 'selectedBarrierOverlapSerialSystem|BlockedScaleAdditivityStatement|blockedBarrierOverlap|blockedScaleAdditive|barrier-failure-overlap' hypostructure/Hypostructure/Graph proofs/hypostructure_erdos_64_eg/HypostructureErdos64EG Assembly_node_audit.md web/data/eg_node_audit.json
python3 .agents/skills/red-team-eg-node/scripts/check_modular_hit.py /tmp/node172-even-spec.json
python3 .agents/skills/red-team-eg-node/scripts/check_modular_hit.py /tmp/node172-range-spec.json
```

The sources inspected sentence by sentence were:

- `def:blocked-class`, `def:barrier-overlap-system`, and `lem:barrier-failure-overlap`, including the fixed conditional-fibre data and connectedness proof;
- `def:serial-window-system` and the complete `lem:window-system-realizability` proof, including its robust scale-spanning sentence and actual-simple-cycle clause;
- the statement and proof of `lem:serial-system-sumset`, including the residue-dependent (T_r) and bounded end ranges;
- every sentence of `lem:system-increment-arithmetic` and its use by `lem:scale-additivity`;
- the analogous `lem:cold-increment-arithmetic` and the “word for word” `lem:pair-system-increment-arithmetic` at node [180];
- the Part-X and Part-XII nodes, edges, captions, overview rows 53--54, detailed dependency rows, and downstream uses of the three arithmetic lemmas;
- `Graph/SerialSystemArithmetic.lean`'s `Spectrum`, `ScaleSpanning`, `realized_of_congruent`, `exists_pow_realized`, serial `System`, and progression construction;
- the selected [170]--[172] branch in `Assembly.lean`, the barrier/additivity vocabulary and rows, and the node-[172] entries in `Assembly_node_audit.md` and `web/data/eg_node_audit.json`.
- review-postmortem entry E12.  That entry correctly rejects a range objection that simply drops scale-spanning and the central interval.  The present `g=48` test keeps both hypotheses and separates the still-missing full-modulus compatibility from the raw odd-part hit.

No manuscript lemma was found that upgrades min/max scale-spanning to a full doubling orbit inside every central range.  No source supplies the omitted (2^a\mid L+r) restriction, the normalized odd-part residue set, or an exact check of (t\in[C_{\rm sys},T_r-C_{\rm sys}]).  The only source with an explicit central-range congruence theorem is Lean's `Spectrum.realized_of_congruent`; its caller assumes the stronger full-orbit `ScaleSpanning` predicate rather than proving it from the manuscript definition.  No graph-level construction instantiates that spectrum at [172], and no live declaration named `selectedBarrierOverlapSerialSystem` was found.

## 8. Residual uncertainty

No actual graph satisfying the complete accumulated node-[172] residual was constructed, so this report does not claim a valid local graph counterexample or global theorem failure.  It remains possible that additional, unstated geometry of a true minimal barrier overlap forces the compatible residue and central-range lift that arbitrary serial systems lack; neither `lem:window-system-realizability` nor `lem:serial-system-sumset` states such a property.  The proposed full-phase repeat proof also requires the repair to specify the finite cut-state and to verify that deleting the intervening segment preserves minimum degree and all declared response coordinates; if that construction fails, the no-exact-hit residual needs an additional nonterminal routing branch rather than G3.

The independent upstream implementation gaps remain: Lean's [170] no-key does not carry the manuscript's obstruction witness, and the graph-to-`Spectrum` producer for [172] is absent.  The arithmetic core in Lean is sound under its stronger full-orbit hypothesis, but equivalence of that hypothesis with the manuscript's scale-spanning condition is false in general.  This audit did not re-prove the finite Frobenius filling in `lem:serial-system-sumset`, the uncrossing alternatives, or the already declared G2/G3/route-8 closure theorems.  No manuscript, diagram, Lean, implementation-audit, or coverage-ledger source was changed.
