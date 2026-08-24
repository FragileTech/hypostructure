<!-- red-team-audit
{
  "schema_version": 1,
  "proof": "erdos-gyarfas",
  "node": 180,
  "node_label": "pair increment arithmetic closes: power-of-two hit, or periodic response class routed to a sparse exit or Type B (\\cref{lem:pair-system-increment-arithmetic})",
  "panel": "fig:proof-diagram-part-x",
  "contract_sha256": "97d693581c604425fb7ecf6e0c84ba5a2b30683c65be2c1d2156827526fd876b",
  "manuscript_sha256": "106a8205a1718fbf90e1686a107b2143b9edca574e2b0c11415e7f44aee2c0f9",
  "graph_sha256": "dc67fae178f947a9607c167e383d85919633341bdd423e4c4a45e4c317b3a765",
  "lean_audit_sha256": "50324ef5594d635a52d83aeb297f2ca3f3d30ef58de4ce3602816c7e78365b12",
  "verdict": "MISSING RANGE OR DIVISIBILITY CHECK",
  "audited_at": "2026-08-24T21:52:51Z"
}
-->

# Red-team audit: node [180]

## 1. Executive verdict

Verdict: **MISSING RANGE OR DIVISIBILITY CHECK**

Node [180] promotes an intersection of the doubling orbit modulo the odd part of (g) with the projected realizable residues to an actual power of two in a finite progression (L+r+tg).  Two independent checks are missing.  If (g=2^au), the selected (r) must satisfy (2^a\mid L+r), and the normalized congruence is (2^{k-a}\equiv(L+r)/2^a\pmod u); a raw hit modulo (u) does not lift modulo (g).  Even after a full-modulus congruence, the integer (t=(2^k-L-r)/g) must lie in the particular central range (C_{\rm sys}\le t\le T_r-C_{\rm sys}).  Explicit scale-spanning spectra with thirteen consecutive offsets fail each implication.  The no-hit periodic branch does not catch them because the statement classifies them as odd-part hits.  The kernel-checked arithmetic helper avoids the error only by assuming an entire full doubling orbit already lies in the central range; no node-[179] producer establishes that stronger hypothesis.

## 2. Exact node contract

### Incoming residual

Node [180] has one immediate edge, `[179] --> [180]`, but the route entering [178] and then [179] is a tagged union:

1. **Free-pair count failure:** the selected graph is on the strict non-near-cubic surplus branch, the canonical pair split chose the blocker-free family, and the entropy count at [131] failed on the current conditional fibre.
2. **Blocked-fibre free-side failure:** the selected graph is on the same strict branch, has the canonical blocker and capacity-token ledgers through [136], and the entropy count on the free side of the coupled test [137] failed.

Both routes retain the same selected finite simple lexicographically minimal counterexample (G), with (delta(G)\ge3), no power-of-two cycle, the context/replacement/uncompressibility facts, and the node-[125] predicate that every named sparse surplus exit is absent.  Both routes also retain an actual pair family (Pi), its response coordinates (r_\pi), and the fixed external edges and previously exposed coordinates of the current conditional fibre.  Route-specific blocker and token data must not be imported onto the free-pair route.

At [178], the selected count-failure branch is claimed to supply a minimal nonempty pair overlap obstruction (mathcal U) with connected overlap support.  At [179], after alternatives (i)--(iv) of `lem:pair-system-realizability` are removed, the retained object is a scale-spanning serial demand system:

- ordered interfaces (x_0,\ldots,x_s) on the shared spine route;
- at each cell, a nonempty family of mutually internally disjoint corridor pieces;
- disjoint interiors between cells;
- two closing port-return pieces meeting the system only at (x_0,x_s);
- every nonzero system increment at most
  [
  D_{\rm sp}=2M_{\rm cold}+2\ell_{\rm ret};
  ]
- every choice of one piece at every cell closes an actual simple cycle through the two selected demands; and
- the manuscript's scale-spanning predicate: after deleting any bounded number of cells at the two ends, the shortest and longest realizable cycles remain on opposite sides of a tested power (2^j).

Node [180] is therefore an arithmetic and routing claim about this literal graph-realized serial system, not about an arbitrary modular orbit.

### Accumulated facts

The common facts available at [180] are:

- `[2]`: an actual finite simple graph (G) with minimum degree at least three and no (C_{2^k}).
- `[4]`, `[8]`, `[11]`--`[14]`: lexicographic minimality, no proper internal three-core, boundaried response profiles, context universality, replacement, and hereditary uncompressibility.
- `[19]`--`[20]`: the strict surplus-pair accounting branch.
- `[125]`: the graph survives all five named sparse surplus exits: direct target, target defect, proper target-complete compression, proper/whole-graph dependence, and the open-port arithmetic exit.
- `[126]`--`[129]`: the sparse envelope, full active demand family, canonical port returns and triangular responses, and the common baseline demand.
- `[130]` and one of the two tagged count-failure histories described above.
- `[178]`: the claimed minimal connected pair overlap obstruction on that same conditional fibre.
- `[179]`: the claimed graph-realized scale-spanning serial demand system, after uncrossing, with bounded increments and simple-cycle realization for every counted choice.

Applying `lem:serial-system-sumset` with the pair constants is intended to add the following arithmetic data.  Let (d_1,\ldots,d_q\in\{1,\ldots,D_{\rm sp}\}) be the nonzero increments with multiplicity; call an increment frequent above the fixed threshold, and let (g>0) be the gcd of the frequent increments.  Let (mathcal R\subseteq\mathbb Z/g\mathbb Z) be the realizable residues obtained from the rare increments and the port-return offsets.  For a constant (C_{\rm sys}), the actual cycle spectrum contains

\[
L+r+tg
\quad
(r\in\mathcal R,
\ C_{\rm sys}\le t\le T_r-C_{\rm sys}).
\tag{1}
\]

Every number asserted by (1) is an actual simple-cycle length.  The quantifier over (t) is finite and depends on (r).  Neither [179] nor the sumset lemma says that every integer in the numerical interval from the shortest to the longest cycle is realized.

No accumulated fact supplies either of the following stronger properties:

- for (g=2^au), every projected residue hit modulo (u) has the necessary divisibility (2^a\mid L+r); or
- the finite exponent window of the tested scale contains a full doubling orbit modulo (g) or (u), with each congruent power lying in the appropriate interval for (T_r).

### Current predicate and exact claim

Write

\[
g=2^a u,\qquad u\text{ odd}.
\]

The exact direct-hit condition for the spectrum (1) is not merely an intersection after projection modulo (u).  It is the existence of (r,k,t) such that

\[
\begin{gathered}
r\in\mathcal R,qquad k\ge a,qquad 2^a\mid L+r,\\
2^{k-a}\equiv\frac{L+r}{2^a}\pmod u,\\
t=\frac{2^k-L-r}{g}\in\mathbb Z,qquad
C_{\rm sys}\le t\le T_r-C_{\rm sys}.
\end{gathered}
\tag{2}
\]

The first two lines of (2) are equivalent to the full congruence

\[
2^k\equiv L+r\pmod g.
\]

The last line is what places the resulting power in the finite central spectrum.  The exponents (k<a) are a finite transient and must be checked directly.

The manuscript instead claims:

\[
\text{doubling orbit modulo the odd part of }g\text{ meets }\mathcal R
\quad\Longrightarrow\quad
\text{the central spectrum contains a power of two}.
\tag{3}
\]

Here (mathcal R) was defined modulo (g), so “meets” modulo (u) can only mean that its image in (mathbb Z/umathbb Z) meets the orbit.  This loses the (2^a)-divisibility class.  The proof then silently replaces (3) with a full congruence modulo (g), and silently asserts that scale-spanning puts its quotient in the central range.  Neither replacement follows.

The odd sufficient criterion

\[
\operatorname{ord}_g(2)>g-|\mathcal R|
\]

does prove an orbit intersection in (mathbb Z/gmathbb Z) when (g) is odd.  It does not prove that the hit exponent lies in a finite coefficient range.  In the even case, the pigeonhole set must be the normalized compatible set

\[
\widetilde{mathcal R}_a
=
\left\{
\frac{L+r}{2^a}\bmod u:
r\in\mathcal R, 2^a\mid L+r
\right\},
\]

not the raw image of all of (mathcal R), and the relevant bound is (u-|\widetilde{mathcal R}_a|).

The current Lean module `SerialSystemArithmetic.lean` proves a correct but stronger arithmetic implication.  Its `Spectrum.ScaleSpanning` requires a start exponent divisible by the full orbit order and requires **every power in one complete orbit** to lie between the central lower and upper bounds.  `Spectrum.exists_pow_realized` then uses a full-modulus congruence and calls `realized_of_congruent`, which verifies the coefficient range.  This file kernel-checks, but no declaration constructs such a `Spectrum` from the pair system, proves this stronger `ScaleSpanning`, or identifies `Realized` with an actual cycle predicate.  The manuscript's scale-spanning definition is weaker than the Lean hypothesis.

### Outgoing contracts

Node [180] is drawn as terminal and has no graph edge leaving it.  Its proof nevertheless has three semantic outcomes:

1. an exact power-of-two length in (1), contradicting node [2];
2. a periodic response class whose visible quotient is sparse exit (b), or whose invisible proper-support quotient is sparse exit (c), both refuted by node [125]; or
3. a periodic response class reaching a same-token routed bottleneck, sent by `lem:same-token-bottleneck-routing` to a sparse exit or Type B fan data.

The first outcome is terminal only after (2) is checked and the corresponding realized length is tied to an actual simple cycle.  The second must retain the two actual equal-phase response states, their common boundaried support, the quotient, and proper-support status.  The third is routing, not contradiction; a Type B outcome must enter the same typed Type B continuation used from node [144].  The live graph has no edge from [180] to that continuation.  This missing continuation is subordinate to the arithmetic failure: the explicit candidates below are wrongly consumed by the direct-hit arm before any periodic routing is attempted.

## 3. Sentence audit

| Sentence | Exact assertion | Facts used | Hidden obligation | Adversarial test | Status |
|---|---|---|---|---|---|
| S1 | On the strict branch, a scale-spanning serial demand system is impossible. | [125], [179], the rest of the lemma. | Every arithmetic alternative must either realize an actual target or meet a typed routed destination. | Use an even gcd with a false projected hit. | FAILED AS CONCLUDED |
| S2 | The pair system has a frequent-increment gcd (g) and residue set (mathcal R) with central spectrum (1). | `lem:serial-system-sumset` transplanted from windows to pair port returns. | The port-return offsets and their conductor bounds must satisfy the transplanted hypotheses, including all nonempty (t)-ranges. | Use one frequent increment and thirteen offsets. | SUPPORTED ONLY IF THE TRANSPLANTED SUMSET LEMMA IS SUPPLIED |
| S3 | An odd-part orbit hit in (mathcal R) puts a power in the central spectrum. | S2 and `lem:cold-increment-arithmetic`. | Need (2^a\mid L+r), normalized congruence modulo (u), an integer lift, and the (r)-specific central range. | (g=24), (L\equiv18\pmod{24}), offsets (0,\ldots,12). | FAILED |
| S4 | Otherwise the interface residue is a periodic response class. | Negation of S3. | The two arms must be exact complements under the **full** hit predicate, not raw odd projection; the 2-adic phase must be retained. | Raw odd hit with no compatible normalized hit. | NONEXHAUSTIVE UNDER THE CORRECT HIT PREDICATE |
| S5 | A compatible context seeing two equal-residue states gives a target-defective quotient. | Context universality [12]. | Need two actual declared states with the same complete phase and a common boundaried support. | Compare equality modulo (u) with different residues modulo (2^a). | SUPPORTED ONLY AFTER FULL PHASE IS RETAINED |
| S6 | No seeing context gives a target-complete quotient of a proper support. | [12]--[14]. | Must prove the support is proper and construct an actual smaller representative; whole-graph dependence must be routed separately. | Let the minimal phase support equal (G). | AMBIGUOUS |
| S7 | A routed bottleneck sends the periodic class to Type B or a sparse exit. | `lem:same-token-bottleneck-routing`. | The response class must carry the same connector configuration and the graph must include the corresponding continuation edge. | Follow the Type B disjunct in the Part-X graph. | ROUTING ONLY; EDGE ABSENT |
| S8 | For odd (g), (operatorname{ord}_g(2)>g-|\mathcal R|) forces a hit. | Pigeonhole principle in (mathbb Z/gmathbb Z). | “Hit” is only a congruence; its exponent still needs the finite coefficient range. | Put the only in-range dyadic power in a missing residue. | SUPPORTED AS A MODULAR HIT, NOT AS A CENTRAL HIT |
| S9 | For (g=2^au), the same criterion applies to (u) after (k<a). | Odd-part reduction. | Restrict to (2^a)-compatible (r), divide (L+r) before reducing, and use (|\widetilde{\mathcal R}_a|). | (g=24=8\cdot3), only compatible offset (r=6), normalized target (0\pmod3). | FAILED |
| S10 | Every length of each displayed coset is realized away from a bounded end segment. | `lem:serial-system-sumset`, [179] simplicity. | “Every” is only for (C_{\rm sys}\le t\le T_r-C_{\rm sys}). | Exact congruence at (t<0) or (t>T_r-C_{\rm sys}). | SUPPORTED WITH THE FINITE RANGE |
| S11 | A congruence (2^k\equiv L+r\pmod g) is a power-of-two cycle. | S10 and target avoidance. | Compute (t) and check its central range before invoking realization. | (g=17), exact congruent powers only far below or above the active interval. | FAILED |
| S12 | Scale-spanning puts the congruent quotient in the central range once bounded scales enter the cold table. | Manuscript scale-spanning and bounded-end routing. | One straddled dyadic scale does not place a full residue orbit in range; the exceptional distance need not be bounded uniformly. | Place (2^{100}) in a four-integer gap between consecutive realized blocks. | FAILED |
| S13 | Under avoidance, route-length residue modulo the odd part is well-defined through every corridor. | All increments are multiples of (g). | Different choices differ by multiples of (g), which is sufficient, but the selected response state should preserve the full post-transient phase. | Two states equal modulo (u) but unequal modulo (2^a). | AMBIGUOUS/WEAKENED |
| S14 | Sparse exits are refuted and the Type B outcome is the continuation of [144]. | Node [125], `lem:same-token-bottleneck-routing`. | Type B must be a live outgoing handoff with its complete carrier data. | Inspect `immediate_outgoing` for node [180]. | FAILED AS A TERMINAL GRAPH CONTRACT |

## 4. Counterexample attempts

### Smallest-parameter test

- **Explicit data:** Take (g=16), whose odd part is (u=1).  Use a frequent increment (16), a base (L\equiv1\pmod{16}) larger than every transient power, and offsets (r=0,1,\ldots,12).  With sufficiently many frequent cells, the spectrum contains (L+r+16t) through a scale-spanning central range.
- **Hypotheses satisfied:** The raw orbit modulo the odd part (mathbb Z/1mathbb Z) trivially meets the projected residue set.  There are thirteen consecutive offsets, and (16\le D_{\rm sp}).  Choosing at least the required frequency threshold gives the sumset progression and enough width to straddle dyadic scales.
- **Accumulated facts violated:** No graph-realized pair overlap obstruction was constructed.  The data are an abstract serial spectrum, not yet the selected graph (G) and pair-response system of [178]--[179].
- **Applicability:** **NON-APPLICABLE TO THE NODE** as a complete graph residual, first missing node [2]'s actual graph object.  It is applicable to the exact arithmetic implication: every sufficiently large power is (0\pmod{16}), while every displayed length has residue (1,\ldots,13\pmod{16}).  Thus the projected odd-part hit is automatic and no power is realized.

### Parity or 2-adic test

- **Explicit data:** Take (g=24=2^3\cdot3), (L=1170\equiv18\pmod{24}), (mathcal R=\{0,1,\ldots,12\}), (C_{\rm sys}=0), and (0\le t\le1152).  The displayed lengths have full residues (18,\ldots,23,0,\ldots,6\pmod{24}), whereas powers (2^k) for (k\ge3) have residues (8,16\pmod{24}).  Early powers are below (L).
- **Hypotheses satisfied:** The interval is the spectrum of 1152 binary cells with one length increment (24), base paths of total length 1152, closing length 18, and offsets (0,\ldots,12).  Its shortest and longest displayed lengths straddle several dyadic scales.  Modulo (u=3), the raw orbit ({1,2}) meets many projected offsets.
- **Accumulated facts violated:** The numerical 1152 is the frequency threshold for a model bound (D=24), not the repository's larger fixed (D_{\rm sp}); replace it by (2D_{\rm sp}^2) and choose the closing length so (L\equiv18\pmod{24}) to obtain the same abstract construction.  No actual minimum-degree-three pair-overlap graph was constructed.
- **Applicability:** **NON-APPLICABLE TO THE NODE** as a full graph residual, first missing node [2].  The bundled modular checker is decisive for the node's arithmetic: it reports many `raw_odd_part_hits`, only (r=6) as 2-adically compatible, normalized target (0\pmod3), no exact full-modulus lift, and `has_valid_direct_hit: false`.  This is the strongest divisibility candidate.

### Boundary or range test

- **Explicit data:** Let (g=17), (mathcal R=\{0,\ldots,12\}), (0\le t\le1152), and
  [
  L=2^{100}-16-17\cdot576
   =1267650600228229401496703195568.
  ]
  Then (L\equiv0\pmod{17}), while (2^{100}\equiv16\pmod{17}).  The power (2^{100}) lies strictly between the block with (t=576), which ends at (L+12+17\cdot576=2^{100}-4), and the block with (t=577), which begins at (2^{100}+1).
- **Hypotheses satisfied:** The spectrum has thirteen consecutive offsets, 1153 consecutive (g)-steps for each offset, and the tested scale lies deep in its central range rather than near either end.  It is robust under deletion of any fixed bounded number of end cells.  The odd doubling orbit modulo 17 meets (mathcal R) at many other exponents.
- **Accumulated facts violated:** As above, this is a serial arithmetic model and not an actual pair obstruction inside the selected graph.  The frequency can be enlarged to the repository threshold without changing the gap at (2^{100}).
- **Applicability:** **NON-APPLICABLE TO THE NODE** as a complete graph residual, first missing node [2].  The checker finds exact congruence hits at exponents (95\)–(99) below the interval and (103\)–(105) above it, but no valid direct hit; the in-scale exponent (100) has the missing residue 16.  This refutes the assertion that scale spanning alone places a congruent orbit hit in the central coefficient range.

### Graph-realizability test

- **Explicit data:** Build a serial theta chain with interfaces (x_0,\ldots,x_M).  Between (x_{i-1}) and (x_i), include a direct edge and an internally disjoint path of length 25; give different cells disjoint interiors.  Add a closing path from (x_M) to (x_0), and a finite closing-offset gadget providing the thirteen lengths (c,c+1,\ldots,c+12).  Choosing the long path in exactly (t) cells realizes global lengths (L+r+24t).
- **Hypotheses satisfied:** This is an actual finite simple serial graph gadget with ordered interfaces, internally disjoint cell pieces, bounded increment 24, and graph-realized cycles for all advertised choices.  Its modular spectrum can be shifted to the (g=24) candidate.
- **Accumulated facts violated:** Internal vertices of the long paths and closing paths have degree two.  The gadget was also not shown to avoid every other power-of-two cycle, to arise from a minimal pair overlap obstruction, or to preserve the declared pair-response profiles.
- **Applicability:** **NON-APPLICABLE TO THE NODE**.  The earliest exclusion is node [2], which requires (delta(G)\ge3) (and target avoidance).  The construction shows that serial simplicity and actual cycle realization do not repair the lost 2-adic phase.

### Branch-routing test

- **Explicit data:** On the (g=24) spectrum, take the raw odd-part hit (2^4\equiv1\pmod3) against an offset with the same raw projection.  Do not add the absent divisibility (8\mid L+r).  The manuscript's first arm calls this a central power hit; the stated second arm is only “orbit avoids (mathcal R),” so it does not receive the candidate.
- **Hypotheses satisfied:** This is the literal case distinction written at [180]: the image of (mathcal R) modulo the odd part is met, and the serial spectrum is scale-spanning.  The candidate also respects node [125]'s absence of an already realized target because it contains no power.
- **Accumulated facts violated:** No actual graph-level response states were supplied, so the periodic quotient itself has not been constructed.  There is, however, no arithmetic accumulated fact excluding this phase pattern.
- **Applicability:** Applicable to the routing contract.  Under the correct direct-hit test (2), the candidate is a no-hit phase and must go to the periodic-response analysis or a finite exceptional table.  Under the printed split it is incorrectly consumed by the direct arm, leaving the genuine no-direct-hit residual unassigned.  A Type B result of the repaired periodic analysis must also receive an explicit outgoing continuation rather than terminate at [180].

## 5. Strongest valid counterexample

No actual minimal target-free graph carrying the complete pair-count failure, minimal overlap obstruction, and [179] serial system was constructed.  The strongest candidate is the parameterized (g=24) serial spectrum.  Let

\[
M\ge2D_{\rm sp}^2,
\qquad
c\in\{0,\ldots,23\}
\text{ with }M+c\equiv18\pmod{24},
\qquad
L=M+c.
\]

Take (M) binary cells whose alternative length is 24 longer than the base and offsets (0,\ldots,12).  Then the increment 24 is frequent at the actual repository threshold, the central spectrum contains every

\[
L+r+24t,qquad0\le r\le12,quad0\le t\le M,
\]

and its multiplicative width is sufficient to straddle dyadic scales even after any fixed bounded end deletion.  Nevertheless all displayed residues lie in

\[
\{18,19,20,21,22,23,0,1,2,3,4,5,6\}\pmod{24},
\]

while all powers after the transient lie in ({8,16\}\pmod{24}).  The odd-part projection modulo three hits immediately.  Thus this object satisfies the arithmetic and finite-sumset premises stated at [180] and falsifies its direct-hit implication.

What remains unproved is graph realization under every accumulated condition.  The candidate therefore witnesses a local divisibility error in the terminal arithmetic, not a counterexample to the theorem.

## 6. Local repair

### Corrected statement

Replace the direct-hit alternative of `lem:pair-system-increment-arithmetic` by:

> Let (g=2^au), with (u) odd, and for each (r\in\mathcal R) retain its exact central range (C_{\rm sys}\le t\le T_r-C_{\rm sys}).  Define
>
> [
> mathcal R_a={r\in\mathcal R:2^a\mid L+r},
> qquad
> \widetilde{mathcal R}_a
> =left\{(L+r)/2^a\bmod u:r\in\mathcal R_a\right\}.
> ]
>
> The direct target arm occurs exactly when there are (r\in\mathcal R_a), (k\ge a), and
>
> [
> t=\frac{2^k-L-r}{g}
> ]
>
> such that (2^{k-a}\equiv(L+r)/2^a\pmod u) and (C_{\rm sys}\le t\le T_r-C_{\rm sys}).  The finitely many exponents (k<a) are checked separately.  An order criterion modulo (u) may be used only with (|\widetilde{mathcal R}_a|), and it gives a central hit only if the active exponent window contains a complete orbit (or if every candidate exponent is checked directly against its (r)-specific range).
>
> If no exact direct hit exists, retain the full post-transient phase and route it as a periodic response class: visible context to sparse exit (b), target-complete proper support to exit (c), proper/whole-graph dependence to exit (d), a same-token first separator to the typed Type B continuation, and genuinely bounded exponent/end ranges to the finite cold table.

### Complete local proof

Assume first that (k\ge a).  If

\[
2^k=L+r+tg,
\]

then (2^a\mid2^k) and (2^a\mid tg), so (2^a\mid L+r).  Divide the equality by (2^a):

\[
2^{k-a}=\frac{L+r}{2^a}+tu.
\]

Hence

\[
2^{k-a}\equiv\frac{L+r}{2^a}\pmod u.
\]

Conversely, if (2^a\mid L+r) and this normalized congruence holds, then

\[
2^{k-a}-\frac{L+r}{2^a}=tu
\]

for some integer (t).  Multiplying by (2^a) gives

\[
2^k=L+r+tg.
\]

This is only an algebraic lift.  It belongs to the realized spectrum (1) exactly when its computed (t) satisfies the corresponding finite inequalities.  At that point [179] turns the length into an actual simple cycle, and node [2] closes the branch.  For (k<a), no division by (2^a) is valid; enumerate those finitely many powers directly against (1).

For an orbit-count shortcut, work in (mathbb Z/umathbb Z) with (\widetilde{mathcal R}_a).  The orbit of two has (operatorname{ord}_u(2)) distinct elements.  If

\[
\operatorname{ord}_u(2)>u-|\widetilde{mathcal R}_a|,
\]

it meets that normalized set by pigeonhole.  To conclude a realized power, choose a complete orbit of exponents whose powers all lie in the common central numerical range, or inspect each hit exponent and its (T_r) individually.  This is precisely the extra hypothesis encoded by the formal `Spectrum.ScaleSpanning`; the manuscript's one-scale straddling does not imply it.

If no triple satisfies the direct test, record the complete phase rather than only its odd projection.  Differences of route choices are multiples of (g), so after the transient the pair consisting of the fixed (2^a)-class and the residue modulo (u) is transported through the interfaces.  A context distinguishing two actual equal-phase declared states gives a target-defective quotient by [12].  If every context agrees and their determination support is proper, construct the target-complete quotient and apply [13]--[14].  If the minimal support is whole-graph or delocalized, use sparse exit (d).  At a same-token first separator, retain the connector configuration required by `lem:same-token-bottleneck-routing` and follow its sparse-exit or Type B result.  This exhausts the no-direct-hit residual without treating a raw modular miss or hit as a contradiction.

### Counterexample disposition

For (g=24), compatibility requires (8\mid L+r).  With (L\equiv18\pmod{24}) and (0\le r\le12), only (r=6) is compatible; then

\[
\frac{L+r}{8}\equiv0\pmod3,
\]

which is not in the doubling orbit ({1,2}\pmod3).  The candidate therefore takes the corrected no-direct-hit arm and is passed to the periodic phase analysis.  It is no longer declared to contain a power.

For the (g=17) boundary candidate, the compatible congruences occur only at powers far outside the active central range; the in-range power has residue 16, absent from (mathcal R).  It also takes the no-direct-hit arm.  Its large central width prevents it from being called a bounded end exception merely because the nearest hit exponent lies elsewhere.

### Graph patch

Replace the terminal ellipse by the exact subdiamond

```text
[179] --> [180a: compute g=2^a u, R_a, normalized residues, and every T_r]

[180a] -- exists exact (r,k,t) satisfying divisibility and central range -->
          actual C_(2^k) contradiction
[180a] -- k<a or genuinely bounded end range --> finite cold table
[180a] -- no exact hit; context sees full phase --> sparse exit (b)
[180a] -- no exact hit; target-complete proper support --> sparse exit (c)
[180a] -- no exact hit; proper/whole-graph dependence --> sparse exit (d)
[180a] -- full phase reaches same-token bottleneck -->
          sparse exit or typed Type B continuation from [144]
```

Every edge must retain the same serial system, (L,g,mathcal R,C_{\rm sys},T_r), the actual interface phase states, and the graph-realization proof from [179].  The Type B edge must be explicit in the proof graph; [180] cannot remain terminal if that outcome is live.

### Downstream impact

Update the Part-X node [180] label and caption, detailed dependency row 54, source-ledger row for `lem:pair-system-increment-arithmetic`, and the wrapper `lem:pair-count-or-arithmetic`.  Node [179]'s definition of scale-spanning must either be strengthened to the full-orbit-in-central-range property used by the Lean arithmetic theorem or left unchanged with the exact per-exponent check added at [180].

The “word for word” source `lem:system-increment-arithmetic` at node [172] repeats both the odd-part and central-range inferences and requires the same correction.  `lem:cold-increment-arithmetic` also says that the criterion applies to the odd part after a bounded transient; its even-modulus use must retain (2^a\mid L+r), and its hit-realized conclusion must check the available copy count.  These are regression targets, not second verdicts in this report.

In Lean, the compiled `SerialSystem.Spectrum.exists_pow_realized` can support the repaired direct arm once a graph-level pair producer constructs the spectrum, proves its much stronger `ScaleSpanning`, and maps `Spectrum.Realized (2^k)` to `Graph.HasCycleWithLength`.  The periodic-response complement still needs a separate proposition and routing implementation.  No such pair-system producer or key currently exists; `selectedSparsePairSerialSystem` remains undefined.

## 7. Regression audit

The following uses and analogues were inspected:

- `to_formalize/erdos_64_proof.tex` lines 4854--5006: `def:pair-overlap-system`, `lem:pair-failure-overlap`, `lem:pair-system-realizability`, `lem:pair-system-increment-arithmetic`, and `lem:pair-count-or-arithmetic`.
- The Part-X diagram and caption at lines 1015--1071, detailed dependency row 54 at line 1232, and source-ledger row at line 1563.  The diagram makes [180] terminal despite the stated Type B outcome.
- `lem:serial-system-sumset` and `lem:system-increment-arithmetic` at lines 7889--7988.  The latter is the exact “word for word” analogue and repeats the missing range assertion.
- `lem:cold-increment-arithmetic` at lines 7233--7289.  Its even-(delta) odd-part sentence also omits the compatible-residue normalization.
- `def:named-surplus-exits` at lines 2549--2570 and `lem:same-token-bottleneck-routing` at lines 5334--5420, to verify the periodic response destinations and whole-graph dependence alternative.
- `hypostructure/Hypostructure/Graph/SerialSystemArithmetic.lean` in full.  Its `ScaleSpanning`, `realized_of_congruent`, and `exists_pow_realized` declarations use a full orbit and exact finite range.  `lake env lean Hypostructure/Graph/SerialSystemArithmetic.lean` succeeded with only deprecation warnings.
- `rg -n "selectedSparsePairSerialSystem|Spectrum.exists_pow_realized|pair-system-increment-arithmetic" hypostructure proofs Assembly_node_audit.md web/data/eg_node_audit.json` found only calls to the undefined assembly producer, the graph-free arithmetic helper, and the audit records.  No graph-to-`Spectrum` constructor or periodic-response producer was found.
- The modular checker was run on `/tmp/eg-node-180-modular.json` and `/tmp/eg-node-180-range.json`.  The former separated numerous raw odd-part hits from zero valid full hits; the latter found full congruence lifts only outside the finite coefficient range.
- Review-postmortem entry E12 was rechecked.  Unlike the withdrawn candidate recorded there, the present `g=24` construction retains a scale-spanning central spectrum after bounded end deletion; it fails because the odd-part projection does not satisfy the omitted `2^a` compatibility.

The fresh dossier reports no reverse item dependency beyond the named pair wrapper, but flags sparse-exit and Type B routing families without a directed edge.  No proof, manuscript, diagram, Lean, audit source, or coverage-ledger file was modified.

## 8. Residual uncertainty

No actual graph satisfying the entire minimal-counterexample, strict-surplus, pair-count-failure, minimal-overlap, and serial-realizability contract was found.  It remains possible that the concrete graph construction at [179] forces an additional 2-adic alignment or a complete orbit of powers inside every central spectrum.  Neither property is stated or proved, and the port-return offset set used in the pair transplant of `lem:serial-system-sumset` is not defined precisely enough to infer it.

The periodic-response proof also leaves two independent matters unverified: existence of two actual equal-full-phase interface states on a proper determination support, and a live Type B continuation from the terminal diagram node.  Finally, Lean verifies only the strengthened abstract arithmetic core; because no pair `Spectrum` is constructed and `selectedSparsePairSerialSystem` is undefined, there is no current kernel evidence that the manuscript's node-[180] hypotheses imply that core's assumptions.
