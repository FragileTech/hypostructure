<!-- red-team-audit
{
  "schema_version": 1,
  "proof": "erdos-gyarfas",
  "node": 177,
  "node_label": "decorated handoff fan data at the heavy centre \\(z\\):\\\\continue at Type B [65]",
  "panel": "fig:proof-diagram-part-v",
  "contract_sha256": "0073811fba066d92ebd38deaf7c10ea7596e698204fecda108dcaf5ce5798bdd",
  "manuscript_sha256": "106a8205a1718fbf90e1686a107b2143b9edca574e2b0c11415e7f44aee2c0f9",
  "graph_sha256": "dc67fae178f947a9607c167e383d85919633341bdd423e4c4a45e4c317b3a765",
  "lean_audit_sha256": "50324ef5594d635a52d83aeb297f2ca3f3d30ef58de4ce3602816c7e78365b12",
  "verdict": "WRONG ROUTING DESTINATION",
  "audited_at": "2026-08-24T21:46:09Z"
}
-->

# Red-team audit: node [177]

## 1. Executive verdict

Verdict: **WRONG ROUTING DESTINATION**

### Post-audit recheck — 2026-08-29

The aggregate noncandidate family, heavy-centre corridor witness, and same-ledger
call into the common Type-B continuation have now been implemented, and the old
seven projection errors are fixed. This resolves the earlier mechanical
failure, but not the semantic conversion identified by this report.
`AbsorbedGermFanEnvelopeWitness` still explicitly says that it does not produce
the counted connected remainder core of `DecoratedHandoff.Envelope`, and
`TypeBFanEntryStatement` admits it as a separate disjunct. No theorem converting
that cold datum to the manuscript's assigned Type-B support was found. Thus the
original **WRONG ROUTING DESTINATION** verdict remains applicable to manuscript
fidelity even though `SpineRows.lean` and `Assembly.lean` now compile. The
code-first correction ledger in `Assembly_node_audit.md` is the current status.

The selected corridor does provide a high-degree vertex (z), cubic neighbours, and two distinct simple corridor tails.  Those data are not the decorated handoff envelope required at Type B node [65].  In particular, the incoming residual does not identify a counted connected (P_{13})-free remainder core (Y), does not make (z) a surviving first separator of declared response coordinates through one completion port, and does not exclude the target-defect, compression, and support-dependence failures in clauses (iii)--(v) of the fan-safe relation.  The cited `lem:typeA-high-degree-handoff` assumes all of those facts; it cannot manufacture them from one cold return corridor.  The current Lean source confirms the type mismatch by defining a weaker cold-corridor witness, expressly saying that it is not a decorated envelope, and then adding that witness as a new disjunct to the Type B entry and its descendants.  That is a parallel formal lane, not a proof that node [177]'s actual residual satisfies node [65]'s manuscript contract.

## 2. Exact node contract

### Incoming residual

This audit conditions on an actual representative reaching node [177], so it does not rely on the separate possible empty-family issue at nodes [174]--[175].  The incoming object consists of:

- the same finite simple lexicographically minimal counterexample (G), with (delta(G)ge3) and no cycle of power-of-two length;
- the fixed maximal vertex-disjoint induced-(P_{13}) packing (mathcal P), its hot/cold partition, and the cold-corridor ledger on the absorbed-configuration route;
- an actual selected branch-excess half-edge (epsilon) of an ambient-cubic cold window, its simple return corridor, its first-failure germ, and its bounded connected support (J);
- the yes-predicate of node [175], namely an actual
  [
  zin J\cap V_{\ge4}(G);
  ]
- the retained node-[10] fact that (V_{\ge4}(G)) is independent.

For an arbitrary eligible (epsilon), the all-heavy arm used by the formal decision is the universal version of the same residual: its first-failure support contains some such (z).  Either reading gives a real corridor and a real high-degree witness once eligibility/nonemptiness is fixed.  Neither reading carries a Type A support or a Type B assigned support.

The immediate graph edge is

```text
[175] -- yes --> [177].
```

The only displayed continuation is

```text
[177] -- from [177] --> [65].
```

### Accumulated facts

The facts available to node [177] and relevant to this handoff are:

- `[2]`, `thm:main`: (G) has minimum degree at least three and avoids every accepted power-of-two cycle.
- `[4]`, `[8]`, `[11]`--`[14]`: minimality, absence of a proper internal three-core, the boundaried replacement language, context universality, replacement, and hereditary target-uncompressibility.  These are general tools; no particular Type A support or response-coordinate quotient is selected at [177].
- `[10]`, `lem:deletion-critical`: (V_{\ge4}(G)) is independent.  Thus a neighbour of (z) cannot also have degree at least four; together with (delta(G)ge3), every neighbour of (z) has degree exactly three.
- `[17]`, `[25]`--`[27]`: the maximal packing and its remainder (R); components of (R) are (P_{13})-free and have no internal three-core.  These facts do not say that either corridor tail terminates in one common component of (R), or that the germ support is a canonical counted remainder core.
- `[145]`--`[153]`: the selected cold-window stubs, return corridors, first-failure routing, and germ-extraction ledger.  These give a simple corridor and a bounded first-failure support, not a saturated Type A continuation family.
- `[173]`--`[175]`: the absorbed route and the branch predicate (J\cap V_{\ge4}(G)\ne\varnothing), with a chosen (z) on the node-[177] arm.

The following facts are not accumulated on this route:

- a Type A support (X) with its boundary response coordinates;
- a finite family of declared response coordinates using one completion port;
- the assertion that (z) is their first separator;
- the assertion that this separator is surviving after exits (3)--(6) have been removed;
- a connected counted remainder core (Y) to which the two arms have first-entry terminals;
- a set (H) of assigned decorations and nonempty assigned first-neighbour sets (K_h);
- the boundary-degree profile, terminal-coordinate record, and exact net-charge identity of a decorated envelope; or
- a proof of fan-safe clauses (ii)--(v) for the selected first neighbours.

Node [14]'s hereditary uncompressibility can refute a compression only after a particular proper boundaried support and target-complete identification have been constructed.  It does not itself select that support or show that the two directions of a corridor are response coordinates in one boundary-degree fibre.  Likewise, the componentwise properties of (R) do not select a common component meeting both corridor-tail terminals.

### Current predicate and exact claim

The part of node [177] that follows from the incoming residual is the heavy corridor-tail datum

\[
\begin{gathered}
z\in J,
\qquad d_G(z)\ge4,
\qquad \forall u\in N_G(z),\ d_G(u)=3,\\
\text{and the simple return corridor has two distinct incidences at }z
\text{ with a simple tail on each side.}
\end{gathered}
\]

Target avoidance also proves fan-safe clause (i) for the two first neighbours: an (a)--(b) return in (G-z) of length (2^j-2), together with (za) and (zb), would be a (2^j)-cycle.

The manuscript claims substantially more.  By `def:decorated-fan-envelope`, it must construct

\[
\mathfrak X=(Y,H),\qquad H\ni z,
\]

where (Y\subseteq R) is a connected (P_{13})-free counted remainder core, (K_z\subseteq N_G(z)) is nonempty, every (a\in K_z) has a simple arm ending at a declared terminal in (Y) and internally avoiding (Y\cup H\cup\{z\}), and (K_z) is a clique in the five-clause fan-safe graph.  The envelope must also retain the response coordinates, terminal coordinates, boundary-degree profile, empty-three-core and uncompressibility data, and its exact net-charge accounting.

The invocation of `lem:typeA-high-degree-handoff` does not fill this gap.  That lemma begins with the hypotheses

> (X) is a Type A support and (z) is a surviving first separator for a finite family of declared response coordinates through one completion port.

Its proof takes (Y=X), and it proves fan-safe clauses (ii)--(v) because exits (3)--(6) have already been removed on the saturated Type A exit-(7) branch.  Node [177] has neither its hypotheses nor an equivalent cold-corridor lemma.  Two directions along one path are not, just by being path directions, two declared response coordinates with a common completion port and a surviving first separator.

The current Lean vocabulary makes the mismatch explicit.  `AbsorbedGermFanEnvelopeWitness` records a germ, a heavy centre, cubic neighbours, two simple tails ending in the union of the selected cubic cold windows, and a reduced `FanSafe` assertion.  Its own comment says it “does **not** misdeclare that union to be the (P_{13})-free remainder core” of a `DecoratedHandoff.Envelope`.  The registered `handoffAbsorbing` predicate tests only window-label collision, while the manuscript's fan-safe clauses also require non-defect, non-compression, and non-delocalization.  `TypeBFanEntryStatement` is then defined as

```text
ordinary assigned Type B fan support OR absorbed cold-germ witness.
```

This changes the destination type.  It does not derive the left disjunct or a genuine `DecoratedHandoff.Envelope` from the right disjunct.

There is also a current formal build failure.  Running

```text
lake env lean Hypostructure/Graph/Strategy/ColdCorridorRows.lean
```

from the `hypostructure/` package failed at lines 516 and 685 because the changed existential state predicates were still introduced as old direct binders; it also reported the removed `Graph.ColdCorridor.candidateGerms` identifier.  Separately, `SpineRows.lean` still applies `AbsorbedGermFanEnvelopeWitness` with its older parameter list.  This build failure is a formal-maintenance observation, not the mathematical reason for the verdict.

### Outgoing contracts

Node [65] is labelled “Type B assigned support: high-degree fan centers and decorated handoff data.”  The ordinary entry is a connected assigned Type B support (X), with counted core (Y_X), assigned high-degree centres (H_X), and the exact ledger identities

\[
\defp(X)=\defp(Y_X),\qquad |V(X)|=|V(Y_X)|,
\qquad \sigma(X)=\sum_{h\in H_X}(d_G(h)-3).
\]

For a decorated entry, the same role is played by the actual decorated envelope and the grouped-envelope transfer identity.  Nodes [67]--[85] then consume, among other things, the assigned centres, fan-certificate labels, cubic-closed neighbour status inside the assigned envelope, local charge contributions, B1/B2 carriers, and disjointness relative to that counted support.  `lem:typeB-exclusion` explicitly fixes (h\in H_X), uses the five-condition clique in (Fsafe_h), and evaluates neighbours by their internal degree in the assigned envelope.

The node-[177] source contract supplies none of (Y_X), (H_X) as an assigned set, the envelope-relative internal degrees, the ledger identity, or the B1/B2 carrier universe.  A custom formal disjunct that replaces these objects with `germ.support` and ({z}) does not validate the manuscript edge; it creates parallel versions of downstream statements.  Therefore the actual [175]-yes residual is not yet typed for [65].

## 3. Sentence audit

| Sentence | Exact assertion | Facts used | Hidden obligation | Adversarial test | Status |
|---|---|---|---|---|---|
| S1 | Fix a selected half-edge (epsilon), its return corridor, and first-failure support (J). | Cold-window/corridor ledger [145]--[153], selected node-[177] representative. | Eligibility and a literal representative must be retained, rather than a vacuous universal statement. | Condition explicitly on one eligible (epsilon). | SUPPORTED ON THE NONEMPTY RESIDUAL |
| S2 | The split (J\cap V_{\ge4}=\varnothing) versus (J\cap V_{\ge4}\ne\varnothing) is exhaustive. | Finite membership and classical logic. | Both arms must retain the same (epsilon), germ, and (J). | Test a support with exactly one high vertex. | SUPPORTED |
| S3 | If (z\in J\cap V_{\ge4}), every neighbour of (z) is cubic. | (delta(G)\ge3), independence of (V_{\ge4}) at [10]. | “Degree at least four” must use the same ambient graph degree. | Give (z) degree four and four degree-three neighbours. | SUPPORTED |
| S4 | The corridor enters and leaves (z) through distinct incidences. | Simplicity of the return corridor and its two boundary stubs. | Endpoint/foot cases must use the window stub on one side; the two boundary stubs must be distinct. | Put (z) at the first inside vertex. | SUPPORTED, WITH THE BOUNDARY-STUB READING |
| S5 | The two corridor segments are separated connector tails “in the sense of” `lem:typeA-high-degree-handoff`. | S4 and the cited lemma. | Need a Type A support, declared response coordinates through one completion port, first-separator status, and survival of exits (3)--(6). | Retain only one simple corridor through (z). | FAILED |
| S6 | The two tails form `def:decorated-fan-envelope` data. | S3--S5. | Need (Y\subseteq R), (H), (K_z), terminals in (Y), avoidance, all five fan-safe clauses, response/profile data, and charge accounting. | Use tails whose recorded endpoints are packed-window vertices, as in the current Lean witness. | FAILED |
| S7 | The half-edge (epsilon) enters Type B at [65]. | S6 and `lem:decorated-fan-admissibility`. | The destination needs an assigned support or an admissible decorated envelope, not a heavy centre plus path. | Compare node [65]'s (Y_X,H_X) ledger with the fields retained at [177]. | FAILED |
| S8 | Nodes [67]--[85] close the routed object. | Type B normal form, certificate, B1/B2, fan-mass, and exclusion results. | Every consumer must operate on the same assigned core and centre set, with envelope-relative internal degrees. | Follow the cold-germ disjunct through the Lean-specific alternate statements. | FAILED AS A MANUSCRIPT INVOCATION |
| S9 | A first-failure support is a bounded connected piece with two active interfaces. | Cold first-failure construction. | “Active interfaces” must be upgraded to declared response coordinates with a shared port before the Type A separator theorem applies. | Treat the two path ends merely as graph boundary incidences. | SUPPORTED ONLY AS COLD-GERM GEOMETRY |
| S10 | The two directions along the corridor are the decorated handoff configuration of `lem:typeA-high-degree-handoff`. | S9 and high degree. | The cited theorem's surviving-separator hypotheses cannot be inferred from path order. | Allow a target-defective quotient of the two would-be response coordinates. | FAILED |
| S11 | The case-(ii) charge transfers to the Type B ledger. | A valid assigned envelope and the Type B transfer identity. | Must prove the exact support/centre ledger and no-double-count assignment. | Ask where (defp(Y_X)), (|Y_X|), and the centre token (d(z)-3) are recorded. | FAILED |
| S12 | After the transfer, the bounded-arm cold mass is exactly the genuine-configuration mass. | Exhaustive per-half-edge assignment plus disjoint/no-overcount ledgers. | Every heavy half-edge must be assigned to a genuine Type B ledger entry, with multiplicities controlled. | Two selected half-edges share the same (z) and corridor suffix. | FAILED AT NODE [177] |

## 4. Counterexample attempts

### Smallest-parameter test

- **Explicit data:** Take the local corridor word (w_L-a-z-b-w_R), where (w_L,w_R) are boundary window vertices, (z) has four neighbours (a,b,c,d), and all four neighbours have ambient degree three.  Let (J=\{a,z,b\}), and choose (epsilon=w_La).  Declare no Type A response-coordinate family and no counted core (Y).
- **Hypotheses satisfied:** This is the smallest abstract path datum with a high vertex internal to a simple return corridor.  It satisfies the node-[175]-yes comparison, the cubic-neighbour conclusion, and the two-distinct-incidence conclusion.
- **Accumulated facts violated:** It is only a local incidence model; it does not provide an actual finite graph, maximal induced-(P_{13}) packing, selected minimal counterexample, or cold first-failure state.
- **Applicability:** **NON-APPLICABLE TO THE NODE** as an actual residual.  The earliest missing contract is node [2], which requires an actual finite minimum-degree-three target-avoiding graph.  It is nevertheless an exact smallest-schema test: the source fields do not determine the destination's (Y,H,K_h), response profile, or ledger.

### Parity or 2-adic test

- **Explicit data:** For the two first neighbours (a,b), compare an (a)--(b) return in (G-z) of length (2) with one of length (3).  Length (2) closes a (4)-cycle through (z); length (3) closes a (5)-cycle and is not rejected by the power-of-two target.
- **Hypotheses satisfied:** The calculation exactly tests fan-safe clause (i): the closed length is return length plus two, with no division or reduction modulo an odd part.
- **Accumulated facts violated:** The length-(2) candidate violates node [2]'s target avoidance.  The length-(3) candidate is only a local return and supplies no complete cold residual or response-coordinate labels.
- **Applicability:** The length-(2) case is **NON-APPLICABLE TO THE NODE**, first excluded at node [2].  The length-(3) case demonstrates that target-length arithmetic says nothing about fan-safe clauses (ii)--(v), but is not a complete residual.  No modular-hit checker was run because node [177] makes no congruence-to-integer or finite-coefficient-range inference.

### Boundary or range test

- **Explicit data:** Put (z) at the first inside vertex of the return corridor.  One incidence is the entry stub (w_Lz) from a cold-window vertex (w_L); the other is the first inside edge (zb).  The two recorded tails end at (w_L) and at the successor boundary-window vertex (w_R).
- **Hypotheses satisfied:** The boundary case still has two distinct incidences, a simple left arm of length one, a simple right arm, and cubic neighbours.  It matches the endpoint branch explicitly handled by the current Lean row.
- **Accumulated facts violated:** No upstream fact is violated at the local corridor level.  What fails is the proposed destination typing: (w_L,w_Rin W), whereas the decorated-envelope arm terminals must lie in one counted core (Y\subseteq R).  An alternative first-entry core (Y) is not selected or proved to exist.
- **Applicability:** Applicable to the exact routing contract.  It shows that handling the endpoint range repairs the two-incidence claim but not the envelope claim; the formal cold witness deliberately records window endpoints and therefore cannot be definitionally used as `def:decorated-fan-envelope`.

### Graph-realizability test

- **Explicit data:** Let (G=W_5), the wheel with centre (z) and rim (u_0u_1u_2u_3u_0).  Then (d(z)=4), every (u_i) has degree three, and (V_{\ge4}(G)=\{z\}) is independent.  The path (u_0-z-u_2) realizes the two-incidence heavy-centre geometry.
- **Hypotheses satisfied:** This is a finite simple minimum-degree-three graph realizing exactly the local degree law and the distinct-incidence path through a heavy centre.
- **Accumulated facts violated:** The rim is a (4)-cycle, so the graph violates the target-avoidance predicate.  It also has no induced-(P_{13}) packing because it has only five vertices.
- **Applicability:** **NON-APPLICABLE TO THE NODE**.  The earliest exclusion is node [2], by the rim (C_4).  The example establishes that minimum degree, high-degree independence, and the path geometry alone do not create any of the assigned-envelope data.

### Branch-routing test

- **Explicit data:** Retain the literal [175]-yes object ((G,\mathcal P,\epsilon,J,z)) and all its corridor facts, but expose the destination fields one at a time.  The source records no (Y\subseteq R), no first-entry terminal coordinates in (Y), no declared response-coordinate quotient, and no “surviving” predicate excluding exits (3)--(6).  Consequently no term of `def:decorated-fan-envelope` or of the assigned ledger at [65] is available.
- **Hypotheses satisfied:** This is exactly the information stated and proved at node [177] up through the cubic-neighbour and two-tail conclusions.  Node [10] proves the degree claim and node [2] proves only the geometric fan-return exclusion.
- **Accumulated facts violated:** None of the missing destination fields is an incoming fact.  `lem:typeA-high-degree-handoff` is downstream-inapplicable because its Type A support and surviving-separator hypotheses are absent.  `lem:decorated-fan-admissibility` is explicitly restricted to exit (7) of a saturated Type A branch.
- **Applicability:** Applicable to the node's routing contract.  The [175]-yes residual has a well-defined heavy corridor datum but fails node [65]'s complete entry type.  The current Lean workaround changes `TypeBFanEntryStatement` to accept this weaker object and propagates an `Or.inr` lane; that is evidence of the mismatch, not an accumulated proof of the manuscript implication.

## 5. Strongest valid counterexample

No graph satisfying the complete minimal-counterexample, packing, absorbed-corridor, and node-[175]-yes contract was constructed.  The strongest surviving candidate is the boundary-corridor residual in the branch-routing test: an actual eligible cold corridor with a high vertex (z), cubic neighbours, and two path tails, including the permitted case in which a tail lands at a packed-window vertex.  It violates no stated local fact at [177].  It is not itself a counterexample to the theorem; it is a witness that the retained source data have a strictly weaker type than the [65] destination.

The formal source sharpens this diagnosis.  Its cold witness has exactly those weaker fields and expressly denies that its window union is a counted remainder core.  A repository-wide search found many downstream predicates parameterized separately by `AbsorbedGermFanEnvelopeWitness`, but no theorem converting that witness to `Graph.DecoratedHandoff.Envelope` or `TypeBFanSupportWith`.  Thus the best candidate is a valid routing-contract counterexample even though no full target-free graph was found.

## 6. Local repair

### Corrected statement

Replace node [177]'s conclusion by the following two-stage statement.

> Let (epsilon) be an actual selected branch-excess half-edge, let (J) be its first-failure support, and suppose (z\in J) has degree at least four.  Then every neighbour of (z) has degree three, and the return corridor determines two distinct first neighbours of (z) and two simple corridor tails ending at its two boundary windows.  Target avoidance rules out a power-of-two fan return between these first neighbours.
>
> These data are a **cold heavy-centre corridor datum**.  They enter Type B node [65] only after a separate conversion theorem constructs a connected counted remainder core (Y), declared first-entry coordinates in (Y), a nonempty assigned set (K_z), the boundary-degree and terminal profile, and proves all five fan-safe clauses and the assigned-ledger identity.  If that conversion fails, the failure must be retained and routed according to its first failed obligation; it is not a Type B assigned support.

The conversion theorem may reuse `lem:typeA-high-degree-handoff` only after proving that the cold datum determines a Type A support and that (z) is a surviving first separator of declared coordinates through one completion port.  Merely citing the theorem is not sufficient.

### Complete local proof

Choose (z\in J) with (d_G(z)\ge4).  Let (u) be any neighbour of (z).  If (d_G(u)\ge4), then (u,z\in V_{\ge4}(G)) and (uzin E(G)), contradicting node [10].  Hence (d_G(u)\le3).  Node [2] gives (d_G(u)\ge3), so (d_G(u)=3).

The return corridor is simple.  If (z) is internal to its inside path, its predecessor (a) and successor (b) are distinct: equality would repeat a vertex and contradict simplicity.  Reverse the corridor segment from (a) to the entry boundary window to obtain the left tail, and retain the segment from (b) to the successor boundary window as the right tail.  Both are simple and start at distinct neighbours of (z).  If (z) is the first or last inside vertex, use the corresponding boundary-stub window endpoint for the missing side.  The entry and successor boundary stubs are distinct, and the outside component is disjoint from the selected cold-window union, so the same simplicity and distinctness conclusions hold.  This proves the cold heavy-centre corridor datum in every position of (z).

Now let (R_{ab}) be a simple (a)--(b) return in (G-z).  If (|R_{ab}|+2=2^j), then (za), (R_{ab}), and (bz) form a simple (2^j)-cycle, contradicting node [2].  This proves fan-safe clause (i).

No further conclusion follows from the accumulated facts.  The tails just constructed end at packed-window boundary vertices, not at a proved common (Y\subseteq R).  No response-coordinate quotient has been declared, so clauses (iii)--(v) are not even instantiated.  In particular, node [14] cannot be applied until a proper support and a target-complete compression on it are supplied.  This completes the proof of the corrected statement and identifies the exact conversion obligation.

For the conversion step, make the missing data a finite explicit test.  On the success arm, retain an actual `DecoratedHandoff.Envelope`, prove its core is a canonical connected (P_{13})-free empty-three-core piece of (R), prove the assigned-centre ledger and no-double-count transfer, and then invoke `lem:decorated-fan-admissibility` before [65].  On a failure arm, retain the first failure:

1. an accepted fan return or illegal label collision closes through the target/label exit;
2. a target-defective response quotient goes to the target-defect route;
3. a target-complete proper compression closes by [13]--[14];
4. proper or whole-graph delocalization goes to the corresponding support-dependence/route-8 residual; and
5. failure to find a common counted remainder core or declared terminal profile remains a new cold-handoff localization residual until separately proved impossible.

This finite split is exhaustive by construction.  It does not assume that every failure already has the Type A semantics needed by exits (3)--(6); the conversion lemma must establish those semantics before reusing those destinations.

### Counterexample disposition

The smallest local word and the wheel graph remain non-applicable as full residuals.  The boundary-corridor candidate lands at the corrected cold heavy-centre datum.  It reaches [65] only if a common remainder core and all response/fan-safe/ledger fields are supplied.  With only window-ending tails it remains on the new localization residual, so it is no longer misrouted.

The length-two parity candidate is closed immediately by target avoidance.  A non-power-of-two return is not falsely accepted as fan-safe: it still undergoes the label, quotient, compression, and delocalization tests.

### Graph patch

Replace the unconditional continuation with the typed conversion split

```text
[175] -- yes; retain epsilon, J, z, and the literal corridor -->
[177a: cold heavy-centre corridor datum]

[177a] -- genuine decorated envelope + admissibility + assigned ledger --> [65]
[177a] -- accepted fan return / illegal label collision --> target closure
[177a] -- target-defective declared quotient --> target-defect route
[177a] -- target-complete proper compression --> replacement closure [13]--[14]
[177a] -- proper/whole-graph support dependence --> support-dependence / route-8 route
[177a] -- no common counted core or declared terminal profile -->
         cold-handoff localization residual
```

The first edge must retain the same (epsilon), germ, support (J), centre (z), both first neighbours, both tails, and the packing.  The success edge must additionally retain (Y,H,K_h), all arms and terminals, the five fan-safe clauses, boundary response/profile data, core admissibility, and the exact Type B assignment/transfer identity.  The final residual may be removed only after a theorem proves that the cold-corridor construction always supplies the missing core/profile data.

### Downstream impact

The Part-V node [177] label and caption, the Part-VI incoming edge to [65], detailed dependency row 52, and the source-ledger row for `lem:absorbed-germ-fan-data` must distinguish “cold heavy-centre corridor datum” from “decorated Type B envelope.”  Node [108]'s genuine Type A exit-(7) handoff is unaffected.

Every node [65], [67]--[85] use from [177] must either consume the genuine success-arm envelope or receive a separately proved theorem showing that its calculation is valid for the weaker cold datum.  In particular, the fan certificate, cubic-closed status, B1/B2 carriers, fan-mass accounting, and `lem:typeB-exclusion` cannot be transferred merely by replacing (Y_X) with a germ support and (H_X) with ({z}).

In Lean, `TypeBFanEntryStatement` should not use a weaker `AbsorbedGermFanEnvelopeStatement` disjunct as a substitute for the manuscript assigned-support type.  Either prove a conversion to `Graph.DecoratedHandoff.Envelope`/`TypeBFanSupportWith` or give the cold residual its own key and explicit routing.  All `AbsorbedGermFanEnvelopeWitness` alternatives in `SpineVocabulary.lean` and `SpineRows.lean` require review.  The existing arity/state inconsistencies in `ColdCorridorRows.lean` and `SpineRows.lean` must also be repaired before the formal node can be called kernel-checked.

## 7. Regression audit

The following repeated uses and interfaces were inspected:

- `rg -n "lem:absorbed-germ-fan-data|def:decorated-fan-envelope|lem:typeA-high-degree-handoff|lem:decorated-fan-admissibility|typeB-assigned-ledger" to_formalize/erdos_64_proof.tex` found the Part-V caption (line 787), detailed dependency row (line 1230), source ledger (line 1560), the lemma and proof (lines 7660--7706), the fan-safe and decorated-envelope definitions (lines 10450--10547), the high-degree handoff (lines 10715--10745), decorated admissibility (lines 10747--10770), and the assigned Type B ledger (from line 12502).
- The Part-VI diagram around lines 802--845 was inspected.  It sends [177] directly into [65], while the genuine Type A exit-(7) handoff enters through [66]/[108].
- `lem:typeB-exclusion` and its proof around lines 13942--14060 were inspected.  They consume an actual connected admissible support, the assigned centre set (H_X), the five-condition fan-safe clique, envelope-relative neighbour charges, and the refined B2 ledger.
- `rg -n "AbsorbedGermFanEnvelopeWitness|AbsorbedGermFanEnvelopeStatement" hypostructure/Hypostructure/Graph/Strategy --glob '*.lean'` found the cold witness and statement in `SpineVocabulary.lean`, the producer in `ColdCorridorRows.lean`, and many separately cased downstream consumers in `SpineVocabulary.lean` and `SpineRows.lean`.
- The negative searches
  `rg -n "AbsorbedGermFanEnvelopeWitness.*DecoratedHandoff\\.Envelope|DecoratedHandoff\\.Envelope.*AbsorbedGermFanEnvelopeWitness" ...`
  and
  `rg -n "AbsorbedGermFanEnvelopeStatement.*TypeBFanSupportWith|TypeBFanSupportWith.*AbsorbedGermFanEnvelopeStatement" ...`
  returned no conversion theorem.
- `DecoratedHandoffEnvelope.lean`'s `FanSafe` and `fanSafe_geometric` definitions were inspected.  The geometric theorem proves only the accepted-return clause; the other four failures are a branch-supplied `Absorbing` predicate.
- A direct Lean check of `ColdCorridorRows.lean` was attempted and failed at the current source as recorded in the exact-claim subsection.  No proof, manuscript, diagram, Lean, audit source, or coverage-ledger file was modified by this audit.

No other reverse item dependency for `lem:absorbed-germ-fan-data` is listed in the fresh dossier.  The semantic repetitions are the diagram captions/table rows and the Type B consumers above.

## 8. Residual uncertainty

No actual minimal target-free graph realizing the full node-[177] residual was found, so this report does not claim a counterexample to the Erdős--Gyárfás theorem or even to the existence of some as-yet-unwritten cold-to-envelope conversion theorem.  It remains possible that the detailed cold first-failure construction has additional properties from which a common remainder core, declared response family, and survival of all fan-safe failures can be proved.  Those properties are neither stated in `lem:absorbed-germ-fan-data` nor retained in its current destination edge, and no such conversion theorem was found.

The fresh dossier's Lean locator predates the stronger but currently noncompiling cold-witness sources in the worktree: it reports a weaker `absorbedGermDichotomy` producer and no complete handoff.  Consequently the formal fidelity assessment is based on direct inspection of the current sources plus the failed local Lean check, not on a successful current kernel build.  The mathematical routing verdict is independent of that build state.
