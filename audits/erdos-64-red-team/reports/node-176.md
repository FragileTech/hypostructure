<!-- red-team-audit
{
  "schema_version": 1,
  "proof": "erdos-gyarfas",
  "node": 176,
  "node_label": "graph-realized (F5) configuration:\\\\closed by [154]--[157], [165]--[168]",
  "panel": "fig:proof-diagram-part-v",
  "contract_sha256": "a93912ae4eb2d0257eeabfdbf4f025b78367ec750ae5a7b34da9e4b01a93ad38",
  "manuscript_sha256": "106a8205a1718fbf90e1686a107b2143b9edca574e2b0c11415e7f44aee2c0f9",
  "graph_sha256": "dc67fae178f947a9607c167e383d85919633341bdd423e4c4a45e4c317b3a765",
  "lean_audit_sha256": "50324ef5594d635a52d83aeb297f2ca3f3d30ef58de4ce3602816c7e78365b12",
  "verdict": "WRONG ROUTING DESTINATION",
  "audited_at": "2026-08-24T21:48:51Z"
}
-->

# Red-team audit: node [176]

## 1. Executive verdict

Verdict: **WRONG ROUTING DESTINATION**

Node [176] does not close the whole graph-realized (F5) residual that reaches
it.  The length-changing, target-distinguished, and canonical-replacement
subcases have the cited destinations, and the two-strand check correctly closes
a genuine symmetric pair when either (2\ell) or (\ell+d) is a power of two.
For a surviving pair, however, node [168] applies only **if** the selected
branch-excess half-edge was chosen among the interior stubs.  The retained
selection is instead the fixed lexicographic tail of all 15 stubs: the first two
are transit and the remaining 13 are selected.  A graph-realized pair reached
from a selected corridor uses the selected half-edge as one of its strand
stubs; node [168]'s own geometry puts that stub at a window endpoint.  Thus the
live no-hit genuine residual fails the entry condition of its advertised final
closure.  This is a local routing-contract failure, not a construction of a
complete minimal-counterexample graph and not a verdict on the theorem.

## 2. Exact node contract

### Incoming residual

The unique diagram edge is the `no` edge [175] -> [176].  Its state consists
of the following data.

- (G) is the selected finite simple minimal counterexample:
  (delta(G)\ge 3), (G) has no cycle of power-of-two length, the target-safe
  return algebra holds, (G) has no proper minimum-degree-three core,
  (V_{\ge4}(G)) is independent, and proper-support target-complete
  replacements are excluded.
- The retained maximal induced-(P_{13}) packing has been split into hot and
  cold windows.  For every ambient-cubic cold window (P), its 15 external
  stubs have the global lexicographic order of
  `def:cold-skeleton-excess`; the first two are transit and the remaining 13
  form the fixed set
  (ℐ_{\rm br}(P)).  Every later corridor and candidate in this route is
  indexed by that fixed selection.
- Node [173]'s exact collision test is false, giving the tagged
  absorbed-configuration residual [174].  A selected half-edge
  (ε\in ℐ_{\rm br}(P)) has its retained return corridor and first-failure
  support (J).
- The [175] `no` predicate is literal: (J\cap V_{\ge4}(G)=\varnothing).
  Since (delta(G)\ge3), the vertices of (J) have ambient degree three.
  This puts (ε)'s actual first-failure germ in the subcubic candidate
  family.  Cases (F1)--(F4) are either refuted or transferred; the residual
  reaching the terminal label is (F5), a bounded same-interface
  configuration tied to (ε)'s corridor.

In the literal Lean continuation, `selectedAbsorbedGermResidual` begins with an
`ExactLedger` carrying `selection`, `uncompressible`, `hotColdPartition`,
`slackIndependent`, and `tightEndpoint`; it then appends bridgelessness,
corridors, first-failure routing, extraction, and the absorbed split.  The
`.inl` arm of `absorbedGermDichotomy` publishes `coldGermCandidates`.  That is
an object-level positive candidate-family decision, not a new interior-stub
selection.

### Accumulated facts

- Nodes [1]--[18]: finite simple target-avoiding graph, minimality,
  bridgeless/return facts, high-degree independence, boundary profiles,
  context universality, replacement exclusion, maximal (P_{13}) packing,
  and the (P_{13}) label algebra.
- The selected large-budget route through [25]--[57]: the retained remainder,
  deficiency/surplus and net-cap data needed by the exact collision test.
- Nodes [145]--[153], as reused on this residual: the hot/cold split, the
  ambient-cubic window family, the 15-stub count, the fixed 13-stub selection,
  actual return corridors, first-failure records, and bounded candidate
  extraction.  A routed Type B, route-8, surplus, or non-ambient-cubic
  incidence is not silently reintroduced.
- Nodes [173]--[175]: failure of the exact collision, the absorbed residual,
  the actual selected half-edge and first-failure incidence, and the chosen
  no-high-degree arm.
- Within the claimed [176] closure: the bounded-germ trichotomy and finite
  same-interface data; on the neutral branch, equal length and context
  equivalence; on the genuine arm, a second ambient strand internally
  disjoint from the corridor strand and using the same two attachments.

The dense-realization decision [158] and its density-specific branch facts are
not ancestors of [176].  Nodes [165]--[168] may be invoked here only as typed
closure lemmas for the retained (F5) object; their dense-branch hypotheses
cannot be imported merely because their numbers are cited.

### Current predicate and exact claim

The terminal annotation and `lem:absorbed-germ-fan-data` case (i) assert the
implication

\[
  F(176)+\bigl(J\cap V_{\ge4}(G)=\varnothing\bigr)
  +\text{``the retained first failure is (F5)''}
  \Longrightarrow \bot,
\]

where the contradiction is claimed to follow from [154]--[157] and
[165]--[168].  Expanded by cases, this requires all of the following.

1. A length-changing germ is hit-realized, target-distinguished/routed, or
   silent with an actual smaller target-complete representative.
2. An equal-length neutral canonical representative is closed by the refined
   minimality exchange.
3. A genuine equal-length second strand gives simple cycles of lengths
   (2\ell) and (ℓ+d); a power-of-two value gives (F1).
4. If both values are non-powers, the remaining genuine pair satisfies every
   hypothesis required by [168]'s endpoint-selection exclusion.

Item 4 is false for the retained selection.  `def:cold-skeleton-excess` does
not state that (ε) is interior, while `lem:symmetric-pair-endpoint` makes its
exclusion conditional on replacing/restricting the selection to interior
stubs.

### Outgoing contracts

Node [176] is terminal and has no outgoing edge.  Therefore every possible
incoming (F5) configuration must be contradicted or transferred before the
node ends.  There is no outgoing contract that retains a no-hit symmetric pair
whose selected strand begins at an endpoint.  The missing precondition cannot
be repaired by treating [168] as an ancestor: [168] is precisely the proposed
destination closure, and its interior-selection hypothesis is absent from
(F(176)).

## 3. Sentence audit

| Sentence | Exact assertion | Facts used | Hidden obligation | Adversarial test | Status |
|---|---|---|---|---|---|
| S1 | On [175]'s no arm, (J) is subcubic. | (delta(G)\ge3); (J\cap V_{\ge4}=\varnothing). | Degree is the ambient degree used by the support predicate. | Set every vertex of (J) to ambient degree three. | SUPPORTED |
| S2 | The selected (ε)'s germ belongs to the extracted candidate route. | First-failure incidence; subcubic support; cold extraction. | The incidence must be the actual one indexed by (ε), not a reconstructed germ. | Compare the manuscript's per-(ε) statement with `ColdGermFamilyWitness`. | AMBIGUOUS |
| S3 | (F1)--(F5) exhaust the retained first failure. | `def:cold-corridor-first-failure`; first-failure lemma. | Terminal and repeat subcases retain their exact interfaces and support. | Stop both before and after (Q_{\rm cold}+1) states. | SUPPORTED |
| S4 | (F1) realizes a power-of-two cycle; (F2)/(F4) transfer to named ledgers; a valid (F3) replacement contradicts uncompressibility. | Target avoidance; routing ledgers; replacement exclusion. | Routing destinations and an actual smaller representative must be present. | Keep a neutral zero-increment row, for which no smaller representative follows. | SUPPORTED FOR NONNEUTRAL CASES |
| S5 | A neutral equal-length (F5) row splits into canonical replacement or genuine second strand. | Retained same-interface record; `lem:neutral-germ-symmetry`. | The alternatives concern the same active extracted germ. | Require membership in the retained disjoint family. | SUPPORTED AS THE INTENDED SPLIT |
| S6 | A nontrivial canonical replacement closes by the refined minimality order. | Equal size, boundary profile, context equivalence, canonical order. | The replacement is an actual simple graph with all minimality hypotheses. | Exchange only the retained boundaried piece. | SUPPORTED CONDITIONALLY |
| S7 | A genuine pair closes exactly the local cycles (2\ell) and (ℓ+d). | Two internally disjoint strands and the window segment. | The walks are simple and meet only at their endpoints. | Use three internally disjoint (x)-(y) paths of lengths (ℓ,ℓ,d). | SUPPORTED |
| S8 | The finite check closes a pair when (2\ell\in\mathrm{Pow}) or (ℓ+d\in\mathrm{Pow}). | Target definition; `TwoStrandEnumeration.lean`. | Test (2\ell), not merely (ℓ). | ((\ell,d)=(2,0)): (2\ell=4) closes although (ℓ\notin\mathrm{Pow}). | SUPPORTED; THE PRINTED SURVIVOR DESCRIPTION IS FAILED |
| S9 | Every surviving genuine pair attaches at window endpoints. | An interior cubic (P_{13}) vertex has one external stub; a genuine pair needs two at each attachment. | The selected strand's first stub must be tracked to its attachment. | Use a selected corridor strand in the pair. | SUPPORTED |
| S10 | Such a survivor is never a selected half-edge. | Conditional sentence in `lem:symmetric-pair-endpoint`. | The already fixed (ℐ_{\rm br}(P)) must consist of interior stubs. | Of 15 stubs, dropping only two leaves 13; at most 11 are interior. | FAILED |
| S11 | The extraction can simply be read with (9C) instead of (13C). | The proposed interior reselection in [168]. | The selection, every corridor, the exact collision constants, and all dependent counts must be redefined and re-proved. | Keep the original lexicographic order with two interior transit stubs. | FAILED FOR THE CURRENT CONTRACT |
| S12 | Hence the graph-realized (F5) arm is terminally closed. | S1--S11; node label and Part V caption. | Every no-hit genuine survivor must have a valid destination. | (ℓ=3,d=12) with selected endpoint stub. | FAILED |

## 4. Counterexample attempts

### Smallest-parameter test

- **Explicit data:** First test the printed survivor characterization at
  ((\ell,d)=(2,0)).  The closing lengths are (2\ell=4) and
  (ℓ+d=2).  Thus the pair is closed, although the manuscript's phrase
  (ℓ\notin\mathrm{Pow}) and (ℓ+d\notin\mathrm{Pow}) would list it as a
  survivor.  For a simple endpoint-to-endpoint no-hit pair, take the first
  useful local value ((\ell,d)=(3,12)), with closing lengths (6) and (15).
- **Hypotheses satisfied:** Both pairs lie in the enumerated range
  (ℓ\le40), (0\le d\le12).  The second has two non-power closing
  lengths and is compatible with distinct (P_{13}) endpoints.
- **Accumulated facts violated:** The ((2,0)) candidate violates (F1), since
  it realizes a 4-cycle; **NON-APPLICABLE TO THE NODE**, excluded at node
  [155]/(F1).  The ((3,12)) numerical candidate violates no checked local
  arithmetic fact, but by itself does not establish a complete graph in the
  minimal-counterexample residual.
- **Applicability:** The first datum diagnoses only the inaccurate printed
  survivor formula.  The second is the smallest endpoint numeric survivor used
  in the later routing and realizability tests.

### Parity or 2-adic test

- **Explicit data:** For ((\ell,d)=(3,12)), (2\ell=6=2\cdot3) and
  (ℓ+d=15).  Each has odd part greater than one, so neither is a power of
  two.  No modulus projection or divisibility lift is involved: these are the
  two literal graph cycle lengths.
- **Hypotheses satisfied:** This is exactly the no-hit arm of the finite
  two-strand predicate, with (d<13) and (ℓ\le40).
- **Accumulated facts violated:** None at the finite-state level.  Target
  avoidance is consistent with these two local cycles.  A complete ambient
  target-avoiding graph has not been constructed.
- **Applicability:** Applicable to the node's claimed arithmetic closure.  It
  proves that [167] intentionally has survivors, so [176] must type-check their
  route into [168]; arithmetic alone cannot close this datum.

### Boundary or range test

- **Explicit data:** At the upper enumerated boundary
  ((\ell,d)=(40,12)), the closing lengths are
  (80=16\cdot5) and (52=4\cdot13), neither a power of two.
- **Hypotheses satisfied:** Equality (ℓ=40) is allowed and (d=12<13) is
  the endpoint gap of (P_{13}).
- **Accumulated facts violated:** None in the finite table.  As above, no
  complete ambient minimal counterexample is asserted.
- **Applicability:** Applicable.  The bounded range does not make the survivor
  list empty at either its low useful values or its upper endpoint.

### Graph-realizability test

- **Explicit data:** Let (P=x=v_0,v_1,\ldots,v_{12}=y) be an induced
  (P_{13}).  Add two internally disjoint outside paths
  (Q=x-a-b-y) and (E=x-c-d-y), each of length three, with all four internal
  vertices new.  Give each interior vertex of (P) one outside stub, and label
  the ambient vertices so two interior stubs precede all four endpoint stubs in
  the global lexicographic order.  Then all four endpoint stubs, including
  (ε=xa), lie in the fixed 13-element selected tail.  In the displayed
  local subgraph the only cycles are (Q\cup E) of length 6 and
  (P\cup Q,P\cup E) of length 15.
- **Hypotheses satisfied:** The object is simple; (P) is induced; (x,y)
  have one window neighbour and two external neighbours; every interior window
  vertex has one external stub; (Q,E) are genuine internally disjoint strands;
  and the selected origin (ε) is an endpoint stub.  Extra third incidences
  at (a,b,c,d) may leave the bounded support, as the first-failure formalism
  permits.
- **Accumulated facts violated:** No local window, selection, simplicity,
  subcubic, or target-length condition is violated.  The test does **not**
  supply a bridgeless cubic completion avoiding all power-of-two cycles, the
  exact global residual inequalities, or minimality; those global conditions
  remain unestablished rather than disproved.
- **Applicability:** It is a graph-realizable counterexample to the local claim
  that a surviving pair cannot originate at a fixed selected stub.  It is not
  claimed as a `VALID LOCAL COUNTEREXAMPLE` to the complete (F(176)).

### Branch-routing test

- **Explicit data:** Retain an active graph-realized neutral (F5) germ whose
  corridor strand begins with selected (ε), and suppose its finite datum is
  ((\ell,d)=(3,12)).  The no-high-degree predicate sends it
  [175] -- no --> [176].  The no-hit result at [167] leaves it for [168].
- **Hypotheses satisfied:** Candidate-family membership, subcubic support,
  equal length, graph realization, endpoint attachment, and failure of both
  direct power tests are precisely the hypotheses retained along this route.
- **Accumulated facts violated:** [168]'s additional interior-selection
  premise is not accumulated.  Indeed, because (Q) begins with (ε) and a
  genuine pair needs two stubs at that attachment, [168]'s supported geometric
  conclusion makes the foot of (ε) an endpoint, the opposite of that
  premise.
- **Applicability:** Applicable as a route-contract test.  The residual has no
  outgoing edge after [176], and none of [154]--[157] or [165]--[167] assigns
  this no-hit endpoint-origin case elsewhere.

## 5. Strongest valid counterexample

No complete minimal-counterexample graph satisfying every global fact in
(F(176)) was constructed.  The strongest candidate is the explicit local
ambient-cubic (P_{13}) theta configuration above: two length-three outside
strands between the window endpoints, with lexicographic ordering that leaves
their endpoint stubs selected.  It satisfies the actual window geometry,
fixed-selection rule, simple graph realization, subcubic local support, and
the no-hit equations (2\ell=6), (ℓ+d=15).  Its global completion remains
open.

The verdict does not require promoting that candidate to a theorem
counterexample.  The destination mismatch is internal to the universal route:
for any genuine pair produced from the selected corridor, its origin
ε is selected by construction; if the pair survives [167], [168] proves its
attachments are endpoints, while its exclusion is available only under the
unstated and incompatible premise that (ε) came from an interior-only
selection.

## 6. Local repair

### Corrected statement

Replace the fixed cold candidate selection used by this closure with an
explicit interior selection.  Publication-quality form:

> For every ambient-cubic induced (P_{13}) window (P), let
> (I(P)) be its eleven external half-edges based at interior vertices.  In the
> inherited global order, declare the first two elements of (I(P)) transit
> and let (ℐ_{\rm br}^{\rm int}(P)) be the remaining nine.  Construct the
> cold return corridors and first-failure candidates from
> (ℐ_{\rm br}^{\rm int}).  On the absorbed residual, if the selected
> corridor of (ε\inℐ_{\rm br}^{\rm int}(P)) has subcubic first-failure
> support, then its (F5) configuration is closed as follows: length-changing,
> target-distinguished, and canonical-replacement cases use [154]--[157] and
> [165]--[166]; a graph-realized equal-length pair is a power-of-two hit when
> (2\ell) or (ℓ+d) is a power of two, and otherwise is impossible because
> its selected attachment is interior but a genuine pair requires two external
> stubs there.

The numerical survivor description must say
`(2\ell\notin\mathrm{Pow}) and (ℓ+d\notin\mathrm{Pow})`; replacing the first
condition by `(ℓ\notin\mathrm{Pow})` is false at (ℓ=2).

### Complete local proof

An ambient-cubic induced (P_{13}) has eleven interior vertices.  Each has two
neighbours in the induced path and ambient degree three, hence exactly one
external stub.  Thus (I(P)) has cardinality eleven and deleting its first two
elements leaves nine selected interior stubs.

Let (εinℐ_{\rm br}^{\rm int}(P)) reach the subcubic (F5) arm.  The
length-changing trichotomy and the target-distinguished/handoff transfers are
unchanged.  On a neutral canonical-replacement arm, the refined exchange closes
provided its stated graph-replacement hypotheses hold.  On the genuine arm,
let (Q) be the actual corridor strand beginning with (ε) and (E) the
internally disjoint equal-length second strand.  Their union is a simple cycle
of length (2\ell), while either strand with the window segment is a simple
cycle of length (ℓ+d).  If either length is a power of two, target avoidance
gives the contradiction at (F1).

Otherwise consider the attachment vertex at the foot of (ε).  The two
internally disjoint strands must leave it through two distinct external stubs,
one belonging to (Q) and one to (E).  But (ε)'s foot is an interior
vertex of (P), where the preceding degree calculation gives exactly one
external stub.  This is impossible.  Hence the corrected interior-selected
route has no surviving genuine pair, and the (F5) arm closes.

This proof is complete only after the upstream quantitative statements are
re-established for the nine-element selection; it does not justify silently
substituting (9C) into the current 13-stub ledger.

### Counterexample disposition

The ((\ell,d)=(3,12)) theta configuration is not forced to contain a target
cycle, and the repair does not claim otherwise.  Its four strand stubs are
based at the endpoints, so none belongs to
(ℐ_{\rm br}^{\rm int}(P)).  It is therefore outside the repaired candidate
family rather than being falsely contradicted.  The ((2,0)) wording test is
still caught directly because (2\ell=4).

### Graph patch

The exact routing patch is

```text
[151] ambient-cubic P13 stub structure
  -> choose E_br^int(P) from the 11 interior stubs and retain |E_br^int(P)| = 9
  -> [152]/[153] build every corridor and extracted germ from that same set
  -> [175] test the actual first-failure support
     -> no high-degree vertex + (F5)
     -> [176] nonneutral/canonical/direct-hit closures
        -> no-hit genuine pair + retained "epsilon is interior"
        -> [168] endpoint-stub contradiction
        -> terminal [176].
```

The destination entry facts are: ambient-cubic induced (P_{13}), actual
selected (ε) based at an interior vertex, two graph-realized internally
disjoint strands sharing its attachment, and failure of the two direct hit
tests.  Node [168]'s degree calculation then supplies the contradiction.  If
the proof keeps the original 13-element selection instead, it must add a real
destination for endpoint-origin survivors; none is presently stated.

### Downstream impact

- Reprove `def:cold-skeleton-excess`, `lem:cold-window-stub-excess`,
  `lem:cold-germ-extraction`, and every (13C)-based inequality with the same
  retained interior selection and the correct (9C) supply.  Recheck the
  thresholds (1/78), (1/73), the constants (D_{\rm cold}), and the exact
  collision coefficients rather than changing numerals mechanically.
- Synchronize the cold quantitative ledger [145]--[157], the dense reuse
  [162]--[168], `rem:dense-residual-status`, and the absorbed repair
  [173]--[176].  The Part V, XI, and XII captions and dependency-table rows
  claiming unchanged reuse or complete closure require the retained
  interior-origin fact.
- In Lean, redefine or add an interior-selected analogue of
  `Graph.ColdCorridor.selectedStubs`/`allSelectedStubs`; connect it to
  `coldWindowStubStructure`; and rebuild `ColdCorridorStateStatement`,
  `ColdGermFamilyWitness`, the [175] split, and the genuine-strand closer from
  the same selected set.  The present `selectedStubs` is literally
  `(externalStubList ...).drop 2`, and `coldWindowStubStructureRow` records only
  endpoint/interior counts, not membership of selected stubs.
- Correct the survivor predicate prose around `lem:two-strand-check` and
  `lem:symmetric-pair-endpoint`.  `TwoStrandEnumeration.lean` already uses the
  correct conditions on `segmentClosing` and `pairClosing` and explicitly
  states that the finite check does not close the symmetric case by itself.
- Replace the unresolved/opaque terminal call used for the genuine arm by a
  source declaration proving the repaired implication, then update
  `Assembly_node_audit.md` and `web/data/eg_node_audit.json` through their normal
  audit workflow.  No such source was edited here.

## 7. Regression audit

The following repeated uses were inspected.

- The Part V node [176], its incoming edge, caption, and the small-order
  dependency row [173]--[177].
- `def:cold-skeleton-excess`, including its sentence that *all later* cold
  counts use the fixed lexicographic 13-stub tail; the 15-stub and (13C)
  counts; `lem:cold-germ-extraction`; and the cold quantitative ledger and
  terminal theorem.
- `lem:dense-cold-pass`, the neutral symmetry split, refined-minimality route,
  `lem:two-strand-check`, `lem:symmetric-pair-endpoint`, and
  `rem:dense-residual-status`.
- `lem:absorbed-germ-fan-data`, both its statement and proof, including the
  assertion that a subcubic selected incidence is routed “as there.”
- `Graph/ColdGermFamily.lean`: `externalStubList`, `selectedStubs`,
  `allSelectedStubs`, and the retained candidate-family construction.
- `Graph/TwoStrandEnumeration.lean`: the two literal closing lengths, complete
  finite range, survivor predicate, and the explicit surviving example.
- `Graph/WindowStubStructure.lean`, `SpineVocabulary.lean`, and
  `ColdCorridorRows.lean`: endpoint/interior stub facts,
  `GenuineSecondStrandStatement`, `ColdGermFamilyWitness`,
  `absorbedGermDichotomy`, `neutralGermSymmetryDichotomy`, and
  `coldBranchClosedRow`.
- `Assembly.lean`: both calls to `selectedGenuineSecondStrandCloses` and the
  [175]--[177] continuation.  No source declaration for that closer was found
  by the source search; a stale compiled `FrontierStubs` artifact contains
  frontier-gap declarations, which is not paper evidence or a source proof.
- The Lean/fidelity sidecar and `Assembly_node_audit.md` were used only as
  locators/status evidence.  The latter currently reports the first [175]
  owner broken and the end-to-end producer incomplete; those formalization
  defects were not used as the mathematical reason for this verdict.

Searches used included:

```text
rg -n 'cold-germ-extraction|cold-bounded-germ-trichotomy|cold-same-interface-table|neutral-germ-symmetry|refined-minimality-swap|two-strand-check|symmetric-pair-endpoint|absorbed-germ-fan-data|def:cold-skeleton-excess' to_formalize/erdos_64_proof.tex
rg -n 'selectedStubs|allSelectedStubs|GenuineSecondStrand|TwoStrand|coldWindowStubStructure|selectedGenuineSecondStrandCloses|absorbedGermDichotomy' hypostructure proofs/hypostructure_erdos_64_eg
rg -n 'graph-realized \(F5\)|surviving pair|interior stubs|9C|13C' to_formalize/erdos_64_proof.tex Assembly_node_audit.md web/data/eg_node_audit.json
```

No other manuscript destination for a selected endpoint-origin no-hit genuine
pair was found.  Occurrences in prior per-node reports were not treated as
mathematical authorities.

## 8. Residual uncertainty

The explicit theta configuration has not been completed to a bridgeless
minimum-degree-three graph satisfying every global residual inequality,
target-avoidance condition, and minimality fact.  Accordingly this report does
not claim a complete local counterexample graph.  It also does not prove that
the proposed nine-stub selection preserves the manuscript's global numerical
thresholds or the exact small-order collision; those quantitative checks are
the main residual uncertainty of the repair.  Finally, concurrent formalization
work leaves the current source assembly incomplete around [175] and its
frontier closers, so no kernel-checked node-[176] implementation was available
to remove the paper-level selection mismatch.
