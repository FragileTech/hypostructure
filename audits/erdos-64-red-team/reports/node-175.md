<!-- red-team-audit
{
  "schema_version": 1,
  "proof": "erdos-gyarfas",
  "node": 175,
  "node_label": "selected corridor\\\\meets a high-degree vertex?",
  "panel": "fig:proof-diagram-part-v",
  "contract_sha256": "d87fcaca29f8e98c4cee2b5f178e317e02f89128443418ca81d76f4b54c5ce2a",
  "manuscript_sha256": "106a8205a1718fbf90e1686a107b2143b9edca574e2b0c11415e7f44aee2c0f9",
  "graph_sha256": "dc67fae178f947a9607c167e383d85919633341bdd423e4c4a45e4c317b3a765",
  "lean_audit_sha256": "50324ef5594d635a52d83aeb297f2ca3f3d30ef58de4ce3602816c7e78365b12",
  "verdict": "WRONG ROUTING DESTINATION",
  "audited_at": "2026-08-24T21:44:19Z"
}
-->

# Red-team audit: node [175]

## 1. Executive verdict

Verdict: **WRONG ROUTING DESTINATION**

The decision whether the actual first-failure support (J) meets
(V_{\ge4}(G)) is exhaustive, and node [10] correctly makes every neighbour
of a chosen high-degree (z\in J) cubic.  The yes-edge nevertheless does not
satisfy node [177]/Type B [65].  The two sides of one cold corridor give two
distinct incidences and two geometric tails at (z); they are not thereby two
declared response coordinates through one completion port with a common
ordered prefix, the same boundary-degree fibre, and a surviving first
separator.  Nor do they provide the connected (P_{13})-free remainder core,
assigned arms ending in that core, decorated response profile, or transfer
identity required by `def:decorated-fan-envelope` and the assigned Type B
ledger.  The Lean vocabulary corroborates the mismatch by putting the cold
corridor witness in a new disjunct of `TypeBFanEntryStatement`, explicitly not
in `Graph.DecoratedHandoff.Envelope`.  Only a corridor already carrying the
declared (F4) envelope may go to [177]/[65]; a remaining graph-realized (F5)
bounded configuration can instead use the existing [176] closure.

## 2. Exact node contract

### Incoming residual

The only immediate graph edge is `[174] -> [175]`.  This audit conditions on
the local representative stated by `lem:absorbed-germ-fan-data`: an actual
selected branch-excess half-edge (epsilon) of an ambient-cubic cold window,
its canonical return corridor, and its actual first-failure bounded support
(J).  Whether the previous node always supplies such an (epsilon) is a
separate entry obligation and is not imported as a conclusion here.

The object remains the fixed lexicographically minimal counterexample: it is a
finite simple graph with minimum degree at least three and no power-of-two
cycle; it has no proper minimum-degree-three core, (V_{\ge4}(G)) is
independent, and the replacement, context-universality, and hereditary
uncompressibility facts are retained.  The fixed maximal induced-(P_{13})
packing, its ambient-cubic cold windows, the selected interior branch-excess
stubs, the outside-component corridor, and the finite first-failure cut-state
are all data of the same graph.

On the surviving cold branch, (F1)--(F3) have already been routed to a target
cycle, target defect, or compression.  (F4) is, by definition, the case in
which the corridor first enters an *already declared* Type B handoff envelope
or route-8 support.  If no such earlier alternative occurs, (F5) supplies the
actual bounded same-interface configuration used by [176].

### Accumulated facts

The facts usable by this node include:

- `[2]`, `[4]`--`[14]`: target avoidance, minimum degree three, minimality,
  high-degree independence, boundary profiles, context universality,
  replacement, and hereditary target-uncompressibility.
- `[17]`, `[22]`, `[25]`--`[29]`: the fixed maximal (P_{13})-window packing,
  remainder (R), hot/cold partition, ambient surplus, and exact window--remainder
  incidence data.
- `[145]`--`[153]`: the selected branch-excess half-edge, bridgeless outside
  component, canonical return corridor with distinct boundary stubs, finite
  cut-state, and first-failure routing on the current object.
- The selected (epsilon) has an actual first-failure support (J).  On the
  live (F5) residual it is a cold bounded configuration with two active
  boundary interfaces and retained response data.
- `[10]`: if (d_G(z)\ge4), every neighbour of (z) has degree exactly three,
  because (delta(G)\ge3) and (V_{\ge4}(G)) is independent.

None of these facts declares the two opposite halves of one cold corridor to
be two response coordinates through the same Type A completion port.  None
chooses a Type A support (X), proves a common prefix and common
boundary-degree fibre, proves that (z) is a surviving first separator, or
constructs the counted core (Y\subseteq R), envelope assignment, and grouped
charge transfer consumed by Type B.

### Current predicate and exact claim

For the retained support (J), the literal predicate is

\[
J\cap V_{\ge4}(G)\ne\varnothing .
\]

Its no-arm is the complement.  Therefore exactly one of the following holds:

\[
\begin{array}{ll}
\text{no:}& \forall v\in J,\ d_G(v)\le3,\\
\text{yes:}& \exists z\in J,\ d_G(z)\ge4.
\end{array}
\]

On the no-arm, the candidate definition in
`lem:cold-germ-extraction` applies to this support.  On the yes-arm, node [10]
adds

\[
\forall u\in N_G(z),\qquad d_G(u)=3,
\]

and simplicity of the corridor gives distinct predecessor/successor
incidences at an internal (z) (with the two distinct boundary stubs supplying
the analogous foot case).  The exact justified conclusion is thus a
*high-corridor datum*: a high centre, cubic neighbourhood, and two simple
corridor halves leading to packed-window boundary stubs.

The manuscript makes the stronger assertion that these halves are
"separated connector tails in the sense of
`lem:typeA-high-degree-handoff, def:decorated-fan-envelope`" and therefore
enter Type B.  The cited lemma instead assumes a surviving first separator
for a finite family of declared response coordinates through one completion
port.  Under that assumption it takes the Type A support (X) as the counted
core (Y).  Node [175] has no corresponding (X), common completion port,
common prefix, response fibre, separation family, or surviving-separator
test.  Its two cold tails end in packed windows, not in a supplied common core
(Y\subseteq R).

### Outgoing contracts

The no-edge `[175] -- no --> [176]` needs the actual graph-realized (F5) cold
bounded configuration.  The current first-failure datum supplies it; the
subcubic condition additionally makes it a counted candidate for the
extraction bound.

The yes-edge `[175] -- yes --> [177]`, followed by the continuation to Type B
[65], is substantially stronger.  A manuscript `DecoratedHandoff.Envelope`
requires at least:

- a connected (P_{13})-free, empty-(3)-core counted remainder core
  (Y\subseteq R);
- assigned high decorations (H), nonempty actual-neighbour sets (K_h), and
  simple arms from those neighbours to terminal vertices of (Y);
- the declared boundary response coordinates, terminal coordinates, and
  boundary-degree profile of the decorated support;
- a fan-safe clique on the assigned neighbours; and
- for the later assigned/grouped ledger, the core--centre assignment and the
  no-double-count/transfer identity used to evaluate
  (operatorname{No}(Y,H)).

The high-corridor predicate supplies none of the first, third, or fifth group
and does not establish the full second or fourth group.  The later Type B
residual mass ranges over ordinary assigned supports and grouped envelopes
produced from genuine Type A exit-(7) handoffs; a bare pair of cold-corridor
tails is not one of those objects.

## 3. Sentence audit

| Sentence | Exact assertion | Facts used | Hidden obligation | Adversarial test | Status |
|---|---|---|---|---|---|
| S1 | Exactly one of (J\cap V_{\ge4}=\varnothing) and (J\cap V_{\ge4}\ne\varnothing) holds. | Finite set membership and classical/decidable logic. | The same actual (J) must be retained on both arms. | Put one degree-four vertex in (J), then remove it. | SUPPORTED |
| S2 | On the no-arm, (J) is subcubic. | Literal complement of the predicate. | Degrees are ambient degrees, as required by the candidate filter. | A degree-three terminal support. | SUPPORTED |
| S3 | The no-arm germ belongs to the counted candidate family and continues to [176]. | `lem:cold-germ-extraction`, retained actual germ, (F5) routing. | Candidate membership must use the same incidence map and support. | Evaluate the filter on the retained (J). | SUPPORTED, conditional on the stated actual incidence |
| S4 | On the yes-arm choose (z\in J) with (d_G(z)\ge4); every neighbour of (z) is cubic. | [10] and (delta(G)\ge3). | Independence must concern ambient high-degree vertices. | Degree-four (z) with four degree-three neighbours. | SUPPORTED |
| S5 | The corridor uses two distinct incidences at (z). | Simplicity of the corridor; distinct entry/successor stubs in the foot case. | The chosen (z) must lie on the retained corridor segment, not merely elsewhere in an enlarged support. | The one-vertex outside path between two distinct stubs. | SUPPORTED for the corridor witness constructed in Lean |
| S6 | The two opposite corridor halves are separated connector configurations under `def:typeA-continuation-classes`. | S5. | Need two declared response coordinates through one completion port, the same ordered prefix to (z), and the same boundary-degree fibre. | Let the halves end in two distinct packed windows. | FAILED |
| S7 | `lem:typeA-high-degree-handoff` applies at (z). | Claimed S6. | Need a Type A support (X) and a *surviving first separator*, not merely a high vertex on a path. | Compare the lemma's hypotheses with (J\cap V_{\ge4}\ne\varnothing). | FAILED |
| S8 | The two cold tails form a decorated handoff fan envelope. | Claimed S7. | Need (Y\subseteq R), arms terminating in (Y), declared response data, and a fan-safe clique. | Both tails terminate in packed-window vertices. | FAILED |
| S9 | The half-edge may enter Type B [65]. | Claimed S8. | Need an ordinary assigned support or a genuine grouped decorated envelope with its charge ledger. | Inspect `def:typeB-assigned-ledger` and `def:typeB-residual-mass`. | FAILED |
| S10 | Every discarded high-corridor half-edge is charged to Type B without loss or overcount. | Per-(epsilon) high-centre choice. | Need a grouped assignment, bounded multiplicity, and the transfer/no-double-count identity. | Several selected corridors choose the same high centre. | FAILED |
| S11 | The node's yes/no predicates are complementary. | S1. | Complementarity alone does not type-check the destinations. | Follow both graph edges with the retained record. | SUPPORTED, but the yes destination is wrong |

## 4. Counterexample attempts

### Smallest-parameter test

- **Explicit data:** Take two ambient-cubic induced (P_{13}) windows (P,Q),
  boundary vertices (p\in P), (q\in Q), and a degree-four outside vertex
  (z) adjacent to (p,q,c,d).  Give each of (p,q,c,d) ambient degree
  three.  Let the selected corridor be the two-stub path (p-z-q), so
  (J=\{z\}).
- **Hypotheses satisfied:** Locally the graph is simple, the two corridor stubs
  are distinct, (J\cap V_{\ge4}\ne\varnothing), the centre has the node-[10]
  cubic-neighbour normal form, and the two one-edge tails are simple.
- **Accumulated facts violated:** No finite completion of this local support was
  shown to avoid every power-of-two cycle, realize the canonical maximal
  packing, and satisfy every earlier entropy/residual branch predicate.
- **Applicability:** **NON-APPLICABLE TO THE NODE.**  As a whole-graph
  counterexample it is first unverified at node [2], target avoidance.  As a
  typed local test it exposes the exact missing data: the tails land in two
  windows and do not produce a common Type A core or a response family through
  one completion port.

### Parity or 2-adic test

- **Explicit data:** Compare the preceding local corridor with
  (d_G(z)=4) and with (d_G(z)=5), adding one further cubic neighbour in the
  latter case.  Insert an even or odd number of degree-three internal vertices
  in either corridor half.
- **Hypotheses satisfied:** In every variant (z\in V_{\ge4}), all neighbours
  are cubic, and the two incident corridor halves remain distinct and simple.
- **Accumulated facts violated:** No globally target-free completion or full
  selected branch history was constructed.
- **Applicability:** **NON-APPLICABLE TO THE NODE.**  The earliest unverified
  global fact is node [2].  The test shows that no parity, 2-adic valuation, or
  choice of high degree repairs the missing common-prefix, core, and ledger
  fields; this node contains no valid modular inference to audit.

### Boundary or range test

- **Explicit data:** Put the high centre at the corridor foot: the inside path
  has the single vertex (z), while the entry and successor stubs are
  (pz) and (zq) with (p\in P), (q\in Q).  The two arms therefore have
  their sharp minimum length and terminate immediately in the packed-window
  union.
- **Hypotheses satisfied:** This is the endpoint case explicitly handled by
  the corridor construction; distinct boundary stubs give distinct
  incidences, and (d_G(z)\ge4) chooses the yes-arm.
- **Accumulated facts violated:** Again, no full minimal target-free completion
  and canonical branch history was supplied.
- **Applicability:** **NON-APPLICABLE TO THE NODE.**  Node [2] is the earliest
  unverified global condition.  The local boundary case is decisive for the
  contract: neither terminal lies in a supplied (Y\subseteq R), and there is
  no prefix before (z) from a common completion port.

### Graph-realizability test

- **Explicit data:** Realize (P) and (Q) as disjoint induced 13-vertex
  paths.  Join one cubic window stub from each to the common degree-four vertex
  (z), add two further neighbours (c,d), and attach open stubs to finite
  cubic gadgets so that all displayed neighbours have degree three and no two
  high-degree vertices are adjacent.  The outside component has boundary
  stubs (pz,zq), whose lexicographically selected return can have the
  one-vertex inside path at (z).
- **Hypotheses satisfied:** The local support is a finite simple graph with the
  required degrees, induced windows, high-degree independence, two distinct
  corridor incidences, and graph-realized simple tails.
- **Accumulated facts violated:** The cubic gadgets were not certified to avoid
  (C_4,C_8,C_{16},\ldots), and the displayed packing was not proved to be the
  canonical maximal packing on a lexicographically minimal counterexample.
- **Applicability:** **NON-APPLICABLE TO THE NODE.**  Node [2]'s target
  avoidance is the earliest missing global fact.  This realization does show
  that simplicity and the degree constraints alone do not manufacture the
  Type B destination record.

### Branch-routing test

- **Explicit data:** Retain exactly the yes-arm record
  ((\epsilon,J,z)) with (z\in J), (d_G(z)\ge4), all neighbours cubic,
  and the two simple opposite corridor tails.  Compare it field by field with
  a destination record ((Y,H,(K_h),(A_{h,a}),\rho_\partial)) satisfying
  `def:decorated-fan-envelope` and the assigned/grouped Type B ledger.
- **Hypotheses satisfied:** Every proposition asserted by the literal node
  predicate and by node [10] is present.  The actual Lean
  `AbsorbedGermFanEnvelopeWitness` proves precisely this high-corridor record.
- **Accumulated facts violated:** None.  The missing common-port response
  family, surviving separator, counted core, terminal-in-core arms, boundary
  response profile, and transfer identity are not accumulated facts.
- **Applicability:** Applicable to the proof-flow contract.  The source record
  does not inhabit the manuscript's destination type.  Lean makes this visible
  by defining `TypeBFanEntryStatement` as the disjunction of an actual
  `TypeBFanSupportWith` and the special
  `AbsorbedGermFanEnvelopeStatement`, rather than constructing
  `Graph.DecoratedHandoff.Envelope` from the cold corridor.

## 5. Strongest valid counterexample

No explicit graph was found that reaches the complete minimal-counterexample
residual; constructing one would be a counterexample search for the main
theorem.  The strongest valid adversarial object is instead the exact routing
record implemented for the yes-arm: a selected bounded germ, a high centre in
its support, cubic neighbours, two distinct corridor incidences, and two
simple fan-safe geometric tails ending in the packed-window union.  It
satisfies every field that node [175] proves, including the node-[10] normal
form, but contains no counted remainder core, common-port declared-response
family, surviving-separator proof, or grouped charge transfer.  The repository
formalization treats this record as a separate Type B-entry disjunct, which is
direct evidence that it is not the manuscript envelope cited by the routing
sentence.  Thus the surviving candidate is a destination-contract
counterexample, not a target-free graph counterexample.

## 6. Local repair

### Corrected statement

Replace the operative yes-arm of `lem:absorbed-germ-fan-data` by:

> Let (epsilon) be an actual selected branch-excess half-edge with retained
> return corridor and first-failure support (J).  Exactly one of
> (J\cap V_{\ge4}(G)=\varnothing) and
> (J\cap V_{\ge4}(G)\ne\varnothing) holds.  In the first case the retained
> germ is subcubic and belongs to the extracted candidate family.  In the
> second case choose the first (z\in J\cap V_{\ge4}(G)) in the canonical
> corridor order.  Then every neighbour of (z) is cubic and the corridor
> supplies two distinct simple tails at (z); call this the high-corridor
> datum.  This datum enters Type B only if it is accompanied by an actual
> declared (F4) decorated handoff envelope, including its counted remainder
> core and transfer record.  Otherwise the retained first failure is the
> graph-realized (F5) bounded configuration and is routed to node [176].

This keeps the high-corridor geometry without identifying it with a Type A
exit-(7) separator.

### Complete local proof

Since (J) is finite, its intersection with (V_{\ge4}(G)) is either empty
or nonempty, and the alternatives are exclusive.  If it is empty, every
ambient degree on (J) is at most three.  Hence the retained incidence passes
the literal subcubic filter defining the cold candidate family, and its actual
first-failure record continues to [176].

If the intersection is nonempty, choose its first member (z) in the fixed
corridor order.  For each (u\in N_G(z)), high-degree independence gives
(d_G(u)<4), while minimum degree gives (d_G(u)\ge3); therefore
(d_G(u)=3).  The retained corridor is simple.  At an internal occurrence of
(z), its predecessor and successor are distinct; at a one-vertex foot, the
entry and successor boundary stubs are distinct.  Splitting the corridor at
(z) therefore yields two simple tails through distinct neighbours.  This
proves exactly the high-corridor datum.

Now inspect the retained first-failure tag.  If it is (F4), its definition
already includes entry into a *declared* Type B handoff envelope or route-8
support.  Retain that actual envelope record and use the existing destination.
If it is not (F4), the surviving branch has already excluded (F1)--(F3), so
the first-failure dichotomy makes it (F5).  The complete bounded support, its
two same-interface representatives, boundary-degree profile, window labels,
and exact response record are therefore available, regardless of whether its
support contains (z).  The statements
`lem:cold-bounded-germ-trichotomy`, `lem:cold-same-interface-table`,
`lem:neutral-germ-symmetry`, `lem:refined-minimality-swap`,
`lem:two-strand-check`, and `lem:symmetric-pair-endpoint` do not assume that
the bounded support is subcubic; subcubicity is used only for the many-germ
overlap count.  Thus this individual graph-realized (F5) datum follows the
existing node-[176] closure.  Every arm is assigned without manufacturing a
Type B envelope.

### Counterexample disposition

The sharp local support (p-z-q) is classified as high-corridor data.  It goes
to Type B only if a separately retained (F4) envelope supplies a core (Y),
declared arms and response profile, and the transfer record.  Otherwise its
actual (F5) germ goes to [176].  The concrete cubic-gadget completion remains
non-applicable as a theorem counterexample because node [2]'s target avoidance
was not verified.

### Graph patch

Replace the unconditional high-degree handoff by the typed subdiamond

```text
[174 with actual epsilon, corridor, and J]
  -> [175: J intersects V_{>=4}?]
     -- no  --> [176: retained subcubic graph-realized F5 germ]
     -- yes --> [175a: high-corridor datum; declared F4 envelope present?]
                  -- yes --> [177] --> [65: retain full envelope/core/transfer]
                  -- no  --> [176: retained graph-realized F5 germ]
```

The `[175a] -- yes` edge must carry the literal
`DecoratedHandoff.Envelope` (or the manuscript-equivalent record), not merely
the high centre and two tails.  The `[175a] -- no` edge retains the bounded
germ and all (F5) cut-state data.  If the intended strategy is instead to keep
the Lean-only special Type B lane, it must be drawn and defined as a distinct
destination and supplied with a proved charge/no-overcount theorem; it cannot
be called the existing decorated envelope by fiat.

### Downstream impact

Synchronize the Part-V node [175]/[177] labels and caption, overview row 52,
the dependency/constraint-ledger occurrence of
`lem:absorbed-germ-fan-data`, its proof, and `rem:no-sufficient-order`.  At Type
B, audit node [65], `def:typeB-assigned-ledger`, the decorated-envelope
grouping/no-double-count identity, `def:typeB-residual-mass`, and every
[67]--[85] consumer to ensure that only actual assigned supports or genuine
envelopes enter their charge sums.  In Lean, either route the non-(F4) cold
bounded germ to the existing [176] facts or prove that the special
`AbsorbedGermFanEnvelopeStatement` is converted to the full manuscript
envelope and its transfer identity.  The present tagged disjunction must not
be cited as fidelity evidence for that missing conversion.

## 7. Regression audit

The audit inspected:

- the Part-V diagram, caption, small-order repair subsection, overview row 52,
  and constraint-ledger row for [175]--[177];
- the full definitions/statements/proofs of
  `def:cold-corridor-first-failure`, `lem:cold-corridor-first-failure`,
  `def:cold-bounded-germ`, `lem:cold-germ-extraction`,
  `lem:cold-bounded-germ-trichotomy`, `lem:cold-same-interface-table`, and
  `lem:absorbed-germ-fan-data`;
- `def:typeA-continuation-classes`, `lem:typeA-cubic-switch-absorption`,
  `lem:typeA-high-degree-handoff`, `def:typeB-fan-safe`,
  `def:decorated-fan-envelope`, `lem:decorated-fan-admissibility`,
  `def:typeB-assigned-ledger`, and `def:typeB-residual-mass`;
- the proof-flow edges `[174] -> [175]`, `[175] -- no --> [176]`, and
  `[175] -- yes --> [177]`, plus the continuation of [177] to Type B [65];
- Lean's `AbsorbedGermSplitStatement`, `AbsorbedGermFanDataStatement`,
  `AbsorbedGermFanEnvelopeWitness`, `AbsorbedGermFanEnvelopeStatement`,
  `TypeBAssignedCentres`, `TypeBFanEntryStatement`,
  `absorbedGermSplitRow`, `absorbedGermFanEnvelopeRow`, and
  `selectedAbsorbedGermResidual` on the literal current object;
- `Assembly_node_audit.md` and the dossier's Lean locator as navigation aids,
  followed by inspection of the cited declarations rather than reliance on
  their status prose.

Search patterns included

```text
rg -n 'absorbed-germ-fan-data|absorbed.*fan|corridor.*Type B|decorated handoff|grouped decorated|typeB-assigned-ledger|typeB-residual-mass' to_formalize/erdos_64_proof.tex
rg -n 'AbsorbedGermSplitStatement|AbsorbedGermFanDataStatement|AbsorbedGermFanEnvelopeWitness|AbsorbedGermFanEnvelopeStatement|TypeBFanEntryStatement|absorbedGermFanEnvelopeRow|selectedAbsorbedGermResidual' hypostructure proofs
rg -n '\[175\]|absorbedGermSplit|absorbedGermFanEnvelope' Assembly_node_audit.md
```

Negative searches found no manuscript declaration converting a cold
high-corridor datum into a counted remainder core, no proof that its two
opposite halves are declared responses through one completion port, no
surviving-first-separator test on this route, and no transfer/no-double-count
identity assigning these cold half-edges to grouped Type A exit-(7) envelopes.
All manuscript occurrences of the special cold handoff point back to
`lem:absorbed-germ-fan-data`; the full decorated-envelope construction is
otherwise explicitly tied to Type A exit (7).

## 8. Residual uncertainty

No finite graph satisfying every accumulated target-avoidance, minimality,
canonical-packing, and branch-selection fact was constructed; the local
(p-z-q) realization is therefore not a counterexample to the theorem.  I did
not re-audit the mathematical correctness of the entire node-[176] closure,
only that its cited bounded-configuration statements do not require
subcubicity.  I also did not prove a downstream charge theorem for Lean's
special absorbed-germ Type B disjunct or kernel-build the current Lean tree;
that disjunct records the contract divergence but might be the start of a
different, explicitly stated repair.  The exact existence of an eligible
(epsilon) before node [175] is an incoming-node issue and was not adjudicated
here.  No manuscript, proof-flow, Lean, diagram, audit-source, or coverage
ledger file was changed.
