# The first missing construction at [172a]

## Result

The branch is **not closed**. The first missing label is
`lem:barrier-failure-overlap`, not the later serial arithmetic. The live graph
now ends at [172a]. The proposed [172b] and [172c] are not established
continuations and have been removed from the live diagram, while their proposed
mathematics remains in the manuscript.

The current [171] finite graph-count induction is valid under its explicit
uniform conditional graph-count hypotheses. The manuscript now states those
hypotheses and gives the same finite-prefix argument. This does not prove that
the hypotheses follow from blockedness or from the selected residual.

## Exact incoming state and required output

Retain the unchanged selected graph G, its minimum-degree baseline, global
target avoidance, refined minimality, maximum packing P, near-cubic budget,
the dense package overflow, the selected hot/cold branch, bridgelessness,
the actual cold corridors and first-failure records, and the universal
neutral canonical-replacement equality Q = E. The two actual call sites of
`selectedCanonicalReplacementContinuation` pass their existing ExactLedger
through [165], [166], [169] and the [170] decision. No history is reset.

The additional negative-arm fact is `BlockedBarrierFailureStatement`:

- every coordinate retains the unconditional state-value bound F + 1 and
  graph-fibre monotonicity;
- there is a least failed exposure coordinate c;
- every earlier coordinate satisfies its relative graph-count inequality;
- there is a member H0 of B(P) selecting an outside record d and prior prefix q
  for which

  `F_c * |A(d,q,c)| < W_c * |S(d,q,c)|`.

Here A is the a-priori near-cubic **graph** fibre and S its surviving subfamily.
H0 need not equal G. Neither global target avoidance nor refined minimality is
part of membership in B(P).

The missing geometric implication, with all indices retained, is:

> For every selected residual (G,P,ledger) on this arm, its failed coordinate
> c = (P0,j,a,b), and failed fibre (H0,d,q), construct a nonempty family
> U ⊆ P and actual completion supports realizing a cardinality-minimal barrier
> obstruction at that fixed scale, with connected union, in the graph/domain
> required by the subsequent uncrossing step. In the manuscript's state-value
> formulation, for every ordering of U there must be a reached nonempty prefix
> at which more than F_(a,b) next-state values occur; every proper nonempty
> subfamily must admit an ordering satisfying the bound at every reached
> prefix. Any use of selected-graph exclusions on a comparison graph requires
> a proved transport.

No executor constructs this output. `blockedBarrierOverlap` is a historical
key name for the failed ratio, not a theorem asserting intersecting paths.
This is a mathematical construction gap, not a missing publication or wiring
of an existing overlap theorem.

## A kernel-checked obstruction in the actual code

`BarrierSystem.code` tests scale `2 ^ coordinate.scale`, beginning at scale 1.
Every registered barrier has positive left and right lengths. A completion
support requires

`left + right + completion.length = scale`.

If `scale < left + right`, no such support exists, in any graph. The actual
`barrierState` is therefore `none`. The actual `IsBlockedSurvivingState`
accepts `none`, so S = A. A reached fibre is nonempty because it contains the
blocked member selecting its record and prefix. Consequently F < W implies
`F * |A| < W * |S|`, despite the absence of any completion support.

`Hypostructure/Fixtures/BlockedFibreAbsentCompletion.lean` kernel-checks this
argument against the actual code and the actual conditional-fibre definitions.
It contains no sorry, axiom, selected-fact producer, or replacement closure.
The registered (1,1) row has W = 543958 and F = 111286; the generated table has
F < W at every accepted row. Thus the first scale can produce a failure
before any graph geometry has been tested.

## The supplied graph gives an all-scale obstruction

Reference: edo, *A counterexample to the blocked-class bound as stated*,
20 September 2026, supplied as `blocked_class_note.pdf`. Both pages were read.
The note expressly concerns the counting class, not the full selected residual.

The independent check in `checks/blocked_class_obstruction.py` reproduces the
66 vertices, 99 edges, cubic degrees, 15 bridges, 208 unoriented induced P13
paths, and maximum packing one. Every such path uses two central-triangle
vertices. An induced path using at most one has at most 12 vertices.

There is additional useful structure. For the displayed window P, the
components of H − P have the following sizes and numbers of vertices adjacent
to P:

| Component size | Vertices adjacent to P | Multiplicity |
| --- | --- | --- |
| 5 | 1 | 1 |
| 6 | 1 | 6 |
| 12 | 2 | 1 |

A `CompletionSupport` has positive outside arms from source to middle and
middle to target, with simple concatenation. Hence source, middle and target
are three **distinct** vertices in one outside component. All three must be
adjacent to P. The table excludes this, independently of the scale or the
proposed closing walk.

This certificate uses only outside edges and window incidences, all of which
are fixed by `outsideEdges`. It therefore excludes supports for **every**
a-priori graph with this outside record, even if its internal window edges
are changed. This whole fibre has state `none` at every barrier and scale;
all its later prefixes remain the same, and S = A throughout. Relabelled
disjoint copies preserve the certificate for each window of H_p.

Thus deleting the initial bounded scales does not repair the graph-count-to-
overlap implication on the explicitly defined class. This is an explicit
absent-support obstruction, not an overlapping-path obstruction.

## Separate multiplicity obstruction

The Lean fixture also checks a finite comparison model with three objects,
both of two state values realized, and one surviving value. Two objects have
that value. There is no absent-completion state, and the state-value ratio is
1/2, but the graph/object ratio is 2/3. This only refutes the proposed counting
inference; it is not claimed to be a graph satisfying the selected residual.

Accordingly, removing `none` or assuming all supports present would still
require a graph-fibre counting or switching argument. The finite label table
alone cannot supply one.

## Repair attempts and their first failed obligations

| Attempt | Retained structure used | First failed obligation |
| --- | --- | --- |
| Omit bounded scales | Dyadic exposure order and exact package count | Removes the scale-1 artefact but not the all-scale outside-component certificate; the exact finite package budget would also need recalculation. |
| Add `none` to both table counts | Honest F+1 auxiliary carrier | An all-absent fibre still has ratio one, greater than (F+1)/(W+1) when F<W. It supplies no positive saving. |
| Extract minimal intersecting supports | First failed ratio, all earlier successful ratios | Actual supports need not exist. Cardinality-minimizing a nonempty family is unavailable before existence is proved. |
| Use bridgelessness | Actual return path at each selected oriented edge | Supplies neither the prescribed two arm lengths nor three outside incidences at a common window; it also does not apply to an arbitrary comparison member H0. |
| Use Q = E and replacement minimality | Actual neutral germs of G and their exact response equivalences | No germ in G, distinct representative, or strict decrease is supplied by excess graph multiplicity in H0's fibre. |
| Restrict the class to selected survivors | Global avoidance and no-exit facts | This changes the counting domain. Membership of G would hold, but the new fibre ratios still require a proof; retaining the same F/W factors is unjustified. |
| Fix the outside record of G | A local comparison class containing G | Avoids unrelated outside records but does not prove conditional multiplicity bounds or existence of supports. It is not the existing whole-class [171] theorem. |
| Split on the desired overlap conclusion | Classical exhaustive decision | Its negative arm adds no constructed geometry or proved decreasing measure. This would move the open obligation, not close it. |

No attempt above is installed as a proved reduction. In particular, no
missing graph witness is supplied by a callback, a new assumption, a detached
theorem, or a renamed residual.

## What a successful next construction must do

The comparison must first be localized or related to the selected graph by an
explicit transport. It must account for absent supports and actual graph
multiplicities. A switching construction would have to preserve the counted
vertex set, edge count, minimum degree, window conditions and fixed earlier
record, and prove the required multiplicity bounds. Failure of that concrete
construction would then have to produce an actual selected-graph obstruction
with an existing consumer, or a strictly decreasing residual. None of these
obligations is supplied by the bare strict ratio.

That is the remaining construction queue, not a claim that an eventual
completion is guaranteed. The successful conditional counting arm remains
available; the other arm remains an honest leaf.

## Resumed construction under the execution recipe

The first pass stopped at diagnosis and presentation repair. That did not
complete the requested closure. The resumed attempt uses the local source of
the linked recipe, `web/frontend/src/methodology/ExecutionRecipe.tsx`, in
particular its branch inventory, prerequisite checks, first-failure repair,
and requirement to construct every consumer's witnesses.

### A second obstruction: minimal state-count obstructions are singletons

Fix the current fibre X, including its outside record and already exposed
prefix. Write X_i for the image of coordinate i. If |X_i| ≤ F for every i in
U, then after conditioning on any earlier coordinates the image at i is a
subset of X_i and still has size at most F. Every ordering of U therefore
works in the sense of `def:barrier-overlap-system`.

Consequently any non-good family U contains an i with |X_i| > F. The
singleton {i} is already non-good: its first exposure has no additional
conditioning. If U is cardinality-minimal, U = {i}. The argument also covers
empty fibres, which cannot produce a non-good family.

`Hypostructure/Fixtures/BlockedOverlapMinimality.lean` proves this for an
arbitrary finite fibre, using an injective rank to represent the ordering and
the exact image of each reached conditional fibre. It is an anonymous
diagnostic example, not a selected-fact producer. Thus the present definition
cannot deliver a dependency among several windows, even after support
existence has been supplied. This is a distinct issue from missing supports.

### Construction inventory and tested repairs

| Retained object / observable | Construction attempted | Exact outcome and consumer check |
| --- | --- | --- |
| Actual cold germs of G and universal Q = E | Construct a different context-equivalent representative and apply refined minimality | The existing statement supplies equality only after `NeutralEqualLengthTerminalConfigurationAt` is established for that representative. It does not construct a different representative. Reusing the source itself preserves the context but gives no strict decrease. No new compression was proved. |
| First failed graph fibre, all earlier successful bounds | Extract a minimal family violating the displayed next-state cardinality condition | The proved argument above forces that family to be a singleton. It cannot provide the several-window intersections required by the proposed serial construction. |
| Joint counting discrepancy | Replace next-state cardinality by a failure of multiplication of individual survival fractions | This can describe genuine multi-coordinate dependence, but dependence of assignments does not yet produce graph intersections. The finite example below rules out that inference without a factorization theorem. |
| Bridgeless G and its actual return corridors | Use the retained returns as the arms of a completion | A return gives two boundary incidences. The completion requires three distinct vertices incident to the same root window, prescribed positive arm lengths, a simple concatenation, and the tested closing length. No construction of those fields from the retained returns was obtained. The comparison member H0 still cannot replace G. |

For the tested joint-count repair, take the realization domain
X = {(0,0),(1,1)}. Testing either coordinate for value 0 individually retains
exactly half of X; testing both still retains half, exceeding the proposed
one-quarter product. Both one-coordinate distributions are uniform; there
are no absent states. The same Lean fixture verifies the exact counts.
Correlation is already present in the realization domain, without an
intersection between the two coordinate sets. A geometric argument must
therefore prove factorization in the actual counted graph domain, rather
than infer it from the names of the coordinates or the marginal table.

These are proved checks of proposed constructions, not an admitted reduction.
No new split is installed: none of the tested replacements has consumers for
all its outcomes. The open construction queue remains: build an actual
selected-graph obstruction or a strictly decreasing replacement using the
retained geometry, with a corrected notion of dependence and all context and
degree preservation proved. This resumed attempt has not discharged it.

## Validation

- Canonical ExactLedger/ExactExecution positive and negative fixtures: passed.
- Actual-code absent-completion and unequal-multiplicity Lean examples: passed.
- Minimal state-count obstructions are singletons, and the uniform-marginal
  correlation example: kernel checked in `BlockedOverlapMinimality.lean`.
- `BlockedCompressionRows.lean`: independently rechecked successfully.
- Explicit 66-vertex graph and outside-component certificate: passed.
- The live graph has no outgoing edge from any open node; [172b] and [172c]
  are not live nodes. The regression test enforces this property.
- Graph extraction: 66 tests passed. App proof views: 53 tests passed.
  Frontend type checking passed.
- The manuscript PDF rebuilt successfully; the changed diagram and mathematical
  pages were visually inspected. The local app PDF and page map were updated.

The repository-wide API check was already blocked before edits by the missing
`ColdCorridorRows.olean` required by `Canonical.WebExport`. The final rerun
completed its export but reported a stale `allowed-api.md` catalog. No
production API was added in this repair, and the catalog was not refreshed to
accept unrelated changes. The audit-table check still reports the pre-existing
extra `cor:conditional-conjecture` row. Neither failure is reported as a
successful global validation or repaired by altering unrelated work.
