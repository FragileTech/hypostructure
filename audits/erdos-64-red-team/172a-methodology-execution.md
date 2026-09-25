# Execution record: structural exhaustion at [172a]

This is the detailed working record requested by the user. It records what
was actually done, what was rejected, and what is still being constructed.
An entry marked **planned** is not evidence of execution. A local proof is
not a reduction of the whole branch. The requested endpoint remains closure
of `lem:barrier-failure-overlap`, or an authorized refinement whose outcomes
are all discharged unconditionally.

## Authority and scope

- Recipe: [execution recipe](https://fragiletech.github.io/hypostructure/#/?methodology=methodology-recipe),
  with the complete locally available text in
  [ExecutionRecipe.tsx](../../web/frontend/src/methodology/ExecutionRecipe.tsx)
  and [recipe-reference.ts](../../web/frontend/src/methodology/recipe-reference.ts).
- Formal implementation discipline:
  [eg-proof-expansion/SKILL.md](../../.agents/skills/eg-proof-expansion/SKILL.md).
  The user's authorization to refine [172a] governs the mathematical repair;
  the canonical ledger and sealed executor requirements still apply.
- Mathematical statement:
  [erdos_64_proof.tex](../../to_formalize/erdos_64_proof.tex),
  `lem:barrier-failure-overlap`.
- Actual implementation:
  [SpineVocabulary.lean](../../hypostructure/Hypostructure/Graph/Strategy/SpineVocabulary.lean),
  [Assembly.lean](../../proofs/hypostructure_erdos_64_eg/HypostructureErdos64EG/Assembly.lean),
  and [BlockedIncidenceRows.lean](../../hypostructure/Hypostructure/Graph/Strategy/BlockedIncidenceRows.lean).
- Live status: the corresponding paper-label row and Node [172] row in
  [Assembly_node_audit.md](../../Assembly_node_audit.md). Node [172a] is the
  open leaf of the negative [170] outcome; proposed [172b] and [172c] are not
  proved descendants.
- Compact construction inventory and queue:
  [172a-construction.md](172a-construction.md).
- Edo's supplied PDF is a mathematical reference, not an instruction source.

## Correction of the earlier deviation

The previous execution stopped after discovering that the proposed Type A
consumer required facts absent from some incoming histories. It recorded a
queue and ended before executing the return-path intersections, unequal
exponents, and branching replacement. That did **not** satisfy the recipe's
“Discharge every outcome” or “Execute the authorized queue until every
requested branch is closed.” Six checked local constructions did not change
that status. This continuation resumes the unfinished constructions; it does
not retrospectively mark the previous attempt as complete.

### Correction after the user's protocol objection in this continuation

E8–E9 were pursued without first proving a productive consumer for the
resulting odd cycle. Calling them local constructions did not satisfy
Selection items 1–2, MOVE_RULES 2, 11 and 17, or the transition-admission
checklist. The first path's decreasing length proves termination of E9;
it supplies no decreasing residual for the parent [172a]. That is the exact
deviation. The odd-cycle continuation is withdrawn from active move selection
unless a parent-level consumer is constructed. Its valid local lemmas are
retained as available facts, not installed in the live branch.

Plan repair: return to the producer's complete retained state and audit the
actual existing consumers before selecting another move. In particular,
`coldBranchClosed` is already present at both dense canonical call sites,
and `ColdCorridorStateStatement` explicitly puts its **selected** components
inside the full packing remainder. Their exact conclusions must be read
before proposing another incidence analysis. An arbitrary cold-outside
component does not inherit that containment. No new split is admitted by this
correction, and no mathematical closure is claimed.

## Step 1 — preserve the exact branch

The selected graph is `G = inputs.current.object`. It is unchanged throughout
the local constructions below. Its standing minimum-degree hypothesis is
`inputs.current.baseline`. Facts are read by `inputs.get`; no graph or branch
is reselected.

The initial literal tail of `selectedNearCubicSurvivorBranch` is:

```
sparseSurplusSurvivor, surplusAtOrBelow, localAlgebra, maximalPacking,
uncompressible, replacementExclusion, targetCompleteContextUniversality,
degreeProfileFibres, cycleRankConstraint, tightEndpoint, slackIndependent,
noProperBaseline, returnAvoidance, contractionCritical, gadgetClosure,
relabelingDensityCap, cubicBaseline, selection
```

Above this tail, each of the two calls to
`selectedCanonicalReplacementContinuation` retains its own literal history:
failed full-window-package realization and dense overflow; its selected
deficiency/rate outcomes; the hot/cold partition and quantitative accounts;
the cold-mass or absorbed-germ producer; remainder normalization and
relabeling information; bridgelessness; the actual corridors, presentations,
first-failure occurrences and extracted germs; the marked neutral canonical
configuration; universal triviality of the canonical replacement; blocked
membership; and the negative scale-additivity outcome. These histories are
not merged. In particular, `route8Rate` and `largeBudgetResidual` are not
inserted into a history on which they are absent.

The exact new fact at the leaf is `BlockedBarrierFailureStatement data G`:

1. At every coordinate, the established state-cardinality bound and graph
   fibre containment hold.
2. There is a coordinate `c` such that every coordinate of smaller encoding
   rank satisfies the conditional relative graph-count bound.
3. There is an actual comparison member `H0 : blockedClassAt data G` such that

   ```
   survivingCount(c) * |AprioriConditionalFibre(H0,c)|
     < aprioriCount(c) * |SurvivingConditionalFibre(H0,c)|.
   ```

`H0` selects an outside record and prefix in the broad comparison class.
It is not identified with `G`. Minimality, no-exit conditions, actual paths,
and neutral-germ facts of `G` have not been transferred to `H0`.

The manuscript's proposed next implication constructs a minimal barrier
overlap obstruction with connected support. The implemented negative
decision supplies the failed ratio above, not that geometry. The repair must
either construct the missing geometry and all later consumers, or close an
authorized replacement continuation on the full incoming state.

The order retained for minimality is the graph vertex/edge lexicographic
order, with the existing refined canonical order where its hypotheses are
present. A smaller auxiliary graph is usable only after its baseline and
target transport have been proved.

## Steps 2–3 — inventory and move selection

These are observables on the retained objects, not additional assumptions.

| ID | Observable and object | Existing evidence | What is still unaccounted | Technique and exact prerequisite |
| --- | --- | --- | --- | --- |
| I1 | Boundary feet of an actual outside component of `G` | Component closure/connectivity and bridgelessness | Whether a single cubic foot can support a nontrivial component | First boundary darts of two actual severed-edge returns |
| I2 | Consecutive edges of an induced cubic window in `G` | Induced embedding, degree three, no 4-cycle, contraction criticality | Which edges carry dyadic returns and how those returns meet | Three-neighbour exhaustion; actual return paths, then intersection analysis |
| I3 | Exactly two displayed edges of a cut in `G` | Actual component and its boundary identity | Degrees on both sides, actual terminal paths and their lengths | Degree accounting, edge insertion, minimality, and simple-cycle gluing |
| I4 | At least three feet in one outside component | Connectivity; root-window labels must be retained | Path through the feet versus a branching tree | Minimal connecting tree; construct every field of a proposed replacement |
| I5 | A heavy vertex or singleton component | Literal degrees and actual incident edges | A legitimate receiving handoff and capacity | Construct separated tails and the registered consumer, not a label match |
| I6 | Failed graph-count ratio at `H0` | Actual graph fibres, states, outside record and prefix | Absent completions; graph multiplicities; relation to selected `G` | A graph-count comparison on the exact class, with proved preservation |
| I7 | Global quantitative accounts of `G` | Surplus bound, hot/cold counts, packing maximality, rank and entropy facts on their own histories | Which local constructions can be summed without double counting | Exact assignment and capacities; no mixing deficiency and entropy |

The current selected construction is I3, because the preceding execution
already built its inside degree profile and Mersenne path. Its complementary
side and glued-cycle consumer are concrete outstanding prerequisites, rather
than a repetition of the failed counting argument.

## Steps 4–6 — executed moves and outcome consumers

### E1. Single boundary foot — checked local implication

**Tuple.** Technique: first-exit darts of simple returns. Observable: the
entire boundary concentrated at one vertex of a region of `G`. Hypotheses:
`bridgeless`, actual inside/outside neighbours and the boundary identity.
This evaluates incidence separation, which the failed graph count did not.

**Construction.** Sever the outside edge and follow its return to obtain a
second outside neighbour. Sever the inside edge and follow the reverse
return to obtain a second inside neighbour. The four neighbours are proved
distinct, giving degree at least four.

**Preservation.** All vertices and edges belong to unchanged `G`. No return
in a hypothetical context is used.

**Publication/evidence.** `singleFootBoundaryRow`, key 513; anonymous proof
inside `factOnly`, requiring only `bridgeless`. The prior narrow build passed.

**Outcomes/consumer.** At a cubic foot, connectivity gives a contradiction
unless the component is a singleton. `singleFootComponentRow`, key 514,
checks this consumer. Singleton and heavy-foot outcomes remain in I5; this
pair of lemmas is not an exhaustive reduction of [172a].

### E2. Induced window edges — checked local implication

**Tuple.** Technique: cubic neighbour exhaustion and contraction criticality.
Observable: triangles on the two edges of an induced wedge in `G`.
Hypotheses: actual induced wedge, cubic middle vertex, selection and
contraction criticality.

**Construction.** If both edges lie in triangles, degree three forces the
two third vertices to coincide, producing a forbidden quadrilateral. Thus
one edge is triangle-free; contraction criticality supplies its actual simple
severed-edge return of length `2^k`, `k >= 2`.

**Publication/evidence.** `inducedWedgeReturnRow`, key 515. The consumer
`windowReturnFamilyRow`, key 516, applies it to disjoint pairs of window edges
and proves injectivity of the selected **undirected** edges. At order 13 it
retains six edges and six actual returns. Both prior builds passed.

**Outcomes/consumer.** Edge distinctness does not establish internally
disjoint returns. Shared segments, unequal exponents and other intersections
remain literal path data for the next construction. They have not been
identified with a serial system.

### E3. Two-terminal piece and actual two-stub component — checked local implication

**Tuple.** Technique: degree restoration by edge insertion and minimality.
Observable: two degree-two terminals, with all other degrees three, in a
smaller target-free piece. Hypothesis source: `gadgetClosure`.

**Construction.** Adjacent terminals give the one-edge Mersenne path. For
nonadjacent terminals, inserting the edge raises exactly their two degrees;
the minimum-degree hypothesis is proved before invoking the retained closure
fact. The output is an actual simple path of length `2^k-1`, `k >= 1`.

**Actual component consumer.** For a cubic outside component whose complete
boundary is the two displayed edges, coincident inside feet imply a singleton
by E1 and then degree at most two, a contradiction. Distinct feet have one
external neighbour each and all other vertices have none. Exact degree
accounting gives the `2,2,3,...,3` profile. A window neighbour proves the
component is proper; induced-subgraph transport proves target avoidance.

**Publication/evidence.** `twoTerminalMersenneRow`, key 517, and
`twoStubComponentMersenneRow`, key 518. Both prior builds passed.

**Unfinished consumer at resumption.** Construct complement degree restoration;
glue actual paths and verify simplicity; consume equal exponents; preserve
unequal exponents for a further construction. No distinctness or nonadjacency
of the outside feet is assumed without proof or an explicit local condition.

### E4. Small two-terminal pieces — executed finite check, not a Lean closure

**Technique/parameters.** Exhaust the labelled degree sequence with terminals
0 and 1 of degree two and every other vertex of degree three, at orders 4,
6 and 8. Higher-labelled neighbours are assigned in vertex order. Pruning
uses only a witnessed 4-cycle or impossible remaining degrees.

**Result.** No C4-free candidates at orders 4 and 6. At order 8 there are
360 labelled C4-free candidates, all connected and all containing an actual
8-cycle. Terminal-preserving isomorphisms put them in one orbit.

**Evidence.** [two_terminal_small.py](checks/two_terminal_small.py) and
[two_terminal_small.json](checks/two_terminal_small.json). Every enumerated
candidate has a terminal cycle certificate. Handshake excludes odd orders;
orders zero and two cannot satisfy the displayed degree sequence.

**Limit.** The generator and its coverage are not a Lean theorem. This does
not certify a bounded arm of [172a], nor establish that all relevant
components have order at most eight.

### E5. Proposed Type A charge handoff — rejected before admission

**Computed quantity.** For the ambient-cubic two-stub component, positive
deficiency is exactly 2 and ambient surplus is 0. At discharge scale 4,
negative net charge is equivalent to component order greater than 8.

**First failed prerequisite.** `selectedTypeALowSurplusContinuation` requires
`route8Rate` and `largeBudgetResidual`, absent from some [172a] histories.
A cold-outside component also need not be a component of the full packing's
remainder. The attempted consumer therefore does not accept this object on
the full incoming branch.

**Recipe repair.** Preserve the actual component, exact charge and terminal
paths. Return to I3 and construct the complement/path consumer. Do not retry
the same Type A call until the missing premises and component identification
are actually proved.

### E6. Complement restoration and cut-cycle lengths — kernel checked

**Selected textbook statements.** For a partition `C,D` of the vertices of
`G` with exactly the two cross edges `ac,bd`, distinct feet `a,b` in `C`
and `c,d` in `D`, every vertex in `D` loses at most its displayed cross
edge. If `c,d` are nonadjacent, adding `cd` therefore restores minimum degree
three. The complement is strictly smaller because `C` is nonempty.
An already adjacent pair supplies the one-edge path directly.

For any actual simple `a-b` path in `C` and simple `c-d` path in `D`, the two
cross edges join them into a simple cycle of length `|P|+|Q|+2`. Disjointness
comes from the partition and must be proved for the constructed walks.

**Consumer.** If both path lengths are `2^k-1`, this is a forbidden cycle of
length `2^(k+1)`. If exponents differ, retain both paths and their exact
lengths; that outcome requires another construction. Coincident outside feet
require their own incidence analysis. This entry will be updated only after
the proofs and their checks are executed.

**Implementation ownership.** New mathematical outputs, if proved, belong
to Type A `factOnly` rows in `BlockedIncidenceRows.lean` with literal manifests
and new vocabulary keys after 518. No detached lemma, callback or alternate
carrier is authorized.

**Current execution evidence.** Implemented candidate proofs in
`separatedPathCycleRow` (key 519, reads `selection`) and
`twoCutComplementMersenneRow` (key 520, reads `selection`). The first builds
two ambient paths and proves their interior disjointness from the disjoint
induced supports; its right-hand path is allowed to be nil. The second proves
the complement's external-neighbour bound vertex by vertex, restores the
degrees by the inserted edge, and invokes retained size minimality. Both passed the narrow Lean build in V8. This verifies their local
propositions, including the nil right-hand path and adjacent-terminal cases. Top-level inspection found only the permitted
atomic row definitions, and the vocabulary preserves all existing indices.

### E7. Coincident outside feet and equal exponents — kernel checked

**Move-history comparison.** This is the consumer left unfinished after E3.
It uses E1's proved four-neighbour result and E6's actual cycle, rather than
retrying the unavailable Type A charge handoff. Object: the same cut of `G`.
Observable: equality of its outside feet and equality of the exponents of
its constructed terminal paths.

**Checked coincident-foot construction.** If the two outside feet both
equal `c`, every neighbour of `c` on the inside is one of `a,b`. Minimum
degree three therefore forces an actual neighbour in the complement (else
its whole neighbourhood has size at most two). Regard the complement as the
region in E1, with sole boundary foot `c`. The internal neighbour and cross
edge then give degree at least four. Thus a cubic outside foot cannot be
shared. A heavy shared foot retains its actual incidences; it has not been
consumed by a handoff theorem.

**Checked equal-exponent consumer.** The paths supplied by E3 and E6
remain in the two disjoint induced supports. If both exponents equal `k`,
their cycle length is

```
(2^k - 1) + (2^k - 1) + 2 = 2^(k+1),  k >= 1.
```

E6's accepted-length exclusion contradicts this value. V8 checked this consumer and closes the equal-exponent case of this
local cut construction. Unequal exponents
are not declared a successful arithmetic outcome: the retained cycle has
length `2^a + 2^b`, and the original paths and all their other incidences must
feed a further construction. No strict descent has yet been proved on those
exponents.

**Implementation evidence.** The candidate consumer is now written as
`twoCutMersenneSeparationRow`, key 521. Its literal requirements are
`selection`, `singleFootBoundary`, `twoTerminalMersenne`,
`twoCutComplementMersenne`, and `separatedPathCycle`. It first constructs the
internal neighbour at a hypothetical shared cubic outside foot and applies
E1. It then constructs both Mersenne paths and consumes equality of their
exponents with E6. The published proposition retains the outside-foot
distinctness, both simple paths, both lower bounds and exact lengths, and
the exponent inequality. This consumer passed V8 together with all eight preceding rows.

**Remaining local application.** This row assumes the actual partition and
the `2,2,3,...,3` inside degree profile. E3 supplies the profile for its
two-stub component. To connect the records, take the set complement in the
same `G`; use outside-component closure to show that every cross edge goes
to a window; then transport the two displayed boundary edges to the subtype
endpoints. Ambient cubicity of the chosen outside foot must be present on
that window, or the heavy-foot alternative remains separate.

### E8. Unequal-exponent continuation: consume contraction criticality at the cut

**Inventory update.** E7 evaluates degree restoration and equal exponents.
It has not evaluated contraction criticality at the two actual cross edges.
That is a different observable on the same cut, with an available retained
fact; it does not retry the rejected Type A handoff or replace `G`.

**Construction selected next.** At a two-edge cut with distinct feet on both
sides, either cross edge is triangle-free. A common neighbour on the inside
would have to be its own inside endpoint (or identify the outside feet);
a common neighbour on the outside would have to be its own outside endpoint
(or identify the inside feet). Loops and the proved endpoint inequalities
exclude all these cases.

Contraction criticality then supplies an actual simple return of length
`2^k`, `k >= 2`, avoiding the first cross edge. Restore that edge. The resulting
simple cycle has length `2^k+1` and crosses the cut exactly twice: it uses a
cross edge, cycle cut parity is even, and there are only two cut edges.
Splitting at the two crossing edges gives actual simple terminal paths
`P'` in the component and `Q'` in its complement with

```
|P'| + |Q'| + 1 = 2^k.
```

**Consumer and all outcomes.** The sum `|P'|+|Q'|` is odd. Hence one of these
new paths is even and the other is odd. The side containing the even path
also contains its earlier odd Mersenne path from E7, so it has two distinct
actual paths of opposite parity with the same endpoints. Retain both
orientations of this alternative; neither is discarded. A fixed-odd-parity
terminal spectrum on both sides is excluded. For the remaining variation,
the next consumer is extraction of an actual odd cycle from the two paths,
including all shared segments. An arbitrary odd cycle is not yet a dyadic
target or a closed handoff.

**Implementation and admission status.** `twoCutDyadicReturnRow` (key 522)
is now written and submitted to V9. It reads only `contractionCritical`,
constructs an injective graph map from `G` into the two-piece closure using
the exact cut identity, maps the actual return cycle, proves its crossing
count is two, and extracts both terminal paths with their exact length
equation and parity inequality. This executor has not yet passed verification;
the odd-cycle consumer of the subsequent path intersections is not yet formalized. It is not an admitted whole-branch
transition and is not counted among the kernel-checked rows.

### E9. Intersections of opposite-parity paths — consumer construction

**Input.** Two actual simple paths `P,Q` with the same endpoints and lengths
of different parity, on the side retained by E8 and the earlier Mersenne
construction. Their paths and supports are retained, not just their lengths.

**Strictly decreasing local construction.** If an internal vertex `w` lies
on both paths, split both paths at `w`. The prefix lengths plus suffix lengths
equal the original lengths. If the prefixes have different parity, recurse
on the prefixes. If their parities agree, the suffixes have different parity,
so recurse on the suffixes. In either case the first path's length strictly
decreases because `w` is neither endpoint. Each chosen arc remains a subwalk
of the original path; simplicity is inherited. This is a natural-number
measure for this path-extraction construction, not for [172a] as a whole.

**Base case and consumer.** With no shared internal vertex, glue the first
path to the reverse of the second. Their disjoint interiors prove it is a
simple cycle. Different parity makes its length odd. The degenerate paths
of length at most one cannot have different parity with the same endpoints,
so the cycle nondegeneracy condition is proved rather than omitted.

**Outcome coverage.** Prefix parity equality and inequality exhaust the
shared-vertex case; the no-shared-vertex case supplies the actual terminal
certificate. The resulting odd cycle lies in the union of the original
paths, hence on their original side of the cut. Its subsequent use still
needs a structural consumer: oddness alone does not close the dyadic target.
This construction is currently a written proof, awaiting its sealed executor
and kernel check.

The sealed executor `pathParityCycleRow`, key 523, is now written. It reads
the current graph directly, with an empty prerequisite manifest, and proves
the subwalk-preserving odd-cycle extraction by strong induction. Both
recursive branches and the internally disjoint base case are implemented.
It is submitted to V10 and is not yet counted as kernel checked.

**Application to the cut, implemented candidate.** `twoCutOddCycleRow`, key
524, reads E7, E8 and E9 through their declared keys. Mersenne paths are odd;
E8 supplies an even path on one of the two sides. On the first-even arm the
row applies E9 to the two inside paths; on the other arm it proves that the
second new path is even and applies E9 to the two complement paths. It maps
the chosen induced paths into `G` injectively and proves that every vertex
of the extracted cycle remains on the chosen side, using both arc-subwalk
certificates. Both parity alternatives are implemented. The current build
will check this consumer together with the extraction proof.

## Step 7 — verification and admission status

| Check | Observed evidence | Meaning |
| --- | --- | --- |
| Six preceding local rows | Prior `lake build Hypostructure.Graph.Strategy.BlockedIncidenceRows` exited 0 | Those local propositions are kernel checked; no whole-branch closure follows |
| Canonical ledger and enforcement fixtures on this resumption | All 15 requested targets built successfully, exit 0; log `/tmp/eg-172a-ledger-checks.log` | The positive and guarded negative interface checks passed before the new row build |
| Canonical API check on this resumption | Export failed because `ColdCorridorRows.olean` was absent | The current API check has not passed; this is not the previous stale-catalog result |
| Audit table checker on this resumption | `missing=[]`, `extra=['cor:conditional-conjecture']` | Existing table/source mismatch remains; checker not represented as passing |
| Live topology | [172a] remains a leaf | No unproved consumer is placed after the open node |
| Replacement/refinement | No new representative of the active graph has been committed | All new constructions so far are local facts on the selected graph |
| Exhaustive parent closure | Not established | Remaining consumers below must still be executed |

## Binding outstanding queue

1. E6: complement degree restoration, actual cycle gluing, equal-exponent
   contradiction, unequal-exponent continuation, and coincident-foot cases.
2. E2: consume intersections of the actual window-return family, including
   shared subpaths and unequal exponents, without assuming independence.
3. I4: minimal connecting tree with both path and branching outcomes;
   construct a smaller representative and every required handoff field before
   invoking a switch theorem.
4. I5: singleton, heavy-foot and cross-window cases with the actual incidences
   and their receiving consumers.
5. I6/I7: reconcile any resulting selected-graph construction with the exact
   comparison fibre and its multiplicities, or prove an exhaustive alternate
   closure of the selected branch while retaining all quantitative accounts.
6. Only after exhaustive consumers exist: publish and wire the admitted
   transition on each literal incoming history, run the closure checks, and
   synchronize manuscript, live audit and app graph from that evidence.

This file is updated as execution proceeds. Recording an item here does not
discharge it, and an unresolved item is not a counterexample to the theorem.

## Verification attempts in this continuation

| Attempt | Scope | Result and response |
| --- | --- | --- |
| V1 | Non-mutating API catalog check | Failed at API export: absent `ColdCorridorRows.olean`. No catalog refresh or new interface was used. |
| V2 | Audit table check | Existing extra `cor:conditional-conjecture` row reported. No unrelated row was removed. |
| V3 | Canonical ledger and 14 companion enforcement targets | Passed, exit 0. This includes guarded negative fixtures. |
| V4 | First build with E6 | Failed on mapped-walk support rewriting, induced endpoint coercions, path-length rewriting and the baseline definition. These were elaboration obligations in the anonymous proofs. The concurrently added E7 key was absent from that build's earlier vocabulary snapshot. No mathematical claim was marked checked. |
| V5 | Rebuild with corrected E6 and current vocabulary including E7 | Failed on the remaining cycle-length rewrite and two explicit finite-set membership proofs; log `/tmp/eg-172a-incidence-v5.log`. The complement proof and the rest of E7 produced no reported errors. |
| V6 | Correct endpoint coercions and finite-set memberships | Only the composed cycle-length simplification still failed; log `/tmp/eg-172a-incidence-v6.log`. |
| V7 | Supply each map, concatenation, reversal and append length identity explicitly | The arithmetic tactic still treated definitionally equal mapped-walk lengths as different terms; log `/tmp/eg-172a-incidence-v7.log`. |
| V8 | Compose the exact length equalities with `calc` and congruence | Passed, exit 0, all nine rows and keys 513–521; log `/tmp/eg-172a-incidence-v8.log`. Arithmetic is used only after the walk expressions have been eliminated. No mathematical hypothesis or conclusion changed. |
| V9 | Add the contraction-critical cut return and opposite-parity terminal paths | The E8 executor produced no errors. The build failed because E9's newly appended key 523 was absent from the vocabulary snapshot built earlier in this run; log `/tmp/eg-172a-incidence-v9.log`. No successful whole-module check is claimed for this attempt. |
| V10 | Rebuild current vocabulary and the parity-cycle executor | Failed: explicit vertex/path arguments were missing at two induction calls, and automated search did not prove the disjoint-interior base case; log `/tmp/eg-172a-incidence-v10.log`. |
| V11 | Explicit induction arguments, subwalk composition and endpoint exclusions | Passed, exit 0; all twelve local rows, keys 513–524, kernel-check. Log `/tmp/eg-172a-incidence-v11.log`. This does not repair the move-admission failure recorded above and does not close [172a]. |

For V4 the fixes preserve the propositions and constructions: they expose
the support map before extracting its source vertex, make the induced
endpoint coercion explicit, prove the composed length identity directly,
and unfold the minimum-degree baseline at the minimality call. No premise
was added to make a failed proof compile.


## Publication correction: the positive [170] branch closes at [171]

Requested endpoint in this follow-up: correct the manuscript's account of
[171], so every unresolved obligation on this counting branch remains at
[172a]. This is a publication and branch-contract correction, not an
execution claiming to close [172a].

1. Read the recipe's branch setup, first-failure repair, execution and closure
   checks, the actual [170]/[171] manuscript statements, and the positive
   and negative continuations in `selectedCanonicalReplacementContinuation`.
2. The retained inputs to [171] are `blockedClassMember` from [169],
   `blockedScaleAdditive` from the positive [170] decision, and
   `densePackingOverflow` from [159]. All refer to the same selected object.
   None is supplied by [172a].
3. The existing `blockedCompressionRow` multiplies the finite graph-fibre
   bounds, publishes the exact package cap, and `blockedCompressionCloses`
   contradicts the retained dense overflow. The application calls this
   closer on `.left additiveHistory`. On `.right overlapHistory`, it returns
   the complete first-failure fact to the open [172a] continuation.
4. Corrected the manuscript statement to a terminal closure on the complete
   positive branch, exposed all three inherited inputs, and wrote its exact
   finite package contradiction before the asymptotic form. Updated the
   realization-test notation, diagram wording and requirement ledger to
   match that same finite package. The existing Lean declarations were not
   changed.
5. The earlier phrase “[171] is conditional” conflated a theorem's proved
   incoming branch facts with outstanding assumptions. The graph-fibre
   counts are conditional on a record and prefix; the [171] closure is fully
   proved on its incoming branch. The unresolved negative arm remains [172a],
   with no outgoing live edge. This correction neither closes that open leaf
   nor claims that the complete closure recipe has finished.
6. Validation: rebuilt the 271-page PDF, inspected the changed realization
   test, [170]/[171] statement and proof, and Part XII diagram. Refreshed the
   EG graph and page links, preserved all graph edges and manuscript labels,
   verified exactly the three open leaves [172a], [182], [186], and confirmed
   [171] has no outgoing edge and is not open. The 66 graph tests and 53
   frontend tests passed. The manuscript and app PDF copies are identical.
