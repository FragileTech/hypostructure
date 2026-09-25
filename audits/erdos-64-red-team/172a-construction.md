# Construction queue for node [172a]

Endpoint: discharge `lem:barrier-failure-overlap` on the full selected
residual, or prove a replacement continuation with all its outcomes consumed.
This is an active construction record, not a closure certificate.

The detailed mapping of each executed move to the methodology, including
failed verification attempts and their repairs, is in
[172a-methodology-execution.md](172a-methodology-execution.md).

## Fixed incoming state

The current object is the unchanged selected graph G. The exact initial tail
of `selectedNearCubicSurvivorBranch` is

```
sparseSurplusSurvivor, surplusAtOrBelow, localAlgebra, maximalPacking,
uncompressible, replacementExclusion, targetCompleteContextUniversality,
degreeProfileFibres, cycleRankConstraint, tightEndpoint, slackIndependent,
noProperBaseline, returnAvoidance, contractionCritical, gadgetClosure,
relabelingDensityCap, cubicBaseline, selection
```

Keep the literal chosen decision history on top of that tail: failed full
window-package realization and dense overflow; the selected deficiency/rate
outcomes; the hot/cold partition and its exact quantitative accounts; the
linear cold mass or the absorbed-germ producer's corresponding witness;
remainder normalization and relabeling entropy; bridgelessness; the actual
return corridors, presentations, first-failure occurrences, routed and
extracted germ families; the marked neutral canonical configuration;
the universal Q = E consequence; blocked membership; and the least failed
conditional graph-count inequality. The two call sites of
`selectedCanonicalReplacementContinuation` retain their own histories.
No sibling rate inequality or missing geometric fact is added.

All below constructions are on G. The comparison member H0 selecting the
failed fibre remains separate. No property of G is transferred to H0.

## Inventory and binding next constructions

| Queue | Concrete observable not evaluated by the earlier counting attempts | Retained inputs | Construction and next consumer |
| --- | --- | --- | --- |
| Q1 | A component's entire boundary concentrated at one vertex | Actual edge returns; vertex degrees; outside-component closure and connectivity | Construct a second neighbour on each side by two return paths. At degree three a nontrivial such component is excluded. A heavy boundary vertex remains attached to its four actual incidences until a handoff consumer is proved. |
| Q2 | Triangles on adjacent edges of an actual induced window | Cubic middle vertex, quadrilateral avoidance, contraction criticality | Show two adjacent window edges cannot both lie in triangles. Select one triangle-free edge from each disjoint pair and construct its dyadic-length return. Feed the actual path family, including intersections, to the next geometric analysis. |
| Q3 | A genuine two-terminal component and its complement | `gadgetClosure`, minimum degree, target avoidance, exact component order | Check the terminal degrees and cross-edge identity before applying the retained edge-addition or two-copy consequences. Retain the actual Mersenne paths and compare their exponents and overlaps. |
| Q4 | Three or more actual boundary feet in an outside component | Component connectivity; induced-path-free remainder; selected graph incidences | Construct a minimal connecting tree and keep both its path and branching cases. Verify the precise arm lengths, simplicity, root-window labels and downstream interfaces before using any barrier or handoff conclusion. |

Q1 is owned by the Type A row `singleFootBoundaryRow`, with literal manifest
`Requires = [bridgeless]`, `Produces = [singleFootBoundary]`. Its proof is
anonymous inside the sealed executor. The full incoming ledger is not reset.
The new key uses index 513, after inspecting the actual maximum existing
index 512; existing keys retain their indices.

### Q1 construction

Let C be a vertex region, v its sole boundary foot, u an internal neighbour
of v and a an external neighbour. Sever va and follow its retained return
from v to a. Its first exit from C must be vb with b outside C and b ≠ a.
Sever vu and follow its return in reverse from u to v. Its first exit from
C − {v} must be cv with c in C and c ≠ u: exiting C elsewhere would violate
the unique-foot condition. Thus u,c,a,b are four distinct neighbours of v.
Every path, dart and incidence used here belongs to G.

This excludes the nontrivial single-foot configuration at a cubic vertex.
It does not identify a heavy vertex with a completed handoff, and it does
not exclude a singleton component with three window incidences.

The consumer `singleFootComponentRow` is kernel-checked. If an outside
component has only the cubic boundary foot v, connectivity supplies an
internal neighbour unless the component is {v}; the four-incidence fact then
contradicts its cubic degree. Its manifest reads `singleFootBoundary` and
publishes `singleFootComponent` (index 514). This is a local implication;
the remaining attachment types still require consumers.

### Q2 construction

`inducedWedgeReturnRow` is kernel-checked. For an induced wedge u-v-w with
v cubic, if uv and vw each have a common neighbour, the three-neighbour
exhaustion at v forces the common neighbours to coincide. The four vertices
then give the excluded quadrilateral u-v-w-x-u. Hence one of uv,vw has no
common neighbour. Contraction criticality, read from the incoming ledger,
supplies an actual simple return of length 2^k, k >= 2, avoiding that edge.
The selected edge, triangle-free certificate and path all belong to G.

The next consumer `windowReturnFamilyRow` applies this to disjoint pairs of
window edges and retains the entire induced embedding. At order 13 the
index set has size six. Distinctness is proved for the undirected selected
edges, not assumed for their return paths. Intersections of these actual
paths are the next geometric observable; a collection of returns by itself
is not a serial system and is not called a reduction. This consumer is
kernel-checked, including injectivity of its undirected edge map.

### Q3 construction

The first consumer of `gadgetClosure` is `twoTerminalMersenneRow`, now
kernel-checked. For a smaller target-free piece with two degree-two terminals
and all other degrees three, adjacent terminals give the one-edge path
(k=1). Otherwise adding their missing edge raises exactly their two degrees
to three and leaves every other degree unchanged. The retained edge-addition
clause then supplies an actual simple terminal path of length 2^k-1.
Thus adjacency of the terminals is consumed rather than silently excluded.
The consumer `twoStubComponentMersenneRow` is also kernel-checked. It starts
from an actual ambient-cubic outside component whose entire boundary is the
two displayed edges. If their inside feet coincide, `singleFootComponent`
makes the component a singleton, whose neighbourhood would then have at most
two vertices, contradicting degree three. Thus the feet are distinct. Their
external-neighbour sets are the displayed singletons; every other component
vertex has no external neighbour. Exact degree accounting gives the required
2,2,3,...,3 internal degree profile. Disjointness from the windows proves that
the component is smaller than G, and induced-subgraph transport proves target
avoidance. The preceding row then constructs its Mersenne path.

The finite selection check `checks/two_terminal_small.py` exhausts the labelled
two-terminal degree sequence through order eight. Odd orders are excluded by
the handshake identity; orders zero and two cannot have the degree sequence.
At orders four and six there are no C4-free candidates. At order eight there
are 360 connected labelled C4-free candidates and each has an 8-cycle. The
generator fixes higher-labelled neighbours one vertex at a time; it prunes
only an existing 4-cycle or an impossible remaining degree. This is a finite
computational check, not a Lean certificate for the general small-order claim.
The terminal-preserving isomorphism check puts all 360 candidates in one
orbit: two triangles joined by three matching connections, two of which are
subdivided by the two terminals. The saved JSON contains the unique labelled
template and its actual 8-cycle; every generated candidate therefore has an
explicit terminal certificate, rather than just a failed search for survivors.

The associated quantity is exact: two degree-two terminals and all other
internal degrees three give positive deficiency 2; ambient cubicity gives
surplus 0. Thus the component has negative net charge exactly when its order
exceeds 8. The attempted direct call to the existing Type A continuation is
not admitted: `selectedTypeALowSurplusContinuation` also requires the literal
`route8Rate` and `largeBudgetResidual` facts, which are not available on every
dense [172a] history. Nor may a cold-outside component be silently identified
with a component of the remainder of the whole packing. Retain the constructed
paths and degree profile; do not manufacture that handoff.

### Remaining construction queue

1. Analyze the intersections and exponents of the actual window return
   family. Equal exponents alone do not establish internal disjointness.
   Construct the exact common subpaths and the cycle or replacement consumer.
2. For a two-stub component, retain the displayed boundary and the actual
   Mersenne path. Complement degree restoration is now kernel-checked in
   `twoCutComplementMersenneRow` (520), including the adjacent-foot case.
   `separatedPathCycleRow` (519) constructs the actual glued cycle and excludes
   every accepted sum. `twoCutMersenneSeparationRow` (521) excludes a shared
   cubic outside foot, constructs both Mersenne paths, and consumes equal
   exponents by that cycle. All nine rows passed build V8. Unequal exponents
   now feed the written `twoCutDyadicReturnRow` (522): use contraction
   criticality at the cut to obtain new terminal paths of opposite parity.
   This tenth row is awaiting build V9, not yet a checked fact. Its next
   consumer extracts an actual odd cycle from the different-parity paths,
   treating their shared segments explicitly.
3. For three or more feet incident to a root window, construct the minimal
   connecting tree and retain both a path through the feet and a branching
   tree. The Type A cubic-switch theorem requires a `SwitchReading` with an
   actual smaller glued representative (`descends`), not merely three arms at
   a cubic vertex. Construct that representative before invoking absorption.
4. The surviving singleton, heavy-foot, cross-window and comparison-fibre
   cases retain their literal data. The six local results do not resolve
   absent completion states or graph multiplicities for the entire comparison
   fibre and have not been installed as a branch-closing transition.

Validation: all six Type A rows and vocabulary keys 513–518 build together in
`Hypostructure.Graph.Strategy.BlockedIncidenceRows`. No axiom, `sorry`, detached
selected-fact theorem, or extra proof-data interface was introduced. The
live [172a] leaf remains open. The API catalog check reports its pre-existing
staleness; the table check reports the pre-existing extra manuscript label
`cor:conditional-conjecture`. Neither check is represented as passing.

## Execution discipline

After each checked construction, update this queue with its actual output and
the first consumer obligation. No failed candidate ends the requested work.
No split is added to the live proof graph until its outcomes have verified
consumers or a proved strictly decreasing continuation. No lemma here is
called a closure of [172a] merely because its local construction compiles.
