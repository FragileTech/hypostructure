# Rejected closure attempt at node [185]: theta extraction

**Progress verdict: no reduction of the outstanding proof obligation.** The
theta table below does not pay demand, construct a permitted replacement,
reach a closed consumer, or establish an exhaustive recursive decrease. It
is retained only as an unsuccessful attempt so that it is not repeated or
mistaken for a proof transition. It should not be implemented in the DAG.

This continuation follows the branch-state, admission, localization, and
exchange rules in `to_formalize/branch_closure_methodology_extended.tex`
(`data-branch-states`, `admission`, `ct:11`, `ct:7`). It proves a local
structural consequence and checks its finite length table. **It does not
close node [185], and it introduces no new proof-DAG node.**

The live manuscript already sends [185] to [186] by
`lem:typeA-unified-joint-balance`. The starting structural data below are
the degree-chain normalization in Theorem 0.9 of `node_181_structure.md`.
That development is distinguished from the implemented [186] ledger: the
present result is conditional on its stated kernel data and is not a new
Lean producer. In particular, its selection of a deficit-heavy support uses
the sufficiently-large branch and the error margin in that note's Corollary
0.6. No assertion here supplies a missing finite-size cutoff.

## 1. Exact state and permitted inputs

Keep the complete [185]/[186] state, with its original graph, components,
receiver and trace schedules, visible returns, Q1 response comparisons,
peel history, maximal demand partition, same-support absorption, open units,
and window blockers. None of these is reconstructed on a smaller shore.

The structural continuation selects a support (X=X_D) with cut size (b_0)
and encodes it by a cubic weighted multigraph Γ. Write

\[
 n_K=|V(\Gamma)|\ge6b_0+2,\qquad
 s=|\{e:\ell(e)>1\}|\le b_0.
\]

Delete the (s) nonunit edges from the *encoding*. The remaining graph is
the actual induced simple graph (U=G[V(\Gamma)]). It has maximum degree
three, is target-free and induced-(P_{13})-free, and every vertex of (U)
has degree three in the original (X). Vertices of (U) are consequently
neither original receivers nor inside endpoints of the original cut.

For (c=c(U)), the cubic degree sum in Γ gives the exact identity

\[
 \beta(U)=|E(U)|-|V(U)|+c
          =\frac{n_K}{2}-s+c.                         \tag{1}
\]

Loops and parallel edges are allowed in Γ, but not in (U). Equation (1)
counts each removed encoding edge once, including a loop. Every edge used
in the local argument below is an actual weight-one edge of (G).

The other concentration supports and the marked-entry fibres remain in the
state. They are not assumed to coincide with the local configuration selected
below. In particular, no selected theta vertex is asserted to own an open unit.

## 2. Local structural extraction

**Proposition.** Under the preceding inputs, (U) contains an induced theta:
three internally vertex-disjoint paths with common distinct endpoints.

**Proof.** From (1),

\[
 3\beta(U)-n_K
   =\frac{n_K}{2}-3s+3c
   \ge 1+3c>0.                                       \tag{2}
\]

Suppose (U) contains no theta. Any two distinct cycles that share a path
produce a theta: follow one cycle until an excursion of the other leaves
it and first returns at a different vertex; the excursion and the two arcs
of the first cycle are the three paths. More generally, two distinct cycles
sharing at least two vertices have such an excursion. Cycles sharing just
one vertex would use four different edges there, impossible in a subcubic
graph. Thus all cycles of (U) are vertex-disjoint.

Remove one edge from each cycle. The graph left is a forest: a cycle left
would itself have been one of the cycles from which an edge was removed.
Each removal preserves connected components, so the number of cycles is
β(U). Every cycle has at least three vertices, whence (3\beta(U)\le n_K),
contradicting (2). Hence a theta exists.

Choose one with the fewest edges, using the fixed order to break ties. Its
two branch vertices already use three incident edges, so a chord of its
vertex set cannot meet either branch vertex. A chord between two interior
vertices on one arm shortcuts that arm and gives a smaller theta.

Consider a chord between interiors of two different arms. The chord, the
route through the first branch vertex, and the route through the second
branch vertex give another theta. If the unused third arm has at least two
edges, this new theta has fewer edges. Therefore that third arm must be a
single edge. The original theta together with the chord is now a subdivision
of (K_4): two opposite links are single edges and the other four links are
the segments into which the chord endpoints split the first two arms.

If any of those four segments has at least two edges, discard that segment.
The other five links form a theta with fewer edges than the original one.
If all four segments are single edges, they form an actual four-cycle.
Both outcomes are impossible. Thus there is no chord and the selected theta
is induced. □

This spends the retained cycle count and the actual subcubic graph. It does
not invoke an unconditional result about cycle lengths in large cubic graphs.

## 3. The exact finite length table

Let the ordered arm lengths be (1\le a\le b\le c). Simplicity permits at
most one length-one arm, so (b\ge2). The only simple cycles of this theta
have lengths

\[
                    a+b,\quad a+c,\quad b+c.           \tag{3}
\]

For any two arms, delete one common endpoint. Their remaining vertices form
an induced path on the sum of their lengths minus one vertices. Even when
the third arm is a single edge, that edge disappears with the endpoint.
Induced-(P_{13})-freeness therefore gives

\[
                         b+c\le13.                    \tag{4}
\]

Equations (3)--(4) give exactly 100 candidate triples. The self-contained
checker `to_formalize/check_node_185_theta.py` constructs every one, enumerates
its simple cycles, and searches every induced path. It cross-checks the cycle
enumeration against (3) and verifies the edges and nonedges of each longest
path witness. Its exhaustive outcomes, testing target cycles first, are:

| Outcome | Number of triples | Status on this structural state |
|---|---:|---|
| A power-of-two cycle | 46 | Excluded by the actual target predicate |
| No target cycle, but an induced (P_{13}) | 14 | Excluded inside the original induced remainder |
| Neither local test fires | 40 | Retained local shapes; not closed leaves |

Here is the complete surviving table. Each row gives (a) and the possible
pairs ((b,c)).

| (a) | ((b,c)) |
|---:|---|
| 1 | (2,4), (2,5), (2,8), (2,9), (2,10), (2,11), (4,5), (4,6), (4,8), (4,9), (5,5), (5,6), (5,8), (6,6) |
| 2 | (3,3), (3,4), (3,7), (3,8), (3,9), (3,10), (4,5), (4,7), (4,8), (4,9), (5,5), (5,7), (5,8) |
| 3 | (3,3), (3,4), (3,6), (3,7), (3,8), (3,9), (4,6), (4,7), (4,8), (6,6) |
| 4 | (5,5), (5,6) |
| 5 | (5,5) |

Every survivor has at most 14 vertices. For example, ((1,2,4)) has six
vertices and only cycle lengths 3, 5, and 6. This is a genuine surviving
*local projection*, not a counterexample satisfying the full incoming
ledger. Conversely it prevents treating theta extraction alone as a direct
target-hit theorem.

Reproduce the table with:

```bash
python3 to_formalize/check_node_185_theta.py
```

## 4. Actual frontier and the local deletion move

Let (H) denote the induced theta just selected and put

\[
             k=a+b+c-3,\qquad |V(H)|=k+2.              \tag{5}
\]

The two branch vertices have all three neighbours in (H). Each of the
other (k) vertices has exactly two neighbours in (H) and, by the original
ambient-cubic condition, one neighbour outside (H). Since every vertex of
(H\subseteq U) has degree three already in (X), that outside neighbour
lies in (X\setminus V(H)). Thus

\[
        |\delta_G(V(H))|=k\le12,\qquad
        \delta_G(V(H))\subseteq E(X).                  \tag{6}
\]

All these cut edges are actual and have distinct inside endpoints. Their
outside endpoints need not be distinct. None is an original cut edge of
(X); none is automatically an unused incidence of the demand supply.

There is a concrete deletion with exact accounting. Let (S_1,\ldots,S_t)
be the components of the induced graph (X-V(H)). The old boundary edges
of (X) and the (k) newly exposed edges partition their cuts, so

\[
 \sum_i|S_i|=|X|-(k+2),\qquad
 \sum_i|\delta_G(S_i)|=b_0+k.                          \tag{7}
\]

Writing (F(S)=|S|-7|\delta_G(S)|), this becomes

\[
                     \sum_i F(S_i)=F(X)-8k-2.         \tag{8}
\]

Every (S_i) is a proper connected induced shore with the inherited
ambient-cubic and local target-avoidance properties. Formula (8) shows both
sides of the proposed deletion: if (F(X)>8k+2), some strictly smaller shore
has positive (F); if not, this move does not force such a child. The
incoming lower bound (F(X)\ge2) does not guarantee the first arm. Even on
that arm, (7) does not transport the demand or response ledger to the child.

In particular, suppression or deletion is not a permitted smaller minimal
counterexample merely because its internal vertex count decreases. The
original ledger is retained with the local configuration and the exact
new-boundary cost (7), rather than relabelled as a ledger on (S_i).

## 5. Framework admission and the unresolved route

| Proposed move | Available certificate | Remaining obligation |
|---|---|---|
| Cycle surplus to theta | (1)--(2) and the complete extraction proof | None for this conditional structural implication |
| Local target and induced-path tests | The exhaustive 100-triple table | Forty local shapes remain |
| Charge the theta's frontier | The actual incidence list (6) | An assignment to eligible original payers with a proved capacity bound; the frontier is not that supply |
| Delete the theta and recurse | The exact identities (7)--(8) | The low-surplus arm, and transport of all ledger facts if a child is to enter an existing ledger theorem |
| Replace the theta | A bounded actual piece and its full labelled frontier | A smaller representative with the same boundary degrees, the ambient degree baseline, and the required target implication in every compatible context |
| Route a replacement defect to exit (4) | A defect can be sought on an explicitly constructed comparison | Literal membership in Q1--Q5, its declared original load, and validity at that load's original peel stage |

The next closure-producing step must use the frontier attachments and the
retained response and demand records together. A finite table of the 40
unlabelled theta shapes alone is insufficient: different outside attachments,
response coordinates, and owner assignments can give different routing
outcomes. Full outside path lengths cannot simply be truncated into a finite
label without proving that the target test uses only the truncated data.

In particular, the actual pieces in a proposed replacement must be compared
with the actual pieces in the exit API. The inspected Q1 constructor in
`hypostructure/Hypostructure/Graph/ExitFourFamily.lean` fixes the two
`visibleResponsePiece` arguments from one selected package. Q4 instead fixes
a declared connector family, a separation, and its `SwitchReading`. Neither
constructor accepts an arbitrary degree-preserving internal modification.
This is the same type distinction that invalidated the earlier fold closure.

The framework's both-sides test therefore admits the extraction and local
exclusions as proved structural information, but does not certify a closure
or a paid/routed successor from the remaining shapes. The unresolved entry
in the branch table is explicit: **one of the 40 induced theta shapes, its
at most 12 actual internal frontier incidences, and the complete unchanged
incoming ledger, with no proved payer or replacement consumer yet.**

No manuscript, Lean declaration, node-status table, or existing structural
note was changed by this continuation.
