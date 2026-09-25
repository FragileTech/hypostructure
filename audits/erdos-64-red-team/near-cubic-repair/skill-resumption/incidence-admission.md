# Stage 3: admission test for incidence charging

## Exact conditional counting calculation

Let E be the extracted event set, J its cardinality, and L the number of
distinct source-pair records removed per event. Choose the actual routing
witness for each event, with high centre h and unordered pair of distinct
first neighbours {a,b}. Let k(h,a,b) count events with this triple. Then

    J = sum_h sum_{ {a,b} subset N(h), |{a,b}|=2 } k(h,a,b).

This is an identity: each event contributes to exactly one fibre, even if paths
overlap, terminals repeat across events, or several witnesses were available.
The choice is fixed before counting. The previous extraction gives H <= LJ.

IF all these fibres have size at most a fixed kappa AND every used centre has
degree between 4 and 8, then

    J <= kappa sum_h binom(d(h),2) <= 6 kappa sum_h (d(h)-3)
      <= 6 kappa sigma(G),
    H <= 6 L kappa sigma(G).

Proof of the middle inequality: at d=4,5,6,7,8, the differences
6(d-3)-binom(d,2) are respectively 0,2,3,3,2. The final inequality sums
nonnegative surplus over a subset of high vertices. This is independent of
any near-cubic conclusion. Substituting D=6 L kappa in the earlier pair-excess
inequality would yield a square-root surplus estimate with its resulting
explicit constant. One must still compare that constant with the fixed strict
branch threshold; a different constant does not itself close that branch.

Neither capitalized premise is proved here or registered as a residual fact.
This calculation does not prove caps on the original role fibres.

## Does the routing output supply the premises?

No. In the inspected source:

- `SameTokenTypeBHandoffStatement` in SpineVocabulary.lean retains the source
  pattern and an envelope-existence statement. The envelope statement does not
  assert any injectivity or bounded multiplicity for source events.
- `Envelope` in DecoratedHandoffEnvelope.lean:902 supplies arms for an assigned
  neighbour set; it does not bound the number of source pairs using them.
- `FanCertificateLabelling` in FanCertificate.lean:240 requires a legal label
  on every neighbour and pairwise compatibility. The geometric `FanSafe` field
  of an envelope is not this labelling and does not provide it.
- The high-separator construction in HomogeneousBottleneckRows.lean:3051
  derives a lower degree bound. Its envelope construction supplies two first
  neighbours, not an upper bound on the ambient degree.

## Why distinct source records do not prove bounded multiplicity

For arbitrary t, take a finite tree with a vertex h of degree four. Two of its
branches are binary trees with t leaves each; its other two branches can be
single leaves. Denote the first vertices of the two large branches by a,b,
and their leaf sets by U,V. All vertex degrees are at most four. For every
(u,v) in U x V, the unique h-u and h-v paths have first separator h and first
neighbours a,b. Each is an actual simple path, and the two paths in a pair are
disjoint outside h. There are t^2 distinct endpoint pairs using that same
triple.

For t divisible by L, index each leaf set by Z/tZ. For each j, the t pairs
(u_i,v_{i+j}) form a matching. These t matchings partition U x V. Splitting
each matching into t/L groups of size L produces t^2/L disjoint L-edge
matching events, all with the same triple (h,{a,b}). Thus even disjoint source
records, actual simple paths, and maximum degree four do not by themselves
bound this triple's fibre by an absolute constant.

This tree does NOT satisfy the complete Node [144] residual: in particular
its leaves violate minimum degree three. It is not a counterexample to the
desired theorem. It isolates what cannot be inferred from the routing-path
fields alone. A proof must use additional retained graph/response facts to
exclude this concentration; the example does not show that this is impossible.

## Admission result and retained obligation

The summation calculation is proved as an implication. The proposed charging
move is not admitted: neither the fibre bound nor the marked-neighbour
construction was derived from the complete residual. No stage 4 construction,
verified successor, or closure certificate follows from this test.

Return to stage 2. Preserve the original root and its entire fact list. The
unresolved obligation remains to consume an actual concentrated family using
the retained response/minimality data, or construct a different admissible
consumer. A concentration model for a projection of the state cannot discharge
that obligation or prove the user's request impossible.
