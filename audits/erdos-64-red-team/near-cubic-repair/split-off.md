# Node [144]: the high-centre split-off check

Status: a further consequence of the retained minimal-counterexample residual,
not a closure of the handoff. No new premise is imposed on that residual.

## Heavy centre: a single split-off

Let h have degree d≥5, and let a,b be distinct nonadjacent neighbours of h.
Such a pair exists because G[N(h)] is a matching. Delete ha,hb and add ab,
obtaining G′ on the same vertex set. The graph is simple, h has degree d−2≥3,
a and b retain their degrees, and every other degree is unchanged. Moreover,
G′ has one fewer edge. The retained lexicographic minimality therefore gives
a cycle C of length 2^j in G′, with j≥2.

C must use ab; otherwise it is already a target cycle of G. Deleting ab
from C produces an actual simple a–b path P in G−{ha,hb} of length 2^j−1.
This is a path in the original graph, not in a hypothetical outside context.

If h is absent from P, adding ah,bh produces a cycle of length 2^j+1. If h
is internal to P, write r,s for its two subpath lengths. Then r,s≥2,
r+s=2^j−1, and the two closures have lengths r+1 and s+1. Both are
non-dyadic by the retained target avoidance. This exhausts the locations of h.
In particular, for j=2 the internal-h outcome cannot occur, since r+s=3.

The modified graph is used only as a minimality comparison. The active graph,
packing, selected demands, token assignment, source pattern and response data
are all retained; none is transferred to G′ without proof.

## Coupling this fact with the previously proved nonadjacent fold

For the same a,b, the fold gives a simple a–b path of dyadic length 2^i;
the split-off gives one of length 2^j−1. No disjointness between these paths
is supplied. Even in the favourable internally disjoint case, a direct target
cycle does not follow from these two lengths and the path a–h–b.

Indeed, take an abstract theta graph whose three internally disjoint a–b
paths have lengths 2, 2^i and 2^j−1, for i,j≥2. Its only simple cycle
lengths are

    2^i+2,  2^j+1,  2^i+2^j−1.

The first lies strictly between consecutive powers of two; the other two are
odd and greater than two. Thus none is a power of two. Folding a,b creates
the required cycle of length 2^i, and adding ab creates one of length 2^j.

This theta is only a counterexample to the proposed length-only implication.
It is not a graph in the full residual: its interior vertices have degree two.
It neither refutes the requested Node [144] theorem nor proves it impossible.
It prevents us from claiming that the two minimality witnesses alone close it.

## Degree four: full smoothing

If d(h)=4, the single split-off leaves h with degree two and is unavailable.
Instead choose a perfect matching M of N(h) consisting of nonedges, delete h,
and add the two edges of M. At least two such matchings exist: G[N(h)] is a
matching, and its at most two edges belong to one of the three perfect
matchings on N(h). The other two avoid every existing edge.

All remaining vertices retain their degrees, so minimality supplies a dyadic
cycle in the smoothed graph. It must use one or two of the new edges. With
one new edge, the remaining path plus the original two-edge route through h
has length 2^j+1. With both new edges, deleting them leaves two disjoint paths
in G−h. Closing each through h gives two simple cycles whose lengths sum to
2^j+2. Target avoidance remains compatible with this arithmetic.

For example, two triangles h–a–x–h and h–b–y–h admit exactly the two cross
smoothings; each creates a four-cycle. The original five-vertex configuration
has only triangles. As with the theta above, this is a local obstruction to
automatic target preservation, not a counterexample to the full residual.

## Exact consumer obligation

Neither smoothing construction proves equality of the declared response
readings, and neither bounds the number of original source pairs using the
same handoff. Both therefore leave the same Node [144] obligation: use the
retained source-pair/response data to prove an excluded exit or a quantitative
bound. These comparisons have not been admitted as decreasing residual
transitions; their smaller graphs do not preserve target avoidance.
