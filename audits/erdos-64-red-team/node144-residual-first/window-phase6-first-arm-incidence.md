# [144] the starting vertex has one own-arm edge

The [144] owner now has an anonymous local `armEdgeSet_first_incidence`
proof. If a list `path` has head `start`, is nodup, and the physical edge
`s(start,other)` belongs to `armEdgeSet path`, it proves

```
∃ next rest, path = start :: next :: rest ∧ other = next.
```

The singleton arm has no consecutive edge. For a longer arm, the first
`zip` edge is `s(start,next)`. If an edge incident to `start` appeared later,
the accepted endpoint lemma would put `start` in the tail, contradicting
nodup. Equality of undirected edges gives `other=next`; the swapped equality
would make `start=next`, also contradicting nodup. Thus this result handles
shared physical arm edges and all arm lengths without assuming disjointness.

On the actual matching/star envelope, the first-entry arms are simple and
issued at the selected `a,b`, so the local rule can identify every own-arm
edge at `a` or `b`. It does not prove whether an arm is singleton or whether
its start lies in the core. Nor does it impose the conditional all-in-`F`
premise. The remaining local incidence work is the exact two-vertex core
edge bound and its interaction with first entry; only then can the degree
three contradiction force a neighbour onto the opposite arm.

Verification: the owner `lake env lean -j 1
Hypostructure/Graph/Strategy/HomogeneousBottleneckRows.lean` exited 0;
the direct EG caller `lake build
HypostructureErdos64EG.Assembly.Surplus.Local` exited 0 after 8777 jobs;
`git diff --check` exited 0. No top-level mathematical declaration, ledger
key, `Holds` change, cap, escape, or closure was added.
