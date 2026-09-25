# [144] exact producer-envelope edge skeleton

Inside the existing `sameTokenBottleneckRoutingRow` executor, local
`armEdgeSet` maps each consecutive pair of a list to its undirected physical
edge. Local `coreEdgeSet Y` enumerates exactly the edges of `G[Y]`: for each
`u∈Y`, it includes `s(u,v)` precisely when `v∈Y` and `G.Adj u v`.
Both functions use `G=inputs.current.object`; neither changes the graph.

After each of the matching and star arms builds its **actual**
`envelopeOfFirstSeparator`, local `skeleton` is

```
armEdgeSet (envelope.arm h a) ∪
armEdgeSet (envelope.arm h b) ∪
{s(h,a),s(h,b)} ∪ coreEdgeSet envelope.core.
```

The `skeletonEq` proof in each arm reduces the same constructed envelope and
uses `a≠b` to identify its two arm projections with the existing first-entry
lists `armLeft` and `armRight` and its core with the existing `core`.
Consequently this is exactly
`E(P_a)∪E(P_b)∪{ha,hb}∪E(G[Y])` for the selected handoff, including equal
terminals, absent core edge, zero arms, and overlapping arms. Its repeated
undirected edges collapse in `Finset` without an assumption of disjointness.

The owner file checked with `lake env lean -j 1
Hypostructure/Graph/Strategy/HomogeneousBottleneckRows.lean` (exit 0).
The direct EG caller checked with
`lake build HypostructureErdos64EG.Assembly.Surplus.Local` (exit 0,
8777 jobs). The API catalog check and `git diff --check` passed. No new
top-level mathematical declaration, `Requires` key, `Produces` key, or
alternate transport was added in this task. The existing `typeBHandoff`
`Holds` is unchanged.

This definition does not assert that every edge at `a,b` lies in the
skeleton, and it does not prove a spare edge. The next inference is
conditional: if every physical edge at the selected cubic `a,b` belongs to
this exact `skeleton`, prove `a` occurs on the opposite first-entry arm.
Its zero-arm/core cases and its source-indexed continuation must be handled
in the owner, then the symmetric crossing and route splice must follow.
