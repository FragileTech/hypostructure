# [144] the exact two-vertex core has at most one edge

The existing [144] atomic owner now proves one anonymous local fact about
its `coreEdgeSet` on the selected graph:

```
∀ u v, coreEdgeSet {u,v} ⊆ {s(u,v)}.
```

The proof opens the existing induced-edge enumeration. Both endpoints must
belong to `{u,v}`. The equal-endpoint cases would be loops and contradict
irreflexivity of the actual simple graph; the two cross cases identify the
same undirected edge `s(u,v)`. This covers `u=v`, nonadjacent `u,v`, and an
actual core edge without assuming core connectedness.

Both matching and star handoff constructors use precisely
`core={left.2,right.2}` and then set `envelope.core=core`, so the fact applies
to the same skeleton already defined there. It restricts the physical
edge sources at the selected cubic `a`, but does not yet prove whether `a`
is in the core or whether its own arm has length zero. The next local proof
must use first entry and nodup to establish that membership of the starting
vertex in the core makes its arm singleton.

Verification: the owner `lake env lean -j 1
Hypostructure/Graph/Strategy/HomogeneousBottleneckRows.lean` exited 0;
the direct EG caller `lake build
HypostructureErdos64EG.Assembly.Surplus.Local` exited 0 after 8777 jobs;
`git diff --check` exited 0. The returned `Holds`, exact ledger and any
quantitative account are unchanged. No crossing, physical escape, or branch
closure is asserted.
