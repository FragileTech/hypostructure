# [144] the forced unused edge pays one cycle-space unit

Fix either actual matching or star producer in the full [144a]
window-history ledger. The checked proof supplies the **physical** edge
`e=s(a,x)∈E(G)` with `e∉F`, where `F` is the same producer's literal
two-arm skeleton. The accepted component repair proves that every edge
of `F` is an edge of `G` on the producer's vertex region `S` and that
`c(F)` is either one or two. Regard `(S,F)` as a spanning subgraph on
all of `V(G)` by adding isolated vertices outside `S`; this does not
change its cycle rank.

The retained `K.bridgeless` proposition says every ordered physical
edge contraction has a return path after that edge is deleted. Apply
it to the contraction with tail `a`, head `x`, and adjacency supplied
by the checked witness. Its return path is a simple `a`-to-`x` path
in `G−e`. Together with `e` it forms a simple cycle `C` of `G`
containing `e`.

Over `𝔽₂`, embed the cycle space of `F` into the cycle space of `G`
by extending edge indicators by zero on `E(G)∖F`. Every vector in
the image has `e` coordinate zero. The indicator of `C` has `e`
coordinate one, so it is outside that image. The dimension formula
for a finite graph's cycle space is

`dim Z₁(H)=|E(H)|−|V(H)|+c(H)=β(H)`.

It follows, for this **same** selected graph and actual producer
skeleton, that

`β(G) ≥ β(F)+1`.

This argument applies whether `x` is an internal core/arm endpoint or
outside `S`. In the possible two-component `F` case, an individual
outside-`F` edge might first merge the components and contribute zero
to the *partial* edge-addition rank. The return path required by
`K.bridgeless` completes a cycle with at least one edge outside
`F`, so the **total** graph still has an independent cycle-space
unit. In the Phase 2 edge/component formula, this is a net unit
after its `−(c(F)−1)` correction, not a second charge added to each
boundary incidence or each source pair.

The generic Phase 2 account knew how to count `F`, internal edges and
outside components, but it did not prove a non-`F` edge existed for
this extremally selected handoff. The new input is that forced edge;
the retained bridgeless fact makes its cost unavoidable. This is one
unit for **one** chosen envelope. No injection from all source pairs,
upper bound on `β(G)`, target cycle length, homogeneous cap or closure
of [144a] follows. The witness and this inequality are still not
exported through `typeBHandoff`; the next local consumer must compare
this one unit with the actual retained capacity/rank account or
derive a sharper restriction from the marked return cycle.
