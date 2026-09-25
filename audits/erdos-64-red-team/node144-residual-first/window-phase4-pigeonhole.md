# [144] window arm: finite-label collision mechanism (Phase 4.1)

**Exact textbook statement.** For any finite pattern `P` and map `label`
into a finite alphabet `Label`, if `Fintype.card Label < P.card`, then there
are distinct `first, second ∈ P` with equal labels. The repository theorem
`SameTokenRoutingGerms.exists_same_routingLabel` states this with
`labelBound Label = Fintype.card Label`. No graph fact is built into the
pigeonhole theorem.

**Application candidate.** On the tagged window [144a] arm, the source
`HomogeneousBottleneckPatternStatement` has a selected matching or star of
size at least `SameTokenRoutingGerms.patternBound Label`, which is the label
bound plus one. The routing owner instantiates this theorem separately for
matching and star at lines 1390–1395 and 2236–2241. The output is two
**original edges of that selected pattern**, not a new pattern. They carry
the same selected token and role because the whole pattern lies in that
role fibre. The selected demands are chosen from those two edges in the
owning proof.

The mechanism alone neither constructs a separator nor proves a cap. Its
role in the candidate move is to supply two source indices that must remain
attached to the later first-separator/envelope construction. The remaining
mechanisms and branch outcomes require separate tasks. This step duplicates
an established selection, so its possible novelty is retention of the
indices through the handoff, not another pigeonhole estimate.

Sources: `SameTokenRoutingGerms.lean:143–163`;
`HomogeneousBottleneckRows.lean:1378–1406,2224–2251`.
