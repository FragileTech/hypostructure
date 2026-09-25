# [144] first failure of the connected-skeleton proposal

The proposed claim that the actual two-arm skeleton `F` is always
connected is not supported by its constructor. Write
`Y={u,v}`, `T={h}∪V(A)∪V(B)`, and `S=T∪Y`. Each arm is a graph chain,
starts at its selected neighbour of `h`, and ends at its **first** entry
into `Y`. The centre edges and the two arm edge sets make `F[T]`
connected, and at least one vertex of `Y` lies in `T`. They do not
show that **both** vertices of `Y` lie in `T`.

In particular, both arms may first enter the same core vertex `u`.
Their first-entry clauses then permit `v∉T`. If `u` and `v` are
nonadjacent, the induced core-edge term `E(G[Y])` is empty and `v` is
isolated in `F`. This is a local model of the available arm and core
clauses, not a claimed counterexample satisfying every fact of the
full fifty-key residual. The missing inference is an actual proof of
second-core-vertex coverage or a core edge. Neither is supplied by
the current producer proof.

The existing Phase 2 rank identity already includes the correction
`−(c(F)−1)`. Removing it now would repeat the old count with an
unproved premise. The repair is to prove the exact two-component
dichotomy on this producer: the arm/centre component contains every
arm vertex and at least one core vertex; any other core vertex is
either joined by the induced core edge or is the single isolated
component. Then the forced non-`F` edge must be classified by whether
it creates a cycle or merely joins those components. This is the
attachment interaction that the proposed connectivity shortcut
would have hidden.

The node [144a] remains open. There is no target cycle, rank surplus,
cap, or closure in this note.
