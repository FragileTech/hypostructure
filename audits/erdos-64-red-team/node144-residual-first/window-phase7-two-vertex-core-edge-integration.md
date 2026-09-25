# [144] integrate the sole possible core edge

The accepted owner-local proof now identifies every edge of the actual
two-vertex core `Y={left.2,right.2}` with the sole possible undirected edge
between its named vertices. If they coincide or are nonadjacent, the induced
core contributes no edge. This is a bound on the physical edge source in the
same selected graph and handoff envelope; it assumes no core connectedness.

Combine it with the accepted unique own-arm first edge under the proposed
one-sided all-in-`F` case at selected cubic `a`. If `a∉Y`, no core edge can
be incident to `a`, so its own arm supplies at most one non-centre edge. If
`a∈Y`, the core can supply at most its sole possible edge. To exclude a
simultaneous own-arm first edge, the next proof must use the **actual**
`armLeftIssued`, `armLeftFirstEntry`, `armLeftLast`, and `armLeftNodup`:
membership of its start `a` in `Y` makes the first-entry terminal equal to
`a`; a nodup list with head and last both `a` is `[a]`. The star arm must
obtain the same relation from its own constructor facts. This is the one
next local inference. Neither membership case is assumed about the returned
handoff.

Once that relation is kernel-proved, the two cases should give at most one
non-centre skeleton edge at `a` unless the opposite arm contains `a`.
The combination with degree three and all-in-`F` is a later proof task; so
are the fixed-right-support splice and source-bound physical escape.

Constraint: no graph outcome is excluded yet. Compression: no smaller
admissible graph is produced. Quantity: this local edge-source bound does
not change a demand or surplus account and yields no homogeneous cap.
The present `typeBHandoff` `Holds`, move, and branch remain open.
