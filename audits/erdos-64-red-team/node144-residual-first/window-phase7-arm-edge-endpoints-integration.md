# [144] integrate arm-edge endpoint membership

The accepted local lemma applies to the two actual lists in the [144]
matching/star constructor. In the conditional all-in-`F` case, suppose
`a=nextLeft` is absent from the opposite first-entry arm `P_b`. Then no edge
of `armEdgeSet P_b` can be incident to `a`, because either endpoint of such
an edge belongs to `P_b`. This is a genuine elimination of one part of the
exact skeleton **under that conditional case**; it does not assert that `a`
is absent or that all physical edges at `a` lie in `F`.

The known centre edge `ha` occupies one of `a`'s three ambient incidences.
If the opposite arm is absent as a payer, the only possible non-centre
sources inside `F` are `armEdgeSet P_a` and `E(G[Y])`. Because `P_a` is simple
and starts at `a`, its own incident edges should consist of its unique first
edge when it has positive length and none when it is the singleton `[a]`.
First-entry into `Y` should make the singleton case exactly the case in
which `a∈Y`; the two-vertex core can then contribute at most one edge.
This combined bound of at most one non-centre incidence remains to be
proved in Lean. It is the next atomic local property; only then may the
degree-three contradiction force `a∈P_b`.

Constraint test: the endpoint lemma alone excludes no current handoff; it
removes a payer only in the proposed all-in-`F`, `a∉P_b` case. Compression:
no new object or decrease. Quantity: no new demand/capacity or global
charge; the degree budget is local and not yet exhausted. The accepted
`typeBHandoff` `Holds` and full inherited ledger remain unchanged. The move
and branch stay open.
