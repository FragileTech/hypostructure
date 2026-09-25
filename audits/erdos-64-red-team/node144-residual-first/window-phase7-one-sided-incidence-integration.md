# [144] integrate the physical edge count with the fixed source routes

The accepted owner now proves, separately in its matching and star producer
histories, `all edges of incidenceFinset(a) lie in F → a ∈ P_b`. Here `F` is the
literal skeleton of the handoff envelope actually returned by that producer,
`a=nextLeft` is its retained tight neighbour, and `P_b=armRight` is its actual
first-entry right arm. This excludes a saturated envelope whose left start is
absent from the right arm. It does not assert that the envelope is saturated.

The previously accepted route choice is source fixed: the left and right
`RoutingConfiguration`s have the original pair-specific supports and
selected terminals, and `maximalPrefix` compares them with every other valid
pair of those same types. `P_b` is a prefix of `nextRight :: tailRight`. If
`a ∈ P_b`, then `a` occurs in `tailRight`, since `a ≠ nextRight`. Split that
tail as `before ++ a :: after`. The proposed replacement right path is
`common ++ separator :: a :: after`, using the graph edge
`separator--a`; its suffix after `a` is the original right suffix. Every
vertex of this candidate was on the original right route, so the same right
routing support contains it. The original right terminal and source root are
retained. Its graph chain, nodup, issuance, terminal and support fields must
be kernel-proved before it is a valid `RoutingConfiguration`. The selected
left path begins `common ++ separator :: a :: tailLeft`; therefore the
candidate would share at least one more vertex with it than the original
right path beginning `common ++ separator :: nextRight :: tailRight`.

The next task is one exact conditional theorem on both producer histories:
`a ∈ P_b → False`, using that legal candidate and `maximalPrefix`. Its first
atomic construction can be a source-preserving shortcut lemma on the two
actual decompositions. If that theorem is checked, the accepted incidence
theorem will yield an edge in `object.graph.incidenceFinset a` outside `F`.
That edge would be a typed, physical attachment obstruction, not a cap or a
cycle in the selected graph.

Closure scan: the current conditional has no target-cycle witness or
constraint contradiction without the shortcut; it constructs no smaller
admissible graph for minimality; and it supplies no incompatible demand versus
capacity count. Thus [144a] remains open. Its exact retained state is the
original selected graph, source pair, packing, core, decorated envelope,
pattern and all incoming ledger facts, plus this newly checked conditional.
There is no newly selected residual arm yet, and no productive-move credit.
