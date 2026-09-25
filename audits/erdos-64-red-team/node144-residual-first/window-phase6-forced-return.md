# [144] kernel-check the return for the forced edge

The [144] owner now lists the inherited `K.bridgeless` fact among its
literal `Requires` and reads it through `inputs.get` on the same
`inputs.current.object`. In each actual matching and star producer,
the already checked `outsideSkeletonNeighbour` supplies one
`neighbour=x`, the adjacency `Adj_G(nextLeft,x)`, and the fact that
`e=s(nextLeft,x)` is outside that producer's literal skeleton `F`.

The owner constructs `EdgeContraction G nextLeft x` using that very
adjacency proof and applies `K.bridgeless`. It retains the same `x`,
adjacency and `e∉F` together with `HasReturn` for the ordered edge.
By the definition of `HasReturn`, this is a simple path from
`nextLeft` to `x` in `G−e`. No new graph, envelope, source pair or
edge witness is selected.

This is the precise new interaction with a previously retained
fact: bridgelessness was known for all physical edges, while the
extremal two-route argument newly forces this particular physical
edge outside its handoff skeleton. The mathematical cycle-space
argument and account reconciliation have separate reviewed notes;
this Lean task checks the return-path premise on the actual owner
branch. The owner file kernel-checks. The direct EG caller originally
lacked `FactKeys.Has (K .bridgeless) known`; accepted task
P6-window-56 added exactly this inherited premise to the same generic
`known` ledger. Both `Assembly.Surplus.Local` and its immediate strict
dependent caller now kernel-check, including all three uses of
`selectedBottleneckDischarge`. No sibling fact or alternate carrier is
involved.

This task does not kernel-prove a cycle-rank inequality or publish
the source-bound edge through `typeBHandoff` yet. [144a] remains open.
