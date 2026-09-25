# [144] integrate the selected cubic neighbours

The accepted Phase 6 construction specialized `highCentreNormalForm` to the
**actual** adjacent vertices `a=nextLeft` and `b=nextRight` of the high first
separator `h=separator` in both matching and star owner arms. Thus each has
ambient degree three in `G=selected.object`, with one known incidence to `h`
and two non-centre incidences. The same owner arms retain the fixed-source
maximal route pair and construct the first-entry arms `P_a,P_b` and
`Y={left.2,right.2}`; no chosen object or source index has changed.

The previously unaccounted observable is the location of the **other two
physical edges at each of `a,b`** relative to the exact constructor skeleton

```
F = E(P_a) ∪ E(P_b) ∪ {ha,hb} ∪ E(G[Y]).
```

This uses the two-arm attachment geometry, not a repeated aggregate degree
estimate. Under the conditional premise that every edge incident to `a` or
`b` lies in `F`, the cubic budgets require two non-centre incidences at each.
The first-entry condition makes a zero arm contribute no edge and puts its
start in `Y`; the other arm starts at the other assigned vertex, while the
two-vertex core contributes at most one incident edge. Both zero-arm
possibilities must therefore be ruled out. With positive arms, `a,b∉Y`, so
the core contributes nothing at either start. Its own simple arm contributes
exactly one edge at its start; the second non-centre edge must be supplied by
the opposite arm. That forces `a` into the interior of `P_b` and `b` into the
interior of `P_a`. This conditional topology is mathematically reviewed in
`window-phase2-two-tail-topology.md`; it is **not yet a Lean theorem**.

The next atomic construction is to formalize the exact skeleton and prove the
first crossing inference, `a∈P_b`, from the all-in-`F` premise and the selected
degree-three facts, including the zero-arm/core cases. A following task must
prove the symmetric placement and the valid splice of the original common
prefix through `h-a` to the old right-route suffix at `a`. That splice must
preserve the original right support, source and buffer and strictly improve
`maximalPrefix`; until it is checked, the physical escape is unproved.

Constraint test: the degree facts alone exclude no returned handoff; the
all-in-`F` crossed-tail contradiction remains the exact pending implication.
Compression test: no replacement object or decrease exists. Quantity test:
there is no additional demand/capacity or cycle-rank charge. No account
changes, no homogeneous cap or near-cubic estimate is obtained, and the weak
`typeBHandoff` `Holds` remains unchanged. The branch and move remain open.
