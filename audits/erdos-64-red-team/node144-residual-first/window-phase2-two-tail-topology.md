# [144a] window history: exact two-tail skeleton topology

Work on the **producer-local** envelope at either matching or star constructor in `sameTokenBottleneckRoutingRow`, on the selected graph `G`. The owner takes the two selected routing configurations with distinct first-separator neighbours `a,b` at `h`. It sets `Y={u,v}`, where `u,v` are their selected terminal vertices and may coincide. It truncates each route suffix at first entry into `Y`, obtaining simple arms `P_a` from `a` and `P_b` from `b`. Each arm meets `Y` only at its last vertex. The full source routes are simple and contain `h` before these suffixes, so `h∉Y` and neither arm contains `h`. The constructor sets `H={h}` and `K_h={a,b}`. The *published* handoff retains none of `Y={u,v}`, `H={h}`, or `K_h={a,b}` as cardinality/equality fields; the present claim is about the actual owner construction.

For this envelope the declared skeleton is exactly

```
E(F)=E(P_a) ∪ E(P_b) ∪ {ha,hb} ∪ E(G[Y]).
```

The last set is empty when `u=v` or `u,v` are nonadjacent, and otherwise contains the single edge `uv`. Arms may intersect, share edges, or pass through the other assigned neighbour. Their first-entry property rules out an interior vertex in `Y`. In particular, an arm starting in `Y` has length zero. No connectedness of `Y` is assumed.

Now impose the **conditional** all-in-skeleton outcome `D_I=D_∂=∅` for this same envelope. The retained high-centre normal form makes `a,b` cubic. Their centre edges lie in `F`; the all-in-`F` condition puts their two other ambient edges in `F`. Hence `d_F(a)=d_F(b)=3` and both have degree two in `F-h`.

First, neither arm can have length zero. If `P_a=[a]`, it contributes no edge and `a∈Y`. At `b`, the only possible incident non-centre edges of `F` then come from its own arm at its starting point (at most one) and the one possible edge of `G[Y]`. If `b∈Y`, its own arm also has length zero, so it has at most the core edge; if `b∉Y`, the core edge is not incident to `b`, so it has at most its own first arm edge. Either way `d_{F-h}(b)≤1`, contrary to two. The same argument with the arms exchanged excludes `P_b=[b]`.

Both arms therefore have positive length, and their first-entry property gives `a,b∉Y`. The core edge is incident to neither. If `a` were absent from the interior of `P_b`, then the only non-centre edge of `F` incident to `a` would be the first edge of its own simple arm. This contradicts `d_{F-h}(a)=2`. Thus `a` is an internal vertex of `P_b`. Symmetrically, `b` is an internal vertex of `P_a`. Each arm's first edge at its own start must coincide with one of the other arm's two incident edges there, since the ambient degree is cubic. The two arms consequently cross each other's starting vertices, and `F-h` has an `a`–`b` path. Together with `ha,hb`, it gives a simple cycle through `h`; its length is **not** asserted to be accepted by the target predicate. `FanSafe` already excludes accepted lengths for such returns.

This result is strictly sharper than `d_F(a)=d_F(b)=3`: the all-in-`F` survivor has a crossed two-tail topology. Equal terminals, an adjacent terminal pair, shared edges, and a disconnected two-vertex core do not evade the argument. Zero-length arms are ruled out only under the all-in-`F` condition, not from the handoff alone. The new topology is not yet a published `Holds` proposition and does not by itself identify a target-defective quotient, a compression, a source-wide cost, or a closed branch.

Sources: exact owner at `hypostructure/Hypostructure/Graph/Strategy/HomogeneousBottleneckRows.lean:1844–1950,2195–2222,2712–2815,3050–3078`; constructor at `hypostructure/Hypostructure/Graph/DecoratedHandoffEnvelope.lean:1115–1165`; reviewed `window-phase2-incidence-ledger.md`, `window-phase2-two-arm-erasure.md`, and `window-phase3-two-arm-tension.md`.
