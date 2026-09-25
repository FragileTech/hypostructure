# [144a] positive marked-edge splice implication

Let `B` be the full literal [144] matching/star producer conjunction, including the original source pattern, its fixed equal-label `p,q` and demands, and the maximal valid configurations `r_p,r_q` on their own routing supports. Let `O` assert the exact marked-edge splice prerequisites of P4-window-61: a q-suffix hit `v_j` with `j≥1`, the displayed candidate's cross-disjointness/nodup, and membership of its new vertices in the *q* support. The root and terminal buffer are those of the unchanged q configuration. All objects live on the same selected `G`.

Write `H=C++[h]`, `D_q=b::B_q`, and uniquely split `D_q=D_0++[v_j]++T_j`. The candidate is `r'_q=H++[a,x,v_{t-1},…,v_j]++T_j`, with the obvious empty middle when `j=t`. Its chain consists of old q's chain along `H`, the original p edge `h–a`, the new physical edge `e=a–x`, reverse edges of the simple `G−e` return from `x` to `v_j`, and old q's chain along `T_j`. The join at `v_j` is the original q edge to the first vertex of `T_j` when that tail is nonempty. Each edge is an edge of the same `G`.

The return path gives nodup *inside* its reverse segment. `O` supplies disjointness from `H` and `T_j`, including the possible reappearance of `a`; hence the entire candidate is nodup. Old q's `inside` field covers `H` and `T_j`; `O` covers the new segment in the exact `capacity.sameTokenRoutingSupport token q`. Its first vertex is unchanged, so the old q `issued` witness still gives the same token source and root. Its last vertex is unchanged, so the old q `lands` witness still gives the same selected local buffer and fixed demand. Thus all five `RoutingConfiguration` fields—`chain`, `nodup`, `issued`, `inside`, and `lands`—hold for `r'_q`. The p route is unchanged.

The old paths have `r_p=C++h::a::A` and `r_q=C++h::b::B_q` with `a≠b`, so their common-prefix length is exactly `|C|+1`. The candidate begins `C++h::a`; hence its common prefix with `r_p` has length at least `|C|+2`. This strictly exceeds the chosen maximum among valid configurations for the *same* `p,q,d_p,d_q,token,root`. Therefore

```
B ∧ O → False.
```

Equivalently, each owner-local marked return satisfies `¬O`. Expanding `¬O` leaves the exact disjunction: no q-suffix hit with index `≥1`; or a hit exists but the e-led detour collides with the old prefix; or it leaves q's exact support; or it collides with the retained q suffix (including `a`); or a remaining route field fails under assembly. The source and buffer fields in the stated candidate follow from unchanged head and tail, but this must be checked when the formal list expression is installed. The disjunction is not itself a useful cap, distinct cost, target cycle, or [144a] closure. Each survivor keeps the full original ledger, and source-bound `typeBHandoff` export remains unproved.
