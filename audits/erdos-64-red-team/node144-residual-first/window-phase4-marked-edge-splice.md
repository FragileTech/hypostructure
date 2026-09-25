# [144a] marked-edge splice candidate and its exact prerequisites

Work only in the fixed [144] matching/star producer on `G`. Write the selected simple configurations as

```
r_p = C ++ h :: a :: A,       r_q = C ++ h :: b :: B,       a≠b,
P_e = (v_0=a,v_1,…,v_t=x),   t≥2,                       e={a,x}∉F.
```

`P_e` lies in `G−e`, so `a,x,v_{t-1},…,v_1` is a simple sequence and every consecutive reverse edge is in `G`. The actual edge `a–x` supplies the one new step that the old skeleton did not have. Let `D_q=b::B` be the old q suffix. If some `v_j`, `1≤j≤t`, occurs in `D_q`, take the **largest** such `j`, the first hit when scanning `P_e` backward from `x`. Decompose the old q route uniquely as `r_q=Q_{≤ j} ++ v_j :: T_j`, where `Q_{≤ j}` ends immediately before `v_j`; the selected route's nodup makes the occurrence unique. Define the candidate

```
r'_q = C ++ h :: a :: x :: v_{t-1} :: … :: v_j :: T_j.
```

When `j=t`, the reverse segment is empty and the new part is exactly `h–a–x`. For `j<t`, its first edge after `a–x` runs backward along `P_e`. The candidate uses `e` in every case; merely following the old right arm would be the previously checked right-shortcut analysis and is not this move.

This is a standard simple-path splice **only under all of these prerequisites**:

1. The chosen `v_j` lies in the q suffix after `h`; a hit only in `C++[h]` is unusable. The old q suffix following `v_j` is exactly `T_j`, so the same terminal and local buffer are retained.
2. The sequence `C++[h,a]` and the marked detour `x,v_{t-1},…,v_j` do not repeat a vertex; the detour's interior avoids the retained `T_j`, and `a` does not occur in `T_j`. Equivalently the displayed entire candidate is nodup. `P_e` simplicity alone does not imply these cross-disjointness conditions.
3. Every vertex of the new segment `a,x,v_{t-1},…,v_j` lies in the **q pair's** exact `capacity.sameTokenRoutingSupport token q`. Membership in the p support or in the union of supports is insufficient.
4. The original root `ρ`, the source token support, q's selected local buffer, and the fixed q demand are unchanged. Graph-chain uses `h–a`, the physical `e=a–x`, the reverse edges of `P_e`, and the old q suffix edges. No quotient or new graph is substituted.

Under these hypotheses `r'_q` is a `RoutingConfiguration` for the original q pair and demand. It begins `C++h::a`, just like `r_p`; the old `r_q` begins `C++h::b` with `a≠b`. The common-prefix length therefore strictly exceeds that of the chosen maximal pair, contradiction. This is the conditional positive arm to prove in Phase 5, not a theorem already obtained merely from `HasReturn`.

The complement is an exact disjunction of failed prerequisites: (i) no `P_e` vertex with index `≥1` reaches the q suffix; (ii) a first reverse hit is in the old prefix or the proposed segment meets that prefix; (iii) the segment leaves q's own support; (iv) it repeats a vertex of the retained q suffix, including a possible later occurrence of `a`; or (v) another `RoutingConfiguration` field, such as source or fixed buffer, fails under the proposed assembly. Several failures can coexist; ordered tests may make them disjoint later. None currently pays a distinct edge, rank unit, or source-pair cost. The endpoint `x` may lie in any of the four reviewed location cases, including outside `S`, and the return may have multiple exterior excursions. The branch remains open in every unproved complement arm.

The attempt fingerprint is the triple `(p,q,e)` together with the **same** `G−e` return path and the largest reverse index `j`. It preserves the fixed pair-specific supports and the source label equality. The earlier all-in-`F` uncrossing used no edge outside `F`; the earlier right-shortcut considered the old routed tails. This candidate spends the newly forced physical edge and is not admitted as a productive move until the positive conditional and all complement payoffs have been proved and integrated.
