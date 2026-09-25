# [144] reconcile the one-unit attachment cost

All counts below refer to the **same** selected graph `G` in the
fifty-key [144a] window history and to one actually produced
matching or star envelope. Write `n=|V(G)|`, `m=|E(G)|`, and let `s`
be the retained surplus in `2m=3n+s`. The selected graph is connected,
so

```
β(G)=m−n+1=(n+s)/2+1.
```

The equation implies `n+s` is even; the displayed half is an exact
integer, not a rounded estimate. The reviewed forced-edge plus
bridgeless argument gives `β(G)≥β(F)+1`, hence the only new comparison
with this global account is

```
β(F) ≤ (n+s)/2.
```

This is an upper bound on the rank of **this chosen skeleton relative
to the existing global rank**. It is not an upper bound on `β(G)` or
on the number of original source pairs.

For the actual envelope vertex set `S`, put
`I=E(G[S])∖F`. For each component `C` of `G−S`, retain its internal
rank `β(G[C])` and total physical boundary count `k_C`. The accepted
Phase 2 account states exactly

```
β(G)−β(F)
  = |I| + Σ_C (β(G[C])+k_C−1) − (c(F)−1).
```

The component repair established `c(F)∈{1,2}`. Combining this formula
with the one-unit lower bound yields the necessary **net** balance

```
|I| + Σ_C (β(G[C])+k_C−1) ≥ c(F).
```

Thus the raw internal/exterior terms total at least one when `F` is
connected, and at least two when it has the one isolated core vertex.
In the latter case one raw unit may merely join the two skeleton
components; a further unit is still required by the bridgeless
return cycle. This is a total over physical edge and component terms.
One exterior component can receive several indexed incidences, and
one edge can serve several fan or source indices, so none of the raw
terms is copied for each use.

The old account and the new forced edge are now reconciled without
double counting. The source pattern still has `|P|≥Q_geom+1`, but no
map assigns every `p∈P` to a distinct unit of this net balance, and
no bounded multiplicity estimate or upper capacity on these units
is retained. Consequently the comparison does not supply the
homogeneous cap, near-cubic estimate, a target cycle, or [144a]
closure. The witness and rank restriction also remain owner-local;
their source-bound export through `typeBHandoff` is the immediate
formal obligation before the residual itself can be narrowed.
