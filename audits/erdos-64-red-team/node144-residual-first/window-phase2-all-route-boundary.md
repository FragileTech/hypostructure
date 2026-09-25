# [144a] window history: boundary of the full source-route support

Fix the literal post-[144] window ledger on `G = selected.object` and **one**
`typeBHandoff` witness with its original matching or star `P`, token `t`,
role `r`, and common root `ρ = tokenRoot t`. For every source demand
`d ∈ e ∈ P`, its retained pattern statement provides a declared simple
route from `ρ` to `d.2`. Choose one such route for each demand, all within
this same witness. Let `R` be the union of their actual edges and route
vertices, and `T=V(R)`. The family is finite and `R` is connected because
every selected route contains `ρ`. It is nonempty. This choice records
physical reuse: different indices may select identical edges or segments.

The selected graph `G` is connected by the retained capacity-token ledger
and bridgeless by its separate retained key. Therefore every component
`C_i` of `G-T` attaches to `T`, and its boundary size
`k_i=|δ_G(C_i)|` is at least two. A single boundary edge would be a bridge
of the **actual** graph `G`. This is a different cut from the earlier
edge-Menger cut *inside* the route-union graph: that auxiliary cut was not
shown to disconnect `G`. If `T=V(G)`, the exterior family is empty and
no outside attachment is claimed.

Put `J=E(G[T]) \ E(R)`. Since `R` is connected and has exactly vertex set
`T`, each distinct edge in `J` contributes one unit to relative cycle
rank. Counting every exterior component once gives the exact identity

```
β(G) = β(R) + |J| + Σ_i [β(G[C_i]) + k_i − 1],
```

where `β(X)=|E(X)|−|V(X)|+c(X)`. Here both `G` and `R` are connected.
There is no component-merger correction because the route support already
contains a connected path from the common root to every selected terminal.
Bridgelessness gives a raw cost of at least one rank unit per distinct
exterior component, but several route indices or spare incidences can
share that component. An apparent spare edge may already be one of the
selected route edges; then it contributes nothing to `J`.

The earlier reviewed terminal count still provides distinct route
terminals from the large source pattern, but it does not force a lower
bound on `β(R)`, `|J|`, or the number of exterior components. The
terminals could lie on repeated or overlapping paths. No source-indexed
assignment to a distinct rank term, bounded multiplicity, cycle-length
obstruction, cap, or closure follows from this account alone. The
unresolved interaction is whether the retained same-token labels and
normal form restrict that physical reuse enough to turn the original
pair count into an actual cost on this **full** route support.

Sources: complete window history in `phase0-evidence.md`; reviewed
`window-phase2-route-overlap.md`, `window-phase2-exterior-cut.md`, and
`window-phase2-relative-cycle-rank.md`; prior failed consumer in
`window-phase5-terminal-significance.md`.
