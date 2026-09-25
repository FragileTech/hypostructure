# Conditional finite-set inference for the [144a] terminal count

Assume the complete window-arm ledger `B` and the Phase 5 output
`O : ∀v, |D_v|≤3` on **one** handoff source witness. Its pattern `P` consists
of distinct two-element demand sets, `|P|≥Q+1`, and `Q≥2`; hence `P` is
nonempty and has at least three edges.

If `P` is a matching, its different edges are disjoint as sets of demands.
Their disjoint union is `D`, so

\[
                         |D|=\sum_{e\in P}|e|=2|P|\ge |P|+1\ge Q+2.
\]

If `P` is a star with central demand `c`, every two-element edge has the
form `{c,d_e}` with `d_e≠c`. Distinct edges have distinct `d_e`; thus the
map `e↦d_e` is a bijection from `P` onto `D\{c}`. Since `P` is nonempty,
`c∈D`, and therefore

\[
                         |D|=|P|+1\ge Q+2.
\]

For either form, the sets `D_v={d∈D:d.2=v}`, indexed by
`T={d.2:d∈D}`, are disjoint and partition `D`. Finite summation and `O`
give

\[
             |D|=\sum_{v\in T}|D_v|\le\sum_{v\in T}3=3|T|.
\]

The routing alphabet contains at least two labels by varying the `Fin 2`
coordinate with all other coordinates fixed (they are inhabited in the
registered EG instance). Hence `Q≥2` and `3|T|≥Q+2≥4`. If `T` had at most
one vertex, `3|T|≤3`, contradiction. Thus `|T|≥2`. Deleting the single
common root `ρ` leaves a nonempty set `T\{ρ}`. Each member is the terminal
of an actual declared handoff route, because configurations are supplied
for every demand in every edge of `P`.

This proves the mathematical conditional `B ∧ O → G_term`; it does not prove
`O` as a Lean fact, establish route-edge congestion, or close [144a].
