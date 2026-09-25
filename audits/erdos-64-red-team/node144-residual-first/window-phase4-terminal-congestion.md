# [144] window arm: terminal congestion on the actual source pattern

Fix the one `typeBHandoff` witness on the selected graph `G`. Write `P` for
its matching-or-star source pattern and
`D = ⋃ (e ∈ P), e` for its selected ordered-port demands. For a vertex `v`,
write `D_v = {d ∈ D : d.2 = v}`. Every `e ∈ P` is a two-demand member of the
same role fibre. The fibre lies in the canonical port-pair schedule, and each
of its demands belongs to `G.excessPorts 3`. Thus, for `d ∈ D_v`, the first
coordinate `d.1` is a high centre adjacent to `v`.

The retained `highCentreNormalForm` applies at `d.1`, so its
`neighbourTight` clause gives `degree_G(v) = 3` whenever `D_v` is nonempty.
The map `d ↦ d.1` is injective on `D_v` because the second coordinate is
fixed, and its image lies in `N_G(v)`. Therefore

\[
                       |D_v| \leq 3 \quad\text{for every }v\in V(G).
\]

This counts **distinct original demand elements**, not route traversals:
many routes can still use one physical edge or centre arm. It does not
identify the separate `windowClassOverload` witness with the handoff token.

Each source edge can be assigned a distinct demand element across edges:
in the matching case choose either member of each edge, since edges are
disjoint; in the star case choose the member other than the common centre,
since distinct two-element edges have distinct noncentral members. (A finite
choice can be made using the object's existing vertex order.) Hence the
terminal of the chosen demand gives a map from `P` to `T` with fibres of
size at most three. This is a **candidate** bound on original source-edge
terminal congestion, not an injective indexing or a bound on route-edge
congestion.

The registered routing alphabet has at least two labels: hold its other
coordinates fixed and vary its `Fin 2` endpoint coordinate. The source
threshold is `L_geom = Q_geom + 1`, so `|P| ≥ 3`. If all selected routes
ended at the common root `ρ`, every chosen source-edge demand would lie in
`D_ρ`, forcing `|P| ≤ |D_ρ| ≤ 3`; this weak inequality alone does **not**
exclude the extremal three-edge case. Use the full demand set instead:
for three matching edges, `|D| ≥ 6`; for three star edges, `|D| ≥ 4`.
Either contradicts `|D_ρ| ≤ 3`. Thus a proved version of this mechanism
would exclude the all-root route outcome.

The earlier owner extracts two same-label edges and one decorated envelope.
The earlier source-indexed event count records all original pairs but leaves
their physical centre/arm multiplicity unbounded. This candidate counts a
different observable, original demand terminals; it would bound that one
projection by three. It does not give the physical route-incidence capacity
needed for the homogeneous cap or a payoff on both remaining Menger arms.

Sources: `ObjectCapacityLedger.lean:623–682`;
`CapacityTokenLedger.lean:123–141`;
`SparsePairLedger.lean:32–48`;
`ExcessPortFamily.lean:137–165`;
`SpineVocabulary.lean:10220–10228`;
`SameTokenRoutingGerms.lean:81–112`;
`Problem.lean:153–159,178–190`.
