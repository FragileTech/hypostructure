# [144a] terminal-count attempt fingerprint

| Field | This candidate |
|---|---|
| Technique | Finite neighbour counting after projecting distinct selected surplus demands to route terminals. |
| Exact observable | For the actual handoff pattern `P`, the fibres `D_v={d∈⋃P:d.2=v}` and the induced source-edge-to-terminal charge. |
| Retained object | The same `selected.object G`, same certified handoff capacity, token, role, source pattern, and declared routes. |
| Hypotheses | Canonical two-demand schedule; source pattern in its role fibre; excess-port high-centre adjacency; global high-centre normal form; registered threshold `3` and `L_geom≥3`. |
| Proposed construction | Select a distinct demand from each pattern edge, project to `d.2`, and prove the at-most-three terminal fibre. No graph change, envelope re-selection, or altered token account. |

The checked same-token routing owner already uses finite-label pigeonhole on
`P`, chooses **two** same-label source edges, applies the common-root route
dichotomy, and produces one decorated envelope on its high-separator arm. It
does not count every original demand by its terminal or bound the terminal
projection's fibres (`HomogeneousBottleneckRows.lean:1378–1406,1710–1756,
2205–2251,2580–2627,3061–3112`). Repeating its two-edge selection would
not be new.

The earlier near-cubic repair retains all original source pairs as event
tags and proves their combinatorial count. Its unresolved consumer is an
assignment with bounded multiplicity at actual high centres or envelope arms
(`near-cubic-repair/execution.md:198–260`). That attempt does not prove the
terminal fibre bound. The new count is therefore on a different physical
projection of the **same** original demands, not a relabelling of event tags.

The terminal bound cannot be substituted for the missing event-to-centre or
event-to-envelope capacity: many routes with distinct terminals may still
share an initial edge or high separator. The candidate's immediate effect is
only the effective terminal count and exclusion of all-root routes. It has
not yet passed the Phase 5 payoff or construction gate.
