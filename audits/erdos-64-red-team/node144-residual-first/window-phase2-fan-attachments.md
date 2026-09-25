# [144a] window history: where the fan neighbours' other edges go

Fix the literal post-[144] window-arm ledger on the selected graph `G` and
choose the source and envelope carried together by **one** `typeBHandoff`
witness. Let `Y` be that envelope's core, `H` its decorations, and `K_h`
the assigned first neighbours at `h ∈ H`. Let `S` be the vertex union of
`Y`, `H`, and every recorded handoff arm. This definition only names a set
already determined by that envelope; it changes neither the graph nor the
original blocked-pair account.

For each `a ∈ K_h`, the retained high-centre normal form gives
`d_G(a)=3`. One incident edge is `ha`. The other **two** incidences are the
actual local observable. Partition them by whether their other endpoint is
in `S`, and, for those outside `S`, by the connected component of `G-S`
that contains that endpoint. Also record whether an edge inside `S` belongs
to a named arm, lies in `Y`, or is another edge of the induced support.
This is a finite incidence relation on the same graph and envelope.

The word *spare* needs care. If an arm has positive length **and its first
edge is distinct from `ha`**, one non-`h` edge at its first neighbour
continues that arm; its other edge need not leave `S`. It may join the
core, another arm, or another decoration. The literal retained envelope
does not exclude a positive arm `[a,h]` when `h` also lies in the core:
its first edge is then `ha`, leaving both non-`h` incidences unaccounted
for by that arm. If the arm has length zero, `a` already lies in `Y`;
both non-`h` edges may lie inside `Y`. The published handoff guarantees a nonempty `K_h`, not a
positive count of edges from these neighbours to `G-S`. Accordingly the
outside-incidence set may be empty. No outside return may be postulated in
that case.

The previous Type B local incidence account counts the two non-`h`
incidences **only for a cubic-closed fan neighbour**, whose other neighbours
already lie in its assigned support. It partitions those counted incidences
by window and non-window destinations. The [144a] handoff makes each assigned
first neighbour cubic but does not make it cubic-closed, so that prior count
does not cover every neighbour in this inventory. The interaction still unmeasured
for [144a] is the **simultaneous attachment pattern**: which assigned
neighbours' outside incidences enter the same component of `G-S`, where
those components attach back to `S`, and whether the remaining source
pattern's declared routes meet these same components. The last relation
is unknown. The `typeBHandoff` proposition retains all source pairs and
one envelope but does not assign every pair to an arm or attachment.

This is Phase 2 inventory only. The two cases `outside-incidence set = ∅`
and `outside-incidence set ≠ ∅` remain live at this point. No return path,
cycle length, pair-to-component map, charge, or closure follows from this
record alone.

Sources: `erdos_64_proof.tex`, definitions
`def:typeB-fan-safe`, `def:marked-typeB-fan`, and
`def:decorated-fan-envelope` (lines 10845–10946); [144] routing lemma
`lem:same-token-bottleneck-routing` (lines 5565–5651); pinned exact ledger
in `phase0-evidence.md`.
The literal envelope contract is in
`DecoratedHandoffEnvelope.lean:902–940`; the handoff proposition exposing it
is in `SpineVocabulary.lean:3944–3979`. The concrete [144] producer's local
separator avoidance is not a retained field of that proposition.
