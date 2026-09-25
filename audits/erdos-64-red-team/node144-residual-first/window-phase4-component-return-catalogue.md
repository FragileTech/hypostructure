# [144a] window history: catalogue the actual component-return move

Work on the literal post-[144] window ledger on `G=selected.object`
and one `typeBHandoff` envelope, with assigned cubic first neighbours
`a∈K_h`, support `S`, declared skeleton `F`, and physical
incidence sets `D_F,D_I,D_∂`. This candidate addresses their
**actual graph** destinations, not source-route overlap.

**Textbook component-return lemma.** If `ax∈δ_G(S)` is a non-`h`
edge at an assigned `a`, let `C` be the component of `G-S`
containing `x`. Connectivity and bridgelessness of `G` give a
second distinct boundary edge `ys∈δ_G(C)` with `s∈S`.
Connectivity of `C` gives a simple `x`–`y` path `P_C`
inside `C`, allowing `x=y`. If `s≠a`, then
`a-x+P_C+y-s` is a simple `a`–`s` path whose internal
vertices lie in `C`. If `s=a`, distinctness of the boundary
edges forces `x≠y`, and the same concatenation is a simple
cycle through `a`, not a simple path. The second-boundary assertion is **already
reviewed** in Phase 2. The proposed new use is to classify `s`
against the same assigned fan and obtain a branch-conditioned
restriction from that location.

The prerequisites are exact: `a∈K_h`, the actual edge
`ax∈D_∂`, `G` connected through the retained capacity-token
ledger, `G` bridgeless, and the one envelope's `S`.
There is no premise that `S` or `F` is connected, no premise that
`ax` exists, and no identification with the separately quantified
window overload witness.

Use the following **ordered** outcome list, with each earlier
existence predicate denied on later rows:

1. `D_∂≠∅`, and some component return lands at its same
   assigned neighbour `s=a`. It yields an actual simple cycle
   `a-x+P_C+y-a` of length `|P_C|+2`. If the selected arm at
   `a` has positive length and first edge distinct from `ha`,
   this landing is impossible by cubic degree; otherwise the
   length-zero and `[a,h]` exceptions remain.
2. `D_∂≠∅`, no row 1 return exists, and some return lands at
   `s=b∈K_h` with `b≠a`. The path through `C` is a
   `FanReturn` from `a` to `b` avoiding `h`; with
   `ha,hb` it makes a simple cycle of length
   `|P_C|+4`. This handoff's `FanSafe` excludes accepted
   shifted lengths and the instantiated
   `WindowLabelCollision.LabelCollision`, only.
3. `D_∂≠∅`, neither earlier landing exists, and some return
   lands elsewhere in `S`. The path `a`–`s` exists,
   but a path from `s` to `a` in `F` or `G[S]` is not
   supplied. The second landing may be in the core, a different
   decoration's fan, or an arm, with overlapping descriptions.
4. `D_∂=∅` and `D_I≠∅`. An extra internal physical edge
   exists. It can join components of disconnected `F` and so
   need not add one relative cycle-rank unit.
5. `D_∂=D_I=∅`, hence `D=D_F`. Both non-`h`
   incidences at every assigned cubic neighbour are represented
   in `F`. This is a locally saturated skeleton incidence
   profile; the literal handoff does not contain the
   certificate-marked fan data needed to invoke the paper's B1
   discharging charge.

The list is exhaustive because `D=D_F⊔D_I⊔D_∂` and every
exterior component return's landing is either its starting
`a`, another member of `K_h`, or neither. It remains exhaustive
when several outside edges enter one component: the first three
rows use existence, and later rows deny earlier existences.

**Candidate effects, not yet payoffs.** Rows 1–2 give identified
return lengths. Those lengths are known to avoid `LengthOK` by
`selection`, and row 2's shifted exclusion repeats `FanSafe`;
neither is a new contradiction. Row 3 locates an unclosed
attachment, row 4 an extra edge with an unresolved component
merger, and row 5 a fully internal fan incidence profile without
a certified B1 charge. Phase 5 must prove a *new* excluded
landing, valid compression, or effective cost on **each** row
before this candidate can be executed as a productive move.

**Fingerprint and rival.** The object is an actual `G-S`
component reached by a cubic fan neighbour, with the full
`F/I/δ(S)` complement. The prior Menger attempt cut an
auxiliary union of source routes and counted distinct terminals;
its separator need not be a cut of `G`. The current candidate
uses a real graph cut but cannot claim novelty from the already
reviewed second-boundary lemma alone. The paper's local B1
discharging is a rival for row 5, and its certificate-marked
prerequisite is currently absent. This catalogue selects the
component-return candidate **only for conditional payoff
verification**; it authorizes no construction or closure.

Sources: accepted `window-phase3-attachment-tension.md`,
`window-phase2-exterior-cut.md`,
`window-phase2-incidence-ledger.md`, and
`window-phase2-relative-cycle-rank.md`;
`DecoratedHandoffEnvelope.lean` definitions of `FanReturn` and
`FanSafe`; `SpineVocabulary.lean` definition of
`handoffAbsorbing`.
