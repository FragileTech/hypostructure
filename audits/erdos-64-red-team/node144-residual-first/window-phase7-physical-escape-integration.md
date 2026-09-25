# [144] locate the omitted edge before charging it

The accepted [144] producer proof supplies an actual neighbour `x` of
`a=nextLeft` with `s(a,x) ∉ F`, where `F` is the literal skeleton of its
own constructed envelope. Define the envelope vertex region on that same
graph by

`S = core ∪ armLeft.toFinset ∪ armRight.toFinset ∪ {separator}`.

The centre edge `s(a,separator)` is in `F`, so the omitted edge cannot end
at `separator`. Graph looplessness also gives `x ≠ a`. With these
exclusions, the following **ordered disjoint** cases cover every possible
endpoint, including arm/core overlaps:

1. `x ∈ core` (even if it is also on either arm): an unused edge into the
   core. If `a ∈ core`, the induced core-edge part of `F` rules this case
   out; that consequence still needs to be checked on the actual core.
2. `x ∉ core` and `x ∈ armLeft`: an unused own-arm edge. If `x` also lies
   on the right arm, retain that overlap as a flag within this case.
3. `x ∉ core ∪ armLeft.toFinset` and `x ∈ armRight`: an unused cross-arm
   edge.
4. `x ∉ S`: a genuine boundary edge from the envelope vertex region to
   the rest of the selected graph.

Cases 1–3 lie inside `G[S]` but outside `F`; case 4 lies in the cut
`δ_G(S)`. These have different accounts. Once `F` is proved connected
and spanning on `S`, an internal unused edge contributes one to the
cycle-rank difference between `G[S]` and `F`. An edge to an outside
component contributes to that component's boundary multiplicity; a
single attachment can be a bridge and contributes no cycle by itself.
The component and cycle-rank identity must be proved with its connectivity
and edge-disjointness hypotheses before assigning an unconditional charge.

The next one Lean task is the exact disjoint location classification of
the checked witness on both producer histories, retaining the original
`a`, `x`, `F`, `core`, arms and centre. The subsequent tasks are to prove
the internal/chord versus external/cut identities, and to expose the
profile through the same-token handoff's existing ExactLedger proposition.
The current exported proposition does not retain the witness, so no
productive-move credit is assigned yet.

Closure scan: no target cycle follows just from an unused graph edge;
there is no smaller admissible graph for minimality; and no compatible
cycle-rank or capacity contradiction has yet been assembled. [144a]
remains open with its full inherited state.
