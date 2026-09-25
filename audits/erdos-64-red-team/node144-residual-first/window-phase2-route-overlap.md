# [144] window arm: overlap of the full source route family

Fix one witness of `typeBHandoff` on the selected graph `G`, including its
certified capacity ledger, token `t`, role `r`, source matching or star `P`,
and common root `ρ = tokenRoot t`. The `HomogeneousBottleneckPatternStatement`
inside this same witness gives, for every edge `e ∈ P` and each demand
`d ∈ e`, a declared simple configuration whose path starts at `ρ`, ends at
`d.2`, and stays in the corresponding declared routing support. Since `P`
is finite, one may inspect any simultaneous selection of these existing
configurations. The observable is their **physical overlap relation** in
`G`: which selected path pairs use a common vertex, edge, first neighbour,
or first separator. Its values have not been established.

The retained `highCentreNormalForm` holds at every high centre of `G`; it
constrains the degrees and adjacency pattern of that centre's neighbours.
The retained `returnAvoidance` excludes its stated return lengths on every
dart of `G`. These restrictions apply to the same graph as every selected
configuration. They do not by themselves assert that a route passes through
a particular high centre or that two routes form a forbidden return.

There is one exact conditional overlap restriction already available from
normal form. If two of these paths leave the same high vertex `h` through
distinct neighbours `x` and `y`, then both `x` and `y` have degree equal to
the baseline. If `x` and `y` are nonadjacent, they cannot have a common
neighbour `z ≠ h`. This follows by applying `NormalForm.neighbourTight` and
`NormalForm.noCommonNeighbourOutside` to the path edges `hx` and `hy`.
It reuses an established graph fact on actual route vertices; it does not
establish how often such a departure occurs in the source family.

The [144] routing owner already selects **two** same-label pattern edges and
uses two configurations to construct one surviving decorated envelope. It
does not classify the overlap relation for the remaining edges of `P`. The
earlier `near-cubic-repair/execution.md` counted source-indexed extraction
events and tested a centre assignment; it left repeated physical incidence
uncontrolled. This register asks for the missing *path-level* relationship:
which overlap profiles of the full configuration family are compatible with
normal form and return avoidance while the original matching or star remains
positive? No multiplicity bound, cycle, capacity charge, or structural move
is claimed.

This is about the one handoff witness. The window-class token from the
separate `windowClassOverload` existential is not identified with `t`.

Sources: `ObjectCapacityLedger.lean:623–682`;
`SameTokenRoutingGerms.lean:216–249`;
`SpineVocabulary.lean:3944–3995,10220–10229,8324–8327`;
`HighCentreNormalForm.lean:69–99`;
`HomogeneousBottleneckRows.lean:1378–1406,2205–2251,3061–3112`;
`near-cubic-repair/execution.md:200–310`.
