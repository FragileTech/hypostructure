# [144] integrate first entry with the edge sources

The accepted [144] owner now proves all three exact source restrictions on
the same produced envelope: a simple arm has only its first edge incident
to its start; the two-vertex core has at most its one possible edge; and if
the start `a=nextLeft` belongs to that core, its actual first-entry arm is
`[a]` and has no edge. These are local, kernel-checked consequences of the
selected graph and constructor, not a homogeneous cap or a change to the
returned handoff.

The next conditional inference is now precise. Assume every physical edge
incident to `a` belongs to the exact skeleton `F`, and assume for
contradiction `a∉armRight`. The accepted endpoint rule eliminates every
right-arm edge at `a`. The centre set contributes only `ha` because the
assigned neighbours are distinct and `a≠h`. If `a∉core`, the core
contributes none and its own arm contributes at most the first edge. If
`a∈core`, its own arm is singleton and contributes none, while the core
contributes at most its sole possible edge. In either case at most two
physical edges are incident to `a`, contradicting its retained
`degree(a)=3`.

The planned Lean proof should use `G.incidenceFinset a` (the actual finite
edge set at `a`) and `card_incidenceFinset_eq_degree` to establish this
implication. It must derive every member's skeleton case from the
conditional all-in-`F` premise and prove the two-edge bound on that same
set. The first crossing `a∈armRight` is not yet a Lean theorem. If it is
proved, it places `a` after `h` on the original right source route and
enables a separately checked splice; it does not itself publish an escape.

Constraint: the conditional exclusion of the all-in-`F`, `a∉armRight`
pattern is the next target, not a result already recorded. Compression:
none. Quantity: this is a local degree contradiction, with no demand count,
cycle-rank charge, homogeneous cap or near-cubic estimate. The structural
move and branch remain open and the exported `typeBHandoff` `Holds` is
unchanged.
