# [144] one-sided saturation forces an actual cross-arm incidence

The exact matching and star producers now each prove the following conditional
statement for their own first-separator envelope. Let `a=nextLeft`, let `P_b`
be the right first-entry arm, and let `F=skeleton` be the literal union of both
arm edge sets, the two centre edges, and the induced edges of the actual
two-vertex core. If every edge of `object.graph.incidenceFinset a` belongs to
`F`, then `a ∈ P_b`.

The proof counts the graph's physical incidence set, whose cardinality is
`object.graph.degree a ≥ 3` by the retained high-centre normal form and
`data.three_le_threshold`. Suppose `a ∉ P_b`. An edge of `F` incident to `a`
cannot be a right-arm edge by the already checked endpoint rule. Of the two
centre edges only `ha` can be incident to `a`, since `a ≠ h,b`. The remaining
own-arm incidence set has cardinality at most one, by the nodup arm's unique
first edge. The core incidence set has cardinality at most one, because the
actual core is `{left.2,right.2}`. These possible second sources are
complementary: if `a` is in the core, first-entry makes its own arm singleton;
if `a` is outside it, no core edge can be incident to `a`. Hence at most two
physical edges can be incident to `a`, contradicting its degree.

This is a conditional exclusion of the saturated, no-crossing pattern. It
does not assert saturation or a cross-arm incidence outright. In particular
it does not yet exhibit an edge outside `F`. The next exact obligation is to
use `a ∈ P_b` on the original right source route to build a legal shortcut
through the edge `ha`, retaining its routing support and selected terminal,
and contradict the locally chosen maximal common-prefix length. Combining
that exclusion with this count would force a physical outside-`F` edge on
each actual handoff envelope.

No homogeneous cap, near-cubic estimate, new graph, alternate arm, productive
move credit, or branch closure is asserted here.
