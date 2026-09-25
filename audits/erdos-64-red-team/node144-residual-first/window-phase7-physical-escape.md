# [144] a physical edge escapes the producer skeleton

The matching and star producer histories now each prove an actual edge
`edge ∈ object.graph.incidenceFinset nextLeft` with `edge ∉ skeleton`.
If no such edge existed, every physical edge incident to the selected
tight neighbour would lie in the literal skeleton of that history's
constructed envelope. The accepted incidence count would then put
`nextLeft` on the right arm, contradicting the accepted fixed-source
maximal-route exclusion. The proof then uses the graph incidence-set
equivalence to expose the same edge as
`s(nextLeft, neighbour)`, with `object.graph.Adj nextLeft neighbour`.
Thus this is a named graph adjacency in the selected graph, not a
missing formal edge or an assumed cap.

The edge is outside the **edge skeleton**. Its other endpoint has not
been classified. It may be a chord among vertices already in the
envelope, a cross-arm edge, an alternate edge to the core, or an edge
leaving the envelope's vertex set. The next structural measurement must
partition these possibilities on the actual graph and account for their
different costs. In particular this theorem does not say that the far
endpoint lies in a detached component.

The verified witness is currently local to each producer arm. The
exported `SameTokenTypeBHandoffStatement` still projects to its envelope
and source pattern without this edge condition. A source-bound export
or exact successor predicate is required before the [144a] residual can
be credited with this restriction. The result alone is no target cycle,
homogeneous cap, near-cubic estimate or branch closure.
