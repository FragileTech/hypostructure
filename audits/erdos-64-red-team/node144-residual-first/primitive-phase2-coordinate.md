# [144] primitive arm: what the routing construction retains

Stay on `G = selected.object` and the tagged primitive blocker-support class history. The
selected `typeBHandoff` fact retains the positive pattern and the decorated
envelope, but it does not retain the intermediate **two selected pattern
edges** by which the routing proof constructs the envelope.

In both the matching case (`HomogeneousBottleneckRows.lean:1378–1406`) and
the star case (`:2224–2251`), the pattern size is used with
`exists_same_routingLabel` to choose distinct `first` and `second` edges
with the same routing label. The proof selects a demand from each edge,
reads their two declared configurations, and analyzes the first separator.
The sparse-exit outcomes are ruled out by `active.survives`. In the decorated
case, `envelopeOfFirstSeparator` constructs **one** envelope from the two
separated configurations (`:2206–2222` and `:3062–3078`).

The published `SameTokenTypeBHandoffEnvelopeStatement` quantifies a packing,
core and one envelope but has no fields for `first`, `second`, their label,
or a relation from the other edges of the source pattern to this envelope.
The enclosing `SameTokenTypeBHandoffStatement` keeps the source pattern and
that envelope in one witness, without an equation identifying the two
selected edges after projection. It therefore proves existence of decorated
Type B data, not a cap or a charge for every selected pair.

The first missing inference is a source-indexed geometric relation strong
enough to control the pattern that remains after this two-edge extraction.
The present task only locates that loss of information. It neither claims
that no such relation can be proved nor chooses a mechanism.

Sources: `HomogeneousBottleneckRows.lean:1378–1406,2206–2251,3062–3112`;
`SpineVocabulary.lean:3944–3979`.
