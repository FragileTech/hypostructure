# [144] window arm: same-root first-separator mechanism (Phase 4.1)

**Exact finite-path statement.** `parallel_or_firstSeparator_of_same_root`
takes two finite configuration paths with the same declared root and with
endpoints in a common selected support. It returns either `Parallel`
(`EnteredTogether`: the shared prefix reaches that support) or a first
separator with `firstSeparator left right = some separator` and
`¬ EnteredTogether`. `firstSeparator` is the last vertex of their maximal
common prefix when both paths diverge. The statement does not assert that
all differing paths separate; its landing and same-root hypotheses are
essential.

**Exact local application.** After the finite-label collision on the
window-arm selected pattern, the owning row reads the two original declared
`RoutingConfiguration`s. At lines 1710–1756 it constructs their common
selected support, proves both paths start at the same canonical token root
and land in that support, then applies this theorem. The parallel outcome is
kept as a separate branch. In the other outcome, the row establishes
divergence and non-prefix conditions and applies
`DecoratedHandoff.exists_separatesAt` to obtain an actual separator of
those same two configuration paths. Both matching and star cases use the
corresponding code; the star case is at lines 2580–2627.

This mechanism supplies a source-linked parallel/separator alternative. It
does not by itself eliminate the parallel branch, prove the separator has
high degree, construct an envelope, or bound multiplicity. Those are distinct
prerequisites and outputs of the candidate move.

Sources: `SameTokenRoutingGerms.lean:385–415,496–540`;
`DecoratedHandoffEnvelope.lean:90–125`;
`HomogeneousBottleneckRows.lean:1710–1756,2580–2627`.
