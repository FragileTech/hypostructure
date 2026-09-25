# [144] the crossed right route has a legal source-preserving shortcut

The owner now contains one local shortcut construction on the selected graph,
then applies it in both actual [144] matching and star producer histories.
Suppose `a=nextLeft` belongs to the actual right first-entry arm. Because
that arm is a prefix of `nextRight :: tailRight` and `a ≠ nextRight`, the
right tail contains `a`. Split it as `before ++ a :: after` and retain the
right configuration selected before the first-separator analysis.

The construction replaces its path
`common ++ separator :: nextRight :: before ++ a :: after` by
`common ++ separator :: a :: after`. The edge `separator--a` comes from the
actual left first-separator adjacency in the selected graph. The new path
is a sublist of the original right path as a vertex list, so it is nodup
and every vertex is in the original right pair-specific support. Its chain
consists of the original prefix through `separator`, that graph edge, and
the original suffix from `a`. Its head and last vertex agree with the
original right configuration. The constructed `RoutingConfiguration`
therefore retains exactly the original source set and selected terminal
set. Both producer histories produce this same-typed configuration from
their own crossing premise and right decomposition.

The construction is conditional on the crossing. It does not yet compare
common-prefix lengths. The next exact obligation is to show that the new
right path shares `common ++ [separator,a]` with the fixed left path while
the old right path has `nextRight ≠ a` after `separator`, then contradict
the accepted source-fixed `maximalPrefix` inequality. Only after that can
the incidence count force a physical edge outside the envelope skeleton.
No productive move or closure is recorded at this construction stage.
