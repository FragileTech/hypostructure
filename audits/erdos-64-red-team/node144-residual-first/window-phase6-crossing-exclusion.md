# [144] the selected maximal routes exclude cross-arm entry

The actual matching and star producers now each prove
`nextLeft ∉ armRight`. This uses the route pair selected earlier within
the same source-specific types. Under a hypothetical crossing, the accepted
construction gives a right `RoutingConfiguration` whose path is
`common ++ separator :: nextLeft :: after`, with the original right
configuration's head and last vertex. Those equalities, together with
`secondRoot` and `secondTerminalEndpoint`, establish the exact validity
predicate required by `maximalPrefix`: head is the fixed root and last is
the original right selected endpoint. Its type also retains the original
right support, source and selected buffer.

A local list calculation on the two separator decompositions shows that
the selected old pair shares exactly `common.length + 1` vertices, because
`nextLeft ≠ nextRight`. The shortcut shares at least
`common.length + 2` vertices with the same fixed left route. Applying
`maximalPrefix` to the fixed left configuration and this same-typed right
shortcut gives the reverse inequality, a contradiction. The generic list
calculation and both owner instantiations kernel check.

This is the first unconditional same-envelope restriction established by
the attachment analysis: the selected left tight neighbour cannot occur
on the right first-entry arm. The physical-incidence theorem previously
proved that saturation of its incident edges by the literal envelope
skeleton would force exactly that forbidden crossing. The next separate
task is to combine the two and extract a graph edge incident to
`nextLeft` that is outside the exact skeleton on each actual producer
history. No edge witness, cap, productive move or [144a] closure is claimed
in this task.
