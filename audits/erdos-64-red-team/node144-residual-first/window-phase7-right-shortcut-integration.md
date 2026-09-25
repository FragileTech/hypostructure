# [144] integrate the legal shortcut with maximality

The accepted shortcut has exactly the same right `RoutingConfiguration` type
as the quantified comparator in the selected `maximalPrefix`: it uses the
original right demand's routing support, the same token source set and the
same selected local buffer. Thus the already retained `firstValid` and the
shortcut's head and terminal facts make it an admissible comparator with
the fixed left configuration. No new source pair is selected.

For the actual separator decompositions, let the fixed left route be
`common ++ separator :: nextLeft :: tailLeft` and the fixed original right
route be `common ++ separator :: nextRight :: tailRight`, with
`nextLeft ≠ nextRight`. Their common-prefix length is exactly
`common.length + 1`. If `nextLeft ∈ armRight`, the accepted construction
returns a right shortcut `common ++ separator :: nextLeft :: after`. Its
common-prefix length with the same fixed left route is at least
`common.length + 2`. The next Lean obligation is precisely these list
calculations, followed by `maximalPrefix firstConfiguration shortcut`.
That inequality would be impossible and would exclude a crossing on both
producer histories.

The accepted earlier physical-incidence theorem then has a direct local
continuation: if all actual incident edges at `nextLeft` were in the exact
envelope skeleton, it would force the excluded crossing. Therefore a
physical graph edge in `incidenceFinset nextLeft` lies outside that
skeleton. This is not yet a checked conclusion; the prefix calculation and
contradiction must be proved first, and the existential edge must then be
derived on the same envelope.

Closure scan: the legal shortcut by itself supplies no target cycle or
contradiction, no smaller graph and no numerical demand/capacity conflict.
It is an admissible candidate for a constraint contradiction with
maximality. The [144a] branch and productive-move status remain open until
the comparison and physical edge extraction are checked and integrated.
