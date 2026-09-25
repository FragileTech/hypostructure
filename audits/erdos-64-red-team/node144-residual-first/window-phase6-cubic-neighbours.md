# [144] selected neighbours are cubic

This task specializes an existing retained fact to the **actual** first-separator
envelope in each [144] producer arm. The exact 50-key window ledger already
contains `highCentreNormalForm`; no new hypothesis or cap is introduced.

The [144] owner's `Requires` manifest now includes `K .highCentreNormalForm`,
and its `FactInputs` read supplies the normal-form law on `selected.object`.
In the matching and star arms, the proof has selected the high first separator
`separator` and the adjacent next vertices `nextLeft` and `nextRight` on the
two maximal fixed-source routes. Each arm applies the normal-form law to
`separatorHigh`, then `neighbourTight` to the **existing** actual adjacencies
`separatorNextLeftAdj` and `separatorNextRightAdj`. Lean proves
`object.degree nextLeft = data.threshold` and
`object.degree nextRight = data.threshold` in both arms. The retained cubic
baseline fixes the threshold at three for the selected graph. These are the
two degree budgets needed for the subsequent crossing argument.

The owner file checked with `lake env lean -j 1
Hypostructure/Graph/Strategy/HomogeneousBottleneckRows.lean` (exit 0).
The direct EG caller checked with
`lake build HypostructureErdos64EG.Assembly.Surplus.Local` (exit 0,
8777 jobs). The caller check verifies that the strengthened `Requires`
manifest is supplied by its ledger routing. Both checks emitted warnings and
no errors. `git diff --check` exited 0.

No all-in-skeleton crossing, same-support splice, physical escape, stronger
`typeBHandoff` `Holds`, or branch closure follows from this task alone. The
local degree facts are currently unused downstream. The next inference must
use these **specific** cubic neighbours and the two actual maximal source
routes to show that the all-in-skeleton case forces crossed tails, then
construct the route splice and contradict maximality. The exact envelope and
its internal versus exterior edge locations remain to be handled after that.
