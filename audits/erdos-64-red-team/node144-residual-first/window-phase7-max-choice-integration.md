# [144] integration after maximal route choice

The accepted construction changes the **choice** of the two configurations
inside the existing [144] owner. The two equal-label source edges, their chosen
demands, certified token and role, root, pair-specific supports and buffers
are fixed before maximizing. Both matching and star arms now use configurations
that maximize the common-prefix length among all valid configurations with
exactly those fixed data. The rest of each owner arm consumes these same
configurations, so its existing sparse-exit-or-envelope conclusion still
holds and the owner kernel-checks.

The current `typeBHandoff` and `[65]` `typeBFanEntry` `Holds` propositions have
**not** changed. Their returned envelope still omits the selected route pair,
maximality, two-arm constructor identity and physical spare edge. Thus the
new local choice is available for the next owner-local argument but is not a
new exported graph restriction. The full 50-key window ancestry remains
unchanged. In particular `highCentreNormalForm` is a retained key, and it can
give cubic degree to the selected neighbours only after the owner proves the
separator is high and its two next incidences are actual adjacencies.
`cubicBaseline` makes the registered threshold 3; no cap is added.

Constraint test: the local maximization alone excludes no configuration;
the all-in-skeleton exclusion still requires proving that it forces the two
tails to cross, followed by a valid same-support splice to a strictly longer
common prefix. Compression test: no quotient or smaller graph was produced.
Quantity test: no original-demand count, fan mark, cycle-rank charge,
homogeneous cap or near-cubic estimate was proved. Accounts are unchanged,
the branch remains open, and the structural move still has no credit.

The next owner-local construction task must read the **same** maximal routes
in both matching and star first-separator arms. Assuming every non-centre
incidence of the selected cubic neighbours lies in the exact skeleton
`E(G[Y])∪{ha,hb}∪edges(P_a)∪edges(P_b)`, it must derive that `a` lies after `h`
on the right source route. It must then splice the original common prefix
through `h` to the right route's suffix from `a`, verify chain, nodup, root,
terminal, issued/inside/lands on the original **right** support, and use
`maximalPrefix` to contradict this all-in-skeleton case. The surviving
outcome is one physical edge outside that skeleton on the same produced
envelope; internal and exterior locations remain separate successor tasks.

Sources: reviewed `window-phase6-max-route-choice.md` and exact owner diff;
accepted `window-phase2-two-tail-topology.md`,
`window-phase5-all-in-F-extremal-payoff.md`, `phase0-evidence.md`;
`HighCentreNormalForm.lean:78–85`.
