# [144] fixed-source maximal connector choice

The current `sameTokenBottleneckRoutingRow` now has one anonymous local
finite-maximization proof. Given two nonempty predicates of simple routes on
`G`, it enumerates the attainable common-prefix lengths inside
`range (G.vertexCount+1)`, proves every length belongs there from
`List.toFinset_card_of_nodup`, and chooses the maximum. Its conclusion has
the universal inequality over **every** route pair satisfying the same two
predicates. This proof is inside the existing atomic owner and declares no
top-level theorem, alternative fact channel, or new ledger key.

Both the matching and star arms apply it only **after** selecting their
existing distinct equal-label pattern edges and their chosen demands. For the
left predicate, the configuration type fixes
`sameTokenRoutingSupport token first.1`, `tokenSupport token`, and
`localBuffer left`, and validity fixes head `root` and terminal `left.2`.
The right predicate analogously fixes `second.1`, `right` and `right.2`.
The same root, token, pair, demand, buffer and support enter every quantified
competitor. The selected `firstConfiguration` and `secondConfiguration` now
come from that maximal choice; all subsequent owner reasoning uses these
same selected routes. The local `maximalPrefix` inequality is available for
the later two-tail splice, though it is not yet used to publish a stronger
`typeBHandoff` fact.

Verification: `lake env lean -j 1
Hypostructure/Graph/Strategy/HomogeneousBottleneckRows.lean` in the
`hypostructure` package exited 0 on 2026-09-25. It reported existing lint
warnings and no errors. `api_catalog.py check --repo-root .` also exited 0.
The changed diff adds only an anonymous local `have` and two local
applications inside `sameTokenBottleneckRoutingRow`; no declaration was added.

This is one construction subtask. It does not yet prove the all-in-skeleton
contradiction, the physical escape, a Type B cap, or [144a] closure.
