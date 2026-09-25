# [144] window arm: weakest label-collision case

Work with one positive source pattern `P` inside the retained `typeBHandoff`
witness on `G`. Let `Q` be the cardinality of its routing-label alphabet.
`SameTokenRoutingGerms.patternBound` is `Q + 1`, and the retained source
pattern has `|P| ≥ Q + 1`. The pattern is nonempty and every edge has a
routing label, so `Q ≥ 1`. Hence two distinct source edges have the same
label. This is exactly the collision used by the existing [144] owner to
construct its one surviving high-separator envelope.

The cardinality premise alone forces no second independent collision. At
the weakest allowed size `|P| = Q + 1`, an abstract assignment can put one
edge in each of the `Q` label classes and the extra edge in just one class.
Then exactly one class repeats, and that class has exactly two edges. This
assignment is a check on what the *numerical premise* entails; it is not a
realization of the complete [144a] graph residual.

The full family of declared configurations remains available on the same
handoff witness. But neither the size premise nor the published envelope
relates the other `Q - 1` source edges to the selected high separator or its
two arms. The conditional normal-form restriction recorded in Phase 2 acts
when routes meet a high centre; it does not prove that the remaining routes
meet this separator. Thus a source-wide overlap payoff requires a new
geometric relation on those other configurations. Repeating the existing
two-edge collision and envelope is not that relation.

Sources: `SameTokenRoutingGerms.lean:106–115`;
`ObjectCapacityLedger.lean:623–682`;
`HomogeneousBottleneckRows.lean:1378–1406,2205–2251,3061–3112`.
