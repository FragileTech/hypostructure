# [144a] terminal-count payoff statement

`B` is the complete outgoing window-arm `ExactLedger` at node [144], not the
short `Node144aOutcome` projection alone. In particular it contains the
same-graph `typeBHandoff`, `highCentreNormalForm`, `surplusAbove`, source
capacity ledger, selected graph, and every earlier key. Fix the handoff's
one source witness with pattern `P`, demand union `D=⋃P`, common root `ρ`,
and actual route-terminal set `T={d.2:d∈D}`. Write `Q=Q_geom` and
`L=Q+1`, the registered pattern threshold; `|P|≥L`.

The local counting output `O` is:

\[
   \forall v\in V(G),\quad |D_v|\le 3,
   \qquad D_v:=\{d\in D:d.2=v\}.
\]

The proposed branch-conditioned payoff is

\[
  B\land O\quad\Longrightarrow\quad
  G_{\rm term}:\;
  |D|\ge Q+2\;\land\;3|T|\ge |D|\;\land\;
  T\setminus\{\rho\}\ne\varnothing.
\]

The first inequality uses the *same* pattern: matching gives
`|D|=2|P|`; star gives `|D|=|P|+1`. The second is the sum of the disjoint
terminal fibres `D_v` over `T`. The registered label alphabet has at least
two members, so `Q≥2`. Then `3|T|≥Q+2≥4`, hence `|T|≥2`, and deleting one
root vertex cannot empty `T`.

This would be an effective lower bound on the number of distinct physical
terminals of the actual source routes, and would eliminate the all-root
exception in the catalogued route-union split. The exact survivor is the
full `B` with this terminal fact; its original source pairs, token, role,
capacity presentation, envelope, strict surplus, and every earlier key
remain. Both non-root route-union alternatives and repeated route-edge or
envelope incidence remain unresolved. This statement defines the payoff;
the conditional proof and admission review are separate tasks.
