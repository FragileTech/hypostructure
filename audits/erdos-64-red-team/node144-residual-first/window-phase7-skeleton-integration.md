# [144] integrate the exact attachment skeleton

The accepted owner construction now has a finite edge set `F` made from the
**same** matching/star handoff envelope that the row returns. Its arm edges
are consecutive edges of the two actual first-entry lists, its centre edges
are `ha,hb`, and its final part is precisely the edges induced by the actual
two-vertex core. This is the physical reference set for the attachment
profile; no selected graph, source pair, or envelope has been replaced.

The previously ignored question is whether the two non-centre incidences at
each selected cubic neighbour `a,b` remain in `F`. Their degrees are already
proved from the retained high-centre normal form, and the selected route pair
already maximizes its common prefix for fixed source data. These facts now
meet on one concrete object. The conditional all-in-`F` case is exactly

```
∀ x, G.Adj a x → s(a,x) ∈ F,
∀ x, G.Adj b x → s(b,x) ∈ F.
```

It is a case to refute, not a hypothesis appended to the handoff. The next
one-inference task is to prove `a ∈ P_b` from this case, the two selected
cubic degrees, the actual first-entry/nodup arm facts, and the exact core.
The proof must cover the possibility `P_a=[a]` and membership of `a,b` in
the two-vertex core. The symmetric `b ∈ P_a` and the same-support route
splice are separate tasks. A future contradiction to route maximality would
force at least one physical edge incident to `a` or `b` outside `F` on this
same envelope; it has not yet been proved.

Constraint: the definition alone excludes no configuration. Compression:
there is no replacement or measure decrease. Quantity: no new charge, cap,
or slack comparison is established. The full inherited window ledger and
accounts remain in force, while `typeBHandoff` `Holds` still projects the
weak envelope. The structural move and branch stay open.
