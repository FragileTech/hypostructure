# [144] endpoints of an arm edge lie on that arm

The existing [144] owner now proves one anonymous local fact about its new
`armEdgeSet`:

```
∀ path edge vertex,
  edge ∈ armEdgeSet path → vertex ∈ edge → vertex ∈ path.
```

The proof reads membership in the exact `zip path path.tail` edge set,
obtains a consecutive ordered pair, and uses the list `zip` membership fact
to put its first endpoint in `path` and its second endpoint in `path.tail`
and hence in `path`. Undirected `Sym2` membership covers either orientation.
No alternate path-edge representation is introduced.

This fact applies in the matching and star arms to their actual first-entry
arm lists. Under the *future conditional* all-in-skeleton case, if `a` is
absent from `P_b`, no edge of `P_b` can be incident to `a`. The proof has
**not** yet established that condition, nor bounded the remaining own-arm
and core incidences, nor concluded `a∈P_b`.

Verification: `lake env lean -j 1
Hypostructure/Graph/Strategy/HomogeneousBottleneckRows.lean` exited 0;
`lake build HypostructureErdos64EG.Assembly.Surplus.Local` exited 0 after
8777 jobs; `git diff --check` exited 0. The caller emitted an existing
duplicate-instance lint warning and no error. The exact returned `Holds` and
ledger manifest are unchanged by this local proof.

The next inference needed for the first crossing is an upper bound on the
physical edges at an arm's starting vertex contributed by its **own** simple
first-entry arm and the two-vertex core, including the zero-arm case. Only
after that bound is combined with the cubic degree and the conditional
all-in-skeleton premise can the opposite-arm membership be forced.
