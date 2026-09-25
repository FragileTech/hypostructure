# [144] first entry makes a core start a singleton arm

Inside the existing [144] owner, an anonymous local list proof shows that a
nodup path with head and last vertex both `start` equals `[start]`. It is
used on the **actual** left first-entry arm in both the matching and star
producer histories. Each application proves

```
nextLeft ∈ core → armLeft = [nextLeft].
```

The selected `armLeftIssued` puts `nextLeft` on that arm. If it lies in the
same constructor core, `armLeftFirstEntry` identifies it with the arm's
first-entry terminal. The existing `armLeftLast` then makes it the last
vertex, and `armLeftNodup` forces the singleton list. No new arm or core is
chosen. The premise `nextLeft∈core` is conditional; it is not added to the
returned handoff. A singleton arm has no edge in the accepted `armEdgeSet`.

This completes the complementary **source descriptions** at selected `a`:
outside the core, the core supplies no edge and the own arm supplies at
most its first edge; inside the core, the own arm supplies none and the
core supplies at most its sole possible edge. It does not yet combine
these cases with the all-in-`F` premise and `degree(a)=3` to prove
`a∈P_b`; that incidence-count implication is the next mathematical task.

Verification: `lake env lean -j 1
Hypostructure/Graph/Strategy/HomogeneousBottleneckRows.lean` exited 0;
`lake build HypostructureErdos64EG.Assembly.Surplus.Local` exited 0
after 8777 jobs; `git diff --check` exited 0. The existing returned
`typeBHandoff` `Holds` and exact ledger are unchanged. There is no new
top-level proof declaration, cap, escape, or closure.
