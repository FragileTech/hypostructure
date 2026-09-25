# [144] exact components of the selected two-arm skeleton

Fix either actual matching or star producer of the [144] handoff and
keep its selected graph `G`, separator `h`, distinct first neighbours
`a,b`, first-entry arm lists `A,B`, and literal core
`Y={left.2,right.2}`. Put

```
T = {h} ∪ V(A) ∪ V(B),                 S = T ∪ Y,
F = E(A) ∪ E(B) ∪ {ha,hb} ∪ E(G[Y]).
```

Here `F` is a graph **on vertex set `S`**, including any core vertex
with no `F` edge. The owner proves the displayed equality for each
producer. Every arm edge is a physical edge of `G`, since the arm is an
`Adj_G` chain. Its endpoints lie in its arm list. The two centre edges
are physical by the producer's separator adjacency proofs, and their
ends lie in `T` because the arms start at `a,b`. Every edge of the last
term is, by its definition, an actual edge induced by `Y`. Therefore
`F⊆E(G[S])`.

For each `x∈V(A)`, take the initial segment of `A` ending at its first
occurrence of `x`; its consecutive edges lie in `E(A)`. Prepending
`ha` gives an `F` walk from `h` to `x`. The same argument with `hb`
and `B` reaches every vertex of `V(B)`. Thus `F` restricted to `T` is
connected. Singleton arms cause no exception: their only vertex is
reached by the centre edge. Overlapping arms only add possible walks.

The left arm has a last vertex `y∈Y`, so `Y∩T` is nonempty. Since
`Y` has at most two vertices, `Y∖T` contains at most one. There are
therefore exactly two possibilities:

* If `Y⊆T`, then `S=T` and `F` is connected.
* If `Y∖T={w}`, let `y` be the other core vertex. All arm and centre
  edges have their endpoints in `T`, so the **only possible** `F` edge
  at `w` is the induced core edge `wy`. If `Adj_G(w,y)`, this edge
  joins `w` to the connected `T` component and `F` is connected. If
  `¬Adj_G(w,y)`, `w` is isolated in `F` and the components of `(S,F)`
  are exactly `T` and `{w}`.

Consequently `c(F)∈{1,2}`, with `c(F)=2` exactly in the final case.
When the two source endpoints coincide, `Y` is a singleton already
reached by an arm and only the connected case occurs. If both arms
first land at the same vertex of a two-vertex core, the other vertex
is the possible `w`; no distinct-landing assumption is used. Arm
overlap does not affect the classification. The matching and star
proofs use the same head, chain, first-entry landing, centre-adjacency
and literal-skeleton clauses, so the argument applies separately to
both producer histories without merging their other facts.

This repairs the failed unconditional connectivity task P7-window-51.
It gives the **actual selected** skeleton's component count; the
earlier Phase 2 identity remains the accounting theorem and its
`−(c(F)−1)` term must still be spent. In the disconnected case a
new edge can merely join the two skeleton components, so this task
claims no rank surplus, target cycle, cap or [144a] closure. The next
local obligation is to classify the forced non-`F` edge by its
endpoints' `F` components and by its actual exterior component.
