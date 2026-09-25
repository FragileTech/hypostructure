# [144] window arm: source indices versus route terminals

In one retained handoff witness, the source pattern `P` is a finite family
of unordered two-demand sets inside one token/role fibre. Each demand is an
ordered pair `(u,v)` and its declared route ends at `v = d.2`. The route
terminal projection is therefore `d ↦ d.2`; the non-root target set for
the catalogued linkage theorem is `T₊ = {d.2 : d ∈ e, e ∈ P} \ {ρ}`.

In the matching form, different source edges have no **demand element** in
common. This does not assert that their demand elements have different
second coordinates. For example, as an abstract pair family, the two
disjoint edges `{(a,b),(c,d)}` and `{(e,b),(f,g)}` can be distinct and
matching while two demands project to the same terminal `b`. This tests
the logical strength of the matching definition only; it is not a graph
satisfying the [144a] residual.

In the star form, every source edge contains a common demand element, so
that demand's terminal repeats by construction. Neither form states that
every `d.2` differs from the common root `ρ`. The configuration fields give
actual routes and their endpoints, but no injective map from original
source edges to distinct vertices of `T₊`.

Thus **source-edge-to-distinct-non-root-terminal indexing is missing**.
The edge-Menger theorem remains applicable to a nonempty `T₊`; its linked
paths cannot yet be counted as paths for distinct original pairs. The
all-root terminal outcome and every source index remain retained. This
task supplies no linkage count, capacity bound, or closure.

Sources: `MatchingStar.lean:54–62`;
`ObjectCapacityLedger.lean:623–682`;
`SameTokenRoutingGerms.lean:216–249`.
