# [144a] window history: every assigned fan incidence counted once by index

Fix the literal window-history post-[144] ledger on `G = selected.object`
and one source-and-envelope witness of `typeBHandoff`. Let `S` be its
actual envelope vertex support and `F` the graph on `S` formed by all
edges of `G[Y]`, every recorded centre edge `ha`, and every recorded arm
edge, with duplicate edges included once. Put
`I=E(G[S])\E(F)`. The handoff gives the finite assignment set
`A={(h,a): h∈H, a∈K_h}`. It does **not** say that the sets `K_h` are
mutually disjoint. Each assigned `a` is cubic by the retained high-centre
normal form.

Define the assignment-indexed incidence set

```
D = {(h,a,e): (h,a)∈A, e is incident to a in G, e≠ha}.
```

For each `(h,a)`, exactly two edges occur, hence `|D|=2|A|` even when
the same vertex `a` is assigned to several centres. Partition `D`
according to the **physical edge** `e`:

* `D_F`: `e∈E(F)`;
* `D_I`: `e∈I`;
* `D_∂`: `e∈δ_G(S)`, with its other endpoint outside `S`.

Because every assigned `a` lies in `S`, these are disjoint and exhaustive:
`2|A|=|D_F|+|D_I|+|D_∂|`. A centre edge `ha` is excluded only for
its own `(h,a)` index; it can occur in `D_F` for a different assignment
`(h',a)`. A first arm edge equal to `ha` does not consume a member of
`D`; this retains the literal positive-arm `[a,h]` exception.

For each physical edge `e`, define its assignment multiplicity
`μ(e)=|{(h,a): (h,a,e)∈D}|`. Then

```
|D_F| = Σ_{e∈E(F)} μ(e),
|D_I| = Σ_{e∈I} μ(e),
|D_∂| = Σ_{e∈δ_G(S)} μ(e).
```

An internal edge `e=uv` can be counted from either endpoint. At `u`,
each contributing centre `h` is a neighbour other than `v`; if `u` is
an assigned first neighbour, `d_G(u)=3`, so there are at most two such
centres. The same holds at `v`; therefore `μ(e)≤4` for an internal edge.
A boundary edge has only one endpoint in `S`, so `μ(e)≤2`. These bounds
do not require disjoint `K_h` or unique arm edges.

For each component `C` of `G-S`, let
`q_C=Σ_{e∈δ_G(C)} μ(e)` and `k_C=|δ_G(C)|`. The selected graph is
connected and `S` is nonempty, so every such component attaches to `S`.
The previous cut trace gives `k_C≥2`; the physical multiplicity bound
gives the exact partition and bound

```
|D_∂| = Σ_C q_C,          0 ≤ q_C ≤ 2 k_C.
```

Here `q_C` counts *assigned fan incidences* entering `C`, including
repetition caused by several centres assigning the same cubic vertex.
It is not the number of original blocked pairs or source routes using
`C`. The retained handoff proves no positive lower bound on `D_∂` or
`D_I`; their zero cases remain unexcluded, and the equations permit all
non-centre incidences to be represented by `F`. Thus the
identities and upper multiplicity bounds give no lower bound on extra
edges or exterior components from `|A|`, let alone from the source
matching/star size.

This completes the incidence count on the one envelope at the level of
physical edges and assigned `(h,a)` indices. The still missing relation
has different indices: which original blocked pairs select or depend on
these assignments, edges, or exterior components, with what multiplicity.
The handoff records one envelope from two selected source edges, and no
such map for the remaining pattern. No cap or closure is inferred.

Sources: the exact ledger in `phase0-evidence.md`; reviewed
`window-phase2-fan-attachments.md`, `window-phase2-exterior-cut.md`, and
`window-phase2-relative-cycle-rank.md`; the envelope definition in
`erdos_64_proof.tex`, `def:decorated-fan-envelope`.
