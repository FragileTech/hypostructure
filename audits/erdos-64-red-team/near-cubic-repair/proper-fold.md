# A proper high-centre fold with an actual target-defect witness

Status: mathematical local construction proved below; not yet identified with
the manuscript's restricted sparse-surplus coordinate exit. It is not a proof
of closure of Node [144]. No new external theorem is assumed.

## Proposition

Let G be a finite simple graph with at least 13 vertices, minimum degree at
least three, and no power-of-two cycle. Suppose G is minimal first in vertex
count and then in edge count among such graphs, and every neighbour of every
vertex of degree at least four is cubic. Let h have degree d≥4. For any two
distinct neighbours a,b of h, there is a proper connected induced support S
containing h,a,b as internal vertices such that identifying a and b:

1. preserves the labelled boundary and its degree profile;
2. gives an ambient finite simple graph G′ of minimum degree at least three
   on |V(G)|−1 vertices;
3. makes the original and modified pieces target-distinguishable by their
   **actual** outside context G−int(S).

Here target-distinguishable means that one glued graph has a power-of-two
cycle and the other does not. It does not assert that the two pieces agree
under any specified declared-coordinate quotient.

## Proof

Because G has no four-cycle, two distinct vertices have at most one common
neighbour. In particular, the common-neighbour set of a and b is exactly {h}.
Both a and b have degree three by the high-centre hypothesis.

Every x in N(h) has at most one neighbour in N(h): two distinct such neighbours
y,z would give the four-cycle h-y-x-z-h. Since x is cubic, it has at least one
neighbour outside N[h]. Choose one such f(x). Distinct x,y in N(h) cannot have
f(x)=f(y), because h-x-f(x)-y-h would be a four-cycle. Therefore f is injective,
and

\[
|V(G)|\ge 2d+1.
\]

Take

\[
S=N[h]\cup N(a)\cup N(b).
\]

The induced support is connected: N[h] contains its centre h, and every
additional vertex is adjacent to a or b. The vertices h,a,b have all their
neighbours in S, so they are internal, not boundary vertices. Since a,b are
cubic and each is adjacent to h,

\[
|S|\le d+5.
\]

If d≥5, then |V(G)|≥2d+1>d+5. If d=4, then |S|≤9<13≤|V(G)|. Thus S is proper.

Identify a,b to a single vertex w, discard the loop if ab is an edge, and
replace duplicated edges by one edge. This defines a finite simple graph G′.
The only vertex outside {a,b} adjacent to both of them is h. Consequently h
loses exactly one incidence and retains degree d−1≥3. Every other unchanged
vertex retains its degree. The new vertex has degree

\[
d_{G'}(w)=|N(a)\cup N(b)\setminus\{a,b\}|
          =5-2\mathbf 1_{ab\in E(G)}\ge3.
\]

Thus δ(G′)≥3 and |V(G′)|=|V(G)|−1. No vertex of the boundary of S is identified.
No boundary vertex is adjacent to both a and b, because their sole common
neighbour h is internal. Hence every boundary vertex retains exactly its
original number of incidences into the piece. The boundary graph is also
unchanged. This proves equality of the boundary degree profiles.

By minimality, G′ contains a power-of-two cycle. G does not. Gluing the original
piece and the folded piece to their same actual outside context yields G and
G′ respectively. This context therefore distinguishes their target responses.
It supplies an actual target-defect witness without adding an artificial cycle
to a hypothetical realization. ∎

## Why this is not yet the missing closure

The incoming Node [144] state provides the graph facts used above: minimality,
target avoidance, cubic neighbours of high centres, and a nonempty induced-P13
packing, which ensures n≥13. The Type B handoff supplies a high centre, so the
construction applies to its actual graph.

However, the paper's sparse exit is not merely the assertion that two arbitrary
pieces have different target responses. It requires an attempted identification
of the **declared surplus-demand/pair or baseline coordinates** on which this
branch excludes defects. The missing field is:

> Construct the permitted quotient reading q from those retained coordinates,
> and prove that q identifies the original piece with this folded piece.

The first-neighbour incidence merge of the graph is concrete, but it need not
merge the entire recorded arm or surplus-pair coordinate: the two arms may
continue to different marked endpoints, and unmerged response coordinates can
still distinguish them. Boundary-degree equality alone does not establish
equality of the quotient readings. Nor can we replace the original reading by
a constant function or by a freely chosen equivalence relation solely to force
the `Identifies` field.

Thus the fold resolves properness, strict progress, ambient minimum degree,
boundary preservation and existence of a target defect. The exact declared
coordinate identification remains unproved. It would be incorrect to invoke
`sparseSurplusSurvivor` before constructing that field.

## Comparison with the already consumed suppression move

If a and b are adjacent, write `N(a)={h,b,u}`. The no-four-cycle condition
implies `bu` is not an edge: otherwise h-a-u-b-h is a four-cycle. Folding a
into b produces exactly `G-a+bu`, the open-port suppression at `(h,a)`.
When that port belongs to the selected excess family, the manuscript already
uses the target cycle in this suppressed graph to produce its activation
return (`lem:single-open-port-suppression-witness` and
`lem:sparse-port-activation`, around tex lines 2613 and 2749).

Therefore the existence of that target cycle is not a new contradiction on
the active-surplus branch. It is consistent with the data the branch was
constructed to retain. The adjacent fold must not be reclassified as a closed
sparse exit solely by renaming its activation witness a target defect.
The nonadjacent fold has a different merged degree (five), but still needs the
declared-coordinate identification proved separately. This comparison rules
out the proposed shortcut without discarding the valid boundary/degree lemma.

## Further consequence on the same residual: exact cycle lifting

No additional hypothesis is imposed here. Keep G,h,a,b and the folded graph
G′ from the proposition, and suppose a,b are nonadjacent. Write w for their
identified vertex. Every power-of-two cycle C in G′ has the following form:

1. C contains w and avoids the edge wh.
2. Splitting w recovers a simple a–b path P in G of the same length
   ℓ=2^j, j≥2.
3. If h is not internal to P, the edges ah,bh close P to a simple cycle of
   length ℓ+2 in G.
4. If h is internal to P, its two subpath lengths r,s satisfy r,s≥2 and
   r+s=ℓ. They close separately with ah,bh to two simple cycles of lengths
   r+1,s+1 in G. Neither length is a power of two.

Proof. A cycle avoiding w is unchanged by the fold, contradicting target
avoidance in G. Every neighbour of w other than h is adjacent to exactly one
of a,b: their sole common neighbour is h. If C uses wh, its other edge at w
has a unique origin, either a or b. Assigning wh to that same origin lifts C
to an unchanged-length simple cycle in G, again impossible. If the two edges
at w have the same origin, the same lifting contradiction applies. Thus they
have opposite origins; splitting w produces the claimed simple path. All its
other vertices are unchanged and distinct, so there is no hidden walk-to-path
step. If h occurs, neither end edge of P is ah or bh, giving r,s≥2. The
closures in (3) and (4) are simple, and target avoidance excludes dyadic
lengths in (4). This exhausts the cycle locations. ∎

The proposition above supplies C by minimality for each distinct nonadjacent
pair a,b. Thus the existential path conclusion is derived on the existing
residual; it is not a hypothesis added to obtain the desired conclusion.

### Consumer check: a created four-cycle need not be a new constraint

The second outcome is real even in the smallest length case. If the induced
matching on N(h) contains edges ax and by with four distinct endpoints, the
path a–x–h–y–b has length four. Folding a,b creates the four-cycle
w–x–h–y–w. In G this lifts to the two triangles h–a–x–h and h–b–y–h,
not to a four-cycle. The five-vertex configuration itself has no dyadic
cycle. It is a local illustration, not a claimed instance of the full
minimum-degree/minimal-counterexample residual.

These triangles **contain h**. They must not be confused with the manuscript's
triangular ports, whose shoulder triangle avoids h
(`def:heavy-center-triangular-port`). In fact a cubic vertex a in such a
triangle has neighbours h,x,u. Its shoulder chord xu is absent, since xu
would give the four-cycle h–a–u–x–h. Thus (h,a) is an **open** port. The
same applies to b. Routing that open pair to its Type B consumer still
requires its actual profile and assignments; it does not eliminate the fan.

More generally, the length equation r+s=2^j alone cannot force a dyadic
cycle: r=2 and s=2^j−2 give cycle lengths 3 and 2^j−1 for every j≥2.
For the outcome avoiding h, 2^j+2 is strictly between consecutive powers
of two for every j≥2. These arithmetic observations do not assert existence
of full residual graphs. They show exactly why the newly derived path fact,
by itself, does not prove a target cycle or the required response equality.

All old facts, including the selected demands, source pattern, response data,
surplus and packing, remain in force. No residual transition, smaller
counterexample, new open leaf, or completed closure is claimed by this
calculation. The consumer still needs the exact declared-coordinate equality
or a further consequence of those retained data; none follows merely from
the existence of C.
