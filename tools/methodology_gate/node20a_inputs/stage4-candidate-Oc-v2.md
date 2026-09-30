<!-- Operator note: verbatim copy of the CURRENT coordinator-supplied candidate file stage4_candidate_20a_Oc.md (with addenda I1–I2 and lemmas L1–L6), superseding the first copy (stage4-candidate-Oc.md) for Stage 4/5. Candidate for evaluation; the executor may reject any move with reasons. The addendum lemmas are coordinator-supplied derivations to be checked, not accepted ledger facts. -->

# Stage 4 candidate for [20a] (from the coordinator, in response to the user's request)

## Facts read off the definitions
- `retainedPiece G Z X` is `G[Z] ⊓ (edges with both ends in X)`, and it lives on the fixed boundary ∂Z = cutBoundary G Z. The two readings are therefore ret_P = G[Z∩P] and ret_N = G[Z∩N], taken as pieces on the same ∂Z.
- The actual outside is G − Z. Both glue ret_P (G−Z) and glue ret_N (G−Z) are subgraphs of G, so both have no accepted cycle. The "actual responses agree" clause of Spec therefore holds automatically. All of the defect's content is in the separating context O.
- y ∈ (P∖N) ∩ Z° (interior), so every edge of y is absent from ret_N. That is why y is isolated in ret_N.

## Structural fact F (a construction, not an assumption)
Let c be any accepted positive certificate in glue ret_P O. Define O_c as the outside context with the same Internal type as O, keeping only the O-owned edges of c.
- F1. glue ret_N O_c ≤ glue ret_N O. This is outside-side monotonicity, the mirror of `glueGraph_mono`. Hence glue ret_N O_c has no accepted cycle.
- F2. glue ret_P O_c contains c. Hence O_c separates P from N.
- F3. The internal O_c edges form a disjoint family of paths ω_1..ω_m. Each ω_j has both ends in ∂Z, its interior in O's internal vertices, and length λ_j ≥ 1. O-owned ∂Z–∂Z edges count as paths of length 1. Every other O_c vertex is isolated.
- F4. c alternates: c = s_1 ω_1 s_2 ω_2 … s_m ω_m, where each s_i is a ret_P path between consecutive boundary contacts. s_1 = q from f129. Call s_i *private* if it uses an edge of ret_P ∖ ret_N; then s_i passes through a vertex of (P∖N)∩Z.

## What F does to the Stage 4 gap
F4 gives the exact domain of the missing routing package M. An accepted cycle of glue ret_N O_c is precisely:
- a cyclic sequence of some of the ω_j,
- joined by pairwise internally disjoint ret_N = G[Z∩N] paths between their endpoints,
- with total length accepted.
(ret_N alone has no accepted cycle, because it embeds in G.)

So "produce M" becomes a linkage-with-lengths demand in G[Z∩N] on the endpoint set of O_c, which is a finite path forest. In particular, the non-private segments s_i already lie in ret_N. Only the private segments need replacing, and each of them passes through Z∖N.

## Textbook moves to evaluate on F
Evaluate each and give its exact output and prerequisites:
- (a) Replacement dominance (lem:replacement), together with noProperBaseline, on G' = glue ret_N (G−Z) with Z∖N deleted. This is a proper subgraph of G, so it has a vertex of degree ≤ 2. Locate that vertex against the equal boundary-degree profile and against S3 (the tight endpoints at y's private edges).
- (b) Segment exchange on F4. A private s_i and an N-path s_i' with the same ends and the same length, internally disjoint from the other segments, give an accepted N-cycle, which is a contradiction. Its negation is an exact length-avoidance statement per private segment. Test that against the retained length facts (windowAttachmentGap, the switch paths 2^j−1, threeRouteFan/Chain at every eligible centre).
- (c) Minimality on the smaller graph glue G[Z] O_c, when |Z| + Σ(λ_j − 1) < n. Check δ ≥ 3 at the ω-ends, using boundary degrees.

Honest status: F is a new exact structure (O_c) and it pins down the domain of M. None of (a)–(c) is known to close the gap. The requirement is that each outcome end as a fact about G or its exact quantified negation.

## Addendum (coordinator, second pass): two further ingredients

### I1. The declared supports are port cycles (Stage 2 aspect a01, partly accounted)
- Read `sparseDeclaredSupport`, `SurplusPort.support`, `declaredSupport` and `pairSeed`.
  - A port coordinate has support T(p) ∪ Γ(p) = {x(p), a(p), b(p)} ∪ V(Q_p).
  - At an open port, Q_p is the suppression path in G − x with |Q_p| + 1 = 2^j. So G[T(p) ∪ Γ(p)] contains the port cycle C_p = x a Q_p b x, of length 2^j + 1.
  - A pair coordinate's seed is the union of its two port supports.
- Consequence: each reading ret_X contains an explicit cycle, or two of them, of length 2^j + 1.
- The active common labels a, b of f129 lie in P ∩ N. So in G they are joined both by q (a ret_P path through y ∈ P∖N) and by the arcs of N's port cycle(s) through a and b.
- Evaluate: the theta and arc structure at a, b in G formed by q, the arcs of C_p and the arcs of C_{p'}. The theta rule is that every pairwise sum of internally disjoint a–b path lengths avoids 2^ℕ. Combine it with segment exchange (move b) and with the case split on whether a, b lie on the port cycles or only on the chords.

### I2. Direction of the consumer: do not try to refute Separates in general
- O is an arbitrary abstract context. Separation at O is equivalent to the existence of one linkage-with-lengths pattern that ret_P realizes and ret_N does not.
- "Produce M" for every O would be the same as proving the identification target-complete, and that is exactly what the exit records as failing.
- A consumer that uses the defect *positively* is therefore the natural one. The paper's own pattern for target defects (exit (4), lem:typeA-exit4-peeling-charge) is to peel: the defect separates the two coordinates, so they count as distinct response classes. That extra class is charged against the [19]/[20] strict-surplus accounting that attempted the identification.
- Evaluate this: which quantity does the separated pair (P, N), with its port-cycle structure (I1), decrease or overload in the retained [20] ledger (the capacity, pair-code and extended-charge keys 7224–7237)? And with what exact amount?

## Addendum 2 (coordinator): facts derived from the definitions, each with its proof
Notation: I = P∩N, D_P = (P∖N)∩Z, D_N = (N∖P)∩Z, W = Z∖(P∪N). Note P, N ⊆ Z, since Z = select?(P∪N) ⊇ P∪N.

L1 (profile ⇒ boundary location; holds for every declared support). For x ∈ ∂Z, Spec's profile equality gives deg_{G[Z∩P]}(x) = deg_{G[Z∩N]}(x). If x ∈ D_N, then x is isolated in ret_P, so deg_{G[P]}(x) = 0 and x has no neighbour in N. Symmetrically for D_P. Proof: unfold retainedPiece; an edge is retained only when both of its ends lie in the support.

L2 (port and pair supports have minimum degree 2). Every vertex of T(p)∪Γ(p) lies on C_p (open port) or on the triangle x a b (triangular port). So every vertex of a port or pair support has degree ≥ 2 inside its support.
Corollary: when P and N are port or pair coordinates, ∂Z ∩ (D_P ∪ D_N) = ∅. D_P and D_N are therefore interior to Z: every G-neighbour of a vertex of D_P lies in Z. The contacts of c with ∂Z lie in I, because W is isolated in ret_P. The private edges are exactly the edges of G[P] with an end in D_P.

L3 (theta at a D_P-run). Let R be a maximal run of D_P vertices on C_p, with ends attached to u ≠ v ∈ I. When N is a port support, u and v lie on C_{p'} and split it into arcs of lengths m and L'−m, where L' = 2^{j'}+1. The path uRv, of length ρ = |R|+1, is internally disjoint from both arcs, because D_P ∩ N = ∅. So G contains a theta, and G has no 2^k cycle, hence ρ+m ∉ 2^ℕ and ρ+L'−m ∉ 2^ℕ. The symmetric statement holds for D_N-runs against C_p (L = 2^j+1). For pair coordinates, apply it per port cycle.

L4 (noProperBaseline at D_P). G − D_P is a proper subgraph (y ∈ D_P), so some vertex w has deg_{G−D_P}(w) ≤ 2. By L2's corollary, w ∈ I ∪ D_N. If w ∈ I ∪ D_N lies on C_{p'}, its two C_{p'} neighbours survive, so w has exactly two non-D_P neighbours and deg_G(w) − 2 neighbours in D_P. Symmetric statement for D_N.

Required of Stage 4: add L1–L4 to the retained facts (all are Lean-provable from the definitions and the ledger keys), then evaluate the peel/charge consumer (I2) and segment exchange (b) against L3 and L4 in the weakest case.

L5 (the quantitative form of L1). For every x ∈ ∂Z ∩ I, the profile equality reads |N(x)∩I| + |N(x)∩D_P| = |N(x)∩I| + |N(x)∩D_N|. Hence |N(x)∩D_P| = |N(x)∩D_N|: each boundary vertex sends equally many edges into the two private sides. Summing over ∂Z gives e(D_P, ∂Z) = e(D_N, ∂Z). In particular, if D_N = ∅ (N ⊊ P), then D_P has no neighbour on ∂Z, so N(D_P) ⊆ D_P ∪ I°, where I° = I∖∂Z.

L6 (exact size of the private sides at open ports). An open port support is exactly V(C_p) with |V(C_p)| = 2^j + 1. If P and N are open-port supports, then |D_P| − |D_N| = |P| − |N| = 2^j − 2^{j'}. When N ⊊ P, this gives |D_P| = 2^j − 2^{j'} > 0 and j > j'. C_p then consists of the D_P-runs R_1..R_t (with Σ|R_i| = 2^j − 2^{j'}) alternating with N-segments of C_p. Each run satisfies the theta constraint of L3 against C_{p'}. By L5, D_P has no neighbour on ∂Z. By L4, some interior w ∈ I° has exactly its two C_{p'}-neighbours outside D_P.
