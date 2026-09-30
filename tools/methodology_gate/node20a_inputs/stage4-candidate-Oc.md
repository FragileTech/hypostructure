<!-- Operator note: verbatim copy of the coordinator-supplied candidate file stage4_candidate_20a_Oc.md (session scratchpad), added to the Stage 4 and 5 scopes in response to the user's request. It is a candidate for evaluation; the executor may reject any move with reasons. It is not a fact about G. -->

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
