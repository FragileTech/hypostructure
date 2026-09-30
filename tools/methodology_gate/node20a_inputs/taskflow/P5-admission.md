# P5 admission review: M-3b-S1

Pinned branch: `node20a-stage3b-S1@7d3186b`. Result: SUBMITTED_RESULT (admission review only).

The assigned construction is exactly items 1–3 of `stage3b-context.md` §3, reproduced verbatim below. Their dependent outputs realize the S1 part of the accepted Stage 3 a03 opportunity in §1, on the same bound tuple. The sole specified outcome is S1 for every original positive certificate, including the stated weakest-case intersection. The conditional payoff is the checked S1 projection required by the Stage 3b consumer in §2. This review establishes that contract identification and conditional payoff; it neither supplies the child proofs nor asserts that a checked S1 declaration already exists.

## Exact construction obligations

1. **Locate the two first contacts on c.** With the tuple and private endpoint above, obtain the two boundary occurrences nearest to the occurrence of pieceEmbedding ret_P O pr, one in each cyclic direction. Prove distinct endpoints a,b, and a proper contiguous segment q of c from inl a to inl b which contains that occurrence strictly internally and has no internal boundary occurrence. Record contiguity by an equality of walks: a rotation of c.walk at inl a is q followed by the complementary arc r. Thus q and r partition the original cyclic edge order, and length(q)+length(r)=c.walk.length. This must include wraparound at the original basepoint. Input two-label existence comes from the retained same-certificate geometry, excluding PieceLocal by f029; it does not supply the nearest-contact assertion. Simplicity of c prevents a repeated contact before a second distinct label. The finite cyclic order gives first contacts on both sides.

2. **Restrict that same q to the positive reading.** For the segment from child 1, prove all vertices belong to the piece embedding and each edge is piece-owned. Start at the retained internal pr. An edge incident to a piece-internal vertex cannot be context-owned; continue toward each endpoint until the first label. Prove that q lifts to a simple ret_P walk with the same vertex and edge order, has length at least two, and decodes injectively into G with every vertex in P subset Z. Neither an unrelated path nor a cycle of equal length satisfies this obligation.

3. **Make its exact endpoints active common labels.** For that same lifted q, use its first and last edges to provide a P-neighbour at a and b. Apply reading-count positivity and f115 on the fixed coordinates, swapping the roles only according to w.Orientation P N. Conclude both labels belong to A intersect B and have positive equal counts in those two readings. This closes S1 on the fixed tuple, without a realization of O or either reading.

## Bound inputs and dependent composition

Let R be the complete 128-conjunct `Node20aOutcome selected` in `residual-record.md`. Retain R throughout. At `G = selected.object` and `data = spineData.toParameters`, f021 supplies the canonical w with `sparseTargetDefectWitness data G = some w` and `w.Spec`. As recorded in §3, equality with that same canonical value identifies the witnesses in f022, f029, f115 and f118 by injectivity of `Option.some`. Thus `Z = w.support`, `O = w.outside`, and the supports A,B of w.first,w.second remain fixed. This is equality identification, not selection of a different witness or domain.

Use the f118 orientation P,N with `w.Orientation P N`, `w.Separates P N` and `w.CyclesUsePrivateEdge P N`. The certificate domain remains exactly

`c : Graph.CycleCertificate (Graph.glue (SupportAtom.retainedPiece G Z P) O) data.LengthOK`.

For each arbitrary original c, retain the pl,pr furnished by f118 at c and the same decoded private endpoint `y = SupportAtom.pieceDecode G Z pr`. The accepted input includes original-cycle edge membership, decoded adjacency, both endpoints in P, and y outside N and the cut boundary. The two-label prerequisite comes from the retained same-certificate geometry and exclusion of PieceLocal by f029, as accepted in §3. It is not itself the nearest-contact conclusion.

The admission inference is dependent conjunction introduction and universal introduction. Conditional on the three exact child outputs, item 1 supplies a,b,q,r on this c, with the specified rotation equality, strict internal occurrence, distinct boundary endpoints and no internal boundary occurrence. Item 2 consumes that very q and supplies its simple positive-piece lift and injective decoding, preserving vertex and edge order and giving length at least two. Item 3 consumes that very lift and its exact endpoints, and supplies positive equal counts and membership in A intersect B, with coordinate roles determined only by the fixed orientation. Retain all these outputs together; do not independently choose witnesses for the three items. Since c was arbitrary in the original domain, their combined result is S1 on every such c. This argument composes the promised outputs; it does not prove any child assertion.

## Accepted claim and productive consumer

Section 1's accepted a03 deduction states: “take the two nearest boundary occurrences along the cyclic order around the actual private endpoint y. Simplicity and at least two labels make them distinct; internal ownership makes the whole segment a ret_P path. Its endpoints have positive equal counts and belong to A intersect B.” Items 1, 2 and 3 supply respectively these three parts, with exactly the contiguity, lift and endpoint evidence required in §3. There is no strengthening or substituted path, certificate, support, context or private endpoint.

Section 2 identifies the consumer field as `claim_projections[S1].declaration`, missing a kernel-checked extraction and lift of the contiguous original-cycle passage through the f118 private endpoint. Checked realizations of the three items on the bound tuple compose into precisely that S1 projection. This is a productive conditional payoff on R: it supplies the specified missing projection of the accepted structural opportunity while retaining R, rather than attempting to infer the branch endpoint from S1.

The Stage 3b consumer must still read and eliminate f021 in its owner-local FactInputs row, finish S2–S3 and the weakest-case projections, publish exactly one proved structure fact through ExactLedger with every inherited key preserved, and obtain the locked kernel check. Those requirements are preserved. They are not additional children or outcomes of M-3b-S1, and an S1 proof alone does not assert completion of that publication. No implementation or kernel check is claimed by this admission artifact.

## Outcome coverage and preservation

The only specified outcome is `node20a-stage3b-S1`: S1 established for every original positive certificate c. Its quantifier includes `c18_02 ∩ c16_04 ∩ c12_04 ∩ c14_03/c14_04`. None of the three items adds a restriction requiring exactly two labels, whole readings, a refined spectrum path, a high private endpoint, a realization of O, or an induced reading realization. Consequently the same conditional composition applies in that weakest case, including an all-tight private wedge and a complementary arc with further private passages. No complementary-arc transfer is asserted.

There is no second outcome in this move's declared contract. In particular, inability to construct a child is not a negative arm, counterexample, Stage 3 revocation or alternative payoff. This is an enumeration of the move's authorized outcomes, not a claim that failure of construction is logically impossible.

All 128 facts, independent witnesses, exclusions, f001 selection minimality, accepted Stages 1–3, and the empty account list are retained. There are no representation or domain changes. S2–S3, Stage 4 exploitation and the branch endpoint remain outside this admission task. No move or branch is marked closed.

## Evidence checks

Both supplied files match the assignment's SHA-256 manifest. Evidence locators are `stage3b-context.md` §§1–3 (accepted opportunity, repair demand, exact items and domain checks) and `residual-record.md` (complete residual definition; facts f001, f021, f022, f029, f115, f118). No missing source, identification or inference was found in the assigned admission check. The unresolved construction proofs are the three quoted children, not additional unresolved admission inferences.
