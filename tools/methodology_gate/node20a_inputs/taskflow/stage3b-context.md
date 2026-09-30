# Node [20a] Stage 3b: context for the taskflow child obligations (verbatim extracts)

Run: /tmp/hypostructure-methodology/node20a-2026-09-29-c4 (continued stage run). The stage controller dispatches one Stage 3b assignment per round and cannot launch children. Three Stage 3b attempts returned NEEDS_DECOMPOSITION, and each was rejected with the same repair: complete S1 locally. The operator therefore runs the stated child obligations as taskflow atomic tasks. Their accepted Lean artifacts are then supplied to Stage 3b by continuation. Everything below is copied verbatim from the run record; nothing is added.

## (1) Accepted Stage 3 structural opportunity (selected aspect a03)

```json
{
 "selected_aspect": "a03",
 "structural_opportunity": {
  "bound_witness": "G = selected.object; w is the f021 witness with sparseTargetDefectWitness data G = some w and w.Spec; alpha=w.first, beta=w.second, A=sparseDeclaredSupport data G alpha, B=sparseDeclaredSupport data G beta, Z=w.support, D=cutBoundary G Z, O=w.outside; (P,N) is its Separates orientation; c is each original CycleCertificate (glue (retainedPiece G Z P) O) data.LengthOK.",
  "prior_account_ids": [
   "pu08",
   "pu09",
   "pu15",
   "pu16",
   "pu03"
  ],
  "shared_structure": "The same c in glue ret_P O, its internal private endpoint in G[Z], and the boundary profiles of the same two readings.",
  "retained_restrictions": "f021/f022 pin w and same-certificate geometry; f029 excludes the local arm; f118 supplies a cycle-private internal endpoint in the separating orientation; f115 supplies equal counts and membership transfer; f007 gives a tight endpoint on each ambient edge. All other 128 conjuncts and independent witnesses remain unchanged.",
  "deduction": "S1-S3 of s3_reasoning: take the two nearest boundary occurrences along the cyclic order around the actual private endpoint y. Simplicity and at least two labels make them distinct; internal ownership makes the whole segment a ret_P path. Its endpoints have positive equal counts and belong to A intersect B. The two incident edges at y are distinct, private and piece-exclusive, and y is isolated in the negative gluing. Each has a tight endpoint; high y forces both neighbours tight. This is a structural decomposition of the original c, not a new target or context.",
  "affected_residual_clause": "The positive-certificate side of separation at O in f021/f022 must route its private internal part through a simple passage joining two active common labels, with a two-edge private wedge absent from the negative reading. It cannot be a dangling private edge or a one-contact private component.",
  "stage4_opportunity": "How does this actual active-to-active passage, with its two private edges and the rest of the SAME cycle, constrain the contextual response difference under the retained profile, degree and outside restrictions? Determine a productive consequence while respecting simultaneous path compatibility; include the three-label both-nonwhole case without replacing it by a two-terminal spectrum witness.",
  "weakest_case_id": "c18_02",
  "weakest_case_analysis": "Intersect c18_02 with c16_04, c12_04 and c14_03/c14_04. S1-S3 hold even when the private wedge is all tight, O is unrealized and no induced reading realization exists. The complementary arc may contain further private passages; no equal-length transfer, outside realization, high centre, baseline restoration or numerical saving is established. Stage 4 owns those further exploitation obligations.",
  "evidence": [
   "s3_reasoning",
   "s3_sources",
   "s3_bound_input"
  ]
 }
}
```

## (2) Stage 3b failure reasons recorded by the controller (reviewers' repair directions)

```
Failure must identify the exact field, reason and retained prefix
```

```
claim_projections[S1].declaration: no kernel-checked extraction and lift of the contiguous original-cycle passage through the f118 private endpoint. This is an incomplete Stage 3b execution, not a demonstrated false Stage 3 inference.
Complete Stage 3b locally: prove nearest-boundary indices and extract the exact simple retained-piece arc through the same private endpoint; derive the remaining S1–S3 consequences, including the weakest case. Read and eliminate f021 inside the owner-local row, publish exactly one fact with all inherited keys preserved, supply each claim projection, and obtain the locked kernel check. Keep accepted Stages 1–3 active.
claim_projections[S1].declaration: no kernel-checked extraction and lift of the original cycle's contiguous boundary-to-boundary passage through the f118 private endpoint. The required owner-local row and publication are absent.
Complete Stage 3b on the unchanged residual: prove the nearest-label cyclic indices and exact passage lift, derive all selected endpoint, private-wedge, isolation, and degree claims on that same tuple, and publish one fact with checked projections through an owner-local FactInputs/ExactLedger row. Preserve every inherited key and obtain the locked Lean check. This incomplete submission is a workflow execution defect, not evidence against the accepted Stage 3 inference.
```

```
S1 has no checked derivation of the contiguous original-cycle passage through the retained private endpoint. The owner-local row, S1–S3 projections, ledger publication and kernel certificate are consequently absent.
Complete Stage 3b on the unchanged residual: implement the owner-local FactInputs elimination; prove the nearest-boundary segment, its positive-piece lift and active common endpoints on the original cycle; derive S2–S3 and the weakest-case projections; append exactly one proved structure fact while retaining all incoming keys; obtain the locked kernel check. Preserve accepted Stages 1–3. This is an incomplete execution, not evidence against the accepted structural opportunity.
claim_projections[S1]: no kernel-checked extraction and lift of the original cycle's contiguous boundary-to-boundary passage through the retained f118 private endpoint. The required owner-local derivation and ledger publication are absent.
Complete Stage 3b on the unchanged residual. Prove the nearest-boundary cyclic segment, its retained-piece lift and active common endpoints on the same cycle and private endpoint; finish S2–S3 and weakest-case projections. Read and eliminate f021 inside the owner-local FactInputs row, publish exactly one proved fact through ExactLedger while preserving every inherited key, and supply the locked kernel check. This is an incomplete workflow execution, not evidence that the accepted Stage 3 inference is false.
```

## (3) Latest Stage 3b submission: exact immediate child obligations (verbatim)

# Stage 3b — first unresolved inference

Result: NEEDS_DECOMPOSITION. This is an incomplete Stage 3b submission, not a new fact, reduction, or objection to accepted Stage 3 mathematics.

The fixed input is Node20aOutcome selected, with all 128 conjuncts retained verbatim in state.json. G = selected.object and data = spineData.toParameters. The incoming witness key is K .sparseTargetDefectResidual (f021). Its existential supplies w, sparseTargetDefectWitness data G = some w, and w.Spec. The canonical some-equalities in f022, f029, f115 and f118 identify their witnesses with this w by injectivity of Option.some. They do not provide a new witness domain. Z = w.support and O = w.outside are fixed. The two declared coordinates remain w.first and w.second, with supports A and B.

f118, at this w, supplies P,N, w.Orientation P N, w.Separates P N and w.CyclesUsePrivateEdge P N. For an arbitrary ORIGINAL c : Graph.CycleCertificate (Graph.glue (SupportAtom.retainedPiece G Z P) O) data.LengthOK, eliminate that last universal at c. Retain its supplied pl,pr, original-cycle edge membership and the decoded private endpoint y = SupportAtom.pieceDecode G Z pr. Its exact conclusions are adjacency of the decoded endpoints, both in P, y not in N, and y not in cutBoundary G Z. In particular no fresh private vertex is substituted.

The first unresolved inference is the checked cyclic-segment assertion in S1, not the preceding accepted private-edge result. No Lean derivation of this assertion or owner-local publication is supplied in this submission.

## Exact immediate child obligations for S1

1. **Locate the two first contacts on c.** With the tuple and private endpoint above, obtain the two boundary occurrences nearest to the occurrence of pieceEmbedding ret_P O pr, one in each cyclic direction. Prove distinct endpoints a,b, and a proper contiguous segment q of c from inl a to inl b which contains that occurrence strictly internally and has no internal boundary occurrence. Record contiguity by an equality of walks: a rotation of c.walk at inl a is q followed by the complementary arc r. Thus q and r partition the original cyclic edge order, and length(q)+length(r)=c.walk.length. This must include wraparound at the original basepoint. Input two-label existence comes from the retained same-certificate geometry, excluding PieceLocal by f029; it does not supply the nearest-contact assertion. Simplicity of c prevents a repeated contact before a second distinct label. The finite cyclic order gives first contacts on both sides.

2. **Restrict that same q to the positive reading.** For the segment from child 1, prove all vertices belong to the piece embedding and each edge is piece-owned. Start at the retained internal pr. An edge incident to a piece-internal vertex cannot be context-owned; continue toward each endpoint until the first label. Prove that q lifts to a simple ret_P walk with the same vertex and edge order, has length at least two, and decodes injectively into G with every vertex in P subset Z. Neither an unrelated path nor a cycle of equal length satisfies this obligation.

3. **Make its exact endpoints active common labels.** For that same lifted q, use its first and last edges to provide a P-neighbour at a and b. Apply reading-count positivity and f115 on the fixed coordinates, swapping the roles only according to w.Orientation P N. Conclude both labels belong to A intersect B and have positive equal counts in those two readings. This closes S1 on the fixed tuple, without a realization of O or either reading.

These are the immediate obligations of the first missing S1 inference only. S2, S3, their weakest-case projections and the single ExactLedger publication remain required by the original assignment; they have not been executed or replaced by new tasks here. The controller, rather than this worker, owns any child launches.

## Evidence and domain checks

* Statements/SurplusPair.lean, SparseTargetDefectResidualStatement: existential canonical witness with Spec (f021's exact retained statement).
* Statements/SparseExitReadings.lean:134-149, CyclesUsePrivateEdge: quantifies over the ORIGINAL c and supplies edge membership on c, not an arbitrary ambient edge.
* Statements/SparseExitReadings.lean:273-287, PositiveCyclePrivateEdgeAtWitness and PositiveCyclePrivateEdgeStatement: existential orientation and separation at this w.
* TargetDefectStructure.lean:130-144, PieceExclusive, PieceLocal and TwoLabels: TwoLabels is support membership of two distinct labels; it contains no contiguous-segment witness.
* TargetDefectStructure.lean:160-178, local_or_mixed, local_target and twoLabels_of_exclusive: their actual types support exclusion of the local arm and the two-label input on c. Their proofs are accepted prerequisites, not re-proved here.
* Statements/SparseExitReadings.lean:192-208, WitnessReadingCountsAtWitness: equality and membership transfer at w's two actual coordinates.
* ReadingProfiles.lean:49,124,135: pieceDecode_injective, retained_boundaryDegree_pos, mem_of_profile_eq identify the decoding and endpoint steps, once the specific segment is supplied.

The weakest case remains c18_02, intersected with c16_04, c12_04 and c14_03/c14_04 as specified in the accepted opportunity. The three obligations neither require exactly two boundary labels nor require whole readings, a refined spectrum path, a high private endpoint or a realized context. The complementary arc may contain more private passages. No transfer to that arc is asserted.

## Unmet contract and retained prefix

Unmet field: claim_projections (S1); consequently ledger_row, structure_fact_id, structure_key and lean_declaration cannot yet truthfully identify a checked publication. No FactInputs executor was implemented, no new key was appended, and no kernel certificate is claimed. The key list discussed above is a dependency specification, not a claim that a Lean row has read those keys.

All accepted Stage 1–3 events, all facts, residuals, evidence, endpoint and queue remain unchanged. No Stage 3 revocation is requested: this is a current-stage implementation obligation. No replacement source file, Stage 4 move or reduction is submitted. The locked build was not run because there is no proof replacement to check. Routine mathematical justification above does not substitute for the required Lean proof and projections.
