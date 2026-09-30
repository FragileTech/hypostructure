# P0-endpoint — unchanged endpoint and current local obligation

Pinned branch: `node20a-stage3b-S1@7d3186b`.

The unchanged endpoint is `Node20aOutcome selected → False`, or a significant exact reduction preserving the complete conjunction. The residual record states exactly (line 9):

> * Target of this run: derive `False` from `Node20aOutcome selected`, or a significant exact reduction of it (an exact surviving residual carrying every one of the 128 facts plus the new ones).

The current local obligation is Stage 3b publication of the accepted Stage 3 a03 structure S1–S3 on the bound witness. The Stage 3 extract states exactly (section (2), line 52):

> Complete Stage 3b on the unchanged residual. Prove the nearest-boundary cyclic segment, its retained-piece lift and active common endpoints on the same cycle and private endpoint; finish S2–S3 and weakest-case projections. Read and eliminate f021 inside the owner-local FactInputs row, publish exactly one proved fact through ExactLedger while preserving every inherited key, and supply the locked kernel check. This is an incomplete workflow execution, not evidence that the accepted Stage 3 inference is false.

The accepted a03 deduction is quoted exactly from section (1), `structural_opportunity.deduction` (line 21):

> S1-S3 of s3_reasoning: take the two nearest boundary occurrences along the cyclic order around the actual private endpoint y. Simplicity and at least two labels make them distinct; internal ownership makes the whole segment a ret_P path. Its endpoints have positive equal counts and belong to A intersect B. The two incident edges at y are distinct, private and piece-exclusive, and y is isolated in the negative gluing. Each has a tight endpoint; high y forces both neighbours tight. This is a structural decomposition of the original c, not a new target or context.

The retained objects and domains are fixed as stated exactly in section (3), line 61:

> The fixed input is Node20aOutcome selected, with all 128 conjuncts retained verbatim in state.json. G = selected.object and data = spineData.toParameters. The incoming witness key is K .sparseTargetDefectResidual (f021). Its existential supplies w, sparseTargetDefectWitness data G = some w, and w.Spec. The canonical some-equalities in f022, f029, f115 and f118 identify their witnesses with this w by injectivity of Option.some. They do not provide a new witness domain. Z = w.support and O = w.outside are fixed. The two declared coordinates remain w.first and w.second, with supports A and B.

All 128 residual facts, including selected minimality, exclusions and independent witnesses, remain retained. No objects, domains or accounts change. The original positive certificate and f118 private endpoint remain those specified in the extract, line 63. Accepted Stages 1–3 remain active; further exploitation belongs to Stage 4 (section (1), lines 23–25).

This artifact states the endpoint and publication obligation only. It does not execute S1–S3, publish a new ledger fact, claim a reduction, or close a branch. No implementation or kernel check is required for this endpoint-identification task. Both supplied source hashes match the assignment manifest; the quotations were checked against the pinned files. There is no missing source, identification or inference for P0-endpoint.

Sources: `tools/methodology_gate/node20a_inputs/residual-record.md` (lines 5–9 and the complete residual definition); `tools/methodology_gate/node20a_inputs/taskflow/stage3b-context.md` (sections (1)–(3), specifically lines 21, 52, 61 and 63).
