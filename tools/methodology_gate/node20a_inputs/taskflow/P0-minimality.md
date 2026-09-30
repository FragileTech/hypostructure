# P0-minimality

Branch: `node20a-stage3b-S1@7d3186b`. The retained input is the complete conjunction `Node20aOutcome selected`.

## Objects and minimality order

Keep `G = selected.object : Graph.FiniteObject`, `data = spineData.toParameters`, and the f021 witness `w : SparseTargetDefectWitness data G` with `sparseTargetDefectWitness data G = some w` and `w.Spec`. Keep `Z = w.support`, `O = w.outside`, `A = sparseDeclaredSupport data G w.first`, and `B = sparseDeclaredSupport data G w.second`.

The minimality import is exactly **f001_selection, `K .selection`**, the first conjunct. At the fixed presentation its statement is:

```lean
¬ Graph.HasCycleWithLength data.LengthOK G ∧
  SelectionMinimality BranchState Graph.ReceiverLoad.LoadCapacityProfile
    erdosReceiverLoadProfile data G
```

G avoids the target; every strictly smaller baseline object in the retained `SelectionMinimality` order satisfies the target. Retain that order and its baseline restriction exactly, without substituting another size comparison. Citation: `tools/methodology_gate/node20a_inputs/residual-record.md`, §1, `K .selection` (`f001_selection`), quoting `hypostructure/Hypostructure/Graph/Statements/Spine.lean:2518–2527`.

## Imports

1. **All 128 facts f001–f128 of `Node20aOutcome selected`, verbatim**, with all inherited keys, statements, domains, exclusions and independent witnesses. Citation: `tools/methodology_gate/node20a_inputs/residual-record.md`, “The residual definition (verbatim)”, the fact table, and “Exact statements (verbatim Lean, in residual order)”, §§1–128. The whole conjunction remains imported, including facts not used directly in S1.
2. **Accepted Stage 1–3 artifacts of the stage run**, as supplied in `tools/methodology_gate/node20a_inputs/taskflow/stage3b-context.md`. Section (1) records accepted Stage 3 aspect `a03` and evidence identifiers `s3_reasoning`, `s3_sources`, `s3_bound_input`. Section (2) requires keeping accepted Stages 1–3 active. Section (3), “Unmet contract and retained prefix”, retains all accepted Stage 1–3 events, facts, residuals and evidence unchanged. These prerequisites are imported at their stated scope; their proofs are not repeated. The pending Stage 3b checked publication is not treated as an accepted artifact.

## S1 uses no minimality descent

**The S1 obligations use no minimality descent.** Section (3), “Exact immediate child obligations for S1”, of the context specifies nearest boundary contacts on the original cycle, restriction of that same segment to the positive reading, and activity/common membership of those exact endpoints. The stated inputs are the same-certificate geometry and f029 exclusion, f118's private endpoint on that cycle, simplicity and finite cyclic order, internal edge ownership and decoding, and f115's reading counts and membership transfer on the fixed coordinates. These obligations do not apply f001 to any smaller baseline object. This records the dependency scope, without executing or claiming the pending S1 derivation.

The minimality conjunct remains retained, including any upstream uses already embodied in accepted facts. Objects, domains, exclusions and accounts are unchanged. No branch or move is closed.

Both source hashes match the supplied manifest; the residual's numbered statement sections are exactly 1–128. This recording task entails no implementation or kernel check.
