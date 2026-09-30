# P0-incoming

Result: SUBMITTED_RESULT

The single tagged incoming alternative for `node20a-stage3b-S1@7d3186b` is **[20a]**, the sparse exit of **[20] on the strict arm of [19]**, at `proofs/hypostructure_erdos_64_eg/HypostructureErdos64EG/Assembly/Final.lean:351`:

```lean
exact Or.inl (node20aReturn privateSwitchHistory)
```

`tools/methodology_gate/node20a_inputs/residual-record.md:5–7` records the residual, return theorem, and exact direct consumer. Lines 14–24 identify its tag and path. Line 7 identifies the injected proposition as the first disjunct of `Node20aOutcome selected ∨ …` (Final.lean:161). The outer constructor `Or.inl` selects exactly that left alternative, with payload `node20aReturn privateSwitchHistory`. This uniquely identifies the recorded tagged incoming alternative; no logical exclusion of other disjuncts is asserted.

The full conjunction of 128 facts is retained (residual record lines 6 and 17–24). Objects remain `G = selected.object`, `data = spineData.toParameters`, and the f021 witness `w : SparseTargetDefectWitness data G`, with `sparseTargetDefectWitness data G = some w` and `w.Spec`. The identities `Z = w.support`, `O = w.outside`, and the declared supports `A,B` of `w.first,w.second` are unchanged, as also recorded in stage3b-context.md:61. Domains, exclusions, minimality and accounts are preserved.

Both declared source hashes match the assignment manifest. This source identification requires no implementation or kernel check. No missing inference or immediate subobligation remains for this task. No move or branch is marked closed; the Stage 3b objectives are unchanged and are not executed here.
