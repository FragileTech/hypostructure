# P0-pin: frozen source identification

Result: SUBMITTED_RESULT. The branch is `node20a-stage3b-S1@7d3186b`. Its source pin is **`g-repair-base @ 7d3186b` (Merge port-20a)**, frozen in stage run `/tmp/hypostructure-methodology/node20a-2026-09-29-c4`.

The assignment's `branch.source_revision` supplies the frozen-run provenance and states that the files read are byte-identical at `4519bdd`. That latter identifier does not replace the assigned source pin. Independently reading `tools/methodology_gate/node20a_inputs/residual-record.md:3` confirms the same branch and commit and the record's explicit verbatim-source attribution. `tools/methodology_gate/node20a_inputs/taskflow/stage3b-context.md:3` identifies the same continued stage run and attributes its extracts verbatim to that run record. These supplied provenance statements are used at their stated scope.

## Independent checks of the supplied evidence

SHA-256 was recomputed from each supplied file's bytes and compared with `/input/assignment.json`, `source_manifest`; both comparisons passed:

| Repository-relative file | SHA-256 |
|---|---|
| `tools/methodology_gate/node20a_inputs/residual-record.md` | `7e2f1c566348dc2091f2f8daf608a69ed7a937f4c46af1bd9bccad033a6c91dc` |
| `tools/methodology_gate/node20a_inputs/taskflow/stage3b-context.md` | `84fdb80dc0cbfaaa1568840f31b33d4990de2e8bc853b4996a06a644ed081b76` |

The first Lean block of the residual record (record lines 14–281, declaration beginning at line 25) contains 128 distinct `Holds` keys at `selected.object`, joined by 127 conjunctions. A programmatic ordered comparison with the 128 numbered fact headings passed: numbers and fact IDs run from 1/f001 to 128/f128, and each heading's key and fact-ID suffix equal the corresponding conjunction key. This checks the identity of the complete residual in the supplied quotation, without selecting a sub-conjunction.

## Source-location cross-check

The following are original-source locations as cited in the supplied records; record line numbers are distinguished explicitly.

| Declaration or citation | Supplied record location | Cited original source |
|---|---|---|
| `Node20aOutcome` | residual record lines 5, 14–281 | `proofs/hypostructure_erdos_64_eg/HypostructureErdos64EG/Assembly/Residuals.lean:25–292` |
| `node20aReturn` and incoming use | residual record lines 6–7 | Same `Assembly/Residuals.lean`; `proofs/hypostructure_erdos_64_eg/HypostructureErdos64EG/Assembly/Final.lean:351`, with result at line 161 |
| `Holds` interpretation | residual record line 8 | `hypostructure/Hypostructure/Graph/Strategy/SpineVocabulary.lean:1971` |
| All f001–f128 statement locations and quotations | residual record lines 284–416 (index), 419–2335 (numbered quotations) | Each entry records its own repository-relative declaration path and source range under the line-3 pin |
| f021, `SparseTargetDefectResidualStatement` | residual record lines 308, 831–849; context lines 61, 79 | `hypostructure/Hypostructure/Graph/Statements/SurplusPair.lean:1200–1212` |
| f022, `SparseTargetDefectStructureStatement` | residual record lines 309, 851–873 | `hypostructure/Hypostructure/Graph/Statements/SurplusPair.lean:1214–1228` |
| f115, `WitnessReadingCountsStatement` | residual record lines 2143–2154; context line 84 | `hypostructure/Hypostructure/Graph/Statements/SparseExitReadings.lean:203–208`; context cites the wider 192–208 range including `WitnessReadingCountsAtWitness` |
| f118, `PositiveCyclePrivateEdgeStatement` | residual record lines 2184–2197; context lines 63, 80–81 | `hypostructure/Hypostructure/Graph/Statements/SparseExitReadings.lean:280–287`; context cites 273–287 including `PositiveCyclePrivateEdgeAtWitness`, and 134–149 for `CyclesUsePrivateEdge` |

The context's remaining helper citations are explicitly located at its lines 82–85: `TargetDefectStructure.lean:130–144,160–178` and `ReadingProfiles.lean:49,124,135`. They are citations in the frozen run extract, not additional full declaration quotations in the residual record. Their proofs are not re-audited in this source-pin task.

The checked quotations preserve `G = selected.object`, `data = spineData.toParameters`, and f021's canonical witness equality and `Spec`. The f022 quotation uses that witness's support, first/second declared coordinates and outside context. Context lines 61–63 identify the same bound witness and original certificate. No object, domain, exclusion, minimality assumption, account or residual conjunct is changed.

This confirmation is from the supplied, hash-verified records and their declared frozen-source provenance. No original Git tree or Lean source files are supplied among the two declared files; no separate Git byte comparison or kernel check is claimed. No mathematical implementation is needed for P0-pin. No branch or move is marked closed.
