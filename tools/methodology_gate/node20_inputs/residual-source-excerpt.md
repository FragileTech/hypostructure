# Node 20 residual source scope

Verbatim narrow excerpts from the listed Lean files. These are current theorem sources, not prior workflow submissions.

## `hypostructure/Hypostructure/Graph/Strategy/SpineVocabulary.lean` lines 11269–11283

```lean
11269:   | .sparsePairExit, object =>
11270:       Graph.SparseSurplusExit (Graph.MinimumDegreeAtLeast data.threshold)
11271:         (Graph.HasCycleWithLength data.LengthOK) data.LengthOK object
11272:   | .sparseTargetDefectResidual, object =>
11273:       ∃ (Coordinate : Type u) (family : Finset Coordinate)
11274:         (coordinateSupport : Coordinate → Finset object.Vertex)
11275:         (attempt : Graph.AttemptedQuotient
11276:           (Graph.MinimumDegreeAtLeast data.threshold)
11277:           (Graph.HasCycleWithLength data.LengthOK) object family
11278:           coordinateSupport),
11279:         ¬ Set.InjOn attempt.label ↑family ∧
11280:           ∃ reduced full, attempt.Identifies reduced full ∧
11281:             Graph.Response.TargetDefect
11282:               (Graph.HasCycleWithLength data.LengthOK) reduced full
11283:   | .canonicalBlockerRoute, object =>
```

## `proofs/hypostructure_erdos_64_eg/HypostructureErdos64EG/Assembly/Entry.lean` lines 214–234

```lean
214: noncomputable def selectedSparseSurplusExitContinuation
215:     {selected : EGInput.{u}}
216:     (history : ExactLedger EGInput.{u} selected
217:       [K .sparsePairExit, K .surplusAbove, K .localAlgebra,
218:         K .maximalPacking, K .uncompressible, K .replacementExclusion,
219:         K .targetCompleteContextUniversality, K .degreeProfileFibres, K .cycleRankConstraint,
220:         K .tightEndpoint, K .slackIndependent, K .noProperBaseline,
221:         K .returnAvoidance, K .contractionCritical, K .gadgetClosure, K .relabelingDensityCap, K .cubicBaseline, K .selection]) :
222:     ExactLedger EGInput.{u} selected
223:       [K .sparseTargetDefectResidual, K .sparsePairExit, K .surplusAbove,
224:         K .localAlgebra, K .maximalPacking, K .uncompressible,
225:         K .replacementExclusion, K .targetCompleteContextUniversality,
226:         K .degreeProfileFibres, K .cycleRankConstraint, K .tightEndpoint, K .slackIndependent,
227:         K .noProperBaseline, K .returnAvoidance, K .contractionCritical, K .gadgetClosure, K .relabelingDensityCap, K .cubicBaseline, K .selection] :=
228:   (sparseSurplusExitRoutingRow (BranchState := BranchState)
229:     (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
230:     (presentation := erdosReceiverLoadProfile) (data := spineData)).run
231:     history (by simp [sparseSurplusExitRoutingRow, K_eq_iff])
232: 
233: /-- Node `[125]` is the manuscript's routing-only survivor node.  It accepts
234: only an incoming ledger on which the enclosing sparse-exit classification has
```

## `hypostructure/Hypostructure/Graph/Strategy/HomogeneousBottleneckRows.lean` lines 3160–3193

```lean
3160:     exitFresh survivorFresh
3161: 
3162: /-- Node `[125]`, named sparse-exit routing.  Four constructors are literal
3163: terminals against facts already present in the incoming residual.  The
3164: target-defect constructor alone survives, retaining its concrete attempted
3165: quotient as the paper's target-defect handoff. -/
3166: @[reducible] noncomputable def sparseSurplusExitRoutingRow :
3167:     AtomicStrategy (Input BranchState Presentation presentation data) :=
3168:   factOnly `Hypostructure.Graph.Strategy.Spine.sparseSurplusExitRouting
3169:     { Requires := [K .sparsePairExit, K .selection,
3170:         K .replacementExclusion]
3171:       Produces := [K .sparseTargetDefectResidual]
3172:       requiresUnique := by simp [K_eq_iff]
3173:       producesUnique := by simp [K_eq_iff]
3174:       producesNonempty := by simp }
3175:     (fun inputs =>
3176:       let exit := (inputs.get (K .sparsePairExit)).down
3177:       let selected := (inputs.get (K .selection)).down
3178:       let replacementExcluded :=
3179:         (inputs.get (K .replacementExclusion)).down
3180:       .cons (key := K .sparseTargetDefectResidual)
3181:         (show Value BranchState Presentation presentation data
3182:             .sparseTargetDefectResidual inputs.current from ⟨by
3183:           cases exit with
3184:           | dyadic cycle =>
3185:               exact (selected.1 cycle).elim
3186:           | targetDefect family coordinateSupport attempt reducing reduced full
3187:               identified defect =>
3188:               exact ⟨_, family, coordinateSupport, attempt, reducing,
3189:                 reduced, full, identified, defect⟩
3190:           | compression support replacement =>
3191:               exact (replacementExcluded support replacement).elim
3192:           | delocalization representative smaller baseline transfer =>
3193:               exact (selected.1
```

## `proofs/hypostructure_erdos_64_eg/HypostructureErdos64EG/Assembly/Final.lean` lines 38–82

```lean
38:   | .left exitHistory =>
39:       let targetDefect :=
40:         (sparseSurplusExitRoutingRow
41:           (BranchState := BranchState)
42:           (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
43:           (presentation := erdosReceiverLoadProfile)
44:           (data := spineData)).run exitHistory
45:           (by simp [K_eq_iff])
46:       exact Or.inl (targetDefect.get (K .sparseTargetDefectResidual)).down
47:   | .right survivorHistory =>
48:       let node125 := selectedSparseSurplusSurvivorNode125 survivorHistory
49:       exact Or.inr (selectedNearCubicSurvivorBranch node125)
50: 
51: /-- Selected-root boundary, assembled directly from the exact-ledger rows.
52: The raw Type B entry alternative is the manuscript's routed outcome at `[144]`
53: and at the later `[178]`/`[180]` routes.  It is not sent through the low-surplus
54: quantitative tail.  The final alternative is the open node-`[182]` fact
55: produced by the repaired `[178]`--`[180]` chain. -/
56: -- EG-NODE none (establishes no manuscript DAG node)
57: abbrev SelectedLedgerBoundaryResult (selected : EGInput.{u}) :=
58:   SelectedSparseTargetDefectBoundary selected ∨
59:     StrictSurplusTypeBOutcome selected ∨
60:       Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
61:           erdosReceiverLoadProfile spineData
62:               .pairConditionalFactorizationResidual selected.object ∨
63:         SelectedNearCubicSurvivorBoundary selected
64: 
65: noncomputable def selectedLedgerBoundary
66:     {selected : EGInput.{u}}
67:     (history : ExactLedger EGInput.{u} selected [EGSelectionKey]) :
68:     SelectedLedgerBoundaryResult selected := by
69:   match selectedSurplusDichotomy history with
70:   | .left strictHistory =>
71:       match selectedSparseSurplusDichotomy strictHistory with
72:       | .left exitHistory =>
73:           -- The enclosing `[20]` classification routes the literal exit forms
74:           -- and retains only the exact attempted-quotient target-defect
75:           -- payload for its later peeling handoff.  It never enters `[125]`.
76:           let targetDefectHistory :=
77:             selectedSparseSurplusExitContinuation exitHistory
78:           exact Or.inl
79:             (targetDefectHistory.get (K .sparseTargetDefectResidual)).down
80:       | .right survivorHistory =>
81:           match selectedStrictSurplusBranch survivorHistory with
82:           | .inl fan => exact Or.inr (Or.inl fan.down)
```
