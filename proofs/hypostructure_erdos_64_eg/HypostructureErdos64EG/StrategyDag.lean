import HypostructureErdos64EG.Problem

/-!
# Erdős--Gyárfás strategy DAG -- **awaiting re-rooting on the entry spine**

The authored topology that used to live here was the legacy `Blueprint` chain.
Its first ten nodes were Block A, and every later row was a continuation passed
*into* one of them, so the legacy Block A was the skeleton the whole DAG hung
from.

Block A now has exactly one implementation: `Graph.Strategy.Spine`, run by
`Graph.Strategy.Spine.run` against the data this problem registers in
`Problem.lean`.  The legacy registration layer that fed the old topology --
`Official/Definition.lean`, `Official/Problem.lean`, `AB/`, and
`Presentation.lean` -- has been deleted, so the old topology no longer
elaborates and is preserved below as commented reference only.

Re-rooting this module on `Spine.run` and re-attaching rows 11 onwards to
`Spine.Result` is the next step; it is deliberately not done here.  Nothing in
the reference below is compiled, and none of it is evidence about the current
proof.
-/

namespace HypostructureErdos64EG

/-! ## Reference: the retired legacy topology

Everything from here to the end of the module is the authored `Blueprint` DAG
as it stood before Block A was ported.  It is kept verbatim as the porting
reference for rows 11 onwards.

open Hypostructure
open Hypostructure.Core.Strategy.Dag

syntax "erdosOfficialBlueprint%" term:max term:max term:max term:max term:max term:max term:max term:max term:max term:max term:max term:max term:max term:max term:max term:max term:max term:max : term

/ -- The one authored EG topology.  Both the official frontier declaration and
the A/B sanity declaration elaborate this same syntax against their own
target-indexed capability registry, preventing the two DAGs from drifting. - /
macro_rules
  | `(erdosOfficialBlueprint% $fanSafeScan $certSplit $b2Split $fanMass $degreeFour $hybridEntry $bridgeDeficit $directCycleSplit $typeASaturated $typeAVisible $typeAExitOne $typeAExitTwo $typeAExitThree $typeAExitFour $typeAExitFive $typeAExitSix $typeAExitSeven $typeARoute8) => `(
    / - Manuscript `[1]`--`[4]`: initialize the proof and select the canonical
    minimal target-avoiding counterexample. - /
    Blueprint.root
      |>.minimalCounterexampleSelection
        (name := "Minimal counterexample")
        (note := "Manuscript nodes [1]–[4]. If the theorem fails, choose a \
          target-avoiding counterexample that is minimal in the prescribed \
          well-founded order. All later arguments concern this fixed \
          minimal counterexample.")
      |>.targetAlgebraReduction
        (name := "Target algebra reduction")
        (note := "Manuscript nodes [5]–[7]. Examine the target-return \
          alternatives forced by the defining cycle-length condition. A \
          successful return proves the target; otherwise the proof continues \
          with the exact target-avoiding alternative.")
      |>.minimalSubobjectExclusion
        (name := "Minimal subobject exclusion")
        (note := "Manuscript node [8]. Minimality rules out every proper \
          subobject that still satisfies the standing hypotheses and avoids \
          the target.")
      |>.criticalModificationStructure
        (name := "Critical modification structure")
        (note := "Manuscript nodes [9]–[10], and with them invariant 4, the \
          node-[67] assertion. Deleting any admissible atomic piece must \
          destroy the counterexample conditions. The two appended ledger \
          entries are exactly the two halves of [67]: every dart of the \
          registered reduction is critical, so every edge has an endpoint at \
          the baseline degree and the fan neighbours of any higher-degree \
          centre are cubic; and the slack carriers, the vertices of degree at \
          least one above the baseline, are pairwise nonadjacent, so V_{>=4} \
          is independent. The Type B continuation reads these entries; it \
          does not re-establish them.")
      |>.interfaceReplacementClosure
        (name := "Interface replacement closure")
        (note := "Nodes [11]–[14]. The ledger rejects every strictly smaller, \
          baseline-preserving replacement with the same boundary-degree \
          profile whose obstruction profile is included one-way in that of \
          the source. A target-complete compression supplies this inclusion, \
          so it is excluded as a corollary.")
      |>.obstructionPackingClosure
        (name := "Induced-obstruction packing")
        (note := "Manuscript nodes [15]–[17]. Either the graph is free of the \
          required induced path, in which case the obstruction theorem \
          finishes that alternative, or choose the canonical maximal \
          collection of pairwise disjoint induced paths for the remaining \
          argument.")
      |>.exactFiniteLocalAlgebra
        (name := "Exact finite local algebra")
        (note := "")
      |>.scaleThresholdDichotomy
        (name := "Non-near-cubic surplus split")
        (note := "Node [19]. Compare the active graph's cubic degree surplus \
          with C_sp · ⌈√n⌉. Here C_sp is one more than the uniform \
          homogeneous-token cap used by the later accounting, and that \
          choice is proved to absorb its bound 1 + √(M₀ n). The strict arm \
          enters [20]; the complementary arm retains the near-cubic bound.")
        (aboveName := "Surplus-pair accounting residual")
        (aboveNote := "")
        (above := fun branch =>
          branch.orderedSurplusActivation
              (name := "Ordered surplus activation")
              (note := "")
            |>.baselineDemandAccounting
              (name := "Baseline demand accounting")
              (note := "")
            |>.canonicalPairResponseAccounting
              (name := "Canonical pair-response accounting")
              (note := "")
            |>.canonicalCapacityTokenAccounting
              (name := "Canonical capacity-token accounting")
              (note := "")
            |>.coupledHomogeneousFibrePressure
              (name := "Coupled homogeneous fibre pressure")
              (note := "")
            |>.finiteBottleneckClassification
              (name := "Finite bottleneck classification")
              (note := "")
            |>.homogeneousBottleneck
              (structured := fun residual =>
                residual.autoroute
                  (name := "Type-B handoff to the near-cubic spine")
                  (note := ""))
              (bounded := fun residual =>
                residual.autoroute
                  (name := "Near-cubic return")
                  (note := ""))
              (name := "Homogeneous bottleneck")
              (note := ""))
        (atOrBelow := fun branch =>
          branch.finiteBarrierEnumeration
              (name := "Near-cubic finite enumeration")
              (note := "")
            |>.finiteDensityBudget
              (overflow := fun overflow =>
                overflow.coldBranchAggregation
                  (name := "Cold-window corridor closure")
                  (note := ""))
              (cap := fun cap =>
                cap.supportComplementNormalization
                    (name := "Support-complement normalization")
                    (note := "")
                  |>.boundaryDemandAccounting
                    (name := "Boundary-demand accounting")
                    (note := "")
                  |>.localSupplyLowerBound
                    (name := "Local supply lower bound")
                    (note := "")
                  |>.compressionLinkedTargetRelativeRankDichotomy
                    (rankDrop := fun rankDropResidual => rankDropResidual)
                    (fullRank := fun fullRankResidual =>
                      fullRankResidual.finiteStateCapacity
                        (nonCapacity := fun branch =>
                          branch.finiteStateNetChargeContinuation)
                        (capacity := fun capacity =>
                          capacity.finiteStateNetChargeContinuation
                            (typeA := fun branch =>
                              / - Manuscript Figure 8, nodes [86]-[109].  Nodes
                              [86] and [90] carry no vertex: [86] restates the
                              node-[63] residual's own no-surplus payload and
                              [90] restates the [89] no-branch payload. - /
                              branch.dichotomy $typeASaturated
                                (name := "Saturated receiver")
                                (note := "")
                                (leftName := "Saturated receiver present")
                                (leftNote := "")
                                (rightName := "Unsaturated Type A charge")
                                (rightNote := "")
                                (left :=
                                  Blueprint.root.dichotomy $typeAVisible
                                    (name := "Visible receiver-entry returns")
                                    (note := "")
                                    (leftName := "Four visible returns")
                                    (leftNote := "")
                                    (rightName := "Visible-first excess")
                                    (rightNote := "")
                                    (right :=
                                      / - Manuscript edge (silent)--(e4) of
                                      Figure 8: the silent branch realizes only
                                      exits (4)-(8), so it enters the chain at
                                      node [101].  Core's autoroute joins only
                                      at a head vertex and would select a
                                      capability-compatible destination on the
                                      Type B side, so the exit-(4)--(7) chain is
                                      written out again here.  The vertices are
                                      duplicated; the registrations are not. - /
                                      Blueprint.root.dichotomy $typeAExitFour
                                        (name := "Exit 4: target-defective quotient")
                                        (note := "")
                                        (leftName := "Target-defect peels one load")
                                        (leftNote := "")
                                        (rightName := "No target-defective quotient")
                                        (rightNote := "")
                                        (right :=
                                          Blueprint.root.dichotomy $typeAExitFive
                                            (name := "Exit 5: target-complete compression")
                                            (note := "")
                                            (leftName := "Uncompressibility contradiction")
                                            (leftNote := "")
                                            (rightName := "No compression")
                                            (rightNote := "")
                                            (right :=
                                              Blueprint.root.dichotomy $typeAExitSix
                                                (name := "Exit 6: response delocalization")
                                                (note := "")
                                                (leftName := "Delocalization branch")
                                                (leftNote := "")
                                                (rightName := "No delocalization")
                                                (rightNote := "")
                                                (right :=
                                                  Blueprint.root.dichotomy $typeAExitSeven
                                                    (name := "Exit 7: decorated handoff fan")
                                                    (note := "")
                                                    (leftName := "Type B handoff")
                                                    (leftNote := "")
                                                    (rightName := "Route-8 residual")
                                                    (rightNote := "")
                                                    (right :=
                                                    Blueprint.root.route8CarrierClosure $typeARoute8
                                                      (name := "Route-8 carrier closure")
                                                      (note := "")
                                                      (nonClosureName := "Carrier supply, census and descent")
                                                      (nonClosureNote := "Nodes [114]-[121] and [123]: the \
                                                        arms that reach no terminal ellipse. The zero-carrier \
                                                        entry of [116], where lem:typeA-one-terminal-collapse \
                                                        gives one of exits (4)-(7); the CT5 supply \
                                                        comparisons; node [118]'s two-carrier entry, which is \
                                                        CT14's aggregate overload at the derived demand; and \
                                                        the descent's own exhaustion.")
                                                      (closureName := "Nodes [122] and [124]: both terminals")
                                                      (closureNote := "Figure 9's two terminal ellipses, both \
                                                        uninhabited, so this arm closes rather than being \
                                                        retained as an open leaf. Node [124] is \
                                                        thm:typeA-two-carrier-nogo: the descent's tier \
                                                        terminal is a terminal two-carrier route-8 \
                                                        obstruction of def:typeA-terminal-two-carrier, whose \
                                                        clause (T5) places each declared deletion witness in \
                                                        the canonical exit-(4) family while clause (T2) \
                                                        denies exit (4). Node [122] is \
                                                        prop:typeA-route8-carrier-reduction: the descent's \
                                                        demand terminal collides the route-8 burden [112], \
                                                        the large-budget deficit [113] and the \
                                                        private-carrier budget [120] below the carrier rate \
                                                        required/(required*dischargeScale + 1), which at the \
                                                        registered values is the manuscript's 3/13."))))))
                                    (left :=
                                      Blueprint.root.dichotomy $typeAExitOne
                                        (name := "Exit 1: Mersenne return")
                                        (note := "")
                                        (leftName := "Target cycle")
                                        (leftNote := "")
                                        (rightName := "No Mersenne return")
                                        (rightNote := "")
                                        (left := Blueprint.root)
                                        (right :=
                                          Blueprint.root.dichotomy $typeAExitTwo
                                            (name := "Exit 2: power-of-two theta")
                                            (note := "")
                                            (leftName := "Target cycle")
                                            (leftNote := "")
                                            (rightName := "No accepted theta")
                                            (rightNote := "")
                                            (left := Blueprint.root)
                                            (right :=
                                              Blueprint.root.dichotomy $typeAExitThree
                                                (name := "Exit 3: P13 label collision")
                                                (note := "")
                                                (leftName := "Label/target collision")
                                                (leftNote := "")
                                                (rightName := "No label collision")
                                                (rightNote := "")
                                                (left := Blueprint.root)
                                                (right :=
                                                  Blueprint.root.dichotomy $typeAExitFour
                                                    (name := "Exit 4: target-defective quotient")
                                                    (note := "")
                                                    (leftName := "Target-defect peels one load")
                                                    (leftNote := "")
                                                    (rightName := "No target-defective quotient")
                                                    (rightNote := "")
                                                    (right :=
                                                      Blueprint.root.dichotomy $typeAExitFive
                                                        (name := "Exit 5: target-complete compression")
                                                        (note := "")
                                                        (leftName := "Uncompressibility contradiction")
                                                        (leftNote := "")
                                                        (rightName := "No compression")
                                                        (rightNote := "")
                                                        (right :=
                                                          Blueprint.root.dichotomy $typeAExitSix
                                                            (name := "Exit 6: response delocalization")
                                                            (note := "")
                                                            (leftName := "Delocalization branch")
                                                            (leftNote := "")
                                                            (rightName := "No delocalization")
                                                            (rightNote := "")
                                                            (right :=
                                                              Blueprint.root.dichotomy $typeAExitSeven
                                                                (name := "Exit 7: decorated handoff fan")
                                                                (note := "")
                                                                (leftName := "Type B handoff")
                                                                (leftNote := "")
                                                                (rightName := "Route-8 residual")
                                                                (rightNote := "")
                                                                (right :=
                                                                Blueprint.root.route8CarrierClosure $typeARoute8
                                                                  (name := "Route-8 carrier closure")
                                                                  (note := "")
                                                                  (nonClosureName := "Carrier supply, census and descent")
                                                                  (nonClosureNote := "Nodes [114]-[121] and [123]: the \
                                                                    arms that reach no terminal ellipse. The zero-carrier \
                                                                    entry of [116], where lem:typeA-one-terminal-collapse \
                                                                    gives one of exits (4)-(7); the CT5 supply \
                                                                    comparisons; node [118]'s two-carrier entry, which is \
                                                                    CT14's aggregate overload at the derived demand; and \
                                                                    the descent's own exhaustion.")
                                                                  (closureName := "Nodes [122] and [124]: both terminals")
                                                                  (closureNote := "Figure 9's two terminal ellipses, both \
                                                                    uninhabited, so this arm closes rather than being \
                                                                    retained as an open leaf. Node [124] is \
                                                                    thm:typeA-two-carrier-nogo: the descent's tier \
                                                                    terminal is a terminal two-carrier route-8 \
                                                                    obstruction of def:typeA-terminal-two-carrier, whose \
                                                                    clause (T5) places each declared deletion witness in \
                                                                    the canonical exit-(4) family while clause (T2) \
                                                                    denies exit (4). Node [122] is \
                                                                    prop:typeA-route8-carrier-reduction: the descent's \
                                                                    demand terminal collides the route-8 burden [112], \
                                                                    the large-budget deficit [113] and the \
                                                                    private-carrier budget [120] below the carrier rate \
                                                                    required/(required*dischargeScale + 1), which at the \
                                                                    registered values is the manuscript's 3/13.")))))))))))
                            (typeB := fun branch =>
                              branch.dichotomy
                                  (name := "Type B heavy-centre split")
                                  (note := "")
                                  (left :=
                                    Blueprint.root.responseClassifier
                                      (name := "Heavy-centre local response")
                                      (note := "")
                                    |>.orderedWitnessScan
                                        $fanSafeScan
                                      (name := "Type B fan-safe cap")
                                      (note := ""))
                                  (right :=
                                    Blueprint.root.orderedWitnessScan
                                        $fanSafeScan
                                      (name := "Type B fan-safe cap")
                                      (note := ""))
                                |>.orderedWitnessScan
                                    $degreeFour
                                  (name := "Degree-four fan profile")
                                  (note := "")
                                |>.dichotomy $certSplit
                                  (name := "Type B certificate labelling")
                                  (note := "")
                                  (left :=
                                    Blueprint.root.dichotomy
                                        $directCycleSplit
                                      (name := "Type B direct-cycle removal")
                                      (note := "")
                                      (left := Blueprint.root)
                                      (leftName := "Direct fan-window or \
                                        two-window cycle")
                                      (leftNote := "")
                                      (rightName := "Direct-cycle-free closed \
                                        pair")
                                      (rightNote := "")
                                      (right :=
                                        Blueprint.root.dichotomy $b2Split
                                          (name := "Type B B2 ledger")
                                          (note := "")
                                          (left :=
                                            Blueprint.root.orderedWitnessScan
                                                $hybridEntry
                                              (name := "Type B hybrid B1 entry")
                                              (note := ""))
                                          (right :=
                                            Blueprint.root.baselineDemandAccounting
                                                $fanMass
                                              (name := "Type B bridge fan-mass")
                                              (note := ""))))
                                  (right :=
                                    Blueprint.root.baselineDemandAccounting
                                        $fanMass
                                      (name := "Type B bridge fan-mass")
                                      (note := ""))
                                |>.orderedWitnessScan $bridgeDeficit
                                  (name := "Type B bridge deficit")
                                  (note := "")
                                |>.autoroute
                                  (name := "Route-8 cores to the Type A ledger")
                                  (note := ""))
                            (name := "Nodes [57]–[64] net-charge continuation")
                            (typeAName := "Node [63] Type A residual")
                            (typeANote := "")
                            (typeBName := "Node [64] Type B residual")
                            (typeBNote := "")
                            (note := ""))
                        (name := "Full-rank finite-state capacity")
                        (note := "")
                        (nonCapacityName :=
                          "Finite-state non-capacity residual")
                        (nonCapacityNote :=
                          "")
                        (capacityName := "Finite-state capacity residual")
                        (capacityNote :=
                          ""))
                    (name := "Target-relative rank dichotomy")
                    (note := "")
                    (rankDropName := "Rank-drop residual")
                    (rankDropNote := "")
                    (fullRankName := "Full-rank exact-code residual")
                    (fullRankNote := ""))
              (name := "Finite window-density budget")
              (note := "")
              (overflowName := "Density overflow residual")
              (overflowNote := "")
              (capName := "Density-cap residual")
              (capNote := ""))
        (atOrBelowName := "Near-cubic envelope")
        (atOrBelowNote := "")
  )

noncomputable def strategyDag : Program Official.definition.data :=
  Program.ofBlueprint (erdosOfficialBlueprint%
    ⟨0, by simp [Official.definition]⟩    -- fanSafeScan       scans 0
    ⟨1, by simp [Official.definition]⟩    -- certSplit         dichotomies 1
    ⟨2, by simp [Official.definition]⟩    -- b2Split           dichotomies 2
    ⟨1, by simp [Official.definition]⟩    -- fanMass           baselineDemand 1
    ⟨1, by simp [Official.definition]⟩    -- degreeFour        scans 1
    ⟨2, by simp [Official.definition]⟩    -- hybridEntry       scans 2
    ⟨3, by simp [Official.definition]⟩    -- bridgeDeficit     scans 3
    ⟨3, by simp [Official.definition]⟩    -- directCycleSplit  dichotomies 3
    ⟨4, by simp [Official.definition]⟩    -- typeASaturated    dichotomies 4   [89]
    ⟨5, by simp [Official.definition]⟩    -- typeAVisible      dichotomies 5   [93]
    ⟨6, by simp [Official.definition]⟩    -- typeAExitOne      dichotomies 6   [95]
    ⟨7, by simp [Official.definition]⟩    -- typeAExitTwo      dichotomies 7   [97]
    ⟨8, by simp [Official.definition]⟩    -- typeAExitThree    dichotomies 8   [99]
    ⟨9, by simp [Official.definition]⟩    -- typeAExitFour     dichotomies 9   [101]
    ⟨10, by simp [Official.definition]⟩   -- typeAExitFive     dichotomies 10   [103]
    ⟨11, by simp [Official.definition]⟩   -- typeAExitSix      dichotomies 11   [105]
    ⟨12, by simp [Official.definition]⟩   -- typeAExitSeven    dichotomies 12   [107]
    ⟨0, by simp [Official.definition]⟩)   -- typeARoute8      route8Closures 0 [111]-[124]

-/

end HypostructureErdos64EG
