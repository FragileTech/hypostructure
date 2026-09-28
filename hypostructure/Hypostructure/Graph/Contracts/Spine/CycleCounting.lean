import Hypostructure.Graph.Statements.Spine
import Hypostructure.Graph.Statements.CycleCounting

/-!
# Contracts: cycles through the vertices of G

Proof-agnostic contract lemmas for `Statements/CycleCounting.lean`.  Each is
stated over a `Graph.FiniteObject` with the registered `Parameters` as a
parameter; its hypotheses are exactly ledger facts (or their projections): the
selection's target avoidance, the presentation laws (`δ = 3`, the accepted
quadrilateral, the dyadic length law), the baseline, `[8]`'s no proper
baseline, `lem:bridgeless`, and `[10]`'s independent high vertices.  One
contract per statement: `<statement>_holds`.

This module imports no strategy, row, or vocabulary module.
-/

namespace Hypostructure.Graph.Contracts.Spine.CycleCounting

open Hypostructure
open Hypostructure.Graph
open Hypostructure.Graph.Strategy.Spine

universe u

variable {data : Parameters} {object : Graph.FiniteObject.{u}}

theorem neighbourhoodPairCount_holds
    (avoid : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (four : data.LengthOK 4) :
    NeighbourhoodPairCountStatement object :=
  Graph.CycleCounting.neighbourhoodPairs avoid four

theorem starCycleConstraint_holds
    (avoid : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (lengthLaw : ∀ length, data.LengthOK length ↔ Core.DyadicLength.PowerOfTwoLength length) :
    StarCycleConstraintStatement object :=
  Graph.CycleCounting.starConstraint avoid lengthLaw

theorem meetingCycleConstraint_holds
    (avoid : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (lengthLaw : ∀ length, data.LengthOK length ↔ Core.DyadicLength.PowerOfTwoLength length) :
    MeetingCycleConstraintStatement object :=
  Graph.CycleCounting.meetingConstraint avoid lengthLaw

theorem highDegreePairSum_holds (three : data.threshold = 3)
    (baseline : MinDegreeBaselineStatement data object) :
    HighDegreePairSumStatement data object := by
  unfold HighDegreePairSumStatement
  rw [three]
  exact Graph.CycleCounting.highPairSum (three ▸ baseline)

theorem vertexDeletionComponents_holds (three : data.threshold = 3)
    (baseline : MinDegreeBaselineStatement data object)
    (noProper : NoProperBaselineStatement data object)
    (bridgeless : BridgelessStatement object) :
    VertexDeletionComponentsStatement object :=
  Graph.CycleCounting.vertexDeletionShape (three ▸ baseline) (three ▸ noProper.1) bridgeless

theorem cyclesThroughVertex_holds (three : data.threshold = 3)
    (baseline : MinDegreeBaselineStatement data object)
    (noProper : NoProperBaselineStatement data object)
    (bridgeless : BridgelessStatement object) :
    CyclesThroughVertexStatement object :=
  Graph.CycleCounting.cyclesThroughVertex (three ▸ baseline) (three ▸ noProper.1) bridgeless

theorem cutVertexBlockPaths_holds (three : data.threshold = 3)
    (baseline : MinDegreeBaselineStatement data object)
    (noProper : NoProperBaselineStatement data object)
    (bridgeless : BridgelessStatement object)
    (avoid : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (lengthLaw : ∀ length, data.LengthOK length ↔ Core.DyadicLength.PowerOfTwoLength length) :
    CutVertexBlockPathsStatement object :=
  Graph.CycleCounting.blockPaths (three ▸ baseline) (three ▸ noProper.1) bridgeless avoid
    lengthLaw

theorem cycleDoubleCount_holds (three : data.threshold = 3)
    (baseline : MinDegreeBaselineStatement data object)
    (noProper : NoProperBaselineStatement data object)
    (bridgeless : BridgelessStatement object)
    (independent : SlackIndependentStatement data object) :
    CycleDoubleCountStatement data object := by
  unfold CycleDoubleCountStatement
  rw [three]
  exact Graph.CycleCounting.cycleDoubleCount (three ▸ baseline) (three ▸ noProper.1) bridgeless
    (three ▸ independent)

end Hypostructure.Graph.Contracts.Spine.CycleCounting
