import Hypostructure.Graph.Statements.JointHubs
import Hypostructure.Graph.WindowLabelCensus

/-!
# Contracts: hubs, cubic vertices, windows and the remainder of G

Proof-agnostic contract lemmas for `Statements/JointHubs.lean`.  Each is stated over a
`Graph.FiniteObject` with the registered `Parameters` as a parameter; its hypotheses are
exactly ledger facts (or their projections): the selection's target avoidance and
minimality, the presentation laws (`δ = 3`, the dyadic length law, the label census, which
fixes the window order to `13`), the baseline, `[8]`'s no proper baseline subgraph and
connectivity, `lem:bridgeless`, `[10]`'s independent high vertices, the replacement
exclusion, the surplus scale of `[19]`'s strict arm, and G's canonical capacity
presentation.  The canonical packing `P₀` is valid and maximal by its definition
(`canonicalWindowPacking_spec`).  One contract per statement: `<statement>_holds`.

This module imports no strategy, row, or vocabulary module.
-/

namespace Hypostructure.Graph.Contracts.Spine.JointHubs

open Hypostructure
open Hypostructure.Graph
open Hypostructure.Graph.Strategy.Spine

universe u v

variable {data : Parameters} {object : Graph.FiniteObject.{u}}

/-! ## The ledger facts in the library's spelling -/

theorem base_of (three : data.threshold = 3) (baseline : MinDegreeBaselineStatement data object) :
    Graph.MinimumDegreeAtLeast 3 object :=
  three ▸ baseline

theorem noProper_of (three : data.threshold = 3) (noProper : NoProperBaselineStatement data object) :
    Graph.JointObject.NoProperCubic object := by
  have h := noProper.1
  rw [three] at h
  exact h

theorem slack_of (three : data.threshold = 3) (slack : SlackIndependentStatement data object) :
    Graph.JointObject.SlackIndependent object := by
  intro l r hl hr
  exact slack l r (three ▸ hl) (three ▸ hr)

theorem dyadic_of (avoid : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (lengthLaw : ∀ length, data.LengthOK length ↔ Core.DyadicLength.PowerOfTwoLength length) :
    ¬ Graph.HasCycleWithLength Core.DyadicLength.PowerOfTwoLength object :=
  Graph.JointObject.avoid_dyadic avoid lengthLaw

/-- The registered label census fixes the window order to `13`. -/
theorem order_of
    (census : (Graph.WindowCurvature.sizeDistribution data.windowOrder).take 7 =
      [13, 60, 122, 122, 63, 17, 2]) :
    data.windowOrder = 13 :=
  Graph.WindowCurvature.order_eq_of_sizeDistribution_head census

theorem valid_of (order : data.windowOrder = 13) :
    object.IsWindowPacking 13 (canonicalWindowPacking data object) :=
  order ▸ (canonicalWindowPacking_spec data object).1

theorem maximal_of (order : data.windowOrder = 13) :
    Graph.JointObject.PackingMaximal object (canonicalWindowPacking data object) := by
  have h := (canonicalWindowPacking_spec data object).2.2
  rw [order] at h
  exact h

/-! ## Hubs and cubic vertices -/

theorem cubicNeighbourSupply_holds (three : data.threshold = 3)
    (baseline : MinDegreeBaselineStatement data object)
    (noProper : NoProperBaselineStatement data object) :
    CubicNeighbourSupplyStatement object :=
  Graph.JointObject.cubicNeighbourSupply (base_of three baseline) (noProper_of three noProper)

theorem hubCountBound_holds (three : data.threshold = 3)
    (baseline : MinDegreeBaselineStatement data object)
    (noProper : NoProperBaselineStatement data object)
    (slack : SlackIndependentStatement data object) :
    HubCountBoundStatement object :=
  Graph.JointObject.hubCountBound (base_of three baseline) (noProper_of three noProper)
    (slack_of three slack)

theorem lowEdgeParity_holds (three : data.threshold = 3)
    (baseline : MinDegreeBaselineStatement data object)
    (slack : SlackIndependentStatement data object) :
    LowEdgeParityStatement object :=
  Graph.JointObject.lowEdgeParity (base_of three baseline) (slack_of three slack)

theorem bigHubBound_holds (three : data.threshold = 3)
    (baseline : MinDegreeBaselineStatement data object)
    (noProper : NoProperBaselineStatement data object)
    (slack : SlackIndependentStatement data object) :
    BigHubBoundStatement object :=
  Graph.JointObject.bigHubBound (base_of three baseline) (noProper_of three noProper)
    (slack_of three slack)

theorem bigHubVShapes_holds (three : data.threshold = 3)
    (avoid : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (lengthLaw : ∀ length, data.LengthOK length ↔ Core.DyadicLength.PowerOfTwoLength length)
    (baseline : MinDegreeBaselineStatement data object)
    (slack : SlackIndependentStatement data object) :
    BigHubVShapesStatement object :=
  Graph.JointObject.bigHubVShapes (base_of three baseline) (slack_of three slack)
    (dyadic_of avoid lengthLaw)

theorem highSurplusBound_holds (three : data.threshold = 3)
    (avoid : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (lengthLaw : ∀ length, data.LengthOK length ↔ Core.DyadicLength.PowerOfTwoLength length)
    (baseline : MinDegreeBaselineStatement data object)
    (noProper : NoProperBaselineStatement data object)
    (slack : SlackIndependentStatement data object) :
    HighSurplusBoundStatement object :=
  Graph.JointObject.highSurplusBound (base_of three baseline) (noProper_of three noProper)
    (slack_of three slack) (dyadic_of avoid lengthLaw)

theorem hubLengthThreePairs_holds (three : data.threshold = 3)
    (avoid : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (lengthLaw : ∀ length, data.LengthOK length ↔ Core.DyadicLength.PowerOfTwoLength length)
    (baseline : MinDegreeBaselineStatement data object)
    (slack : SlackIndependentStatement data object) :
    HubLengthThreePairsStatement object :=
  Graph.JointObject.hubLengthThreePairs (base_of three baseline) (slack_of three slack)
    (dyadic_of avoid lengthLaw)

theorem densityExcess_holds (three : data.threshold = 3)
    (noProper : NoProperBaselineStatement data object)
    (bridgeless : BridgelessStatement object) :
    DensityExcessStatement object :=
  Graph.JointObject.densityExcess (noProper_of three noProper) noProper.2 bridgeless

/-! ## The canonical packing `P₀` -/

theorem remainderSlack_holds (three : data.threshold = 3)
    (census : (Graph.WindowCurvature.sizeDistribution data.windowOrder).take 7 =
      [13, 60, 122, 122, 63, 17, 2])
    (baseline : MinDegreeBaselineStatement data object)
    (noProper : NoProperBaselineStatement data object) :
    RemainderSlackStatement data object :=
  Graph.JointObject.remainderSlack_holds (base_of three baseline) (noProper_of three noProper)
    (valid_of (order_of census))

theorem hubWindowBudget_holds (three : data.threshold = 3)
    (census : (Graph.WindowCurvature.sizeDistribution data.windowOrder).take 7 =
      [13, 60, 122, 122, 63, 17, 2])
    (baseline : MinDegreeBaselineStatement data object)
    (noProper : NoProperBaselineStatement data object)
    (slack : SlackIndependentStatement data object) :
    HubWindowBudgetStatement data object :=
  Graph.JointObject.hubWindowBudget_holds (base_of three baseline) (noProper_of three noProper)
    (slack_of three slack) (valid_of (order_of census))

theorem windowHubBounds_holds (three : data.threshold = 3)
    (census : (Graph.WindowCurvature.sizeDistribution data.windowOrder).take 7 =
      [13, 60, 122, 122, 63, 17, 2])
    (avoid : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (lengthLaw : ∀ length, data.LengthOK length ↔ Core.DyadicLength.PowerOfTwoLength length)
    (baseline : MinDegreeBaselineStatement data object)
    (noProper : NoProperBaselineStatement data object)
    (slack : SlackIndependentStatement data object) :
    WindowHubBoundsStatement data object :=
  Graph.JointObject.windowHubBounds (base_of three baseline) (noProper_of three noProper)
    (slack_of three slack) (dyadic_of avoid lengthLaw) (valid_of (order_of census))

theorem remainderPathBounds_holds (three : data.threshold = 3)
    (census : (Graph.WindowCurvature.sizeDistribution data.windowOrder).take 7 =
      [13, 60, 122, 122, 63, 17, 2])
    (avoid : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (lengthLaw : ∀ length, data.LengthOK length ↔ Core.DyadicLength.PowerOfTwoLength length)
    (baseline : MinDegreeBaselineStatement data object) :
    RemainderPathBoundsStatement data object :=
  Graph.JointObject.remainderPathBounds (maximal_of (order_of census)) (base_of three baseline)
    (dyadic_of avoid lengthLaw)

theorem windowFreeGeometry_holds (three : data.threshold = 3)
    (census : (Graph.WindowCurvature.sizeDistribution data.windowOrder).take 7 =
      [13, 60, 122, 122, 63, 17, 2])
    (avoid : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (lengthLaw : ∀ length, data.LengthOK length ↔ Core.DyadicLength.PowerOfTwoLength length)
    (baseline : MinDegreeBaselineStatement data object) :
    WindowFreeGeometryStatement data object :=
  Graph.JointObject.windowFreeGeometry (maximal_of (order_of census)) (base_of three baseline)
    (dyadic_of avoid lengthLaw)

theorem inducedPathAttachment_holds (three : data.threshold = 3)
    (avoid : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (lengthLaw : ∀ length, data.LengthOK length ↔ Core.DyadicLength.PowerOfTwoLength length)
    (baseline : MinDegreeBaselineStatement data object) :
    InducedPathAttachmentStatement object :=
  Graph.JointObject.inducedPathAttachment (base_of three baseline) (dyadic_of avoid lengthLaw)

/-! ## The strict arm of the surplus scale -/

theorem highSurplusOrder_holds (three : data.threshold = 3)
    (bound : HighSurplusBoundStatement object)
    (bigHub : BigHubBoundStatement object)
    (above : SurplusAboveStatement data object)
    (ceil : CeilSqrtAboveScaleStatement data object) :
    HighSurplusOrderStatement data object := by
  have hσ : object.degreeSurplus 3 ≤ object.vertexCount := by
    have := bigHub.2; omega
  have habove : data.spineScale * Core.ceilSqrt object.vertexCount < object.degreeSurplus 3 := by
    have := above; unfold SurplusAboveStatement Parameters.surplusThreshold at this
    rw [three] at this; exact this
  refine ⟨Graph.JointSystem.closure_at_window _ _ _ bound.2 habove hσ, fun t ht => ?_⟩
  have hC : data.spineScale * (data.spineScale + 1) ≤
      data.spineScale * Core.ceilSqrt object.vertexCount :=
    Nat.mul_le_mul_left _ ceil
  exact Graph.JointSystem.first_band_of_closure _ _ _ t bound.2 (by omega) hσ ht

/-! ## G's canonical capacity presentation -/

theorem windowChargeKinds_holds (explicit : CanonicalCapacityExplicitStatement data object) :
    WindowChargeKindsStatement data object := by
  obtain ⟨active, avoids, connected, h⟩ := explicit
  exact ⟨active, avoids, connected, h,
    Graph.WindowChargeKinds.windowChargeStructure _ _ _ _,
    Graph.WindowChargeKinds.recordedActivationFacts _ _⟩

theorem responseObstructionTargetDefect_holds
    {BranchState : Graph.FiniteObject.{u} → Type v} {Presentation : Type}
    {presentation : Presentation}
    (explicit : CanonicalCapacityExplicitStatement data object)
    (minimal : SelectionMinimality BranchState Presentation presentation data object)
    (replacement : ReplacementExclusionStatement data object) :
    ResponseObstructionTargetDefectStatement data object := by
  obtain ⟨active, avoids, connected, h⟩ := explicit
  exact ⟨active, avoids, connected, h,
    Graph.WindowChargeKinds.responseObstructionsAreTargetDefects _ _ replacement avoids
      (fun H hlt hb => minimal.sizeMinimal H hlt hb)⟩

end Hypostructure.Graph.Contracts.Spine.JointHubs
