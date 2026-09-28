import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.Spine.SparseExitResidual

/-!
# Node `[20a]`: the strict-surplus named sparse exit, made explicit

Type A rows on the `[20a]` path, after `[20a]`'s existing facts and before its
return.  Each row reads its prerequisites through `inputs.get` and publishes,
at G, the bounds, ratios, identities and obstructions that the residual's own
facts force (contracts: `Graph/Contracts/Spine/SparseExitResidual.lean`).
No row decides or splits anything.
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-- Node `[20a]`: the canonical witness `(first, second, Z, O)`: its readings, `Z`, `O`, and the excluded exits (d), (e). -/
@[reducible] noncomputable def sparseExitWitnessFactsRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.sparseExitWitnessFacts
    { Requires := [K .targetCompleteContextUniversality, K .sparseTargetDefectResidual, K .selection]
      Produces := [K .witnessReadingsNotTargetComplete, K .witnessActualOutsideNegative, K .witnessReadingsCycleFree, K .witnessSupportOrderBound, K .witnessReadingGluesNotSmallerBaseline, K .noSuppressionChordViolation]
      requiresUnique := by key_fresh
      producesUnique := by key_fresh
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .witnessReadingsNotTargetComplete)
        ⟨Contracts.Spine.SparseExitResidual.witnessReadingsNotTargetComplete_holds (object := inputs.current.object) (inputs.get (K .targetCompleteContextUniversality)).down (inputs.get (K .sparseTargetDefectResidual)).down⟩
      (.cons (key := K .witnessActualOutsideNegative)
        ⟨Contracts.Spine.SparseExitResidual.witnessActualOutsideNegative_holds (object := inputs.current.object) (inputs.get (K .selection)).down.1 (inputs.get (K .sparseTargetDefectResidual)).down⟩
      (.cons (key := K .witnessReadingsCycleFree)
        ⟨Contracts.Spine.SparseExitResidual.witnessReadingsCycleFree_holds (object := inputs.current.object) (inputs.get (K .selection)).down.1 (inputs.get (K .sparseTargetDefectResidual)).down⟩
      (.cons (key := K .witnessSupportOrderBound)
        ⟨Contracts.Spine.SparseExitResidual.witnessSupportOrderBound_holds (object := inputs.current.object) (inputs.get (K .selection)).down.1 (inputs.get (K .sparseTargetDefectResidual)).down⟩
      (.cons (key := K .witnessReadingGluesNotSmallerBaseline)
        ⟨Contracts.Spine.SparseExitResidual.witnessReadingGluesNotSmallerBaseline_holds (object := inputs.current.object) (inputs.get (K .selection)).down.1 (inputs.get (K .selection)).down.2.sizeMinimal (inputs.get (K .sparseTargetDefectResidual)).down⟩
      (.cons (key := K .noSuppressionChordViolation)
        ⟨Contracts.Spine.SparseExitResidual.noSuppressionChordViolation_holds (object := inputs.current.object) (inputs.get (K .selection)).down.1⟩
      .nil))))))

/-- Node `[20a]`: the single budget: handshake, dart identity, packing ratio, the square-root chain. -/
@[reducible] noncomputable def sparseExitBudgetRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.sparseExitBudget
    { Requires := [K .cubicBaseline, K .minDegreeBaseline, K .tightEndpoint, K .noProperBaseline, K .surplusAbove]
      Produces := [K .edgeSurplusIdentity, K .surplusDartIdentity, K .highDegreeCountBound, K .packingOrderBound, K .ceilSqrtAboveScale]
      requiresUnique := by key_fresh
      producesUnique := by key_fresh
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .edgeSurplusIdentity)
        ⟨Contracts.Spine.SparseExitResidual.edgeSurplusIdentity_holds (object := inputs.current.object) (inputs.get (K .cubicBaseline)).down.1.1 (inputs.get (K .minDegreeBaseline)).down (inputs.get (K .tightEndpoint)).down (inputs.get (K .noProperBaseline)).down (inputs.get (K .surplusAbove)).down⟩
      (.cons (key := K .surplusDartIdentity)
        ⟨Contracts.Spine.SparseExitResidual.surplusDartIdentity_holds (object := inputs.current.object) (inputs.get (K .cubicBaseline)).down.1.1 (inputs.get (K .minDegreeBaseline)).down (inputs.get (K .tightEndpoint)).down⟩
      (.cons (key := K .highDegreeCountBound)
        ⟨Contracts.Spine.SparseExitResidual.highDegreeCountBound_holds (object := inputs.current.object) (inputs.get (K .cubicBaseline)).down.1.1 (inputs.get (K .minDegreeBaseline)).down (inputs.get (K .tightEndpoint)).down⟩
      (.cons (key := K .packingOrderBound)
        ⟨Contracts.Spine.SparseExitResidual.packingOrderBound_holds (object := inputs.current.object) ⟩
      (.cons (key := K .ceilSqrtAboveScale)
        ⟨Contracts.Spine.SparseExitResidual.ceilSqrtAboveScale_holds (object := inputs.current.object) (inputs.get (K .cubicBaseline)).down.1.1 (inputs.get (K .minDegreeBaseline)).down (inputs.get (K .tightEndpoint)).down (inputs.get (K .noProperBaseline)).down (inputs.get (K .surplusAbove)).down⟩
      .nil)))))

/-- Node `[20a]`: the envelope sharpened by the absent quadrilateral and by `ex(6, C₄) = 7`. -/
@[reducible] noncomputable def sparseExitEnvelopeRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.sparseExitEnvelope
    { Requires := [K .cubicBaseline, K .selection, K .minDegreeBaseline, K .tightEndpoint, K .noProperBaseline, K .surplusAbove]
      Produces := [K .orderAboveScaleSquare, K .sixVertexExtremalEnvelope]
      requiresUnique := by key_fresh
      producesUnique := by key_fresh
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .orderAboveScaleSquare)
        ⟨Contracts.Spine.SparseExitResidual.orderAboveScaleSquare_holds (object := inputs.current.object) (inputs.get (K .cubicBaseline)).down.1.1 (inputs.get (K .cubicBaseline)).down.2.1.1 (inputs.get (K .selection)).down.1 (inputs.get (K .minDegreeBaseline)).down (inputs.get (K .tightEndpoint)).down (inputs.get (K .noProperBaseline)).down (inputs.get (K .surplusAbove)).down⟩
      (.cons (key := K .sixVertexExtremalEnvelope)
        ⟨Contracts.Spine.SparseExitResidual.sixVertexExtremalEnvelope_holds (object := inputs.current.object) (inputs.get (K .cubicBaseline)).down.1.1 (inputs.get (K .cubicBaseline)).down.2.1.1 (inputs.get (K .selection)).down.1 (inputs.get (K .minDegreeBaseline)).down (inputs.get (K .tightEndpoint)).down (inputs.get (K .noProperBaseline)).down (inputs.get (K .surplusAbove)).down⟩
      .nil))

/-- Node `[20a]`: the canonical packing `P₀`: `def⁺(R) ≤ e(R, W)` and the window cut capacity. -/
@[reducible] noncomputable def sparseExitPackingRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.sparseExitPacking
    { Requires := [K .minDegreeBaseline]
      Produces := [K .remainderDeficiencyBelowCut, K .windowCutCapacity]
      requiresUnique := by key_fresh
      producesUnique := by key_fresh
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .remainderDeficiencyBelowCut)
        ⟨Contracts.Spine.SparseExitResidual.remainderDeficiencyBelowCut_holds (object := inputs.current.object) (inputs.get (K .minDegreeBaseline)).down⟩
      (.cons (key := K .windowCutCapacity)
        ⟨Contracts.Spine.SparseExitResidual.windowCutCapacity_holds (object := inputs.current.object) (inputs.get (K .minDegreeBaseline)).down⟩
      .nil))

/-- Node `[20a]`: contexts realized in `G − Z`, sub-contexts of `O`, and the path spectrum. -/
@[reducible] noncomputable def sparseExitRealizedContextsRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.sparseExitRealizedContexts
    { Requires := [K .selection, K .sparseTargetDefectResidual, K .cubicBaseline]
      Produces := [K .witnessOutsideNotRealized, K .realizedContextsNegative, K .negativeSubGluingNotSmallerBaseline, K .cycleSubContextSeparates, K .pathSpectrumSplit]
      requiresUnique := by key_fresh
      producesUnique := by key_fresh
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .witnessOutsideNotRealized)
        ⟨Contracts.Spine.SparseExitResidual.witnessOutsideNotRealized_holds (object := inputs.current.object) (inputs.get (K .selection)).down.1 (inputs.get (K .sparseTargetDefectResidual)).down⟩
      (.cons (key := K .realizedContextsNegative)
        ⟨Contracts.Spine.SparseExitResidual.realizedContextsNegative_holds (object := inputs.current.object) (inputs.get (K .selection)).down.1 (inputs.get (K .sparseTargetDefectResidual)).down⟩
      (.cons (key := K .negativeSubGluingNotSmallerBaseline)
        ⟨Contracts.Spine.SparseExitResidual.negativeSubGluingNotSmallerBaseline_holds (object := inputs.current.object) (inputs.get (K .selection)).down.2.sizeMinimal (inputs.get (K .sparseTargetDefectResidual)).down⟩
      (.cons (key := K .cycleSubContextSeparates)
        ⟨Contracts.Spine.SparseExitResidual.cycleSubContextSeparates_holds (object := inputs.current.object) (inputs.get (K .cubicBaseline)).down.1.1 (inputs.get (K .selection)).down.1 (inputs.get (K .selection)).down.2.sizeMinimal (inputs.get (K .sparseTargetDefectResidual)).down⟩
      (.cons (key := K .pathSpectrumSplit)
        ⟨Contracts.Spine.SparseExitResidual.pathSpectrumSplit_holds (object := inputs.current.object) (inputs.get (K .cubicBaseline)).down.2.1.2.1 (inputs.get (K .selection)).down.1 (inputs.get (K .sparseTargetDefectResidual)).down⟩
      .nil)))))

/-- Node `[20a]`: admissible and attempted quotients of G at the pinned pair. -/
@[reducible] noncomputable def sparseExitQuotientsRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.sparseExitQuotients
    { Requires := [K .selection, K .replacementExclusion]
      Produces := [K .admissibleQuotientsLabelInjective]
      requiresUnique := by key_fresh
      producesUnique := by key_fresh
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .admissibleQuotientsLabelInjective)
        ⟨Contracts.Spine.SparseExitResidual.admissibleQuotientsLabelInjective_holds (object := inputs.current.object) (inputs.get (K .selection)).down.1 (inputs.get (K .selection)).down.2.sizeMinimal (inputs.get (K .replacementExclusion)).down⟩
      .nil)

/-- Node `[20a]`: the boundary `∂Z` of the canonical support and its two-boundary case. -/
@[reducible] noncomputable def sparseExitBoundaryRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.sparseExitBoundary
    { Requires := [K .cubicBaseline, K .minDegreeBaseline, K .noProperBaseline, K .bridgeless, K .selection, K .sparseTargetDefectResidual]
      Produces := [K .singleBoundaryShape, K .positiveSupportBoundaryTwo, K .supportCutEdgesTwo, K .boundaryLowInsideVertex, K .outsideLowVertex, K .twoBoundaryLowOutsideSide, K .twoBoundarySupportClosure, K .twoBoundaryOutsideClosure, K .twoBoundaryNoTargetSum, K .outsideOrBoundaryLarge]
      requiresUnique := by key_fresh
      producesUnique := by key_fresh
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .singleBoundaryShape)
        ⟨Contracts.Spine.SparseExitResidual.singleBoundaryShape_holds (object := inputs.current.object) (inputs.get (K .cubicBaseline)).down.1.1 (inputs.get (K .minDegreeBaseline)).down (inputs.get (K .noProperBaseline)).down (inputs.get (K .bridgeless)).down⟩
      (.cons (key := K .positiveSupportBoundaryTwo)
        ⟨Contracts.Spine.SparseExitResidual.positiveSupportBoundaryTwo_holds (object := inputs.current.object) (inputs.get (K .selection)).down.1 (inputs.get (K .sparseTargetDefectResidual)).down⟩
      (.cons (key := K .supportCutEdgesTwo)
        ⟨Contracts.Spine.SparseExitResidual.supportCutEdgesTwo_holds (object := inputs.current.object) (inputs.get (K .selection)).down.1 (inputs.get (K .sparseTargetDefectResidual)).down⟩
      (.cons (key := K .boundaryLowInsideVertex)
        ⟨Contracts.Spine.SparseExitResidual.boundaryLowInsideVertex_holds (object := inputs.current.object) (inputs.get (K .cubicBaseline)).down.1.1 (inputs.get (K .minDegreeBaseline)).down (inputs.get (K .noProperBaseline)).down (inputs.get (K .selection)).down.1 (inputs.get (K .sparseTargetDefectResidual)).down⟩
      (.cons (key := K .outsideLowVertex)
        ⟨Contracts.Spine.SparseExitResidual.outsideLowVertex_holds (object := inputs.current.object) (inputs.get (K .cubicBaseline)).down.1.1 (inputs.get (K .minDegreeBaseline)).down (inputs.get (K .noProperBaseline)).down (inputs.get (K .selection)).down.1 (inputs.get (K .sparseTargetDefectResidual)).down⟩
      (.cons (key := K .twoBoundaryLowOutsideSide)
        ⟨Contracts.Spine.SparseExitResidual.twoBoundaryLowOutsideSide_holds (object := inputs.current.object) (inputs.get (K .cubicBaseline)).down.1.1 (inputs.get (K .minDegreeBaseline)).down (inputs.get (K .noProperBaseline)).down (inputs.get (K .sparseTargetDefectResidual)).down⟩
      (.cons (key := K .twoBoundarySupportClosure)
        ⟨Contracts.Spine.SparseExitResidual.twoBoundarySupportClosure_holds (object := inputs.current.object) (inputs.get (K .cubicBaseline)).down.1.1 (inputs.get (K .minDegreeBaseline)).down (inputs.get (K .selection)).down.1 (inputs.get (K .selection)).down.2.sizeMinimal (inputs.get (K .sparseTargetDefectResidual)).down⟩
      (.cons (key := K .twoBoundaryOutsideClosure)
        ⟨Contracts.Spine.SparseExitResidual.twoBoundaryOutsideClosure_holds (object := inputs.current.object) (inputs.get (K .cubicBaseline)).down.1.1 (inputs.get (K .minDegreeBaseline)).down (inputs.get (K .selection)).down.1 (inputs.get (K .selection)).down.2.sizeMinimal (inputs.get (K .sparseTargetDefectResidual)).down⟩
      (.cons (key := K .twoBoundaryNoTargetSum)
        ⟨Contracts.Spine.SparseExitResidual.twoBoundaryNoTargetSum_holds (object := inputs.current.object) (inputs.get (K .selection)).down.1 (inputs.get (K .sparseTargetDefectResidual)).down⟩
      (.cons (key := K .outsideOrBoundaryLarge)
        ⟨Contracts.Spine.SparseExitResidual.outsideOrBoundaryLarge_holds (object := inputs.current.object) (inputs.get (K .cubicBaseline)).down.1.1 (inputs.get (K .minDegreeBaseline)).down (inputs.get (K .selection)).down.1 (inputs.get (K .sparseTargetDefectResidual)).down⟩
      .nil))))))))))

/-- Node `[20a]`: the compression route at G's own pieces: modified pieces and the whole case. -/
@[reducible] noncomputable def sparseExitCompressionRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.sparseExitCompression
    { Requires := [K .tightEndpoint, K .sparseTargetDefectResidual, K .cubicBaseline, K .selection]
      Produces := [K .droppedEdgeTightDeficit, K .notBothReadingsWhole, K .firstWholeOrientation, K .firstWholeDeficitNonempty, K .firstWholeDeficitStructure, K .firstWholeDeficitSum, K .secondWholeOrientation, K .secondWholeDeficitNonempty, K .secondWholeDeficitStructure, K .secondWholeDeficitSum]
      requiresUnique := by key_fresh
      producesUnique := by key_fresh
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .droppedEdgeTightDeficit)
        ⟨Contracts.Spine.SparseExitResidual.droppedEdgeTightDeficit_holds (object := inputs.current.object) (inputs.get (K .tightEndpoint)).down (inputs.get (K .sparseTargetDefectResidual)).down⟩
      (.cons (key := K .notBothReadingsWhole)
        ⟨Contracts.Spine.SparseExitResidual.notBothReadingsWhole_holds (object := inputs.current.object) (inputs.get (K .sparseTargetDefectResidual)).down⟩
      (.cons (key := K .firstWholeOrientation)
        ⟨Contracts.Spine.SparseExitResidual.firstWholeOrientation_holds (object := inputs.current.object) (inputs.get (K .cubicBaseline)).down.1.1 (inputs.get (K .selection)).down.1 (inputs.get (K .sparseTargetDefectResidual)).down⟩
      (.cons (key := K .firstWholeDeficitNonempty)
        ⟨Contracts.Spine.SparseExitResidual.firstWholeDeficitNonempty_holds (object := inputs.current.object) (inputs.get (K .cubicBaseline)).down.1.1 (inputs.get (K .selection)).down.1 (inputs.get (K .sparseTargetDefectResidual)).down⟩
      (.cons (key := K .firstWholeDeficitStructure)
        ⟨Contracts.Spine.SparseExitResidual.firstWholeDeficitStructure_holds (object := inputs.current.object) (inputs.get (K .cubicBaseline)).down.1.1 (inputs.get (K .selection)).down.1 (inputs.get (K .sparseTargetDefectResidual)).down⟩
      (.cons (key := K .firstWholeDeficitSum)
        ⟨Contracts.Spine.SparseExitResidual.firstWholeDeficitSum_holds (object := inputs.current.object) (inputs.get (K .cubicBaseline)).down.1.1 (inputs.get (K .selection)).down.1 (inputs.get (K .sparseTargetDefectResidual)).down⟩
      (.cons (key := K .secondWholeOrientation)
        ⟨Contracts.Spine.SparseExitResidual.secondWholeOrientation_holds (object := inputs.current.object) (inputs.get (K .cubicBaseline)).down.1.1 (inputs.get (K .selection)).down.1 (inputs.get (K .sparseTargetDefectResidual)).down⟩
      (.cons (key := K .secondWholeDeficitNonempty)
        ⟨Contracts.Spine.SparseExitResidual.secondWholeDeficitNonempty_holds (object := inputs.current.object) (inputs.get (K .cubicBaseline)).down.1.1 (inputs.get (K .selection)).down.1 (inputs.get (K .sparseTargetDefectResidual)).down⟩
      (.cons (key := K .secondWholeDeficitStructure)
        ⟨Contracts.Spine.SparseExitResidual.secondWholeDeficitStructure_holds (object := inputs.current.object) (inputs.get (K .cubicBaseline)).down.1.1 (inputs.get (K .selection)).down.1 (inputs.get (K .sparseTargetDefectResidual)).down⟩
      (.cons (key := K .secondWholeDeficitSum)
        ⟨Contracts.Spine.SparseExitResidual.secondWholeDeficitSum_holds (object := inputs.current.object) (inputs.get (K .cubicBaseline)).down.1.1 (inputs.get (K .selection)).down.1 (inputs.get (K .sparseTargetDefectResidual)).down⟩
      .nil))))))))))

/-- Node `[20a]`: deleting the whole-case deficit set, and the keeps-all split. -/
@[reducible] noncomputable def sparseExitDeletionRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.sparseExitDeletion
    { Requires := [K .cubicBaseline, K .selection, K .minDegreeBaseline, K .noProperBaseline, K .tightEndpoint, K .sparseTargetDefectResidual]
      Produces := [K .deletedSupportReduction, K .deletedSupportDeficientVertex, K .deletedSupportDeficitSums, K .deletedSupportEdgeRestoration, K .deletedSupportEdgeSetRestoration, K .firstKeepsAllNotWhole, K .secondKeepsAllNotWhole]
      requiresUnique := by key_fresh
      producesUnique := by key_fresh
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .deletedSupportReduction)
        ⟨Contracts.Spine.SparseExitResidual.deletedSupportReduction_holds (object := inputs.current.object) (inputs.get (K .cubicBaseline)).down.1.1 (inputs.get (K .selection)).down.1 (inputs.get (K .selection)).down.2.sizeMinimal (inputs.get (K .minDegreeBaseline)).down (inputs.get (K .noProperBaseline)).down (inputs.get (K .tightEndpoint)).down (inputs.get (K .sparseTargetDefectResidual)).down⟩
      (.cons (key := K .deletedSupportDeficientVertex)
        ⟨Contracts.Spine.SparseExitResidual.deletedSupportDeficientVertex_holds (object := inputs.current.object) (inputs.get (K .cubicBaseline)).down.1.1 (inputs.get (K .selection)).down.1 (inputs.get (K .selection)).down.2.sizeMinimal (inputs.get (K .minDegreeBaseline)).down (inputs.get (K .noProperBaseline)).down (inputs.get (K .tightEndpoint)).down (inputs.get (K .sparseTargetDefectResidual)).down⟩
      (.cons (key := K .deletedSupportDeficitSums)
        ⟨Contracts.Spine.SparseExitResidual.deletedSupportDeficitSums_holds (object := inputs.current.object) (inputs.get (K .cubicBaseline)).down.1.1 (inputs.get (K .selection)).down.1 (inputs.get (K .selection)).down.2.sizeMinimal (inputs.get (K .minDegreeBaseline)).down (inputs.get (K .noProperBaseline)).down (inputs.get (K .tightEndpoint)).down (inputs.get (K .sparseTargetDefectResidual)).down⟩
      (.cons (key := K .deletedSupportEdgeRestoration)
        ⟨Contracts.Spine.SparseExitResidual.deletedSupportEdgeRestoration_holds (object := inputs.current.object) (inputs.get (K .cubicBaseline)).down.1.1 (inputs.get (K .selection)).down.1 (inputs.get (K .selection)).down.2.sizeMinimal (inputs.get (K .minDegreeBaseline)).down (inputs.get (K .noProperBaseline)).down (inputs.get (K .tightEndpoint)).down (inputs.get (K .sparseTargetDefectResidual)).down⟩
      (.cons (key := K .deletedSupportEdgeSetRestoration)
        ⟨Contracts.Spine.SparseExitResidual.deletedSupportEdgeSetRestoration_holds (object := inputs.current.object) (inputs.get (K .cubicBaseline)).down.1.1 (inputs.get (K .selection)).down.1 (inputs.get (K .selection)).down.2.sizeMinimal (inputs.get (K .minDegreeBaseline)).down (inputs.get (K .noProperBaseline)).down (inputs.get (K .tightEndpoint)).down (inputs.get (K .sparseTargetDefectResidual)).down⟩
      (.cons (key := K .firstKeepsAllNotWhole)
        ⟨Contracts.Spine.SparseExitResidual.firstKeepsAllNotWhole_holds (object := inputs.current.object) (inputs.get (K .selection)).down.1 (inputs.get (K .sparseTargetDefectResidual)).down⟩
      (.cons (key := K .secondKeepsAllNotWhole)
        ⟨Contracts.Spine.SparseExitResidual.secondKeepsAllNotWhole_holds (object := inputs.current.object) (inputs.get (K .selection)).down.1 (inputs.get (K .sparseTargetDefectResidual)).down⟩
      .nil)))))))

/-- Node `[20a]`: the combined facts: the pair arm excluded, `|∂Z| = 2` forcing arm (i), the Steiner support, the whole-case counts, the high-degree range. -/
@[reducible] noncomputable def sparseExitCombinationRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.sparseExitCombination
    { Requires := [K .cubicBaseline, K .minDegreeBaseline, K .tightEndpoint, K .surplusAbove, K .sparseTargetDefectResidual, K .selection]
      Produces := [K .highDegreePositive, K .highDegreeSurplusCapacity, K .pairArmExcluded, K .twoBoundaryForcesArmOne, K .armOneForcedPath, K .twoBoundaryForcedPathCross, K .supportSteinerMinimal, K .steinerVerticesCut, K .wholeSupportEqual, K .wholeDeficitBoundaryCount, K .wholeCutEdgeSurplusBound]
      requiresUnique := by key_fresh
      producesUnique := by key_fresh
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .highDegreePositive)
        ⟨Contracts.Spine.SparseExitResidual.highDegreePositive_holds (object := inputs.current.object) (inputs.get (K .cubicBaseline)).down.1.1 (inputs.get (K .minDegreeBaseline)).down (inputs.get (K .tightEndpoint)).down (inputs.get (K .surplusAbove)).down⟩
      (.cons (key := K .highDegreeSurplusCapacity)
        ⟨Contracts.Spine.SparseExitResidual.highDegreeSurplusCapacity_holds (object := inputs.current.object) (inputs.get (K .cubicBaseline)).down.1.1 (inputs.get (K .minDegreeBaseline)).down (inputs.get (K .tightEndpoint)).down (inputs.get (K .surplusAbove)).down⟩
      (.cons (key := K .pairArmExcluded)
        ⟨Contracts.Spine.SparseExitResidual.pairArmExcluded_holds (object := inputs.current.object) (inputs.get (K .sparseTargetDefectResidual)).down⟩
      (.cons (key := K .twoBoundaryForcesArmOne)
        ⟨Contracts.Spine.SparseExitResidual.twoBoundaryForcesArmOne_holds (object := inputs.current.object) (inputs.get (K .cubicBaseline)).down.2.1.2.1 (inputs.get (K .selection)).down.1 (inputs.get (K .sparseTargetDefectResidual)).down⟩
      (.cons (key := K .armOneForcedPath)
        ⟨Contracts.Spine.SparseExitResidual.armOneForcedPath_holds (object := inputs.current.object) (inputs.get (K .sparseTargetDefectResidual)).down⟩
      (.cons (key := K .twoBoundaryForcedPathCross)
        ⟨Contracts.Spine.SparseExitResidual.twoBoundaryForcedPathCross_holds (object := inputs.current.object) (inputs.get (K .cubicBaseline)).down.1.1 (inputs.get (K .cubicBaseline)).down.2.1.2.1 (inputs.get (K .minDegreeBaseline)).down (inputs.get (K .selection)).down.1 (inputs.get (K .selection)).down.2.sizeMinimal (inputs.get (K .sparseTargetDefectResidual)).down⟩
      (.cons (key := K .supportSteinerMinimal)
        ⟨Contracts.Spine.SparseExitResidual.supportSteinerMinimal_holds (object := inputs.current.object) (inputs.get (K .sparseTargetDefectResidual)).down⟩
      (.cons (key := K .steinerVerticesCut)
        ⟨Contracts.Spine.SparseExitResidual.steinerVerticesCut_holds (object := inputs.current.object) (inputs.get (K .sparseTargetDefectResidual)).down⟩
      (.cons (key := K .wholeSupportEqual)
        ⟨Contracts.Spine.SparseExitResidual.wholeSupportEqual_holds (object := inputs.current.object) (inputs.get (K .sparseTargetDefectResidual)).down⟩
      (.cons (key := K .wholeDeficitBoundaryCount)
        ⟨Contracts.Spine.SparseExitResidual.wholeDeficitBoundaryCount_holds (object := inputs.current.object) (inputs.get (K .selection)).down.1 (inputs.get (K .sparseTargetDefectResidual)).down⟩
      (.cons (key := K .wholeCutEdgeSurplusBound)
        ⟨Contracts.Spine.SparseExitResidual.wholeCutEdgeSurplusBound_holds (object := inputs.current.object) (inputs.get (K .cubicBaseline)).down.1.1 (inputs.get (K .minDegreeBaseline)).down (inputs.get (K .sparseTargetDefectResidual)).down⟩
      .nil)))))))))))

/-- Node `[129]`'s baseline spine demand on the `[20a]` path: its survivor
premise is used only against exits (c) and (d), which the replacement
exclusion and selection refute. -/
@[reducible] noncomputable def sparseExitBaselineSpineDemandRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.sparseExitBaselineSpineDemand
    { Requires := [K .cubicBaseline, K .selection, K .minDegreeBaseline,
        K .replacementExclusion, K .noProperBaseline, K .tightEndpoint, K .surplusAbove]
      Produces := [K .baselineSpineDemand]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .baselineSpineDemand)
        ⟨Contracts.Spine.SparseExitResidual.baselineSpineDemand_of_selection
          (inputs.get (K .cubicBaseline)).down.1.1
          (inputs.get (K .cubicBaseline)).down.2.2.1.1
          (inputs.get (K .selection)).down.1
          (inputs.get (K .selection)).down.2.sizeMinimal
          (inputs.get (K .minDegreeBaseline)).down
          (inputs.get (K .replacementExclusion)).down
          (inputs.get (K .noProperBaseline)).down
          (inputs.get (K .tightEndpoint)).down
          (inputs.get (K .surplusAbove)).down⟩
        .nil)

end Hypostructure.Graph.Strategy.Spine
