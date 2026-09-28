import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.Spine.SparseExitReadings

/-!
# The readings of `[20a]`'s canonical witness and the edge switches of G

Type A rows.  Each reads its prerequisites through `inputs.get` and publishes,
at G, one fact per key (contracts: `Graph/Contracts/Spine/SparseExitReadings.lean`).
No row decides or splits anything.  A row runs right after the last producer
of the keys it reads, on the shared prefix, so every branch below inherits its
facts:
- the entry prefix (`Assembly/Entry.lean`): the spectrum split at every
  clause-(b) witness (after `[4]`);
- the top of the strict arm of `[19]` (`Assembly/Final.lean`, before `[20]`):
  where the surplus sits and the switch at every high/baseline edge;
- the `[20a]` exit arm: the facts at the canonical witness.
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-- Entry prefix, right after `[4]`'s selection: the path-spectrum split at every
clause-(b) witness of G. -/
@[reducible] noncomputable def everyWitnessSpectrumRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.everyWitnessSpectrum
    { Requires := [K .selection]
      Produces := [K .everyWitnessSpectrumSplit]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .everyWitnessSpectrumSplit)
        ⟨Contracts.Spine.SparseExitReadings.everyWitnessSpectrumSplit_holds
          (object := inputs.current.object) (inputs.get (K .selection)).down.1⟩
      .nil)

/-- Top of the strict arm of `[19]` (after `C + 1 ≤ ⌈√n⌉` is published): where the
surplus of G sits. -/
@[reducible] noncomputable def highSurplusConfigurationRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.highSurplusConfiguration
    { Requires := [K .cubicBaseline, K .minDegreeBaseline, K .surplusAbove,
        K .ceilSqrtAboveScale]
      Produces := [K .highSurplusConfiguration]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .highSurplusConfiguration)
        ⟨Contracts.Spine.SparseExitReadings.highSurplusConfiguration_holds
          (object := inputs.current.object)
          (inputs.get (K .cubicBaseline)).down.1.1
          (inputs.get (K .minDegreeBaseline)).down
          (inputs.get (K .cubicBaseline)).down.2.2.1.2.2.2
          (inputs.get (K .surplusAbove)).down
          (inputs.get (K .ceilSqrtAboveScale)).down⟩
      .nil)

/-- Top of the strict arm of `[19]`: the switch at every high/baseline edge. -/
@[reducible] noncomputable def highEndpointSwitchRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.highEndpointSwitch
    { Requires := [K .slackIndependent, K .twoSwitchForcedPath, K .sameVertexSwitchForcedPath,
        K .highSurplusConfiguration]
      Produces := [K .highEndpointSwitch]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .highEndpointSwitch)
        ⟨Contracts.Spine.SparseExitReadings.highEndpointSwitch_holds
          (object := inputs.current.object)
          (inputs.get (K .slackIndependent)).down
          (inputs.get (K .twoSwitchForcedPath)).down
          (inputs.get (K .sameVertexSwitchForcedPath)).down
          (inputs.get (K .highSurplusConfiguration)).down⟩
      .nil)

/-- Node `[20a]` (and `[187]`): the readings at the canonical witness: counts, active labels, the partition of `∂Z`, private edges, the whole case, arm (i) refined, and the single-edge contexts. -/
@[reducible] noncomputable def sparseExitReadingsRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.sparseExitReadings
    { Requires := [K .cubicBaseline, K .selection, K .returnAvoidance, K .sparseTargetDefectResidual]
      Produces := [K .witnessReadingCounts, K .witnessActiveLabels, K .boundaryPartition, K .positiveCyclePrivateEdge, K .wholeCycleMeetsDeficit, K .wholePrivateEdges, K .spectrumArmOneRefined, K .separatingEdgeContextWitness]
      requiresUnique := by key_fresh
      producesUnique := by key_fresh
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .witnessReadingCounts)
        ⟨Contracts.Spine.SparseExitReadings.witnessReadingCounts_holds
          (object := inputs.current.object)
          (inputs.get (K .sparseTargetDefectResidual)).down⟩
      (.cons (key := K .witnessActiveLabels)
        ⟨Contracts.Spine.SparseExitReadings.witnessActiveLabels_holds
          (object := inputs.current.object)
          (inputs.get (K .sparseTargetDefectResidual)).down
          (inputs.get (K .selection)).down.1⟩
      (.cons (key := K .boundaryPartition)
        ⟨Contracts.Spine.SparseExitReadings.boundaryPartition_holds
          (object := inputs.current.object)
          (inputs.get (K .sparseTargetDefectResidual)).down⟩
      (.cons (key := K .positiveCyclePrivateEdge)
        ⟨Contracts.Spine.SparseExitReadings.positiveCyclePrivateEdge_holds
          (object := inputs.current.object)
          (inputs.get (K .sparseTargetDefectResidual)).down
          (inputs.get (K .selection)).down.1⟩
      (.cons (key := K .wholeCycleMeetsDeficit)
        ⟨Contracts.Spine.SparseExitReadings.wholeCycleMeetsDeficit_holds
          (object := inputs.current.object)
          (inputs.get (K .sparseTargetDefectResidual)).down
          (inputs.get (K .selection)).down.1⟩
      (.cons (key := K .wholePrivateEdges)
        ⟨Contracts.Spine.SparseExitReadings.wholePrivateEdges_holds
          (object := inputs.current.object)
          (inputs.get (K .sparseTargetDefectResidual)).down
          (inputs.get (K .cubicBaseline)).down.1.1
          (inputs.get (K .selection)).down.1⟩
      (.cons (key := K .spectrumArmOneRefined)
        ⟨Contracts.Spine.SparseExitReadings.spectrumArmOneRefined_holds
          (object := inputs.current.object)
          (inputs.get (K .sparseTargetDefectResidual)).down
          (inputs.get (K .cubicBaseline)).down.2.1.2.1
          (inputs.get (K .selection)).down.1
          (inputs.get (K .returnAvoidance)).down⟩
      (.cons (key := K .separatingEdgeContextWitness)
        ⟨Contracts.Spine.SparseExitReadings.separatingEdgeContextWitness_holds
          (object := inputs.current.object)
          (inputs.get (K .sparseTargetDefectResidual)).down
          (inputs.get (K .selection)).down.1
          (inputs.get (K .returnAvoidance)).down⟩
      .nil))))))))

/-- Node `[20a]` (and `[187]`): `|∂Z| = 2` all active, the swap object, the outside returns of baseline labels, the two-boundary outside paths, and the spectrum at a separating single-edge context. -/
@[reducible] noncomputable def sparseExitReadingsConsequencesRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.sparseExitReadingsConsequences
    { Requires := [K .cubicBaseline, K .selection, K .minDegreeBaseline, K .noProperBaseline, K .tightEndpoint, K .bridgeless, K .returnAvoidance, K .everyWitnessSpectrumSplit, K .sparseTargetDefectResidual]
      Produces := [K .twoBoundaryAllActive, K .privateEdgeSwap, K .cubicLabelOutsidePath, K .separatingEdgeContextSpectrum, K .twoBoundaryOutsideBoth]
      requiresUnique := by key_fresh
      producesUnique := by key_fresh
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .twoBoundaryAllActive)
        ⟨Contracts.Spine.SparseExitReadings.twoBoundaryAllActive_holds
          (object := inputs.current.object)
          (inputs.get (K .sparseTargetDefectResidual)).down
          (inputs.get (K .selection)).down.1⟩
      (.cons (key := K .privateEdgeSwap)
        ⟨Contracts.Spine.SparseExitReadings.privateEdgeSwap_holds
          (object := inputs.current.object)
          (inputs.get (K .sparseTargetDefectResidual)).down
          (inputs.get (K .tightEndpoint)).down
          (inputs.get (K .selection)).down.1⟩
      (.cons (key := K .cubicLabelOutsidePath)
        ⟨Contracts.Spine.SparseExitReadings.cubicLabelOutsidePath_holds
          (object := inputs.current.object)
          (inputs.get (K .sparseTargetDefectResidual)).down
          (inputs.get (K .cubicBaseline)).down.1.1
          (inputs.get (K .minDegreeBaseline)).down
          (inputs.get (K .noProperBaseline)).down
          (inputs.get (K .bridgeless)).down
          (inputs.get (K .selection)).down.1⟩
      (.cons (key := K .separatingEdgeContextSpectrum)
        ⟨Contracts.Spine.SparseExitReadings.separatingEdgeContextSpectrum_holds
          (object := inputs.current.object)
          (inputs.get (K .sparseTargetDefectResidual)).down
          (inputs.get (K .selection)).down.1
          (inputs.get (K .returnAvoidance)).down
          (inputs.get (K .everyWitnessSpectrumSplit)).down⟩
      (.cons (key := K .twoBoundaryOutsideBoth)
        ⟨Contracts.Spine.SparseExitReadings.twoBoundaryOutsideBoth_holds
          (object := inputs.current.object)
          (inputs.get (K .sparseTargetDefectResidual)).down
          (inputs.get (K .cubicBaseline)).down.1.1
          (inputs.get (K .minDegreeBaseline)).down
          (inputs.get (K .noProperBaseline)).down
          (inputs.get (K .bridgeless)).down
          (inputs.get (K .selection)).down.1⟩
      .nil)))))

/-- Node `[20a]` (strict arm only: it reads the switch at every high/baseline edge): the switch at the private edge. -/
@[reducible] noncomputable def sparseExitPrivateSwitchRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.sparseExitPrivateSwitch
    { Requires := [K .selection, K .minDegreeBaseline, K .tightEndpoint, K .highEndpointSwitch, K .sparseTargetDefectResidual]
      Produces := [K .privateEdgeSwitch]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .privateEdgeSwitch)
        ⟨Contracts.Spine.SparseExitReadings.privateEdgeSwitch_holds
          (object := inputs.current.object)
          (inputs.get (K .sparseTargetDefectResidual)).down
          (inputs.get (K .minDegreeBaseline)).down
          (inputs.get (K .tightEndpoint)).down
          (inputs.get (K .highEndpointSwitch)).down
          (inputs.get (K .selection)).down.1⟩
      .nil)

end Hypostructure.Graph.Strategy.Spine
