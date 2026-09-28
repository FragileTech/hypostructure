import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.Spine.JointHubs
import Hypostructure.Graph.Contracts.Spine.HubLinks
import Hypostructure.Graph.Contracts.Spine.PairArms

/-!
# Hubs, cubic vertices, windows and the remainder of G, each published at the earliest point

Type A rows over `Graph/Contracts/Spine/JointHubs.lean`.  Each row reads its prerequisites
through `inputs.get` and publishes facts of G; no row decides or splits anything.
- entry prefix, right after the canonical packing `P₀`'s rigidity row (reads
  `K .selection`, `K .cubicBaseline`, `K .minDegreeBaseline`): paths inside the remainder,
  the window-free geometry and the attachments to induced `P13`s;
- entry prefix, right after `[8]` (reads `K .cubicBaseline`, `K .minDegreeBaseline`,
  `K .noProperBaseline`, `K .bridgeless`): density in excess form and the remainder slack;
- entry prefix, right after `[9]`/`[10]` (reads also `K .selection`,
  `K .slackIndependent`): the cubic/hub facts and the hub–window facts;
- the top of the strict arm of `[19]`, right after the budget row (reads
  `K .highSurplusBound`, `K .bigHubBound`, `K .surplusAbove`, `K .ceilSqrtAboveScale`):
  the orders the high-surplus closure excludes;
- the top of the strict arm of `[19]`, right after G's canonical capacity presentation
  (reads `K .canonicalCapacityExplicit`, `K .selection`, `K .replacementExclusion`): the
  window structure of the canonical charge and the target-response obstructions.
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-- Entry prefix, right after the rigidity of `P₀`: paths and cycles inside the remainder,
the window-free geometry of `P₀`, and the attachments to the induced `P13`s of G. -/
@[reducible] noncomputable def remainderGeometryRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.remainderGeometry
    { Requires := [K .selection, K .cubicBaseline, K .minDegreeBaseline]
      Produces := [K .remainderPathBounds, K .windowFreeGeometry, K .inducedPathAttachment]
      requiresUnique := by key_fresh
      producesUnique := by key_fresh
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .remainderPathBounds)
        ⟨Contracts.Spine.JointHubs.remainderPathBounds_holds (object := inputs.current.object)
          (inputs.get (K .cubicBaseline)).down.1.1
          (inputs.get (K .cubicBaseline)).down.1.2.2.2.2.2
          (inputs.get (K .selection)).down.1 (inputs.get (K .cubicBaseline)).down.2.1.2.1
          (inputs.get (K .minDegreeBaseline)).down⟩
      (.cons (key := K .windowFreeGeometry)
        ⟨Contracts.Spine.JointHubs.windowFreeGeometry_holds (object := inputs.current.object)
          (inputs.get (K .cubicBaseline)).down.1.1
          (inputs.get (K .cubicBaseline)).down.1.2.2.2.2.2
          (inputs.get (K .selection)).down.1 (inputs.get (K .cubicBaseline)).down.2.1.2.1
          (inputs.get (K .minDegreeBaseline)).down⟩
      (.cons (key := K .inducedPathAttachment)
        ⟨Contracts.Spine.JointHubs.inducedPathAttachment_holds (object := inputs.current.object)
          (inputs.get (K .cubicBaseline)).down.1.1
          (inputs.get (K .selection)).down.1 (inputs.get (K .cubicBaseline)).down.2.1.2.1
          (inputs.get (K .minDegreeBaseline)).down⟩
      .nil)))

/-- Entry prefix, right after `[8]`: density of G in excess form, and the remainder slack
of `P₀` with its hanging windows. -/
@[reducible] noncomputable def densitySlackRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.densitySlack
    { Requires := [K .cubicBaseline, K .minDegreeBaseline, K .noProperBaseline, K .bridgeless]
      Produces := [K .densityExcess, K .remainderSlack]
      requiresUnique := by key_fresh
      producesUnique := by key_fresh
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .densityExcess)
        ⟨Contracts.Spine.JointHubs.densityExcess_holds (object := inputs.current.object)
          (inputs.get (K .cubicBaseline)).down.1.1 (inputs.get (K .noProperBaseline)).down
          (inputs.get (K .bridgeless)).down⟩
      (.cons (key := K .remainderSlack)
        ⟨Contracts.Spine.JointHubs.remainderSlack_holds (object := inputs.current.object)
          (inputs.get (K .cubicBaseline)).down.1.1
          (inputs.get (K .cubicBaseline)).down.1.2.2.2.2.2
          (inputs.get (K .minDegreeBaseline)).down (inputs.get (K .noProperBaseline)).down⟩
      .nil))

/-- Entry prefix, right after `[9]`/`[10]`: the cubic vertices and hubs of G —
cubic neighbours, `5|H| + σ ≤ 2n`, the `L–L` parity, hub domination and `2|B| + σ ≤ n`,
the V-shape caps, the high-surplus bound, and the length-3 pairs at the hubs. -/
@[reducible] noncomputable def jointHubRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.jointHub
    { Requires := [K .selection, K .cubicBaseline, K .minDegreeBaseline, K .noProperBaseline,
        K .slackIndependent]
      Produces := [K .cubicNeighbourSupply, K .hubCountBound, K .lowEdgeParity, K .bigHubBound,
        K .bigHubVShapes, K .highSurplusBound, K .hubLengthThreePairs]
      requiresUnique := by key_fresh
      producesUnique := by key_fresh
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .cubicNeighbourSupply)
        ⟨Contracts.Spine.JointHubs.cubicNeighbourSupply_holds (object := inputs.current.object)
          (inputs.get (K .cubicBaseline)).down.1.1 (inputs.get (K .minDegreeBaseline)).down
          (inputs.get (K .noProperBaseline)).down⟩
      (.cons (key := K .hubCountBound)
        ⟨Contracts.Spine.JointHubs.hubCountBound_holds (object := inputs.current.object)
          (inputs.get (K .cubicBaseline)).down.1.1 (inputs.get (K .minDegreeBaseline)).down
          (inputs.get (K .noProperBaseline)).down (inputs.get (K .slackIndependent)).down⟩
      (.cons (key := K .lowEdgeParity)
        ⟨Contracts.Spine.JointHubs.lowEdgeParity_holds (object := inputs.current.object)
          (inputs.get (K .cubicBaseline)).down.1.1 (inputs.get (K .minDegreeBaseline)).down
          (inputs.get (K .slackIndependent)).down⟩
      (.cons (key := K .bigHubBound)
        ⟨Contracts.Spine.JointHubs.bigHubBound_holds (object := inputs.current.object)
          (inputs.get (K .cubicBaseline)).down.1.1 (inputs.get (K .minDegreeBaseline)).down
          (inputs.get (K .noProperBaseline)).down (inputs.get (K .slackIndependent)).down⟩
      (.cons (key := K .bigHubVShapes)
        ⟨Contracts.Spine.JointHubs.bigHubVShapes_holds (object := inputs.current.object)
          (inputs.get (K .cubicBaseline)).down.1.1
          (inputs.get (K .selection)).down.1 (inputs.get (K .cubicBaseline)).down.2.1.2.1
          (inputs.get (K .minDegreeBaseline)).down (inputs.get (K .slackIndependent)).down⟩
      (.cons (key := K .highSurplusBound)
        ⟨Contracts.Spine.JointHubs.highSurplusBound_holds (object := inputs.current.object)
          (inputs.get (K .cubicBaseline)).down.1.1
          (inputs.get (K .selection)).down.1 (inputs.get (K .cubicBaseline)).down.2.1.2.1
          (inputs.get (K .minDegreeBaseline)).down (inputs.get (K .noProperBaseline)).down
          (inputs.get (K .slackIndependent)).down⟩
      (.cons (key := K .hubLengthThreePairs)
        ⟨Contracts.Spine.JointHubs.hubLengthThreePairs_holds (object := inputs.current.object)
          (inputs.get (K .cubicBaseline)).down.1.1
          (inputs.get (K .selection)).down.1 (inputs.get (K .cubicBaseline)).down.2.1.2.1
          (inputs.get (K .minDegreeBaseline)).down (inputs.get (K .slackIndependent)).down⟩
      .nil)))))))

/-- Entry prefix, right after the cubic/hub facts: the hub–window budget at `P₀` and the
windows of `P₀` against the big hubs. -/
@[reducible] noncomputable def hubWindowRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.hubWindow
    { Requires := [K .selection, K .cubicBaseline, K .minDegreeBaseline, K .noProperBaseline,
        K .slackIndependent]
      Produces := [K .hubWindowBudget, K .windowHubBounds]
      requiresUnique := by key_fresh
      producesUnique := by key_fresh
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .hubWindowBudget)
        ⟨Contracts.Spine.JointHubs.hubWindowBudget_holds (object := inputs.current.object)
          (inputs.get (K .cubicBaseline)).down.1.1
          (inputs.get (K .cubicBaseline)).down.1.2.2.2.2.2
          (inputs.get (K .minDegreeBaseline)).down (inputs.get (K .noProperBaseline)).down
          (inputs.get (K .slackIndependent)).down⟩
      (.cons (key := K .windowHubBounds)
        ⟨Contracts.Spine.JointHubs.windowHubBounds_holds (object := inputs.current.object)
          (inputs.get (K .cubicBaseline)).down.1.1
          (inputs.get (K .cubicBaseline)).down.1.2.2.2.2.2
          (inputs.get (K .selection)).down.1 (inputs.get (K .cubicBaseline)).down.2.1.2.1
          (inputs.get (K .minDegreeBaseline)).down (inputs.get (K .noProperBaseline)).down
          (inputs.get (K .slackIndependent)).down⟩
      .nil))

/-- Top of the strict arm of `[19]`, right after the budget row: the orders the
high-surplus closure excludes. -/
@[reducible] noncomputable def highSurplusOrderRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.highSurplusOrder
    { Requires := [K .cubicBaseline, K .highSurplusBound, K .bigHubBound, K .surplusAbove,
        K .ceilSqrtAboveScale]
      Produces := [K .highSurplusOrder]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .highSurplusOrder)
        ⟨Contracts.Spine.JointHubs.highSurplusOrder_holds (object := inputs.current.object)
          (inputs.get (K .cubicBaseline)).down.1.1 (inputs.get (K .highSurplusBound)).down
          (inputs.get (K .bigHubBound)).down (inputs.get (K .surplusAbove)).down
          (inputs.get (K .ceilSqrtAboveScale)).down⟩
      .nil)

/-- Top of the strict arm of `[19]`, right after G's canonical capacity presentation: the
window structure of the canonical charge, the recorded activation, and the target-response
obstructions. -/
@[reducible] noncomputable def windowChargeRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.windowCharge
    { Requires := [K .selection, K .replacementExclusion, K .canonicalCapacityExplicit]
      Produces := [K .windowChargeKinds, K .responseObstructionTargetDefect]
      requiresUnique := by key_fresh
      producesUnique := by key_fresh
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .windowChargeKinds)
        ⟨Contracts.Spine.JointHubs.windowChargeKinds_holds (object := inputs.current.object)
          (inputs.get (K .canonicalCapacityExplicit)).down⟩
      (.cons (key := K .responseObstructionTargetDefect)
        ⟨Contracts.Spine.JointHubs.responseObstructionTargetDefect_holds
          (object := inputs.current.object)
          (inputs.get (K .canonicalCapacityExplicit)).down (inputs.get (K .selection)).down.2
          (inputs.get (K .replacementExclusion)).down⟩
      .nil))

/-- Entry prefix, right after the hub–window facts: the links between the hubs of `R` (chains,
rainbow paths, degeneracy, two-hop links, closed classes), the hub classes of the cubic
vertices, and the slot relations. -/
@[reducible] noncomputable def hubLinkRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.hubLink
    { Requires := [K .selection, K .cubicBaseline, K .minDegreeBaseline, K .noProperBaseline,
        K .slackIndependent]
      Produces := [K .hubLinkStructure, K .hubClassCounts, K .slotRelation, K .closedClasses,
        K .hubTwoHopLinks, K .slotLinear]
      requiresUnique := by key_fresh
      producesUnique := by key_fresh
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .hubLinkStructure)
        ⟨Contracts.Spine.HubLinks.hubLinkStructure_holds (object := inputs.current.object) (inputs.get (K .cubicBaseline)).down.1.1 (inputs.get (K .cubicBaseline)).down.1.2.2.2.2.2 (inputs.get (K .minDegreeBaseline)).down (inputs.get (K .slackIndependent)).down⟩
      (.cons (key := K .hubClassCounts)
        ⟨Contracts.Spine.HubLinks.hubClassCounts_holds (object := inputs.current.object) (inputs.get (K .cubicBaseline)).down.1.1 (inputs.get (K .selection)).down.1 (inputs.get (K .cubicBaseline)).down.2.1.2.1 (inputs.get (K .minDegreeBaseline)).down (inputs.get (K .noProperBaseline)).down (inputs.get (K .slackIndependent)).down⟩
      (.cons (key := K .slotRelation)
        ⟨Contracts.Spine.HubLinks.slotRelation_holds (object := inputs.current.object) (inputs.get (K .cubicBaseline)).down.1.1 (inputs.get (K .selection)).down.1 (inputs.get (K .cubicBaseline)).down.2.1.2.1 (inputs.get (K .minDegreeBaseline)).down (inputs.get (K .noProperBaseline)).down (inputs.get (K .slackIndependent)).down⟩
      (.cons (key := K .closedClasses)
        ⟨Contracts.Spine.HubLinks.closedClasses_holds (object := inputs.current.object) (inputs.get (K .cubicBaseline)).down.1.1 (inputs.get (K .cubicBaseline)).down.1.2.2.2.2.2 (inputs.get (K .minDegreeBaseline)).down (inputs.get (K .noProperBaseline)).down (inputs.get (K .slackIndependent)).down⟩
      (.cons (key := K .hubTwoHopLinks)
        ⟨Contracts.Spine.HubLinks.hubTwoHopLinks_holds (object := inputs.current.object) (inputs.get (K .cubicBaseline)).down.1.1 (inputs.get (K .cubicBaseline)).down.1.2.2.2.2.2 (inputs.get (K .minDegreeBaseline)).down (inputs.get (K .slackIndependent)).down⟩
      (.cons (key := K .slotLinear)
        ⟨Contracts.Spine.HubLinks.slotLinear_holds (object := inputs.current.object) (inputs.get (K .cubicBaseline)).down.1.1 (inputs.get (K .cubicBaseline)).down.1.2.2.2.2.2 (inputs.get (K .selection)).down.1 (inputs.get (K .cubicBaseline)).down.2.1.2.1 (inputs.get (K .minDegreeBaseline)).down (inputs.get (K .noProperBaseline)).down (inputs.get (K .slackIndependent)).down⟩
      .nil))))))

/-- Top of the strict arm of `[19]`, right after the high-surplus orders: the scale pressure. -/
@[reducible] noncomputable def scalePressureRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.scalePressure
    { Requires := [K .selection, K .cubicBaseline, K .minDegreeBaseline, K .noProperBaseline,
        K .slackIndependent, K .surplusAbove]
      Produces := [K .scalePressure]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .scalePressure)
        ⟨Contracts.Spine.HubLinks.scalePressure_holds (object := inputs.current.object) (inputs.get (K .cubicBaseline)).down.1.1 (inputs.get (K .cubicBaseline)).down.1.2.2.2.2.2 (inputs.get (K .selection)).down.1 (inputs.get (K .cubicBaseline)).down.2.1.2.1 (inputs.get (K .minDegreeBaseline)).down (inputs.get (K .noProperBaseline)).down (inputs.get (K .slackIndependent)).down
          (inputs.get (K .surplusAbove)).down⟩
      .nil)

/-- Top of the strict arm of `[19]`, right after the window charge facts: the structure of
the free side of G's canonical capacity charge, and the separated pairs. -/
@[reducible] noncomputable def freeSideStructureRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.freeSideStructure
    { Requires := [K .selection, K .minDegreeBaseline, K .canonicalCapacityExplicit]
      Produces := [K .freeSideStructure, K .separatedPairs]
      requiresUnique := by key_fresh
      producesUnique := by key_fresh
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .freeSideStructure)
        ⟨Contracts.Spine.HubLinks.freeSideStructure_holds (object := inputs.current.object)
          (inputs.get (K .selection)).down.2 (inputs.get (K .minDegreeBaseline)).down (inputs.get (K .canonicalCapacityExplicit)).down⟩
      (.cons (key := K .separatedPairs)
        ⟨Contracts.Spine.HubLinks.separatedPairs_holds (object := inputs.current.object)
          (inputs.get (K .canonicalCapacityExplicit)).down⟩
      .nil))

/-- Top of the strict arm of `[19]`, right after the canonical capacity counts: the free-side
count, G2 with it, and the capped-arm consequences. -/
@[reducible] noncomputable def freeSideCountRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.freeSideCount
    { Requires := [K .cubicBaseline, K .freeSideStructure, K .canonicalLedgerDeficit,
        K .canonicalFreeExcessOfCapped]
      Produces := [K .freeSideCount]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .freeSideCount)
        ⟨Contracts.Spine.HubLinks.freeSideCount_holds (object := inputs.current.object) (inputs.get (K .cubicBaseline)).down.1.1
          (inputs.get (K .freeSideStructure)).down (inputs.get (K .canonicalLedgerDeficit)).down
          (inputs.get (K .canonicalFreeExcessOfCapped)).down⟩
      .nil)

/-- Top of the strict arm of `[19]`, right after the free-side count: the free side against
the hubs. -/
@[reducible] noncomputable def freeSideHubsRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.freeSideHubs
    { Requires := [K .cubicBaseline, K .selection, K .slackIndependent, K .freeSideCount]
      Produces := [K .freeSideHubs]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .freeSideHubs)
        ⟨Contracts.Spine.HubLinks.freeSideHubs_holds (object := inputs.current.object) (inputs.get (K .cubicBaseline)).down.1.1 (inputs.get (K .cubicBaseline)).down.2.1.1
          (inputs.get (K .selection)).down.1 (inputs.get (K .slackIndependent)).down
          (inputs.get (K .freeSideCount)).down⟩
      .nil)

/-- Top of the strict arm of `[19]`, right after the free side against the hubs: the extended
charge `Θ_ext` at G's canonical capacity presentation. -/
@[reducible] noncomputable def extendedChargeRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.extendedCharge
    { Requires := [K .cubicBaseline, K .selection, K .minDegreeBaseline, K .slackIndependent,
        K .canonicalCapacityExplicit, K .pairCountDeficit, K .canonicalBlockedFreePartition,
        K .ceilSqrtAboveScale]
      Produces := [K .extFreeEmpty, K .extLoadSum, K .extOverload, K .extOverloadedToken,
        K .newLoadBound]
      requiresUnique := by key_fresh
      producesUnique := by key_fresh
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .extFreeEmpty)
        ⟨Contracts.Spine.HubLinks.extFreeEmpty_holds (object := inputs.current.object) (inputs.get (K .cubicBaseline)).down.1.1 (inputs.get (K .cubicBaseline)).down.2.1.1
          (inputs.get (K .selection)).down.2 (inputs.get (K .minDegreeBaseline)).down
          (inputs.get (K .slackIndependent)).down (inputs.get (K .canonicalCapacityExplicit)).down
          (inputs.get (K .pairCountDeficit)).down (inputs.get (K .canonicalBlockedFreePartition)).down
          (inputs.get (K .ceilSqrtAboveScale)).down⟩
      (.cons (key := K .extLoadSum)
        ⟨Contracts.Spine.HubLinks.extLoadSum_holds (object := inputs.current.object) (inputs.get (K .cubicBaseline)).down.1.1 (inputs.get (K .cubicBaseline)).down.2.1.1
          (inputs.get (K .selection)).down.2 (inputs.get (K .minDegreeBaseline)).down
          (inputs.get (K .slackIndependent)).down (inputs.get (K .canonicalCapacityExplicit)).down
          (inputs.get (K .pairCountDeficit)).down (inputs.get (K .canonicalBlockedFreePartition)).down
          (inputs.get (K .ceilSqrtAboveScale)).down⟩
      (.cons (key := K .extOverload)
        ⟨Contracts.Spine.HubLinks.extOverload_holds (object := inputs.current.object) (inputs.get (K .cubicBaseline)).down.1.1 (inputs.get (K .cubicBaseline)).down.2.1.1
          (inputs.get (K .selection)).down.2 (inputs.get (K .minDegreeBaseline)).down
          (inputs.get (K .slackIndependent)).down (inputs.get (K .canonicalCapacityExplicit)).down
          (inputs.get (K .pairCountDeficit)).down (inputs.get (K .canonicalBlockedFreePartition)).down
          (inputs.get (K .ceilSqrtAboveScale)).down⟩
      (.cons (key := K .extOverloadedToken)
        ⟨Contracts.Spine.HubLinks.extOverloadedToken_holds (object := inputs.current.object) (inputs.get (K .cubicBaseline)).down.1.1 (inputs.get (K .cubicBaseline)).down.2.1.1
          (inputs.get (K .selection)).down.2 (inputs.get (K .minDegreeBaseline)).down
          (inputs.get (K .slackIndependent)).down (inputs.get (K .canonicalCapacityExplicit)).down
          (inputs.get (K .pairCountDeficit)).down (inputs.get (K .canonicalBlockedFreePartition)).down
          (inputs.get (K .ceilSqrtAboveScale)).down⟩
      (.cons (key := K .newLoadBound)
        ⟨Contracts.Spine.HubLinks.newLoadBound_holds (object := inputs.current.object) (inputs.get (K .cubicBaseline)).down.1.1 (inputs.get (K .cubicBaseline)).down.2.1.1
          (inputs.get (K .selection)).down.2 (inputs.get (K .minDegreeBaseline)).down
          (inputs.get (K .slackIndependent)).down (inputs.get (K .canonicalCapacityExplicit)).down
          (inputs.get (K .pairCountDeficit)).down (inputs.get (K .canonicalBlockedFreePartition)).down
          (inputs.get (K .ceilSqrtAboveScale)).down⟩
      .nil)))))

/-- Entry prefix, right after the hub links: every selected port endpoint has degree `δ`. -/
@[reducible] noncomputable def portEndDegreeRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.portEndDegree
    { Requires := [K .minDegreeBaseline, K .slackIndependent]
      Produces := [K .portEndDegree]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .portEndDegree)
        ⟨Contracts.Spine.PairArms.portEndDegree_holds (object := inputs.current.object)
          (inputs.get (K .minDegreeBaseline)).down (inputs.get (K .slackIndependent)).down⟩
      .nil)

/-- Top of the strict arm of `[19]`, right after the free-side structure: arm A of the pair
code as implications. -/
@[reducible] noncomputable def pairArmARow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.pairArmA
    { Requires := [K .canonicalCapacityExplicit]
      Produces := [K .pairArmAPattern, K .pairArmARoleAlphabet]
      requiresUnique := by simp
      producesUnique := by key_fresh
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .pairArmAPattern)
        ⟨Contracts.Spine.PairArms.pairArmAPattern_holds (object := inputs.current.object)
          (inputs.get (K .canonicalCapacityExplicit)).down⟩
      (.cons (key := K .pairArmARoleAlphabet)
        ⟨Contracts.Spine.PairArms.pairArmARoleAlphabet_holds (object := inputs.current.object)
          (Contracts.Spine.PairArms.pairArmAPattern_holds (object := inputs.current.object)
            (inputs.get (K .canonicalCapacityExplicit)).down)⟩
      .nil))

/-- Top of the strict arm of `[19]`, right after the high-endpoint switch: arm B of the pair
code as implications. -/
@[reducible] noncomputable def pairArmBRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.pairArmB
    { Requires := [K .cubicBaseline, K .selection, K .minDegreeBaseline, K .noProperBaseline,
        K .slackIndependent, K .surplusAbove, K .highEndpointSwitch]
      Produces := [K .pairArmB]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .pairArmB)
        ⟨Contracts.Spine.PairArms.pairArmB_holds (object := inputs.current.object)
          (inputs.get (K .cubicBaseline)).down.1.1 (inputs.get (K .selection)).down.1
          (inputs.get (K .minDegreeBaseline)).down (inputs.get (K .noProperBaseline)).down
          (inputs.get (K .slackIndependent)).down (inputs.get (K .surplusAbove)).down
          (inputs.get (K .highEndpointSwitch)).down⟩
      .nil)

/-- Node `[20a]`, after the witness rows: arm B, (B2) at the pinned witness. -/
@[reducible] noncomputable def pairArmBDefectRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.pairArmBDefect
    { Requires := [K .cubicBaseline, K .selection, K .minDegreeBaseline, K .noProperBaseline,
        K .tightEndpoint, K .returnAvoidance, K .highEndpointSwitch,
        K .sparseTargetDefectResidual, K .specWitnessStructure]
      Produces := [K .pairArmBDefect]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .pairArmBDefect)
        ⟨Contracts.Spine.PairArms.pairArmBDefect_holds (object := inputs.current.object)
          (inputs.get (K .cubicBaseline)).down.1.1 (inputs.get (K .selection)).down.1
          (inputs.get (K .cubicBaseline)).down.2.1.2.1
          (inputs.get (K .minDegreeBaseline)).down (inputs.get (K .noProperBaseline)).down
          (inputs.get (K .tightEndpoint)).down (inputs.get (K .returnAvoidance)).down
          (inputs.get (K .highEndpointSwitch)).down
          (inputs.get (K .sparseTargetDefectResidual)).down
          (inputs.get (K .specWitnessStructure)).down⟩
      .nil)

end Hypostructure.Graph.Strategy.Spine
