import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.Spine.SparseExitResidual

/-!
# The strict-surplus facts of `[20]` at G, each published at the earliest point of the DAG

Type A rows of the strict-surplus arm.  Each row reads its
prerequisites through `inputs.get` and publishes, at G, the bounds, ratios,
identities and obstructions that those facts force (contracts:
`Graph/Contracts/Spine/SparseExitResidual.lean`).  No row decides or splits
anything.  A row runs right after the last producer of the keys it reads, on
the shared prefix, so every branch below inherits its facts:
- the entry prefix (`Assembly/Entry.lean`), for rows reading only entry facts;
- the top of the strict arm of `[19]` (`Assembly/Final.lean`, before `[20]`),
  for rows reading `K .surplusAbove`;
- `sparseExitFreePairCountRow` at the top of the dependent arm of `[130]`
  (`Assembly/Surplus/Strict/Dependent.lean`); on the independent arm the key
  comes from `[131]`'s decision, so no ledger publishes it twice.

G survives the named sparse exits of `[125]`, the two cycle conclusions in G
(`sparseSurplusSurvivorRow`).
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-- Entry prefix, right after `[4]`'s selection: facts of G that read only `K .selection` (or nothing): the packing ratio, no suppression chord violation, and the witness triples of clause (b) (canonical support structure; no witness of G).  Every branch below `[4]` carries them. -/
@[reducible] noncomputable def entrySelectionFactsRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.entrySelectionFacts
    { Requires := [K .selection]
      Produces := [K .packingOrderBound, K .noSuppressionChordViolation, K .specWitnessStructure]
      requiresUnique := by simp
      producesUnique := by key_fresh
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .packingOrderBound)
        ⟨Contracts.Spine.SparseExitResidual.packingOrderBound_holds (object := inputs.current.object) ⟩
      (.cons (key := K .noSuppressionChordViolation)
        ⟨Contracts.Spine.SparseExitResidual.noSuppressionChordViolation_holds (object := inputs.current.object) (inputs.get (K .selection)).down.1⟩
      (.cons (key := K .specWitnessStructure)
        ⟨Contracts.Spine.SparseExitResidual.specWitnessStructure_holds (object := inputs.current.object) (inputs.get (K .selection)).down.1⟩
      .nil)))

/-- Entry prefix, after `[1]`--`[3]`'s baseline: the canonical packing `P₀`: `def⁺(R) ≤ e(R, W)` and the window cut capacity. -/
@[reducible] noncomputable def sparseExitPackingRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.sparseExitPacking
    { Requires := [K .minDegreeBaseline]
      Produces := [K .remainderDeficiencyBelowCut, K .windowCutCapacity]
      requiresUnique := by simp
      producesUnique := by key_fresh
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .remainderDeficiencyBelowCut)
        ⟨Contracts.Spine.SparseExitResidual.remainderDeficiencyBelowCut_holds (object := inputs.current.object) (inputs.get (K .minDegreeBaseline)).down⟩
      (.cons (key := K .windowCutCapacity)
        ⟨Contracts.Spine.SparseExitResidual.windowCutCapacity_holds (object := inputs.current.object) (inputs.get (K .minDegreeBaseline)).down⟩
      .nil))

/-- Entry prefix, after `[1]`--`[3]`'s baseline: the primitive carrier count of G. -/
@[reducible] noncomputable def primitiveCarrierCountRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.primitiveCarrierCount
    { Requires := [K .cubicBaseline, K .minDegreeBaseline]
      Produces := [K .primitiveCarrierCount]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .primitiveCarrierCount)
        ⟨Contracts.Spine.SparseExitResidual.primitiveCarrierCount_holds (object := inputs.current.object) (inputs.get (K .cubicBaseline)).down.1.1 (inputs.get (K .minDegreeBaseline)).down⟩
      .nil)

/-- Entry prefix, after `[8]` (`lem:bridgeless` is published after the presentation laws): the single-boundary shape. -/
@[reducible] noncomputable def singleBoundaryShapeRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.singleBoundaryShape
    { Requires := [K .cubicBaseline, K .minDegreeBaseline, K .noProperBaseline, K .bridgeless]
      Produces := [K .singleBoundaryShape]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .singleBoundaryShape)
        ⟨Contracts.Spine.SparseExitResidual.singleBoundaryShape_holds (object := inputs.current.object) (inputs.get (K .cubicBaseline)).down.1.1 (inputs.get (K .minDegreeBaseline)).down (inputs.get (K .noProperBaseline)).down (inputs.get (K .bridgeless)).down⟩
      .nil)

/-- Entry prefix, after `[9]`/`[10]`: the dart identity and the high-degree count bound. -/
@[reducible] noncomputable def degreeCountRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.degreeCount
    { Requires := [K .cubicBaseline, K .minDegreeBaseline, K .tightEndpoint]
      Produces := [K .surplusDartIdentity, K .highDegreeCountBound]
      requiresUnique := by key_fresh
      producesUnique := by key_fresh
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .surplusDartIdentity)
        ⟨Contracts.Spine.SparseExitResidual.surplusDartIdentity_holds (object := inputs.current.object) (inputs.get (K .cubicBaseline)).down.1.1 (inputs.get (K .minDegreeBaseline)).down (inputs.get (K .tightEndpoint)).down⟩
      (.cons (key := K .highDegreeCountBound)
        ⟨Contracts.Spine.SparseExitResidual.highDegreeCountBound_holds (object := inputs.current.object) (inputs.get (K .cubicBaseline)).down.1.1 (inputs.get (K .minDegreeBaseline)).down (inputs.get (K .tightEndpoint)).down⟩
      .nil))

/-- Entry prefix, after `[13]`: admissible and attempted quotients of G at the pinned pair. -/
@[reducible] noncomputable def sparseExitQuotientsRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.sparseExitQuotients
    { Requires := [K .selection, K .replacementExclusion]
      Produces := [K .admissibleQuotientsLabelInjective]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .admissibleQuotientsLabelInjective)
        ⟨Contracts.Spine.SparseExitResidual.admissibleQuotientsLabelInjective_holds (object := inputs.current.object) (inputs.get (K .selection)).down.1 (inputs.get (K .selection)).down.2.sizeMinimal (inputs.get (K .replacementExclusion)).down⟩
      .nil)

/-- Top of the strict arm of `[19]` (before `[20]`): the single budget: handshake and the square-root chain. -/
@[reducible] noncomputable def sparseExitBudgetRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.sparseExitBudget
    { Requires := [K .cubicBaseline, K .minDegreeBaseline, K .noProperBaseline, K .tightEndpoint, K .surplusAbove]
      Produces := [K .edgeSurplusIdentity, K .ceilSqrtAboveScale]
      requiresUnique := by key_fresh
      producesUnique := by key_fresh
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .edgeSurplusIdentity)
        ⟨Contracts.Spine.SparseExitResidual.edgeSurplusIdentity_holds (object := inputs.current.object) (inputs.get (K .cubicBaseline)).down.1.1 (inputs.get (K .minDegreeBaseline)).down (inputs.get (K .tightEndpoint)).down (inputs.get (K .noProperBaseline)).down (inputs.get (K .surplusAbove)).down⟩
      (.cons (key := K .ceilSqrtAboveScale)
        ⟨Contracts.Spine.SparseExitResidual.ceilSqrtAboveScale_holds (object := inputs.current.object) (inputs.get (K .cubicBaseline)).down.1.1 (inputs.get (K .minDegreeBaseline)).down (inputs.get (K .tightEndpoint)).down (inputs.get (K .noProperBaseline)).down (inputs.get (K .surplusAbove)).down⟩
      .nil))

/-- Top of the strict arm of `[19]`: the envelope sharpened by the absent quadrilateral and by `ex(6, C₄) = 7`. -/
@[reducible] noncomputable def sparseExitEnvelopeRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.sparseExitEnvelope
    { Requires := [K .cubicBaseline, K .selection, K .minDegreeBaseline, K .noProperBaseline, K .tightEndpoint, K .surplusAbove]
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

/-- Top of the strict arm of `[19]`: the high-degree range. -/
@[reducible] noncomputable def highDegreeSurplusRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.highDegreeSurplus
    { Requires := [K .cubicBaseline, K .minDegreeBaseline, K .tightEndpoint, K .surplusAbove]
      Produces := [K .highDegreePositive, K .highDegreeSurplusCapacity]
      requiresUnique := by key_fresh
      producesUnique := by key_fresh
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .highDegreePositive)
        ⟨Contracts.Spine.SparseExitResidual.highDegreePositive_holds (object := inputs.current.object) (inputs.get (K .cubicBaseline)).down.1.1 (inputs.get (K .minDegreeBaseline)).down (inputs.get (K .tightEndpoint)).down (inputs.get (K .surplusAbove)).down⟩
      (.cons (key := K .highDegreeSurplusCapacity)
        ⟨Contracts.Spine.SparseExitResidual.highDegreeSurplusCapacity_holds (object := inputs.current.object) (inputs.get (K .cubicBaseline)).down.1.1 (inputs.get (K .minDegreeBaseline)).down (inputs.get (K .tightEndpoint)).down (inputs.get (K .surplusAbove)).down⟩
      .nil))

/-- Top of the strict arm of `[19]`: G's canonical capacity presentation is the explicit one; `|𝔘_sp(G)| = 4n + 2σ`. -/
@[reducible] noncomputable def sparseExitCanonicalCapacityRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.sparseExitCanonicalCapacity
    { Requires := [K .cubicBaseline, K .selection, K .minDegreeBaseline, K .slackIndependent, K .noProperBaseline, K .tightEndpoint, K .surplusAbove]
      Produces := [K .canonicalCapacityExplicit]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .canonicalCapacityExplicit)
        ⟨Contracts.Spine.SparseExitResidual.canonicalCapacityExplicit_holds (object := inputs.current.object) (inputs.get (K .cubicBaseline)).down.1.1 (inputs.get (K .cubicBaseline)).down.2.2.1.2.1 (inputs.get (K .selection)).down (inputs.get (K .minDegreeBaseline)).down (inputs.get (K .slackIndependent)).down (inputs.get (K .noProperBaseline)).down (inputs.get (K .tightEndpoint)).down (inputs.get (K .surplusAbove)).down⟩
      .nil)

/-- Top of the strict arm of `[19]`: every quantity at the canonical capacity presentation and its canonical object ledger. -/
@[reducible] noncomputable def sparseExitCanonicalCapacityCountsRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.sparseExitCanonicalCapacityCounts
    { Requires := [K .cubicBaseline, K .selection, K .minDegreeBaseline, K .slackIndependent, K .noProperBaseline, K .tightEndpoint, K .surplusAbove]
      Produces := [K .canonicalTokenCount, K .canonicalBlockedFreePartition, K .canonicalLedgerDeficit, K .pairCountDeficit, K .canonicalCertificationCriterion, K .canonicalOverloadOfFits, K .canonicalFreeExcessOfCapped]
      requiresUnique := by key_fresh
      producesUnique := by key_fresh
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .canonicalTokenCount)
        ⟨Contracts.Spine.SparseExitResidual.canonicalTokenCount_holds (object := inputs.current.object) (inputs.get (K .cubicBaseline)).down.1.1 (inputs.get (K .cubicBaseline)).down.2.2.1.2.1 (inputs.get (K .cubicBaseline)).down.2.2.1.1 (inputs.get (K .selection)).down (inputs.get (K .minDegreeBaseline)).down (inputs.get (K .slackIndependent)).down (inputs.get (K .noProperBaseline)).down (inputs.get (K .tightEndpoint)).down (inputs.get (K .surplusAbove)).down⟩
      (.cons (key := K .canonicalBlockedFreePartition)
        ⟨Contracts.Spine.SparseExitResidual.canonicalBlockedFreePartition_holds (object := inputs.current.object) (inputs.get (K .cubicBaseline)).down.1.1 (inputs.get (K .cubicBaseline)).down.2.2.1.2.1 (inputs.get (K .cubicBaseline)).down.2.2.1.1 (inputs.get (K .selection)).down (inputs.get (K .minDegreeBaseline)).down (inputs.get (K .slackIndependent)).down (inputs.get (K .noProperBaseline)).down (inputs.get (K .tightEndpoint)).down (inputs.get (K .surplusAbove)).down⟩
      (.cons (key := K .canonicalLedgerDeficit)
        ⟨Contracts.Spine.SparseExitResidual.canonicalLedgerDeficit_holds (object := inputs.current.object) (inputs.get (K .cubicBaseline)).down.1.1 (inputs.get (K .cubicBaseline)).down.2.2.1.2.1 (inputs.get (K .cubicBaseline)).down.2.2.1.1 (inputs.get (K .selection)).down (inputs.get (K .minDegreeBaseline)).down (inputs.get (K .slackIndependent)).down (inputs.get (K .noProperBaseline)).down (inputs.get (K .tightEndpoint)).down (inputs.get (K .surplusAbove)).down⟩
      (.cons (key := K .pairCountDeficit)
        ⟨Contracts.Spine.SparseExitResidual.pairCountDeficit_holds (object := inputs.current.object) (inputs.get (K .cubicBaseline)).down.1.1 (inputs.get (K .cubicBaseline)).down.2.2.1.2.1 (inputs.get (K .cubicBaseline)).down.2.2.1.1 (inputs.get (K .selection)).down (inputs.get (K .minDegreeBaseline)).down (inputs.get (K .slackIndependent)).down (inputs.get (K .noProperBaseline)).down (inputs.get (K .tightEndpoint)).down (inputs.get (K .surplusAbove)).down⟩
      (.cons (key := K .canonicalCertificationCriterion)
        ⟨Contracts.Spine.SparseExitResidual.canonicalCertificationCriterion_holds (object := inputs.current.object) (inputs.get (K .cubicBaseline)).down.1.1 (inputs.get (K .cubicBaseline)).down.2.2.1.2.1 (inputs.get (K .cubicBaseline)).down.2.2.1.1 (inputs.get (K .selection)).down (inputs.get (K .minDegreeBaseline)).down (inputs.get (K .slackIndependent)).down (inputs.get (K .noProperBaseline)).down (inputs.get (K .tightEndpoint)).down (inputs.get (K .surplusAbove)).down⟩
      (.cons (key := K .canonicalOverloadOfFits)
        ⟨Contracts.Spine.SparseExitResidual.canonicalOverloadOfFits_holds (object := inputs.current.object) (inputs.get (K .cubicBaseline)).down.1.1 (inputs.get (K .cubicBaseline)).down.2.2.1.2.1 (inputs.get (K .cubicBaseline)).down.2.2.1.1 (inputs.get (K .selection)).down (inputs.get (K .minDegreeBaseline)).down (inputs.get (K .slackIndependent)).down (inputs.get (K .noProperBaseline)).down (inputs.get (K .tightEndpoint)).down (inputs.get (K .surplusAbove)).down⟩
      (.cons (key := K .canonicalFreeExcessOfCapped)
        ⟨Contracts.Spine.SparseExitResidual.canonicalFreeExcessOfCapped_holds (object := inputs.current.object) (inputs.get (K .cubicBaseline)).down.1.1 (inputs.get (K .cubicBaseline)).down.2.2.1.2.1 (inputs.get (K .cubicBaseline)).down.2.2.1.1 (inputs.get (K .selection)).down (inputs.get (K .minDegreeBaseline)).down (inputs.get (K .slackIndependent)).down (inputs.get (K .noProperBaseline)).down (inputs.get (K .tightEndpoint)).down (inputs.get (K .surplusAbove)).down⟩
      .nil)))))))

/-- Top of the strict arm of `[19]`: the paper's budget at the canonical spine family and where G sits in the pair-code chain. -/
@[reducible] noncomputable def sparseExitPairChainRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.sparseExitPairChain
    { Requires := [K .cubicBaseline, K .selection, K .minDegreeBaseline, K .slackIndependent, K .noProperBaseline, K .tightEndpoint, K .replacementExclusion, K .surplusAbove, K .baselineSpineDemand]
      Produces := [K .paperBudgetBound, K .paperBudgetCertifies, K .pairCodeConfiguration]
      requiresUnique := by key_fresh
      producesUnique := by key_fresh
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .paperBudgetBound)
        ⟨Contracts.Spine.SparseExitResidual.paperBudgetBound_holds (object := inputs.current.object) (inputs.get (K .cubicBaseline)).down.1.1 (inputs.get (K .minDegreeBaseline)).down (inputs.get (K .tightEndpoint)).down (inputs.get (K .noProperBaseline)).down (inputs.get (K .surplusAbove)).down (inputs.get (K .baselineSpineDemand)).down⟩
      (.cons (key := K .paperBudgetCertifies)
        ⟨Contracts.Spine.SparseExitResidual.paperBudgetCertifies_holds (object := inputs.current.object) (inputs.get (K .cubicBaseline)).down.1.1 (inputs.get (K .cubicBaseline)).down.2.2.1.2.1 (inputs.get (K .cubicBaseline)).down.2.2.1.1 (inputs.get (K .selection)).down (inputs.get (K .minDegreeBaseline)).down (inputs.get (K .slackIndependent)).down (inputs.get (K .noProperBaseline)).down (inputs.get (K .tightEndpoint)).down (inputs.get (K .surplusAbove)).down (inputs.get (K .baselineSpineDemand)).down⟩
      (.cons (key := K .pairCodeConfiguration)
        ⟨Contracts.Spine.SparseExitResidual.pairCodeConfiguration_holds (object := inputs.current.object) (inputs.get (K .cubicBaseline)).down.1.1 (inputs.get (K .cubicBaseline)).down.2.2.1.2.1 (inputs.get (K .cubicBaseline)).down.2.2.1.1 (inputs.get (K .cubicBaseline)).down.2.2.1.2.2.2 (inputs.get (K .cubicBaseline)).down.2.2.1.2.2.1 (inputs.get (K .cubicBaseline)).down.2.1.2.1 (inputs.get (K .selection)).down (inputs.get (K .minDegreeBaseline)).down (inputs.get (K .slackIndependent)).down (inputs.get (K .noProperBaseline)).down (inputs.get (K .tightEndpoint)).down (inputs.get (K .replacementExclusion)).down (inputs.get (K .surplusAbove)).down (inputs.get (K .baselineSpineDemand)).down⟩
      .nil)))

/-- Node `[129]`'s baseline spine demand at the top of the strict arm of `[19]`
(before `[20]`): the paper's survivor premise is used only against clauses (c)
and (d) of `def:named-surplus-exits`, which the replacement exclusion and
selection refute.  Published once there,
it is on every ledger below `[20]`. -/
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

/-- Node `[131]`'s full-schedule entropy count fails at G's canonical objects
(unconditionally); run at the top of `[130]`'s dependent arm (it reads only
strict-arm facts).  It is not run on `[130]`'s independent
arm: there the same key is the no-arm of the paper's `[131]` decision. -/
@[reducible] noncomputable def sparseExitFreePairCountRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.sparseExitFreePairCount
    { Requires := [K .cubicBaseline, K .selection, K .minDegreeBaseline, K .slackIndependent,
        K .noProperBaseline, K .tightEndpoint, K .surplusAbove, K .baselineSpineDemand]
      Produces := [K .freePairCountFails]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .freePairCountFails)
        ⟨Contracts.Spine.SparseExitResidual.freePairCountFails_at (object := inputs.current.object)
          (inputs.get (K .cubicBaseline)).down.1.1
          (inputs.get (K .cubicBaseline)).down.2.2.1.2.1
          (inputs.get (K .cubicBaseline)).down.2.2.1.1
          (inputs.get (K .selection)).down
          (inputs.get (K .minDegreeBaseline)).down
          (inputs.get (K .slackIndependent)).down
          (inputs.get (K .noProperBaseline)).down
          (inputs.get (K .tightEndpoint)).down
          (inputs.get (K .surplusAbove)).down
          (inputs.get (K .baselineSpineDemand)).down⟩
        .nil)

end Hypostructure.Graph.Strategy.Spine
