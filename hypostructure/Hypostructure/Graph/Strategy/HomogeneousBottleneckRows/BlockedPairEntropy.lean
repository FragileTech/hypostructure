import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.NamedSurplusExits
import Hypostructure.Graph.SparsePressureLedger
import Hypostructure.Graph.GluedCrossingCycle
import Hypostructure.Graph.Strategy.HomogeneousBottleneckRows.Basic

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-- Node `[137]`: assemble the exact token map, canonical pair schedule, and
node-`[129]` baseline realization through their ledger keys before deciding the
free-side entropy count. -/
@[reducible] noncomputable def blockedPairEntropySetupRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.blockedPairEntropySetup
    { Requires := [K .capacityTokenLedger, K .canonicalPairLedger,
        K .baselineSpineDemand]
      Produces := [K .blockedPairEntropySetup]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .blockedPairEntropySetup)
        (show Value BranchState Presentation presentation data
            .blockedPairEntropySetup inputs.current from
          ⟨by
            let capacityFact :=
              (inputs.get (K .capacityTokenLedger)).down
            let active := capacityFact.choose
            let capacity := capacityFact.choose_spec.choose
            let capacityProperties := capacityFact.choose_spec.choose_spec
            have activationEq := capacityProperties.1
            have primitiveEq := capacityProperties.2.1
            have primitiveLe := capacityProperties.2.2.1
            have concrete := capacityProperties.2.2.2.1
            obtain ⟨_activePairFamily, _blockerCertificate, _pairsEq,
                scheduleCard, _partition, _incidence, _multiplicity,
                _blocked⟩ :=
              (inputs.get (K .canonicalPairLedger)).down
            obtain ⟨_active, Coordinate, family, coordinateSupport,
                properties⟩ :=
              (inputs.get (K .baselineSpineDemand)).down
            exact ⟨active, capacity, activationEq, primitiveEq, primitiveLe,
              concrete, scheduleCard, Coordinate, family, coordinateSupport,
              properties⟩⟩)
        .nil)

/-- Node `[137]`: decide the free-side entropy count from the exact setup
assembled by `blockedPairEntropySetupRow`. -/
noncomputable def blockedPairEntropyDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous : ExactLedger (Input BranchState Presentation presentation data)
      current known)
    [FactKeys.Has (K .blockedPairEntropySetup) known]
    (sandwichFresh : K .blockedPairEntropySandwich ∉ known)
    (unrealizedFresh : K .blockedPairCodeUnrealized ∉ known) :
    Decision (K .blockedPairEntropySandwich) (K .blockedPairCodeUnrealized) previous := by
  classical
  exact Decision.run previous (K .blockedPairEntropySandwich)
    (K .blockedPairCodeUnrealized)
    `Hypostructure.Graph.Strategy.Spine.blockedPairEntropyDichotomy
    (Classical.choice (show Nonempty
        ((K .blockedPairEntropySandwich).At current ⊕
          (K .blockedPairCodeUnrealized).At current) from by
      obtain ⟨active, capacity, activationEq, primitiveEq, primitiveLe,
          concrete, scheduleCard, Coordinate, family, coordinateSupport,
          properties⟩ :=
        (previous.get (K .blockedPairEntropySetup)).down
      have survives := properties.1
      have realizationExists : Nonempty
          (Graph.BaselineCodeRealization current.object family) := properties.2.1
      have demand : Graph.cubicBaselineBudget current.object.vertexCount
          data.threshold ≤ 2 ^ (family.card + Graph.spineDeficit
            current.object.vertexCount data.threshold family.card) := properties.2.2.1
      have deficitBound : Graph.spineDeficit current.object.vertexCount
          data.threshold family.card ≤ data.surplusScale * current.object.vertexCount :=
        properties.2.2.2
      let realization := Classical.choice realizationExists
      let free := Graph.freeSide current.object.vertexPairDecidableEq
        (current.object.portPairSchedule data.threshold)
        capacity.tokenOrder capacity.Eligible capacity.eligibleDecidable
      let count : Prop :=
        2 ^ (family.card + free.card) ≤
          Graph.skeletonBudget current.object
      exact if realized : count then
        ⟨.inl ⟨active, capacity, activationEq, primitiveEq, primitiveLe,
          concrete, scheduleCard,
          Coordinate, family, coordinateSupport, survives, realizationExists,
          demand, deficitBound, realized⟩⟩
      else
        have freeNonempty : free.Nonempty :=
          freeSide_nonempty_of_baseline_realized realization realized
        let firstWitness : FirstFailedPairExtension current.object family free :=
          firstFailedPairExtensionOf realization realized
        ⟨.inr ⟨active, capacity, activationEq, primitiveEq, primitiveLe,
          concrete, scheduleCard,
          Coordinate, family, coordinateSupport, survives,
          realizationExists, demand, deficitBound, realized, freeNonempty,
          ⟨firstWitness⟩⟩⟩))
    sandwichFresh unrealizedFresh

end Hypostructure.Graph.Strategy.Spine
