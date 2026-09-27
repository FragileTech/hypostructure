import Hypostructure.Graph.Statements.SurplusPairCode
import Hypostructure.Graph.NamedSurplusExits
import Hypostructure.Graph.SparsePressureLedger
import Hypostructure.Graph.GluedCrossingCycle
import Hypostructure.Graph.SparseUpperEnvelope

/-!
# Contract lemmas: the coupled high-load test `[137]`

The exact role-fibre partition of the certified capacity-token ledger and
`lem:capacity-token-high-load`, over a finite object.
-/

namespace Hypostructure.Graph.Contracts.SurplusPair

open Hypostructure
open Hypostructure.Graph.Strategy.Spine

universe u

variable {data : Parameters} {object : Graph.FiniteObject.{u}}

/-- Node `[137]`, `lem:exact-surplus-pair-charge-partition` with
`thm:sharp-classwise-homogeneous-token-budget` (a)--(c) and
`thm:sharp-surplus-overload-audit` (b)--(c): the free-side entropy count of
`[137]` at G's canonical presentation `𝔗_cap` and G's canonical spine family
certifies a capacity-token ledger of G on that presentation, whose pair
schedule decomposes exactly into the free side and the class/token/role
fibres, with the classwise budgets.  The node publishes the canonical certified
ledger of G, which that construction shows to exist. -/
theorem roleFibrePartition_of_sandwich
    (sandwich : BlockedPairEntropySandwichStatement data object)
    (pairLedger : CanonicalPairLedgerStatement data object)
    (slackFact : SparseSlackSurplusStatement data object)
    (aboveFact : data.surplusThreshold object.vertexCount <
      object.degreeSurplus data.threshold)
    (threeLe : 3 ≤ data.threshold) :
    RoleFibrePartitionSchema data object := by
  classical
  obtain ⟨capacity, capacitySelected, spine, spineSelected, entropy⟩ :=
    sandwich
  obtain ⟨⟨_active, _activationEq⟩, _primitiveEq, _primitiveLe, concrete,
      _connected, _packingEq⟩ :=
    canonicalCapacity_spec_of_eq_some data object capacitySelected
  obtain ⟨_independent, _realization, demand, deficitLe⟩ :=
    canonicalBaselineSpineFamily_spec_of_eq_some data object spineSelected
  obtain ⟨_activation, _selected, _certificate, scheduleCard, _rest⟩ :=
    pairLedger
  have slack : 2 * object.edgeCount =
      data.threshold * object.vertexCount +
        object.degreeSurplus data.threshold :=
    slackFact
  have above : data.surplusThreshold object.vertexCount <
      object.degreeSurplus data.threshold :=
    aboveFact
  have aboveEdges : Graph.cubicBaselineEdgeCount object.vertexCount
      data.threshold ≤ object.edgeCount := by
    unfold Graph.cubicBaselineEdgeCount
    omega
  have surplusPos : 0 < object.degreeSurplus data.threshold :=
    lt_of_le_of_lt (Nat.zero_le _) above
  have slackLe : object.edgeCount -
      Graph.cubicBaselineEdgeCount object.vertexCount data.threshold ≤
        object.degreeSurplus data.threshold := by
    unfold Graph.cubicBaselineEdgeCount
    omega
  have sizePos : 0 < object.vertexCount :=
    object.vertexCount_pos_of_degreeSurplus_pos surplusPos
  obtain ⟨vertex, _vertexMem⟩ : object.vertexFinset.Nonempty :=
    Finset.card_pos.mp (by
      rw [object.card_vertexFinset]
      exact sizePos)
  let certified : Graph.CertifiedObjectCapacityLedger object
      data.threshold data.windowOrder data.surplusScale capacity :=
    Graph.certifiedLedger_of_sandwich capacity
      (le_trans (by norm_num) threeLe) aboveEdges
      spine.family.card
      (Graph.spineDeficit object.vertexCount data.threshold spine.family.card)
      demand deficitLe slackLe entropy scheduleCard
      (object.capacityTokens_nonempty data.threshold capacity.packing vertex)
      concrete.2.1
  let ledger := certified.ledger
  have spec : CertifiedLedgerSpec data object capacity certified := by
    refine ⟨ledger.presented.choose_two_eq_free_add_sum_roleFibre
        ledger.presented.tokenClass,
      fun token => ledger.presented.load_eq_sum_roleFibre token,
      ledger.presented.classwise_split.1.1,
      ledger.presented.classwise_split.1.2,
      ledger.presented.classwise_split.2,
      ledger.presented.subtype_split.1.1,
      ledger.presented.subtype_split.2, ?_⟩
    intro patternBound positive value noMatching noStar
    exact ledger.presented.grainLoad_le_of_no_homogeneous
      ledger.presented.tokenClass value patternBound positive
      noMatching noStar
  obtain ⟨chosen, chosenSelected, chosenSpec⟩ :=
    canonicalCertifiedCapacityDataAt_spec data object capacity ⟨certified, spec⟩
  exact ⟨capacity, chosen,
    (canonicalCertifiedCapacityData_eq_some_iff data object capacity chosen).2
      ⟨capacitySelected, chosenSelected⟩,
    chosenSpec⟩

/-- Node `[137]`, `lem:capacity-token-high-load` with
`cor:forced-homogeneous-same-token-scale`: at G's canonical certified ledger,
some role fibre carries at least a `Q_st`-th of the load and all of the forced
demand up to the token supply, and contains a matching or a star of its own
count. -/
theorem fibrePressure_of_partition
    (partition : RoleFibrePartitionSchema data object) :
    FibrePressureSchema data object := by
  obtain ⟨capacity, certified, selected, _spec⟩ := partition
  exact ⟨capacity, certified, selected, Graph.fibrePressureAt certified⟩

end Hypostructure.Graph.Contracts.SurplusPair
