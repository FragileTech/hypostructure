import Hypostructure.Graph.Contracts.TypeB.SublinearGaps
import Hypostructure.Graph.Statements.TypeBSublinearFlow

/-!
# Contracts: ports, flow values and the size profile of the Type B sublinear failure
-/

namespace Hypostructure.Graph.Contracts.TypeB

open Hypostructure
open Hypostructure.Graph.Strategy.Spine

universe u

variable {data : Parameters} {object : Graph.FiniteObject.{u}}

open scoped Classical in
theorem receiverPortsAreWindowStubs :
    ReceiverPortsAreWindowStubsStatement data object := by
  classical
  intro component _present
  constructor
  · intro receiver isReceiver atBaseline
    have same := object.internalDegree_pieceSupport
      (object.remainderSupport (canonicalWindowPacking data object)) component
      isReceiver.1
    unfold Graph.FiniteObject.missingPorts
    rw [same]
    omega
  · unfold Graph.FiniteObject.positiveDeficiency Graph.FiniteObject.receivers
    unfold Graph.FiniteObject.missingPorts
    symm
    apply Finset.sum_filter_of_ne
    intro vertex _ nonzero
    omega

theorem saturatedReceiverBasin :
    SaturatedReceiverBasinStatement data object := by
  classical
  intro component _present receiver _isReceiver saturated
  refine ⟨saturated, fun vertex member => ?_⟩
  obtain ⟨inside, full, routed⟩ := object.mem_routedLoads.mp member
  exact ⟨inside, full, object.traceTo_of_traceReceiver?_eq_some routed⟩

open scoped Classical in
theorem loadFlowValue :
    LoadFlowValueStatement data object := by
  classical
  intro piece excluded routes unsaturated
  have total := object.sum_restrictedLoad piece excluded data.threshold routes
  have step : ∑ receiver ∈ object.receivers piece data.threshold \ excluded,
      (1 + object.restrictedLoad piece excluded data.threshold receiver) ≤
      ∑ receiver ∈ object.receivers piece data.threshold \ excluded,
        data.dischargeScale * object.missingPorts piece data.threshold receiver :=
    Finset.sum_le_sum unsaturated
  rw [Finset.sum_add_distrib, total, Finset.sum_const, smul_eq_mul, mul_one,
    ← Finset.mul_sum] at step
  omega

theorem pieceSizeProfile
    (normalized : RemainderNormalizedStatement data object) :
    PieceSizeProfileStatement data object := by
  classical
  have hasReceiver : ∀ component ∈ object.canonicalPieces
      (object.remainderSupport (canonicalWindowPacking data object)),
      ∃ receiver, object.IsReceiver
        (object.pieceSupport
          (object.remainderSupport (canonicalWindowPacking data object)) component)
        data.threshold receiver := by
    intro component present
    obtain ⟨vertex, member⟩ := Graph.SupportComponents.Connected.member_nonempty
      object (object.remainderSupport (canonicalWindowPacking data object))
      ((object.mem_canonicalPieces _).mp present)
    by_cases below : object.internalDegree
        (object.pieceSupport
          (object.remainderSupport (canonicalWindowPacking data object)) component)
        vertex < data.threshold
    · exact ⟨vertex, member, below⟩
    · have inside := object.pieceSupport_subset
        (object.remainderSupport (canonicalWindowPacking data object)) component
      have noCore : ∀ inner : Finset object.Vertex,
          inner ⊆ object.pieceSupport
            (object.remainderSupport (canonicalWindowPacking data object)) component →
          ¬ Graph.MinimumDegreeAtLeast data.threshold (object.induce inner) :=
        fun inner contained => (normalized inner (contained.trans inside)).2
      obtain ⟨target, trace⟩ :=
        object.exists_traceTo_of_no_baseline_subsupport _ data.threshold
          noCore member (not_lt.mp below)
      exact ⟨target, object.isReceiver_of_traceTo trace⟩
  refine ⟨object.sum_pieceSupport_card _, hasReceiver, ?_⟩
  rw [← object.sum_positiveDeficiency_canonicalPieces
    (object.remainderSupport (canonicalWindowPacking data object)) data.threshold]
  calc (object.canonicalPieces
        (object.remainderSupport (canonicalWindowPacking data object))).card
      = ∑ _component ∈ object.canonicalPieces
          (object.remainderSupport (canonicalWindowPacking data object)), 1 := by simp
    _ ≤ _ := Finset.sum_le_sum fun component present => by
        obtain ⟨receiver, member, below⟩ := hasReceiver component present
        unfold Graph.FiniteObject.positiveDeficiency
        calc 1 ≤ data.threshold - object.internalDegree
              (object.pieceSupport
                (object.remainderSupport (canonicalWindowPacking data object))
                component) receiver := by omega
          _ ≤ _ := Finset.single_le_sum (f := fun vertex => data.threshold -
              object.internalDegree
                (object.pieceSupport
                  (object.remainderSupport (canonicalWindowPacking data object))
                  component) vertex) (fun _ _ => Nat.zero_le _) member

/-- An absorbed core has at most two vertices when the separator lies outside the
piece: it lies in the two assigned first neighbours. -/
theorem absorbedCore_card_le_two
    {piece : Finset object.Vertex}
    (outside : ∀ centre ∈ (canonicalHandoffSeparatorAt data object piece).toFinset,
      centre ∉ piece) :
    (canonicalGroupedAbsorbedCore data object piece).card ≤ 2 := by
  classical
  unfold canonicalGroupedAbsorbedCore
  split
  · next envelope hEnv =>
      unfold canonicalHandoffEnvelopeAt at hEnv
      split at hEnv
      · obtain ⟨separated, hsep, built⟩ := Option.bind_eq_some_iff.mp hEnv
        split at built
        · cases built
          have hz : separated.2.separation.separator ∉ piece := by
            apply outside
            unfold canonicalHandoffSeparatorAt
            simp [hsep]
          refine le_trans (Finset.card_le_card (t := {separated.2.separation.nextLeft,
            separated.2.separation.nextRight}) ?_) Finset.card_le_two
          intro vertex member
          obtain ⟨inPiece, rest⟩ := Finset.mem_inter.mp member
          rcases Finset.mem_union.mp rest with dec | assigned
          · exfalso
            simp [ExitSevenSeparation.envelope,
              Graph.DecoratedHandoff.envelopeOfSeparation] at dec
            exact hz (dec ▸ inPiece)
          · obtain ⟨h, _hh, ha⟩ := Finset.mem_biUnion.mp assigned
            simpa [ExitSevenSeparation.envelope,
              Graph.DecoratedHandoff.envelopeOfSeparation] using ha
        · cases built
      · cases hEnv
  · simp

open scoped Classical in
theorem separator_outside_handoffPiece (cubic : data.threshold = 3)
    {component : Graph.SupportComponents.Connected.Component object
      (object.remainderSupport (canonicalWindowPacking data object))}
    (present : component ∈ object.canonicalPieces
      (object.remainderSupport (canonicalWindowPacking data object)))
    (handoff : TypeBGroupedHandoffPiece data object component) :
    ∀ centre ∈ (canonicalHandoffSeparatorAt data object
      (object.pieceSupport
        (object.remainderSupport (canonicalWindowPacking data object)) component)).toFinset,
      centre ∉ object.pieceSupport
        (object.remainderSupport (canonicalWindowPacking data object)) component := by
  classical
  intro centre separatorMem inPiece
  have centreMem : centre ∈ canonicalGroupedCentres data object := by
    unfold canonicalGroupedCentres
    exact Finset.mem_biUnion.mpr ⟨component, Finset.mem_filter.mpr ⟨present, handoff⟩,
      separatorMem⟩
  have high := groupedCentresHigh (object := object) cubic centre centreMem
  have zero := handoff.2.1
  unfold Graph.FiniteObject.ambientSurplus at zero
  have := (Finset.sum_eq_zero_iff.mp zero) centre inPiece
  omega

open scoped Classical in
theorem coverFlowValue (cubic : data.threshold = 3) :
    CoverFlowValueStatement data object := by
  classical
  unfold CoverFlowValueStatement
  intro handoffPieces absorbed unpaid
  have subset := groupedAbsorbedCoreSubset (data := data) (object := object)
  have disjoint : (handoffPieces : Set _).PairwiseDisjoint absorbed := by
    intro left leftMem right rightMem different
    exact Finset.disjoint_of_subset_left (subset _)
      (Finset.disjoint_of_subset_right (subset _)
        (Graph.SupportComponents.Connected.disjoint_members object _ different))
  have bound : ∀ component ∈ handoffPieces, (absorbed component).card ≤ 2 := by
    intro component member
    obtain ⟨present, handoff⟩ := Finset.mem_filter.mp member
    exact absorbedCore_card_le_two (separator_outside_handoffPiece cubic present handoff)
  have union : ∑ component ∈ handoffPieces, (absorbed component).card =
      (handoffPieces.biUnion absorbed).card := (Finset.card_biUnion disjoint).symm
  set paid := (handoffPieces.biUnion absorbed).filter fun vertex =>
    ¬ ∀ centre ∈ canonicalGroupedCentres data object,
      vertex ∉ Graph.TypeBFanIncidence.closedNeighbours object data.threshold
        (typeBFanEnvelope (canonicalGroupedBridgeUnion data object)
          (canonicalGroupedCentres data object) centre) centre with hpaid
  have split : unpaid.card + paid.card = (handoffPieces.biUnion absorbed).card :=
    Finset.card_filter_add_card_filter_not _
  have paidLe : paid.card ≤ ∑ centre ∈ canonicalGroupedCentres data object,
      Graph.TypeBFanIncidence.closedCount object data.threshold
        (typeBFanEnvelope (canonicalGroupedBridgeUnion data object)
          (canonicalGroupedCentres data object) centre) centre := by
    refine le_trans (Finset.card_le_card (t := (canonicalGroupedCentres data object).biUnion
      fun centre => Graph.TypeBFanIncidence.closedNeighbours object data.threshold
        (typeBFanEnvelope (canonicalGroupedBridgeUnion data object)
          (canonicalGroupedCentres data object) centre) centre) ?_) Finset.card_biUnion_le
    intro vertex member
    obtain ⟨_, notAll⟩ := Finset.mem_filter.mp member
    push Not at notAll
    obtain ⟨centre, centreMem, closed⟩ := notAll
    exact Finset.mem_biUnion.mpr ⟨centre, centreMem, closed⟩
  have sumBound : ∑ component ∈ handoffPieces, (absorbed component).card ≤
      2 * handoffPieces.card := by
    calc _ ≤ ∑ _component ∈ handoffPieces, 2 := Finset.sum_le_sum bound
      _ = _ := by simp [mul_comm]
  have main : ∑ component ∈ handoffPieces, (absorbed component).card ≤
      ∑ centre ∈ canonicalGroupedCentres data object,
        Graph.TypeBFanIncidence.closedCount object data.threshold
          (typeBFanEnvelope (canonicalGroupedBridgeUnion data object)
            (canonicalGroupedCentres data object) centre) centre + unpaid.card := by
    omega
  have small : unpaid.card ≤ 2 * handoffPieces.card := by omega
  refine ⟨main, fun empty => ?_, bound, small⟩
  have zero : unpaid.card = 0 := by rw [empty]; rfl
  have cover : ∑ component ∈ handoffPieces, (absorbed component).card ≤
      ∑ centre ∈ canonicalGroupedCentres data object,
        Graph.TypeBFanIncidence.closedCount object data.threshold
          (typeBFanEnvelope (canonicalGroupedBridgeUnion data object)
            (canonicalGroupedCentres data object) centre) centre := by omega
  exact cover

end Hypostructure.Graph.Contracts.TypeB
