import Hypostructure.Graph.Statements.SurplusPair
import Hypostructure.Graph.SparsePortActivation
import Hypostructure.Graph.PrimitiveCarrier
import Hypostructure.Graph.SparsePairLedger
import Hypostructure.Graph.SameTokenBlockerRoles
import Hypostructure.Graph.SparseEntropySandwich
import Hypostructure.Graph.CapacityTokenAssignment
import Hypostructure.Graph.SparseUpperEnvelope
import Hypostructure.Graph.ObjectCapacityLedger
import Hypostructure.Graph.Induced

/-!
# Contract lemmas: the pair schedule and blocker/token ledgers `[131]`--`[136]`

`lem:mixed-sparse-spine-dependence`, `lem:exact-cubic-baseline-budget`,
`lem:incremental-skeleton-room`, `lem:skeleton-dominates`, the canonical
blocker ledger, `lem:sparse-upper-envelope` with the exact window-join
identity, and the capacity-token ledger, each over a finite object with the
paper's assumptions as explicit hypotheses.
-/

namespace Hypostructure.Graph.Contracts.SurplusPair

open Hypostructure
open Hypostructure.Graph.Strategy.Spine

universe u

variable {data : Parameters} {object : Graph.FiniteObject.{u}}

/-- Node `[131]`, `lem:mixed-sparse-spine-dependence` (tex 4872-4930): on the
node-`[129]` baseline spine family of G and G's full pair-response schedule at
its canonical activation, if the mixed family is not independently
target-testable then G has a sparse surplus exit of its declared family or a
scheduled pair has a blocker of type (d) or (e).

The proof follows the paper's case order.  The rank-reducing quotient is an
admissible declared quotient, so it preserves the boundary-degree profile and is
context-universal (`DeclaredQuotient.fibrewise`, `contextUniversal`): the
paper's first two cases (a profile-crossing or a target-defective
determination) do not arise.  It is therefore target-complete, and
`DeclaredQuotient.localize` gives the remaining two: a proper determination
support admits a target-complete replacement (exit (c)), and the whole-graph
support has a strictly smaller closed representative (the whole-graph
support-dependence exit (d)).  In both cases the exit disjunct of the paper's
conclusion holds; for a pair coordinate the paper additionally reads the same
event as a blocker of type (e), which is not needed for the disjunction. -/
theorem mixedSparseSpineDependence_of_baseline
    (active : ActiveSurplusDemandsStatement data object)
    (baselineDemand : BaselineSpineDemandStatement data object) :
    MixedSparseSpineDependenceStatement data object := by
  classical
  obtain ⟨⟨Coordinate, family, coordinateSupport⟩, spineSelected, _spec⟩ :=
    baselineDemand
  refine ⟨Graph.pairResponseActivation active,
    canonicalPairActivation_eq data object active,
    ⟨Coordinate, family, coordinateSupport⟩, spineSelected, ?_⟩
  dsimp only
  intro notIndependent
  push Not at notIndependent
  obtain ⟨declared, _functional, reducing⟩ := notIndependent
  rcases declared.localize reducing with replacement |
      ⟨representative, smaller, baseline, transfer⟩
  · exact Or.inl (.compression declared.support replacement)
  · exact Or.inl (.delocalization representative smaller baseline transfer)

/-- Node `[131]`, `lem:exact-cubic-baseline-budget`, two-sided with
logarithms cleared. -/
theorem exactCubicBaselineBudget_of_threshold
    (threeLe : 3 ≤ data.threshold) :
    ExactCubicBaselineBudgetStatement data object := by
  have two_le_threshold : 2 ≤ data.threshold :=
    le_trans (by norm_num) threeLe
  constructor
  · exact Graph.cubicBaselineBudget_le_pow
      object.vertexCount two_le_threshold
  · intro room
    exact Graph.pow_pred_le_cubicBaselineBudget_mul
      object.vertexCount room

/-- Node `[131]`, `lem:incremental-skeleton-room` at the object's edge count. -/
theorem incrementalSkeletonRoom_of_baseline
    (atBaseline : Graph.MinimumDegreeAtLeast data.threshold object)
    (threeLe : 3 ≤ data.threshold) :
    IncrementalSkeletonRoomStatement data object := by
  have two_le_threshold : 2 ≤ data.threshold :=
    le_trans (by norm_num) threeLe
  have handshake : data.threshold * object.vertexCount ≤
      2 * object.edgeCount :=
    Graph.baselineDegree_mul_vertexCount_le_two_mul_edgeCount
      object data.threshold fun vertex =>
        le_trans atBaseline
          (object.minDegree_le_degree vertex)
  have above : Graph.cubicBaselineEdgeCount object.vertexCount
      data.threshold ≤ object.edgeCount :=
    Graph.cubicBaselineEdgeCount_le_edgeCount_of_handshake
      object data.threshold handshake
  constructor
  · exact Graph.skeletonBudget_le_cubicBaselineBudget_mul_pow
      object two_le_threshold above
  · have lower : data.threshold * object.vertexCount ≤
        2 * Graph.cubicBaselineEdgeCount object.vertexCount
          data.threshold := by
      unfold Graph.cubicBaselineEdgeCount
      omega
    change 2 * (object.edgeCount -
        Graph.cubicBaselineEdgeCount object.vertexCount
          data.threshold) ≤
      (2 * object.edgeCount -
        data.threshold * object.vertexCount) + 2
    omega

/-- `lem:skeleton-dominates` at the object's exact edge stratum. -/
theorem skeletonDominates_of_object :
    SkeletonDominatesStatement object := by
  have count : Nat.card
      (Graph.PackedWindowRealization.Skeleton
        object.vertexCount object.edgeCount) =
      Graph.skeletonBudget object := by
    simpa [Graph.skeletonBudget, Graph.edgeStratumCount] using
      Graph.PackedWindowRealization.card_skeleton
        object.vertexCount object.edgeCount
  refine ⟨count, ?_⟩
  intro State stateOf
  have realized :=
    Core.FiniteEntropy.card_range_le_card_ambient stateOf
  exact realized.trans_eq count

/-- Nodes `[134]`, `def:canonical-blocker-ledger` with
`lem:canonical-blocker-ledger-no-overcount`, on the blocker arm of `[132]`: the
pair schedule has `C(σ,2)` members, blocked and free pairs exhaust it, and the
canonical charge is single-valued, so `|Π_blk| = Σ_B μ(B)`. -/
theorem canonicalPairLedger_of_blockerRoute
    (atBaseline : Graph.MinimumDegreeAtLeast data.threshold object)
    (blockerRoute : CanonicalBlockerRouteStatement data object) :
    CanonicalPairLedgerStatement data object := by
  obtain ⟨_survives, activation, selected, certificate, _canonical⟩ :=
    blockerRoute
  let pairs := object.portPairSchedule data.threshold
  let recorded := Graph.recordSparsePairDEBlockers
    (Baseline := Graph.MinimumDegreeAtLeast data.threshold)
    (LengthOK := data.LengthOK) activation pairs
  have baseline : ∀ vertex : object.Vertex,
      data.threshold ≤ object.degree vertex :=
    fun vertex => le_trans atBaseline
      (object.minDegree_le_degree vertex)
  refine ⟨activation, selected, certificate, ?_, ?_, ?_, ?_, ?_⟩
  · exact object.card_portPairSchedule baseline
  · simpa [recorded] using
      recorded.card_blockedPairs_add_card_unblockedPairs data.threshold
  · exact recorded.card_canonicalIncidenceLedger data.threshold
  · exact recorded.card_blockedPairs_eq_sum_blockerMultiplicity
      data.threshold
  · exact certificate

/-- Node `[135]`, `lem:sparse-upper-envelope` with
`lem:exact-window-join-identity`: `m + 2 ≤ (δ − 1)n`, and the fixed maximal
packing satisfies the exact window-join identity. -/
theorem sparseUpperEnvelope_of_packing
    (atBaseline : Graph.MinimumDegreeAtLeast data.threshold object)
    (noProperBaseline : NoProperBaselineStatement data object)
    (tight : TightEndpointStatement data object)
    (above : data.surplusThreshold object.vertexCount <
      object.degreeSurplus data.threshold)
    (threeLe : 3 ≤ data.threshold) :
    SparseUpperEnvelopeStatement data object := by
  have baseline : ∀ vertex : object.Vertex,
      data.threshold ≤ object.degree vertex :=
    fun vertex => le_trans atBaseline
      (object.minDegree_le_degree vertex)
  have surplusPositive :
      0 < object.degreeSurplus data.threshold :=
    lt_of_le_of_lt (Nat.zero_le _)
      above
  have edgePositive : 0 < object.edgeCount :=
    object.edgeCount_pos_of_degreeSurplus_pos
      surplusPositive
  have envelope := object.edgeCount_add_two_le
    threeLe
    noProperBaseline.1
    tight edgePositive
  -- `𝒫` is the maximal packing fixed at node `[19]`.
  have valid : object.IsWindowPacking data.windowOrder
      (canonicalWindowPacking data object) :=
    (Classical.choose_spec
      (object.exists_windowPacking_card_eq data.windowOrder)).1
  exact ⟨envelope, object.exact_window_join_identity valid baseline⟩

/-- Node `[136]`, `def:capacity-token-ledger` with `lem:capacity-token-supply`,
`lem:token-ledger-no-overcount` and `def:same-token-patterns`: the object's
capacity-token ledger at the canonical blocker ledger and the fixed maximal
packing, with every accounting identity of the node. -/
theorem capacityTokenLedger_of_pairLedger
    (atBaseline : Graph.MinimumDegreeAtLeast data.threshold object)
    (pairLedger : CanonicalPairLedgerStatement data object)
    (upperEnvelope : SparseUpperEnvelopeStatement data object)
    (noProperBaseline : NoProperBaselineStatement data object)
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (threeLe : 3 ≤ data.threshold)
    (joinSlack : data.threshold * data.windowOrder + 2 ≤ 4 * data.windowOrder) :
    CapacityTokenLedgerStatement data object := by
  obtain ⟨canonical, selected, certificate, _scheduleCard,
      _partition, _incidence, _multiplicity, _blocked⟩ :=
    pairLedger
  obtain ⟨active, rfl⟩ :=
    exists_active_of_canonicalPairActivation_eq_some selected
  obtain ⟨envelope, _joinIdentity⟩ := upperEnvelope
  -- `𝒫` is the maximal packing fixed at node `[19]`.
  let packing := canonicalWindowPacking data object
  have valid : object.IsWindowPacking data.windowOrder packing :=
    (Classical.choose_spec
      (object.exists_windowPacking_card_eq data.windowOrder)).1
  have maximal : packing.card = object.windowPackingNumber data.windowOrder :=
    (Classical.choose_spec
      (object.exists_windowPacking_card_eq data.windowOrder)).2
  let activation := Graph.recordSparsePairDEBlockers
    (Baseline := Graph.MinimumDegreeAtLeast data.threshold)
    (LengthOK := data.LengthOK)
    (Graph.pairResponseActivation active)
    (object.portPairSchedule data.threshold)
  have pairCard : certificate.choose.card = 2 :=
    Graph.card_of_mem_portPairSchedule object data.threshold
      certificate.choose_spec.1
  have pairNonempty : certificate.choose.Nonempty :=
    Finset.card_pos.mp (by omega : 0 < certificate.choose.card)
  let port := pairNonempty.choose
  letI : Nonempty object.Vertex := ⟨port.1⟩
  have graphConnected : object.graph.Connected :=
    noProperBaseline.2
  have connectedOn :
      Graph.SupportComponents.Connected.ConnectedOn
        object object.vertexFinset :=
    Graph.SupportComponents.Connected.connectedOn_vertexFinset
      object graphConnected
  letI : DecidableEq object.Vertex := Classical.decEq _
  have pairCoordinateNonempty
      (pair : Finset
        (object.Vertex × object.Vertex)) :
      (Graph.DeclaredSignature.Coordinate.support
        (Graph.FiniteObject.DemandActivation.pairCoordinate pair
          (((Graph.pairResponseActivation active).pairSupport pair).getD
            ∅))).Nonempty := by
    have pairSupportSome :=
      Graph.FiniteObject.DemandActivation.pairSupport_isSome_of_connected
        (Graph.pairResponseActivation active) pair connectedOn
    obtain ⟨pairSupport, pairSupportEq⟩ :=
      Option.isSome_iff_exists.mp pairSupportSome
    have pairSupportNonempty : pairSupport.Nonempty :=
      (Graph.FiniteObject.DemandActivation.pairSupport_mem_candidates
        pairSupportEq).2.1
    change (((Graph.pairResponseActivation active).pairSupport pair).getD
      ∅).Nonempty
    rw [pairSupportEq]
    exact pairSupportNonempty
  let presentation : object.CarrierPresentation
      object.PairCoordinate
      (object.Vertex ×
        object.Vertex) := {
    coordinateSupport := by
      letI := object.vertices.decEq
      exact Graph.DeclaredSignature.Coordinate.support
    chordEnds := Graph.pairResponseChordEnds active
    chordPort := id }
  have carried : ∀ pair ∈
      object.portPairSchedule data.threshold,
      ∀ blocker ∈ activation.blockers pair,
        (Graph.FiniteObject.Blocker.carrier object
          data.threshold presentation.coordinateSupport
          presentation.chordPort blocker).isSome := by
    classical
    intro pair _pairMem blocker blockerMem
    cases blocker with
    | sharedDeclaredSupport item =>
        cases item <;> rfl
    | sharedReturnSupport item =>
        cases item <;> rfl
    | sharedLocalBuffer _ => rfl
    | boundaryProfile coordinate =>
        have coordinateMem :
            coordinate ∈ activation.profileObstructions pair := by
          simpa [Graph.FiniteObject.DemandActivation.blockers] using
            blockerMem
        have coordinateEq : coordinate =
            Graph.FiniteObject.DemandActivation.pairCoordinate pair
              (((Graph.pairResponseActivation active).pairSupport pair).getD
                ∅) := by
          simp only [activation, Graph.recordSparsePairDEBlockers] at coordinateMem
          split at coordinateMem
          · simpa using coordinateMem
          · simp at coordinateMem
        subst coordinate
        rw [Graph.FiniteObject.Blocker.carrier]
        simp only [Option.isSome_map, List.isSome_head?]
        exact List.ne_nil_of_mem (by
          simpa [presentation] using
            (pairCoordinateNonempty pair).choose_spec)
    | targetResponse coordinate =>
        have coordinateMem :
            coordinate ∈ activation.responseObstructions pair := by
          simpa [Graph.FiniteObject.DemandActivation.blockers] using
            blockerMem
        have coordinateEq : coordinate =
            Graph.FiniteObject.DemandActivation.pairCoordinate pair
              (((Graph.pairResponseActivation active).pairSupport pair).getD
                ∅) := by
          simp only [activation, Graph.recordSparsePairDEBlockers] at coordinateMem
          split at coordinateMem
          · simpa using coordinateMem
          · simp at coordinateMem
        subst coordinate
        rw [Graph.FiniteObject.Blocker.carrier]
        simp only [Option.isSome_map, List.isSome_head?]
        exact List.ne_nil_of_mem (by
          simpa [presentation] using
            (pairCoordinateNonempty pair).choose_spec)
    | arithmeticChordSet chords =>
        have chordMem :
            chords ∈ activation.chordObstructions pair := by
          simpa [Graph.FiniteObject.DemandActivation.blockers] using
            blockerMem
        change chords ∈ (Graph.pairResponseActivation active).chordObstructions pair at chordMem
        simp only [Graph.pairResponseActivation] at chordMem
        have chordFacts := List.mem_filter.mp chordMem
        have orderedFacts := List.mem_filter.mp chordFacts.1
        have powersetMember : chords ∈
            (object.excessPorts data.threshold).powerset :=
          of_decide_eq_true orderedFacts.2
        have chordSubset :
            chords ⊆ object.excessPorts data.threshold :=
          Finset.mem_powerset.mp powersetMember
        have obstruction :
            Graph.SparsePairSuppressionChordObstruction active pair
              chords :=
          of_decide_eq_true chordFacts.2
        obtain ⟨_pairSubset, family, suppressionCertificate,
            _familyPorts, _chordEnds, usedChords⟩ := obstruction
        have usedNonempty :=
          family.usedChords_nonempty_of_avoids avoids
            suppressionCertificate
        have chordsNonempty : chords.Nonempty := by
          let portOf := fun index : family.Index =>
            ((family.configuration index).center,
              (family.configuration index).vertex)
          have imageNonempty :
              (family.usedChords suppressionCertificate.walk).image
                portOf |>.Nonempty :=
            usedNonempty.image portOf
          have imageEq :
              (family.usedChords suppressionCertificate.walk).image
                portOf = chords := by
            simpa only [portOf] using usedChords
          rw [← imageEq]
          exact imageNonempty
        have chosenInIntersection : chordsNonempty.choose ∈
            (chords.image presentation.chordPort) ∩
              object.excessPorts data.threshold := by
          refine Finset.mem_inter.mpr ⟨?_,
            chordSubset chordsNonempty.choose_spec⟩
          simpa [presentation] using
            (Finset.mem_image_of_mem presentation.chordPort
              chordsNonempty.choose_spec)
        rw [Graph.FiniteObject.Blocker.carrier]
        simp only [Option.isSome_map, List.isSome_head?]
        exact List.ne_nil_of_mem (by
          simpa using chosenInIntersection)
  have baseline : ∀ vertex : object.Vertex,
      data.threshold ≤ object.degree vertex :=
    fun vertex => le_trans atBaseline
      (object.minDegree_le_degree vertex)
  have handshake : data.threshold * object.vertexCount ≤
      2 * object.edgeCount :=
    Graph.baselineDegree_mul_vertexCount_le_two_mul_edgeCount
      object data.threshold baseline
  let accounting : Graph.CapacityPresentation object
      data.threshold data.windowOrder := {
    activation := activation
    carrierComplete := carried
    packing := packing
    packingValid := valid
    packingMaximal := maximal }
  have concrete : Graph.FiniteObject.ConcreteCapacityTokenLedgerStatement
      object data.threshold data.windowOrder activation
      presentation packing := by
    refine ⟨object.card_capacityTokens_add_internalMass
        valid baseline, ?_, ?_, ?_, ?_, ?_⟩
    · exact object.card_capacityTokens_le valid baseline
        threeLe handshake envelope data.windowOrder_pos
        joinSlack
    · intro pair token charged
      exact Graph.FiniteObject.capacityCharge_mem_capacityTokens
        activation presentation data.threshold packing charged
    · rw [← Graph.FiniteObject.capacityTokenOrder_toFinset
          (object := object) (threshold := data.threshold)
          (packing := packing)]
      exact Graph.FiniteObject.card_chargedPairs_eq_sum_load
        activation presentation data.threshold packing
    · exact ⟨carried,
        Graph.FiniteObject.chargedPairs_eq_blockedPairs
          activation presentation data.threshold packing carried⟩
    · have rolePartition : ∀ token :
          Graph.FiniteObject.CapacityToken object,
          (Graph.FiniteObject.tokenFibre activation presentation
            data.threshold packing token).card =
            ∑ role : Graph.SameTokenBlockerRoles.Role,
              (Graph.FiniteObject.tokenRoleFibre activation presentation
                data.threshold packing token role).card :=
          fun token =>
            Graph.FiniteObject.card_tokenFibre_eq_sum_roleFibre
              activation presentation data.threshold packing token
      refine ⟨rolePartition, ?_, ?_⟩
      · rw [← Graph.FiniteObject.chargedPairs_eq_blockedPairs
            activation presentation data.threshold packing carried]
        rw [← Graph.FiniteObject.capacityTokenOrder_toFinset
          (object := object) (threshold := data.threshold)
          (packing := packing)]
        rw [Graph.FiniteObject.card_chargedPairs_eq_sum_load
          activation presentation data.threshold packing]
        apply Finset.sum_congr rfl
        intro token _tokenMem
        exact rolePartition token
      · intro token
        exact ⟨Graph.FiniteObject.tokenFibre_subset activation presentation
            data.threshold packing token,
          fun pair member =>
            Graph.FiniteObject.card_of_mem_tokenFibre activation presentation
              data.threshold packing member,
          Graph.FiniteObject.card_tokenFibre_eq_pairMultiplicity activation
            presentation data.threshold packing token⟩
  -- The node publishes the canonical choice of its own `∃`-body: the
  -- presentation constructed above witnesses that `𝔗_cap` of G exists.
  refine canonicalCapacity_spec data object ⟨accounting, ⟨active, rfl⟩,
    object.card_primitiveCarrier baseline,
    object.card_primitiveCarrier_le baseline
      threeLe handshake envelope, ?_, connectedOn, rfl⟩
  change Graph.FiniteObject.ConcreteCapacityTokenLedgerStatement
    object data.threshold data.windowOrder activation
      presentation packing
  exact concrete

end Hypostructure.Graph.Contracts.SurplusPair
