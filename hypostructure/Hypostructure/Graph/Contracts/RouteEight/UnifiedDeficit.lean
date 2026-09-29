import Hypostructure.Graph.Contracts.RouteEight.Basic
import Hypostructure.Graph.Statements.TypeBLanes

/-!
# Contracts: the unified deficit

Proof-agnostic contract lemma for node `[123]`, `lem:typeA-unified-deficit`:
the unified negative collection `\tilde{\mathcal X}` carries the whole
large-budget deficit, `|R| ≤ s·\tilde D_A + s·|supply| + F·s·T(n)`.

The canonical pieces split into the unified class, the decorated handoff class
and the rest.  The handoff class is paid by the grouped fan envelope of
`TypeBSublinearHypotheses`, the rest by the exact centre-by-centre cost of the
flat routing pair; both costs are charged once on the union of their centres,
paid by the registered bridge slack, and converted by the near-cubic surplus
cap.

This module imports no vocabulary, row, or strategy module.
-/

namespace Hypostructure.Graph.Contracts.RouteEight

open Hypostructure
open Hypostructure.Graph
open Hypostructure.Graph.Strategy.Spine

universe u

/-- **Node `[123]`, `lem:typeA-unified-deficit`**: the unified collection
carries the whole large-budget deficit, cleared of denominators. -/
theorem route8UnifiedDeficit (data : Parameters) (object : FiniteObject.{u})
    (baseline : data.threshold ≤ object.minDegree)
    (bridgeSlack : data.threshold + 2 + data.dischargeScale ≤
      data.bridgeMassFactor * data.dischargeScale)
    (sublinear : TypeBSublinearHypotheses data object)
    (surplusCap : SurplusAtOrBelowStatement data object) :
    Route8UnifiedDeficitFact data object := by
  classical
  letI : DecidableEq object.Vertex := object.vertices.decEq
  obtain ⟨valid, -, maximal⟩ := canonicalWindowPacking_spec data object
  have degreeAt : ∀ vertex : object.Vertex, data.threshold ≤ object.degree vertex :=
    degree_ge_of_minDegree data object baseline
  obtain ⟨pairAt, handoffPieces, handoffChar, centres, _centresEq, high,
    fanEnvelope, _fanEnvelopeEq, absorbedAt, _absorbedAtEq, perPiece, covered⟩ :=
    sublinear
  -- |R| = Σ pieces |piece|, split as cleared deficiency plus cleared mass
  have totalCard : (object.remainderSupport
      (canonicalWindowPacking data object)).card ≤
      (∑ component ∈ object.canonicalPieces
        (object.remainderSupport (canonicalWindowPacking data object)),
        data.dischargeScale * object.positiveDeficiency
          (object.pieceSupport
            (object.remainderSupport (canonicalWindowPacking data object))
            component) data.threshold) +
      ∑ component ∈ object.canonicalPieces
        (object.remainderSupport (canonicalWindowPacking data object)),
        ((object.pieceSupport
            (object.remainderSupport (canonicalWindowPacking data object))
            component).card -
          data.dischargeScale * object.positiveDeficiency
            (object.pieceSupport
              (object.remainderSupport (canonicalWindowPacking data object))
              component) data.threshold) := by
    have cardSum : (∑ component ∈ object.canonicalPieces
        (object.remainderSupport (canonicalWindowPacking data object)),
        (object.pieceSupport
          (object.remainderSupport (canonicalWindowPacking data object))
          component).card) =
        (object.remainderSupport (canonicalWindowPacking data object)).card := by
      calc (∑ component ∈ object.canonicalPieces
          (object.remainderSupport (canonicalWindowPacking data object)),
          (object.pieceSupport
            (object.remainderSupport (canonicalWindowPacking data object))
            component).card)
          = ∑ component ∈ object.canonicalPieces
              (object.remainderSupport (canonicalWindowPacking data object)),
              ∑ _vertex ∈ object.pieceSupport
                (object.remainderSupport (canonicalWindowPacking data object))
                component, 1 :=
            Finset.sum_congr rfl fun component _ => Finset.card_eq_sum_ones _
        _ = ∑ _vertex ∈ object.remainderSupport
              (canonicalWindowPacking data object), 1 :=
            object.sum_canonicalPieces _ (fun _ => 1)
        _ = (object.remainderSupport (canonicalWindowPacking data object)).card :=
            (Finset.card_eq_sum_ones _).symm
    rw [← cardSum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun component _ => by omega
  -- Σ pieces s·def⁺ = s·def⁺(R) ≤ s·|supply|
  have deficiencySum : (∑ component ∈ object.canonicalPieces
      (object.remainderSupport (canonicalWindowPacking data object)),
      data.dischargeScale * object.positiveDeficiency
        (object.pieceSupport
          (object.remainderSupport (canonicalWindowPacking data object))
          component) data.threshold) =
      data.dischargeScale * object.positiveDeficiency
        (object.remainderSupport (canonicalWindowPacking data object))
        data.threshold := by
    rw [← Finset.mul_sum, Graph.FiniteObject.sum_positiveDeficiency_canonicalPieces]
  have supplyBound : data.dischargeScale *
      object.positiveDeficiency
        (object.remainderSupport (canonicalWindowPacking data object))
        data.threshold ≤
      data.dischargeScale *
        (Graph.Route8Census.supply object (canonicalWindowPacking data object)).card := by
    rw [Graph.Route8Census.card_supply]
    exact Nat.mul_le_mul_left _
      (object.positiveDeficiency_le_boundaryIncidence _ data.threshold degreeAt)
  -- class partition of the mass sum
  have unifiedSubset : route8UnifiedComponents data object ⊆
      object.canonicalPieces
        (object.remainderSupport (canonicalWindowPacking data object)) :=
    Finset.filter_subset _ _
  have handoffSubset : handoffPieces ⊆
      (object.canonicalPieces
        (object.remainderSupport (canonicalWindowPacking data object))) \
        route8UnifiedComponents data object := by
    intro component member
    obtain ⟨present, _negative, _zero, handoff⟩ := (handoffChar component).mp member
    refine Finset.mem_sdiff.mpr ⟨present, ?_⟩
    intro unifiedMember
    exact ((Finset.mem_filter.mp unifiedMember).2).2.2 handoff
  -- the handoff class: its exact grouped-envelope cost
  have handoffRaw : (∑ component ∈ handoffPieces,
      ((object.pieceSupport
          (object.remainderSupport (canonicalWindowPacking data object))
          component).card -
        data.dischargeScale * object.positiveDeficiency
          (object.pieceSupport
            (object.remainderSupport (canonicalWindowPacking data object))
            component) data.threshold)) ≤
      ∑ centre ∈ centres,
        Graph.TypeBFanIncidence.closedCount object
          data.threshold (fanEnvelope centre) centre := by
    have pointwise : ∀ component ∈ handoffPieces,
        ((object.pieceSupport
            (object.remainderSupport (canonicalWindowPacking data object))
            component).card -
          data.dischargeScale *
            object.positiveDeficiency
              (object.pieceSupport
                (object.remainderSupport (canonicalWindowPacking data object))
                component) data.threshold) ≤
        (absorbedAt
          (object.pieceSupport
            (object.remainderSupport (canonicalWindowPacking data object))
            component)).card := by
      intro component member
      have discharged :=
        Graph.TypeBEnvelopeCharge.card_le_scaled_deficiency_add_absorbed
          object
          (object.pieceSupport
            (object.remainderSupport (canonicalWindowPacking data object))
            component)
          (absorbedAt
            (object.pieceSupport
              (object.remainderSupport (canonicalWindowPacking data object))
              component))
          data.threshold data.dischargeScale
          (perPiece component member).1
          (perPiece component member).2.1
          (perPiece component member).2.2.1
          (perPiece component member).2.2.2
      omega
    exact le_trans (Finset.sum_le_sum pointwise) covered
  -- the rest: nonnegative pieces carry nothing; negative positive-surplus
  -- pieces are paid centre by centre, `s·(d-δ)+1` per centre
  have restExactBound : ∀ component ∈
      ((object.canonicalPieces
        (object.remainderSupport (canonicalWindowPacking data object))) \
        route8UnifiedComponents data object) \
        handoffPieces,
      ((object.pieceSupport
          (object.remainderSupport (canonicalWindowPacking data object))
          component).card -
        data.dischargeScale * object.positiveDeficiency
          (object.pieceSupport
            (object.remainderSupport (canonicalWindowPacking data object))
            component) data.threshold) ≤
      ∑ centre ∈ Graph.TypeBRefinedSupport.centres
          object data.threshold
          (object.pieceSupport
            (object.remainderSupport (canonicalWindowPacking data object))
            component),
        (data.dischargeScale *
            (object.degree centre - data.threshold) + 1) := by
    intro component memberRest
    have memberSdiff := Finset.mem_sdiff.mp memberRest
    have memberPieces := (Finset.mem_sdiff.mp memberSdiff.1).1
    have notUnified := (Finset.mem_sdiff.mp memberSdiff.1).2
    have notHandoff := memberSdiff.2
    let piece := object.pieceSupport
      (object.remainderSupport (canonicalWindowPacking data object)) component
    let pieceCentres := Graph.TypeBRefinedSupport.centres object data.threshold piece
    by_cases negative : object.NegativeNetCharge piece
        data.threshold data.dischargeScale
    · by_cases zero : object.ambientSurplus piece data.threshold = 0
      · -- negative zero-surplus outside the unified collection is a
        -- handoff piece, excluded here
        exfalso
        have handoff : SeparatorHandoffAt data object piece := by
          by_contra noHandoff
          exact notUnified (Finset.mem_filter.mpr
            ⟨memberPieces, zero, negative, noHandoff⟩)
        exact notHandoff ((handoffChar component).mpr
          ⟨memberPieces, negative, zero, handoff⟩)
      · obtain ⟨routes, unsaturated⟩ :=
          pairAt component memberPieces negative (Nat.pos_of_ne_zero zero)
        have ledger :=
          Graph.TypeBEnvelopeCharge.neg_centreAllowance_le_augmentedLedger
            object piece data.threshold
            data.dischargeScale degreeAt routes unsaturated
        have identity :=
          Graph.TypeBEnvelopeCharge.augmentedLedger_add_card_centres
            object data.threshold data.dischargeScale piece
        change -(∑ centre ∈ pieceCentres,
            ((data.dischargeScale *
                (object.degree centre - data.threshold) + 2 :
              Nat) : Int)) ≤
            Graph.TypeBRefinedSupport.augmentedLedger
              object data.threshold data.dischargeScale piece
          at ledger
        change Graph.TypeBRefinedSupport.augmentedLedger
              object data.threshold data.dischargeScale piece +
            (pieceCentres.card : Int) =
          ((data.dischargeScale *
              object.positiveDeficiency piece data.threshold : Nat) : Int) -
            ((data.dischargeScale *
              object.ambientSurplus piece data.threshold : Nat) : Int) -
            (piece.card : Int)
          at identity
        have allowance : (∑ centre ∈ pieceCentres,
            ((data.dischargeScale *
                (object.degree centre - data.threshold) + 2 :
              Nat) : Int)) =
            ((∑ centre ∈ pieceCentres,
              (data.dischargeScale *
                (object.degree centre - data.threshold) + 1) :
              Nat) : Int) + (pieceCentres.card : Int) := by
          push_cast
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
            Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
          ring
        rw [allowance] at ledger
        have cardCast : (piece.card : Int) ≤
            ((data.dischargeScale *
              object.positiveDeficiency piece data.threshold : Nat) : Int) +
            ((∑ centre ∈ pieceCentres,
              (data.dischargeScale *
                (object.degree centre - data.threshold) + 1) :
              Nat) : Int) := by
          have surplusNonneg : (0 : Int) ≤
              ((data.dischargeScale *
                object.ambientSurplus piece data.threshold : Nat) : Int) :=
            Int.natCast_nonneg _
          linarith [identity, ledger, surplusNonneg]
        have card : piece.card ≤
            data.dischargeScale *
                object.positiveDeficiency piece data.threshold +
              ∑ centre ∈ pieceCentres,
                (data.dischargeScale *
                  (object.degree centre - data.threshold) + 1) := by
          exact_mod_cast cardCast
        change piece.card - data.dischargeScale *
            object.positiveDeficiency piece data.threshold ≤
          ∑ centre ∈ pieceCentres,
            (data.dischargeScale *
              (object.degree centre - data.threshold) + 1)
        omega
    · have nonneg := (object.not_negativeNetCharge_iff
          piece data.threshold data.dischargeScale).mp negative
      rw [Graph.FiniteObject.NonNegativeNetCharge] at nonneg
      change piece.card - data.dischargeScale *
            object.positiveDeficiency piece data.threshold ≤
          ∑ centre ∈ pieceCentres,
            (data.dischargeScale *
              (object.degree centre - data.threshold) + 1)
      omega
  -- Shared-centre amortization: on the union of the ordinary and handoff
  -- centres, give every centre both exact costs; the registered slack pays
  -- that sum once.
  let support := object.remainderSupport (canonicalWindowPacking data object)
  let rest := ((object.canonicalPieces support) \
      route8UnifiedComponents data object) \ handoffPieces
  let restMass := fun component :
      Graph.SupportComponents.Connected.Component object support =>
    (object.pieceSupport support component).card -
      data.dischargeScale * object.positiveDeficiency
        (object.pieceSupport support component) data.threshold
  let ordinary := Graph.TypeBRefinedSupport.centres object data.threshold support
  let allCentres := ordinary ∪ centres
  let ordinaryCost := fun centre : object.Vertex =>
    data.dischargeScale * (object.degree centre - data.threshold) + 1
  let handoffCost := fun centre : object.Vertex =>
    Graph.TypeBFanIncidence.closedCount object data.threshold
      (fanEnvelope centre) centre
  have centreSum (piece : Finset object.Vertex) :
      (∑ centre ∈ Graph.TypeBRefinedSupport.centres object data.threshold piece,
        ordinaryCost centre) =
      ∑ vertex ∈ piece,
        if Graph.IsHighCentre object data.threshold vertex
        then ordinaryCost vertex else 0 := by
    unfold Graph.TypeBRefinedSupport.centres
    rw [Finset.sum_filter]
  have restSubset : rest ⊆ object.canonicalPieces support := by
    intro component member
    exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp member).1).1
  have restRaw : (∑ component ∈ rest, restMass component) ≤
      ∑ centre ∈ ordinary, ordinaryCost centre := by
    calc
      (∑ component ∈ rest, restMass component) ≤
          ∑ component ∈ rest,
            ∑ centre ∈ Graph.TypeBRefinedSupport.centres
                object data.threshold (object.pieceSupport support component),
              ordinaryCost centre :=
        Finset.sum_le_sum fun component member => restExactBound component member
      _ ≤ ∑ component ∈ object.canonicalPieces support,
            ∑ centre ∈ Graph.TypeBRefinedSupport.centres
                object data.threshold (object.pieceSupport support component),
              ordinaryCost centre :=
        Finset.sum_le_sum_of_subset restSubset
      _ = ∑ component ∈ object.canonicalPieces support,
            ∑ vertex ∈ object.pieceSupport support component,
              if Graph.IsHighCentre object data.threshold vertex
              then ordinaryCost vertex else 0 :=
        Finset.sum_congr rfl fun component _ => centreSum _
      _ = ∑ vertex ∈ support,
            if Graph.IsHighCentre object data.threshold vertex
            then ordinaryCost vertex else 0 :=
        object.sum_canonicalPieces support _
      _ = ∑ centre ∈ ordinary, ordinaryCost centre := by
        unfold ordinary Graph.TypeBRefinedSupport.centres
        rw [Finset.sum_filter]
  have ordinaryToAll : (∑ centre ∈ ordinary, ordinaryCost centre) ≤
      ∑ centre ∈ allCentres, ordinaryCost centre :=
    Finset.sum_le_sum_of_subset Finset.subset_union_left
  have handoffToAll : (∑ centre ∈ centres, handoffCost centre) ≤
      ∑ centre ∈ allCentres, handoffCost centre :=
    Finset.sum_le_sum_of_subset Finset.subset_union_right
  have sharedPointwise : ∀ centre ∈ allCentres,
      handoffCost centre + ordinaryCost centre ≤
        data.bridgeMassFactor * data.dischargeScale *
          (object.degree centre - data.threshold) := by
    intro centre member
    have highCentre : data.threshold < object.degree centre := by
      rcases Finset.mem_union.mp member with member | member
      · exact (Graph.TypeBRefinedSupport.mem_centres.mp member).2
      · exact high centre member
    have counted := Graph.TypeBFanIncidence.closedCount_le_degree
      object data.threshold (fanEnvelope centre) centre
    obtain ⟨surplus, degree⟩ : ∃ surplus : Nat,
        object.degree centre = data.threshold + surplus + 1 :=
      ⟨object.degree centre - data.threshold - 1, by omega⟩
    have spent :
        (data.threshold + 2 + data.dischargeScale) * (surplus + 1) ≤
          data.bridgeMassFactor * data.dischargeScale * (surplus + 1) :=
      Nat.mul_le_mul_right _ bridgeSlack
    simp only [handoffCost, ordinaryCost]
    rw [degree] at counted ⊢
    have reduce : data.threshold + surplus + 1 - data.threshold =
        surplus + 1 := by omega
    rw [reduce]
    nlinarith [spent, counted]
  have unionBound :
      (∑ centre ∈ allCentres, handoffCost centre) +
          ∑ centre ∈ allCentres, ordinaryCost centre ≤
        data.bridgeMassFactor * data.dischargeScale *
          object.ambientSurplus allCentres data.threshold := by
    rw [← Finset.sum_add_distrib]
    calc
      (∑ centre ∈ allCentres, (handoffCost centre + ordinaryCost centre)) ≤
          ∑ centre ∈ allCentres,
            data.bridgeMassFactor * data.dischargeScale *
              (object.degree centre - data.threshold) :=
        Finset.sum_le_sum sharedPointwise
      _ = data.bridgeMassFactor * data.dischargeScale *
            object.ambientSurplus allCentres data.threshold := by
        unfold Graph.FiniteObject.ambientSurplus
        rw [Finset.mul_sum]
  have unionPaid := Nat.mul_le_mul_left
    (data.bridgeMassFactor * data.dischargeScale)
    (Graph.TypeBEnvelopeCharge.ambientSurplus_le_degreeSurplus
      object allCentres data.threshold degreeAt)
  change (∑ component ∈ handoffPieces, restMass component) ≤
      ∑ centre ∈ centres, handoffCost centre at handoffRaw
  have sharedSurplusSum :
      (∑ component ∈ handoffPieces, restMass component) +
          ∑ component ∈ rest, restMass component ≤
        data.bridgeMassFactor * data.dischargeScale *
          object.degreeSurplus data.threshold :=
    le_trans (Nat.add_le_add handoffRaw restRaw)
      (le_trans (Nat.add_le_add handoffToAll ordinaryToAll)
        (le_trans unionBound unionPaid))
  -- assemble: split the total mass over the three classes
  have massSplitOuter := Finset.sum_sdiff (f := fun component =>
      (object.pieceSupport
          (object.remainderSupport (canonicalWindowPacking data object))
          component).card -
        data.dischargeScale * object.positiveDeficiency
          (object.pieceSupport
            (object.remainderSupport (canonicalWindowPacking data object))
            component) data.threshold) unifiedSubset
  have massSplitInner := Finset.sum_sdiff (f := fun component =>
      (object.pieceSupport
          (object.remainderSupport (canonicalWindowPacking data object))
          component).card -
        data.dischargeScale * object.positiveDeficiency
          (object.pieceSupport
            (object.remainderSupport (canonicalWindowPacking data object))
            component) data.threshold) handoffSubset
  -- the unified sum is the cleared deficit itself
  have unifiedEq : (∑ component ∈ route8UnifiedComponents data object,
      ((object.pieceSupport
          (object.remainderSupport (canonicalWindowPacking data object))
          component).card -
        data.dischargeScale * object.positiveDeficiency
          (object.pieceSupport
            (object.remainderSupport (canonicalWindowPacking data object))
            component) data.threshold)) =
      Graph.TypeBEnvelopeCharge.route8Deficit object
        (object.remainderSupport (canonicalWindowPacking data object))
        data.threshold data.dischargeScale
        (route8UnifiedComponents data object) := rfl
  -- the near-cubic conversion of the surplus role
  have surplusRole : data.bridgeMassFactor * data.dischargeScale *
      object.degreeSurplus data.threshold ≤
      data.bridgeMassFactor * data.dischargeScale *
        data.surplusThreshold object.vertexCount :=
    Nat.mul_le_mul_left _ surplusCap
  show (object.remainderSupport (canonicalWindowPacking data object)).card ≤
    Graph.TypeBEnvelopeCharge.route8Deficit object
        (object.remainderSupport (canonicalWindowPacking data object))
        data.threshold data.dischargeScale
        (route8UnifiedComponents data object) +
      data.dischargeScale *
        (Graph.Route8Census.supply object (canonicalWindowPacking data object)).card +
      data.bridgeMassFactor * data.dischargeScale *
        data.surplusThreshold object.vertexCount
  simp only [restMass, rest, support] at sharedSurplusSum
  omega

/-- **Lean improvement: the quotient-free arm of the unified route-`8` ledger
is empty at G** (node `[123]`, stated about G).  At a target-avoiding G every
graph-owned entry has `α(ξ) = 0` (`PresentedEntry.ofTraceBasin_alpha_eq_zero`,
`Entry.Complete` read in `G − B_u`); the census's `2 ≤ α(ξ)`
(`lem:typeA-unified-carriers`, alternative (b) refuted by the quotient-freeness)
therefore leaves no unified entry; the stage accounting of the descent
(`lem:typeA-peeling-stage-accounting`: `s·\tilde D_A ≤ |\tilde\Xi ∖ P_4| + |P_4|`)
clears the unified deficit; and `lem:typeA-unified-deficit` leaves
`|R| ≤ s·|∂R| + F·s·T(n)`. -/
theorem route8UnifiedEmptyAtG (data : Parameters) (object : FiniteObject.{u})
    (census : Route8UnifiedEntryCensusFact data object)
    (avoids : ¬ HasCycleWithLength data.LengthOK object)
    (descent : Route8PeelingDescentStatement data object)
    (deficit : Route8UnifiedDeficitFact data object) :
    Route8UnifiedEmptyAtGStatement data object := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  have alphaZero : ∀ index : Route8Census.Index object,
      ((Route8Census.presented object data.threshold data.LengthOK
        index).toEntry (HasCycleWithLength data.LengthOK)).alpha = 0 :=
    fun index => Route8.PresentedEntry.ofTraceBasin_alpha_eq_zero
      (support := index.1) (basin := Route8Census.basin object data.threshold index)
      (threshold := data.threshold) (receiver := index.2.1) (load := index.2.2)
      avoids
  have entriesEmpty : route8UnifiedEntries data object = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro index member
    have two := (census index member).2.1
    have zero := alphaZero index
    change 2 ≤ ((Route8Census.presented object data.threshold data.LengthOK
      index).toEntry (HasCycleWithLength data.LengthOK)).alpha at two
    omega
  obtain ⟨_chain, accounting, _outcome⟩ := descent
  obtain ⟨_peeledSubset, entriesEq, _disjoint, _peeledLe, _deficitEq,
    deficitLe, _reducedLe, _stageDeficit⟩ := accounting
  rw [entriesEmpty] at entriesEq
  obtain ⟨reducedEmpty, peeledEmpty⟩ := Finset.union_eq_empty.mp entriesEq.symm
  have deficitZero : TypeBEnvelopeCharge.route8Deficit object
      (object.remainderSupport (canonicalWindowPacking data object))
      data.threshold data.dischargeScale (route8UnifiedComponents data object) =
        0 := by
    rw [entriesEmpty, reducedEmpty, peeledEmpty] at deficitLe
    simpa using deficitLe
  refine ⟨alphaZero, entriesEmpty, deficitZero, ?_⟩
  have bound : (object.remainderSupport (canonicalWindowPacking data object)).card ≤
      TypeBEnvelopeCharge.route8Deficit object
          (object.remainderSupport (canonicalWindowPacking data object))
          data.threshold data.dischargeScale (route8UnifiedComponents data object) +
        data.dischargeScale *
          (Route8Census.supply object (canonicalWindowPacking data object)).card +
        data.bridgeMassFactor * data.dischargeScale *
          data.surplusThreshold object.vertexCount := deficit
  rw [deficitZero, Nat.zero_add] at bound
  exact bound

/-- **The private-carrier rate refutes the empty quotient-free arm at G**: the
rate `s·|∂R| + F·s·T(n) < |R|` (`K .route8Rate`) against
`|R| ≤ s·|∂R| + F·s·T(n)`. -/
theorem route8UnifiedEmptyAtG_contradiction (data : Parameters)
    (object : FiniteObject.{u})
    (rate : Route8RateStatement data object)
    (empty : Route8UnifiedEmptyAtGStatement data object) : False := by
  obtain ⟨_alphaZero, _entriesEmpty, _deficitZero, bound⟩ := empty
  unfold Route8RateStatement Route8Census.StrongRate at rate
  omega

end Hypostructure.Graph.Contracts.RouteEight
