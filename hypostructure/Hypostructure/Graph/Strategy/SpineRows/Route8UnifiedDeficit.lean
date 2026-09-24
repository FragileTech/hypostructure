import Hypostructure.Graph.Strategy.SpineVocabulary

/-! Independently compiled spine row declarations. -/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

variable [FactSystem (Input BranchState Presentation presentation data)]

omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def route8UnifiedDeficitRow :
    @AtomicStrategy (Input BranchState Presentation presentation data) _
      (instFactSystem (BranchState := BranchState)
        (Presentation := Presentation) (presentation := presentation)
        (data := data)) :=
  letI : FactSystem (Input BranchState Presentation presentation data) :=
    instFactSystem (BranchState := BranchState) (Presentation := Presentation)
      (presentation := presentation) (data := data)
  @factOnly (Input BranchState Presentation presentation data) _
    (instFactSystem (BranchState := BranchState)
      (Presentation := Presentation) (presentation := presentation)
      (data := data))
    `Hypostructure.Graph.Strategy.Spine.route8UnifiedDeficit
    { Requires := [K .typeBSublinearLedger, K .surplusAtOrBelow]
      Produces := [K .route8UnifiedDeficit]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let sublinear := (inputs.get (K .typeBSublinearLedger)).down
      let surplusCap := (inputs.get (K .surplusAtOrBelow)).down
      .cons (key := K .route8UnifiedDeficit)
        (⟨by
          classical
          letI : DecidableEq inputs.current.object.Vertex :=
            inputs.current.object.vertices.decEq
          have packingSpec := Classical.choose_spec
            (inputs.current.object.exists_windowPacking_card_eq data.windowOrder)
          have valid : inputs.current.object.IsWindowPacking data.windowOrder
              (canonicalWindowPacking data inputs.current.object) :=
            packingSpec.1
          have maximal : ∀ window : Finset inputs.current.object.Vertex,
              inputs.current.object.InducesWindow data.windowOrder window →
              ∃ member ∈ canonicalWindowPacking data inputs.current.object,
                ¬ Disjoint window member := fun window induces =>
            inputs.current.object.exists_mem_not_disjoint_of_card_eq
              data.windowOrder_pos valid packingSpec.2 induces
          have baseline : ∀ vertex : inputs.current.object.Vertex,
              data.threshold ≤ inputs.current.object.degree vertex :=
            fun vertex =>
              le_trans inputs.current.baseline
                (inputs.current.object.minDegree_le_degree vertex)
          obtain ⟨pairAt, handoffPieces, handoffChar, centres, high,
            fanEnvelope, absorbedAt, perPiece, covered⟩ :=
            sublinear (canonicalWindowPacking data inputs.current.object)
              valid maximal
          -- names
          have supportEq : inputs.current.object.remainderSupport
              (canonicalWindowPacking data inputs.current.object) =
              inputs.current.object.remainderSupport
                (canonicalWindowPacking data inputs.current.object) := rfl
          -- the per-piece cleared mass
          have pointwiseCard : ∀ component ∈ inputs.current.object.canonicalPieces
              (inputs.current.object.remainderSupport
                (canonicalWindowPacking data inputs.current.object)),
              (inputs.current.object.pieceSupport
                (inputs.current.object.remainderSupport
                  (canonicalWindowPacking data inputs.current.object))
                component).card ≤
                data.dischargeScale * inputs.current.object.positiveDeficiency
                  (inputs.current.object.pieceSupport
                    (inputs.current.object.remainderSupport
                      (canonicalWindowPacking data inputs.current.object))
                    component) data.threshold +
                ((inputs.current.object.pieceSupport
                    (inputs.current.object.remainderSupport
                      (canonicalWindowPacking data inputs.current.object))
                    component).card -
                  data.dischargeScale * inputs.current.object.positiveDeficiency
                    (inputs.current.object.pieceSupport
                      (inputs.current.object.remainderSupport
                        (canonicalWindowPacking data inputs.current.object))
                      component) data.threshold) := by
            intro component _member
            omega
          -- |R| = Σ pieces |piece|
          have cardSum : (∑ component ∈ inputs.current.object.canonicalPieces
              (inputs.current.object.remainderSupport
                (canonicalWindowPacking data inputs.current.object)),
              (inputs.current.object.pieceSupport
                (inputs.current.object.remainderSupport
                  (canonicalWindowPacking data inputs.current.object))
                component).card) =
              (inputs.current.object.remainderSupport
                (canonicalWindowPacking data inputs.current.object)).card := by
            have base := inputs.current.object.sum_canonicalPieces
              (inputs.current.object.remainderSupport
                (canonicalWindowPacking data inputs.current.object))
              (fun _ => 1)
            calc (∑ component ∈ inputs.current.object.canonicalPieces
                (inputs.current.object.remainderSupport
                  (canonicalWindowPacking data inputs.current.object)),
                (inputs.current.object.pieceSupport
                  (inputs.current.object.remainderSupport
                    (canonicalWindowPacking data inputs.current.object))
                  component).card)
                = ∑ component ∈ inputs.current.object.canonicalPieces
                    (inputs.current.object.remainderSupport
                      (canonicalWindowPacking data inputs.current.object)),
                    ∑ _vertex ∈ inputs.current.object.pieceSupport
                      (inputs.current.object.remainderSupport
                        (canonicalWindowPacking data inputs.current.object))
                      component, 1 :=
                  Finset.sum_congr rfl fun component _ =>
                    Finset.card_eq_sum_ones _
              _ = ∑ _vertex ∈ inputs.current.object.remainderSupport
                    (canonicalWindowPacking data inputs.current.object), 1 :=
                  base
              _ = (inputs.current.object.remainderSupport
                    (canonicalWindowPacking data inputs.current.object)).card :=
                  (Finset.card_eq_sum_ones _).symm
          -- Σ pieces s·def⁺ = s·def⁺(R) ≤ s·|supply|
          have deficiencySum : (∑ component ∈
              inputs.current.object.canonicalPieces
                (inputs.current.object.remainderSupport
                  (canonicalWindowPacking data inputs.current.object)),
              data.dischargeScale * inputs.current.object.positiveDeficiency
                (inputs.current.object.pieceSupport
                  (inputs.current.object.remainderSupport
                    (canonicalWindowPacking data inputs.current.object))
                  component) data.threshold) =
              data.dischargeScale * inputs.current.object.positiveDeficiency
                (inputs.current.object.remainderSupport
                  (canonicalWindowPacking data inputs.current.object))
                data.threshold := by
            rw [← Finset.mul_sum,
              Graph.FiniteObject.sum_positiveDeficiency_canonicalPieces]
          have supplyBound : data.dischargeScale *
              inputs.current.object.positiveDeficiency
                (inputs.current.object.remainderSupport
                  (canonicalWindowPacking data inputs.current.object))
                data.threshold ≤
              data.dischargeScale *
                (Graph.Route8Census.supply inputs.current.object
                  (canonicalWindowPacking data inputs.current.object)).card := by
            rw [Graph.Route8Census.card_supply]
            exact Nat.mul_le_mul_left _
              (inputs.current.object.positiveDeficiency_le_boundaryIncidence
                _ data.threshold baseline)
          -- class partition of the mass sum
          have unifiedSubset : route8UnifiedComponents data inputs.current.object ⊆
              inputs.current.object.canonicalPieces
                (inputs.current.object.remainderSupport
                  (canonicalWindowPacking data inputs.current.object)) :=
            Finset.filter_subset _ _
          have handoffSubset : handoffPieces ⊆
              (inputs.current.object.canonicalPieces
                (inputs.current.object.remainderSupport
                  (canonicalWindowPacking data inputs.current.object))) \
                route8UnifiedComponents data inputs.current.object := by
            intro component member
            obtain ⟨present, negative, zero, handoff⟩ :=
              (handoffChar component).mp member
            refine Finset.mem_sdiff.mpr ⟨present, ?_⟩
            intro unifiedMember
            exact ((Finset.mem_filter.mp unifiedMember).2).2.2 handoff
          -- the handoff family bound
          have handoffBound : (∑ component ∈ handoffPieces,
              ((inputs.current.object.pieceSupport
                  (inputs.current.object.remainderSupport
                    (canonicalWindowPacking data inputs.current.object))
                  component).card -
                data.dischargeScale * inputs.current.object.positiveDeficiency
                  (inputs.current.object.pieceSupport
                    (inputs.current.object.remainderSupport
                      (canonicalWindowPacking data inputs.current.object))
                    component) data.threshold)) ≤
              data.bridgeMassFactor * data.dischargeScale *
                inputs.current.object.degreeSurplus data.threshold := by
            refine Graph.TypeBEnvelopeCharge.envelopeFamilyNegativePart_le_degreeSurplus
              inputs.current.object handoffPieces
              (fun component => inputs.current.object.pieceSupport
                (inputs.current.object.remainderSupport
                  (canonicalWindowPacking data inputs.current.object))
                component)
              (fun component => absorbedAt
                (inputs.current.object.pieceSupport
                  (inputs.current.object.remainderSupport
                    (canonicalWindowPacking data inputs.current.object))
                  component))
              centres fanEnvelope data.bridgeMassSlack baseline high
              (fun component member => (perPiece component member).1)
              (fun component member => (perPiece component member).2.1)
              (fun component member => (perPiece component member).2.2.1)
              (fun component member => (perPiece component member).2.2.2)
              covered
          -- Keep the exact grouped-envelope cost before the old conversion
          -- to a whole surplus role.  This is the part of the incoming
          -- ledger that the former factor-two account did not expose.
          have handoffRaw : (∑ component ∈ handoffPieces,
              ((inputs.current.object.pieceSupport
                  (inputs.current.object.remainderSupport
                    (canonicalWindowPacking data inputs.current.object))
                  component).card -
                data.dischargeScale * inputs.current.object.positiveDeficiency
                  (inputs.current.object.pieceSupport
                    (inputs.current.object.remainderSupport
                      (canonicalWindowPacking data inputs.current.object))
                    component) data.threshold)) ≤
              ∑ centre ∈ centres,
                Graph.TypeBFanIncidence.closedCount inputs.current.object
                  data.threshold (fanEnvelope centre) centre := by
            have pointwise : ∀ component ∈ handoffPieces,
                ((inputs.current.object.pieceSupport
                    (inputs.current.object.remainderSupport
                      (canonicalWindowPacking data inputs.current.object))
                    component).card -
                  data.dischargeScale *
                    inputs.current.object.positiveDeficiency
                      (inputs.current.object.pieceSupport
                        (inputs.current.object.remainderSupport
                          (canonicalWindowPacking data inputs.current.object))
                        component) data.threshold) ≤
                (absorbedAt
                  (inputs.current.object.pieceSupport
                    (inputs.current.object.remainderSupport
                      (canonicalWindowPacking data inputs.current.object))
                    component)).card := by
              intro component member
              have discharged :=
                Graph.TypeBEnvelopeCharge.card_le_scaled_deficiency_add_absorbed
                  inputs.current.object
                  (inputs.current.object.pieceSupport
                    (inputs.current.object.remainderSupport
                      (canonicalWindowPacking data inputs.current.object))
                    component)
                  (absorbedAt
                    (inputs.current.object.pieceSupport
                      (inputs.current.object.remainderSupport
                        (canonicalWindowPacking data inputs.current.object))
                      component))
                  data.threshold data.dischargeScale
                  (perPiece component member).1
                  (perPiece component member).2.1
                  (perPiece component member).2.2.1
                  (perPiece component member).2.2.2
              omega
            exact le_trans (Finset.sum_le_sum pointwise) covered
          -- the rest: nonnegative pieces carry nothing, positive-surplus
          -- negative pieces are paid by the bridge deficit bound
          have restBound : ∀ component ∈
              ((inputs.current.object.canonicalPieces
                (inputs.current.object.remainderSupport
                  (canonicalWindowPacking data inputs.current.object))) \
                route8UnifiedComponents data inputs.current.object) \
                handoffPieces,
              ((inputs.current.object.pieceSupport
                  (inputs.current.object.remainderSupport
                    (canonicalWindowPacking data inputs.current.object))
                  component).card -
                data.dischargeScale * inputs.current.object.positiveDeficiency
                  (inputs.current.object.pieceSupport
                    (inputs.current.object.remainderSupport
                      (canonicalWindowPacking data inputs.current.object))
                    component) data.threshold) ≤
              data.bridgeMassFactor * data.dischargeScale *
                inputs.current.object.ambientSurplus
                  (inputs.current.object.pieceSupport
                    (inputs.current.object.remainderSupport
                      (canonicalWindowPacking data inputs.current.object))
                    component) data.threshold := by
            intro component memberRest
            have memberSdiff := Finset.mem_sdiff.mp memberRest
            have memberPieces := (Finset.mem_sdiff.mp memberSdiff.1).1
            have notUnified := (Finset.mem_sdiff.mp memberSdiff.1).2
            have notHandoff := memberSdiff.2
            by_cases negative : inputs.current.object.NegativeNetCharge
                (inputs.current.object.pieceSupport
                  (inputs.current.object.remainderSupport
                    (canonicalWindowPacking data inputs.current.object))
                  component) data.threshold data.dischargeScale
            · by_cases zero : inputs.current.object.ambientSurplus
                  (inputs.current.object.pieceSupport
                    (inputs.current.object.remainderSupport
                      (canonicalWindowPacking data inputs.current.object))
                    component) data.threshold = 0
              · -- negative zero-surplus outside the unified collection is a
                -- handoff piece, excluded here
                exfalso
                have handoff : HandoffProduced data inputs.current.object
                    (canonicalWindowPacking data inputs.current.object)
                    (inputs.current.object.pieceSupport
                      (inputs.current.object.remainderSupport
                        (canonicalWindowPacking data inputs.current.object))
                      component) := by
                  by_contra noHandoff
                  exact notUnified (Finset.mem_filter.mpr
                    ⟨memberPieces, zero, negative, noHandoff⟩)
                exact notHandoff ((handoffChar component).mpr
                  ⟨memberPieces, negative, zero, handoff⟩)
              · -- negative positive-surplus: the tested flat pair pays
                have pair := pairAt component memberPieces negative
                  (Nat.pos_of_ne_zero zero)
                have bound := Graph.TypeBEnvelopeCharge.bridgeDeficitBound
                  inputs.current.object
                  (inputs.current.object.pieceSupport
                    (inputs.current.object.remainderSupport
                      (canonicalWindowPacking data inputs.current.object))
                    component)
                  data.bridgeMassSlack baseline pair.1 pair.2
                omega
            · -- nonnegative: no cleared mass at all
              have nonneg := (inputs.current.object.not_negativeNetCharge_iff
                _ data.threshold data.dischargeScale).mp negative
              rw [Graph.FiniteObject.NonNegativeNetCharge] at nonneg
              omega
          -- The ordinary role also has an exact centre-by-centre cost.  Do
          -- not spend the coarse bridge factor yet: each centre contributes
          -- only `s·(d-δ)+1` to this role.
          have restExactBound : ∀ component ∈
              ((inputs.current.object.canonicalPieces
                (inputs.current.object.remainderSupport
                  (canonicalWindowPacking data inputs.current.object))) \
                route8UnifiedComponents data inputs.current.object) \
                handoffPieces,
              ((inputs.current.object.pieceSupport
                  (inputs.current.object.remainderSupport
                    (canonicalWindowPacking data inputs.current.object))
                  component).card -
                data.dischargeScale * inputs.current.object.positiveDeficiency
                  (inputs.current.object.pieceSupport
                    (inputs.current.object.remainderSupport
                      (canonicalWindowPacking data inputs.current.object))
                    component) data.threshold) ≤
              ∑ centre ∈ Graph.TypeBRefinedSupport.centres
                  inputs.current.object data.threshold
                  (inputs.current.object.pieceSupport
                    (inputs.current.object.remainderSupport
                      (canonicalWindowPacking data inputs.current.object))
                    component),
                (data.dischargeScale *
                    (inputs.current.object.degree centre - data.threshold) + 1) := by
            intro component memberRest
            have memberSdiff := Finset.mem_sdiff.mp memberRest
            have memberPieces := (Finset.mem_sdiff.mp memberSdiff.1).1
            have notUnified := (Finset.mem_sdiff.mp memberSdiff.1).2
            have notHandoff := memberSdiff.2
            let piece := inputs.current.object.pieceSupport
              (inputs.current.object.remainderSupport
                (canonicalWindowPacking data inputs.current.object)) component
            let pieceCentres := Graph.TypeBRefinedSupport.centres
              inputs.current.object data.threshold piece
            by_cases negative : inputs.current.object.NegativeNetCharge piece
                data.threshold data.dischargeScale
            · by_cases zero : inputs.current.object.ambientSurplus piece
                  data.threshold = 0
              · exfalso
                have handoff : HandoffProduced data inputs.current.object
                    (canonicalWindowPacking data inputs.current.object) piece := by
                  by_contra noHandoff
                  exact notUnified (Finset.mem_filter.mpr
                    ⟨memberPieces, zero, negative, noHandoff⟩)
                exact notHandoff ((handoffChar component).mpr
                  ⟨memberPieces, negative, zero, handoff⟩)
              · obtain ⟨routes, unsaturated⟩ :=
                  pairAt component memberPieces negative (Nat.pos_of_ne_zero zero)
                have ledger :=
                  Graph.TypeBEnvelopeCharge.neg_centreAllowance_le_augmentedLedger
                    inputs.current.object piece data.threshold
                    data.dischargeScale baseline routes unsaturated
                have identity :=
                  Graph.TypeBEnvelopeCharge.augmentedLedger_add_card_centres
                    inputs.current.object data.threshold data.dischargeScale piece
                change -(∑ centre ∈ pieceCentres,
                    ((data.dischargeScale *
                        (inputs.current.object.degree centre - data.threshold) + 2 :
                      Nat) : Int)) ≤
                    Graph.TypeBRefinedSupport.augmentedLedger
                      inputs.current.object data.threshold data.dischargeScale piece
                  at ledger
                change Graph.TypeBRefinedSupport.augmentedLedger
                      inputs.current.object data.threshold data.dischargeScale piece +
                    (pieceCentres.card : Int) =
                  ((data.dischargeScale *
                      inputs.current.object.positiveDeficiency piece
                        data.threshold : Nat) : Int) -
                    ((data.dischargeScale *
                      inputs.current.object.ambientSurplus piece
                        data.threshold : Nat) : Int) - (piece.card : Int)
                  at identity
                have allowance : (∑ centre ∈ pieceCentres,
                    ((data.dischargeScale *
                        (inputs.current.object.degree centre - data.threshold) + 2 :
                      Nat) : Int)) =
                    ((∑ centre ∈ pieceCentres,
                      (data.dischargeScale *
                        (inputs.current.object.degree centre - data.threshold) + 1) :
                      Nat) : Int) + (pieceCentres.card : Int) := by
                  push_cast
                  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
                    Finset.sum_const, Finset.sum_const, nsmul_eq_mul,
                    nsmul_eq_mul]
                  ring
                rw [allowance] at ledger
                have cardCast : (piece.card : Int) ≤
                    ((data.dischargeScale *
                      inputs.current.object.positiveDeficiency piece
                        data.threshold : Nat) : Int) +
                    ((∑ centre ∈ pieceCentres,
                      (data.dischargeScale *
                        (inputs.current.object.degree centre - data.threshold) + 1) :
                      Nat) : Int) := by
                  have surplusNonneg : (0 : Int) ≤
                      ((data.dischargeScale *
                        inputs.current.object.ambientSurplus piece
                          data.threshold : Nat) : Int) := Int.natCast_nonneg _
                  linarith [identity, ledger, surplusNonneg]
                have card : piece.card ≤
                    data.dischargeScale *
                        inputs.current.object.positiveDeficiency piece
                          data.threshold +
                      ∑ centre ∈ pieceCentres,
                        (data.dischargeScale *
                          (inputs.current.object.degree centre - data.threshold) + 1) := by
                  exact_mod_cast cardCast
                change piece.card - data.dischargeScale *
                    inputs.current.object.positiveDeficiency piece data.threshold ≤
                  ∑ centre ∈ pieceCentres,
                    (data.dischargeScale *
                      (inputs.current.object.degree centre - data.threshold) + 1)
                omega
            · have nonneg := (inputs.current.object.not_negativeNetCharge_iff
                  piece data.threshold data.dischargeScale).mp negative
              rw [Graph.FiniteObject.NonNegativeNetCharge] at nonneg
              change piece.card - data.dischargeScale *
                    inputs.current.object.positiveDeficiency piece data.threshold ≤
                  ∑ centre ∈ pieceCentres,
                    (data.dischargeScale *
                      (inputs.current.object.degree centre - data.threshold) + 1)
              omega
          -- sum the rest through the global surplus
          have restSum : (∑ component ∈
              ((inputs.current.object.canonicalPieces
                (inputs.current.object.remainderSupport
                  (canonicalWindowPacking data inputs.current.object))) \
                route8UnifiedComponents data inputs.current.object) \
                handoffPieces,
              ((inputs.current.object.pieceSupport
                  (inputs.current.object.remainderSupport
                    (canonicalWindowPacking data inputs.current.object))
                  component).card -
                data.dischargeScale * inputs.current.object.positiveDeficiency
                  (inputs.current.object.pieceSupport
                    (inputs.current.object.remainderSupport
                      (canonicalWindowPacking data inputs.current.object))
                    component) data.threshold)) ≤
              data.bridgeMassFactor * data.dischargeScale *
                inputs.current.object.degreeSurplus data.threshold := by
            calc (∑ component ∈
                ((inputs.current.object.canonicalPieces
                  (inputs.current.object.remainderSupport
                    (canonicalWindowPacking data inputs.current.object))) \
                  route8UnifiedComponents data inputs.current.object) \
                  handoffPieces,
                ((inputs.current.object.pieceSupport
                    (inputs.current.object.remainderSupport
                      (canonicalWindowPacking data inputs.current.object))
                    component).card -
                  data.dischargeScale * inputs.current.object.positiveDeficiency
                    (inputs.current.object.pieceSupport
                      (inputs.current.object.remainderSupport
                        (canonicalWindowPacking data inputs.current.object))
                      component) data.threshold)) ≤
                ∑ component ∈
                  ((inputs.current.object.canonicalPieces
                    (inputs.current.object.remainderSupport
                      (canonicalWindowPacking data inputs.current.object))) \
                    route8UnifiedComponents data inputs.current.object) \
                    handoffPieces,
                  data.bridgeMassFactor * data.dischargeScale *
                    inputs.current.object.ambientSurplus
                      (inputs.current.object.pieceSupport
                        (inputs.current.object.remainderSupport
                          (canonicalWindowPacking data inputs.current.object))
                        component) data.threshold :=
                Finset.sum_le_sum restBound
              _ ≤ ∑ component ∈ inputs.current.object.canonicalPieces
                    (inputs.current.object.remainderSupport
                      (canonicalWindowPacking data inputs.current.object)),
                  data.bridgeMassFactor * data.dischargeScale *
                    inputs.current.object.ambientSurplus
                      (inputs.current.object.pieceSupport
                        (inputs.current.object.remainderSupport
                          (canonicalWindowPacking data inputs.current.object))
                        component) data.threshold := by
                refine Finset.sum_le_sum_of_subset ?_
                intro component member
                exact (Finset.mem_sdiff.mp
                  (Finset.mem_sdiff.mp member).1).1
              _ = data.bridgeMassFactor * data.dischargeScale *
                  inputs.current.object.ambientSurplus
                    (inputs.current.object.remainderSupport
                      (canonicalWindowPacking data inputs.current.object))
                    data.threshold := by
                rw [← Finset.mul_sum,
                  Graph.FiniteObject.sum_ambientSurplus_canonicalPieces]
              _ ≤ data.bridgeMassFactor * data.dischargeScale *
                  inputs.current.object.degreeSurplus data.threshold := by
                refine Nat.mul_le_mul_left _ ?_
                letI : FinEnum inputs.current.object.Vertex :=
                  inputs.current.object.vertices
                rw [← inputs.current.object.ambientSurplus_univ_eq_degreeSurplus
                  data.threshold baseline]
                exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
          -- Shared-centre amortization.  The two old bounds above are kept as
          -- valid consequences, but they must not be added: they charge an
          -- overlapping high centre twice.  On the union of the actual
          -- ordinary and handoff centres, deliberately give every centre both
          -- exact costs.  The registered slack pays even that larger sum once.
          let support := inputs.current.object.remainderSupport
            (canonicalWindowPacking data inputs.current.object)
          let rest := ((inputs.current.object.canonicalPieces support) \
              route8UnifiedComponents data inputs.current.object) \
              handoffPieces
          let restMass := fun component :
              Graph.SupportComponents.Connected.Component
                inputs.current.object support =>
            (inputs.current.object.pieceSupport support component).card -
              data.dischargeScale * inputs.current.object.positiveDeficiency
                (inputs.current.object.pieceSupport support component)
                data.threshold
          let ordinary := Graph.TypeBRefinedSupport.centres
            inputs.current.object data.threshold support
          let allCentres := ordinary ∪ centres
          let ordinaryCost := fun centre : inputs.current.object.Vertex =>
            data.dischargeScale *
                (inputs.current.object.degree centre - data.threshold) + 1
          let handoffCost := fun centre : inputs.current.object.Vertex =>
            Graph.TypeBFanIncidence.closedCount inputs.current.object
              data.threshold (fanEnvelope centre) centre
          have centreSum (piece : Finset inputs.current.object.Vertex) :
              (∑ centre ∈ Graph.TypeBRefinedSupport.centres
                  inputs.current.object data.threshold piece,
                ordinaryCost centre) =
              ∑ vertex ∈ piece,
                if Graph.IsHighCentre inputs.current.object data.threshold vertex
                then ordinaryCost vertex else 0 := by
            unfold Graph.TypeBRefinedSupport.centres
            rw [Finset.sum_filter]
          have restSubset : rest ⊆
              inputs.current.object.canonicalPieces support := by
            intro component member
            exact (Finset.mem_sdiff.mp
              (Finset.mem_sdiff.mp member).1).1
          have restPointwise : ∀ component ∈ rest,
              restMass component ≤
                ∑ centre ∈ Graph.TypeBRefinedSupport.centres
                    inputs.current.object data.threshold
                    (inputs.current.object.pieceSupport support component),
                  ordinaryCost centre := by
            intro component member
            simp only [restMass, ordinaryCost]
            exact restExactBound component member
          have restRaw : (∑ component ∈ rest, restMass component) ≤
              ∑ centre ∈ ordinary, ordinaryCost centre := by
            calc
              (∑ component ∈ rest, restMass component) ≤
                  ∑ component ∈ rest,
                    ∑ centre ∈ Graph.TypeBRefinedSupport.centres
                        inputs.current.object data.threshold
                        (inputs.current.object.pieceSupport support component),
                      ordinaryCost centre := Finset.sum_le_sum restPointwise
              _ ≤ ∑ component ∈ inputs.current.object.canonicalPieces support,
                    ∑ centre ∈ Graph.TypeBRefinedSupport.centres
                        inputs.current.object data.threshold
                        (inputs.current.object.pieceSupport support component),
                      ordinaryCost centre :=
                    Finset.sum_le_sum_of_subset restSubset
              _ = ∑ component ∈ inputs.current.object.canonicalPieces support,
                    ∑ vertex ∈ inputs.current.object.pieceSupport support component,
                      if Graph.IsHighCentre inputs.current.object data.threshold vertex
                      then ordinaryCost vertex else 0 := by
                    apply Finset.sum_congr rfl
                    intro component _
                    exact centreSum _
              _ = ∑ vertex ∈ support,
                    if Graph.IsHighCentre inputs.current.object data.threshold vertex
                    then ordinaryCost vertex else 0 :=
                    inputs.current.object.sum_canonicalPieces support _
              _ = ∑ centre ∈ ordinary, ordinaryCost centre := by
                    unfold ordinary Graph.TypeBRefinedSupport.centres
                    rw [Finset.sum_filter]
          have ordinarySubset : ordinary ⊆ allCentres :=
            Finset.subset_union_left
          have centresSubset : centres ⊆ allCentres :=
            Finset.subset_union_right
          have ordinaryToAll : (∑ centre ∈ ordinary, ordinaryCost centre) ≤
              ∑ centre ∈ allCentres, ordinaryCost centre :=
            Finset.sum_le_sum_of_subset ordinarySubset
          have handoffToAll : (∑ centre ∈ centres, handoffCost centre) ≤
              ∑ centre ∈ allCentres, handoffCost centre :=
            Finset.sum_le_sum_of_subset centresSubset
          have allHigh : ∀ centre ∈ allCentres,
              data.threshold < inputs.current.object.degree centre := by
            intro centre member
            rcases Finset.mem_union.mp member with member | member
            · exact (Graph.TypeBRefinedSupport.mem_centres.mp member).2
            · exact high centre member
          have sharedPointwise : ∀ centre ∈ allCentres,
              handoffCost centre + ordinaryCost centre ≤
                data.bridgeMassFactor * data.dischargeScale *
                  (inputs.current.object.degree centre - data.threshold) := by
            intro centre member
            have highCentre := allHigh centre member
            have counted := Graph.TypeBFanIncidence.closedCount_le_degree
              inputs.current.object data.threshold (fanEnvelope centre) centre
            obtain ⟨surplus, degree⟩ : ∃ surplus : Nat,
                inputs.current.object.degree centre =
                  data.threshold + surplus + 1 :=
              ⟨inputs.current.object.degree centre - data.threshold - 1,
                by omega⟩
            have spent :
                (data.threshold + 2 + data.dischargeScale) * (surplus + 1) ≤
                  data.bridgeMassFactor * data.dischargeScale * (surplus + 1) :=
              Nat.mul_le_mul_right _ data.bridgeMassSlack
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
                  inputs.current.object.ambientSurplus allCentres
                    data.threshold := by
            rw [← Finset.sum_add_distrib]
            calc
              (∑ centre ∈ allCentres,
                  (handoffCost centre + ordinaryCost centre)) ≤
                  ∑ centre ∈ allCentres,
                    data.bridgeMassFactor * data.dischargeScale *
                      (inputs.current.object.degree centre - data.threshold) :=
                Finset.sum_le_sum sharedPointwise
              _ = data.bridgeMassFactor * data.dischargeScale *
                    inputs.current.object.ambientSurplus allCentres
                      data.threshold := by
                unfold Graph.FiniteObject.ambientSurplus
                rw [Finset.mul_sum]
          have globalSurplus :=
            Graph.TypeBEnvelopeCharge.ambientSurplus_le_degreeSurplus
              inputs.current.object allCentres data.threshold baseline
          have unionPaid := Nat.mul_le_mul_left
            (data.bridgeMassFactor * data.dischargeScale) globalSurplus
          change (∑ component ∈ handoffPieces, restMass component) ≤
              ∑ centre ∈ centres, handoffCost centre at handoffRaw
          have sharedSurplusSum :
              (∑ component ∈ handoffPieces, restMass component) +
                  ∑ component ∈ rest, restMass component ≤
                data.bridgeMassFactor * data.dischargeScale *
                  inputs.current.object.degreeSurplus data.threshold :=
            le_trans (Nat.add_le_add handoffRaw restRaw)
              (le_trans (Nat.add_le_add handoffToAll ordinaryToAll)
                (le_trans unionBound unionPaid))
          -- assemble: split the total mass over the three classes
          have massSplitOuter := Finset.sum_sdiff (f := fun component =>
              (inputs.current.object.pieceSupport
                  (inputs.current.object.remainderSupport
                    (canonicalWindowPacking data inputs.current.object))
                  component).card -
                data.dischargeScale * inputs.current.object.positiveDeficiency
                  (inputs.current.object.pieceSupport
                    (inputs.current.object.remainderSupport
                      (canonicalWindowPacking data inputs.current.object))
                    component) data.threshold) unifiedSubset
          have massSplitInner := Finset.sum_sdiff (f := fun component =>
              (inputs.current.object.pieceSupport
                  (inputs.current.object.remainderSupport
                    (canonicalWindowPacking data inputs.current.object))
                  component).card -
                data.dischargeScale * inputs.current.object.positiveDeficiency
                  (inputs.current.object.pieceSupport
                    (inputs.current.object.remainderSupport
                      (canonicalWindowPacking data inputs.current.object))
                    component) data.threshold) handoffSubset
          -- the unified sum is the cleared deficit itself
          have unifiedEq : (∑ component ∈
              route8UnifiedComponents data inputs.current.object,
              ((inputs.current.object.pieceSupport
                  (inputs.current.object.remainderSupport
                    (canonicalWindowPacking data inputs.current.object))
                  component).card -
                data.dischargeScale * inputs.current.object.positiveDeficiency
                  (inputs.current.object.pieceSupport
                    (inputs.current.object.remainderSupport
                      (canonicalWindowPacking data inputs.current.object))
                    component) data.threshold)) =
              Graph.TypeBEnvelopeCharge.route8Deficit inputs.current.object
                (inputs.current.object.remainderSupport
                  (canonicalWindowPacking data inputs.current.object))
                data.threshold data.dischargeScale
                (route8UnifiedComponents data inputs.current.object) := rfl
          -- the near-cubic conversion of both surplus roles
          have surplusRole : data.bridgeMassFactor * data.dischargeScale *
              inputs.current.object.degreeSurplus data.threshold ≤
              data.bridgeMassFactor * data.dischargeScale *
                data.surplusThreshold inputs.current.object.vertexCount :=
            Nat.mul_le_mul_left _ surplusCap
          -- total
          show (inputs.current.object.remainderSupport
              (canonicalWindowPacking data inputs.current.object)).card ≤
            Graph.TypeBEnvelopeCharge.route8Deficit inputs.current.object
                (inputs.current.object.remainderSupport
                  (canonicalWindowPacking data inputs.current.object))
                data.threshold data.dischargeScale
                (route8UnifiedComponents data inputs.current.object) +
              data.dischargeScale *
                (Graph.Route8Census.supply inputs.current.object
                  (canonicalWindowPacking data inputs.current.object)).card +
              data.bridgeMassFactor * data.dischargeScale *
                data.surplusThreshold inputs.current.object.vertexCount
          have totalCard : (inputs.current.object.remainderSupport
              (canonicalWindowPacking data inputs.current.object)).card ≤
              (∑ component ∈ inputs.current.object.canonicalPieces
                (inputs.current.object.remainderSupport
                  (canonicalWindowPacking data inputs.current.object)),
                data.dischargeScale * inputs.current.object.positiveDeficiency
                  (inputs.current.object.pieceSupport
                    (inputs.current.object.remainderSupport
                      (canonicalWindowPacking data inputs.current.object))
                    component) data.threshold) +
              ∑ component ∈ inputs.current.object.canonicalPieces
                (inputs.current.object.remainderSupport
                  (canonicalWindowPacking data inputs.current.object)),
                ((inputs.current.object.pieceSupport
                    (inputs.current.object.remainderSupport
                      (canonicalWindowPacking data inputs.current.object))
                    component).card -
                  data.dischargeScale * inputs.current.object.positiveDeficiency
                    (inputs.current.object.pieceSupport
                      (inputs.current.object.remainderSupport
                        (canonicalWindowPacking data inputs.current.object))
                      component) data.threshold) := by
            rw [← cardSum, ← Finset.sum_add_distrib]
            exact Finset.sum_le_sum pointwiseCard
          simp only [restMass, rest, support] at sharedSurplusSum
          omega⟩)
        .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
