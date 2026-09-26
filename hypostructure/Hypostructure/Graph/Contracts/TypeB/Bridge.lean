import Hypostructure.Graph.Contracts.TypeB.Ledger

/-!
# Contracts: the Type B bridge

`prop:typeB-bridge-reduction` with `lem:typeB-bridge-to-overlap`,
`lem:typeB-bridge-deficit-bound`, `lem:typeB-bridge-with-route8-core`,
`lem:decorated-envelope-with-route8-core` and `prop:typeB-bridge-sublinear`.
-/

namespace Hypostructure.Graph.Contracts.TypeB

open Hypostructure
open Hypostructure.Graph.Strategy.Spine

universe u

variable {data : Parameters} {object : Graph.FiniteObject.{u}}

/-- `prop:typeB-bridge-reduction` with `lem:typeB-bridge-to-overlap`, in the
contrapositive form: at every negative positive-surplus canonical piece, B2 at
its own high centres gives a disjoint ledger whose remaining core stays
negative (else the exact refinement would give `N₀ ≥ 0`), with its post-ledger
core closure, or a minimal overlap obstruction. -/
theorem typeBBridgeReduction
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (baseline : ∀ vertex : object.Vertex, data.threshold ≤ object.degree vertex)
    (uncompressible : UncompressibleStatement data object)
    (normalized : RemainderNormalizedStatement data object) :
    TypeBBridgeReductionStatement data object := by
  classical
  intro packing valid maximal canonicalPiece negative _surplusPos
  rcases Graph.TypeBRefinedSupport.b2_or_overlap object
      data.threshold data.dischargeScale packing canonicalPiece.vertices
      (Graph.TypeBRefinedSupport.centres object data.threshold
        canonicalPiece.vertices)
      (Graph.TypeBRefinedSupport.centres_high object data.threshold
        canonicalPiece.vertices) with
    choice | obstruction
  · let ledger : Graph.TypeBRefinedSupport.DisjointLedger object data.threshold
        data.dischargeScale packing canonicalPiece.vertices
        (Graph.TypeBRefinedSupport.centres object data.threshold
          canonicalPiece.vertices) :=
      ⟨Classical.choice choice,
        Graph.TypeBRefinedSupport.centres_high object data.threshold
          canonicalPiece.vertices,
        Finset.Subset.refl _⟩
    obtain ⟨components, grouped⟩ := disjointLedgerCoreClosure avoids baseline
      uncompressible normalized valid maximal ledger
    have notClean : ¬ (0 : Int) ≤ ∑ vertex ∈ ledger.remainingCore,
        Graph.TypeBRefinedSupport.scaledCoreCharge object data.threshold
          data.dischargeScale canonicalPiece.vertices vertex := by
      intro clean
      exact (object.not_negativeNetCharge_iff canonicalPiece.vertices
        data.threshold data.dischargeScale).mpr
          (Graph.TypeBEnvelopeCharge.nonNegativeNetCharge_of_disjointLedger_remainingCore_nonneg
            (object := object) ledger ledger.exactAugmentedLedgerRefinement clean)
          negative
    exact Or.inl ⟨ledger, ledger.exactAugmentedLedgerRefinement, notClean,
      components, grouped⟩
  · exact Or.inr obstruction

/-- `def:typeB-residual-mass`, `lem:typeB-bridge-deficit-bound`,
`lem:typeB-bridge-with-route8-core` and `lem:decorated-envelope-with-route8-core`
at the registered mass factor. -/
theorem typeBBridgeMass
    (baseline : ∀ vertex : object.Vertex, data.threshold ≤ object.degree vertex)
    (massSlack :
      data.threshold + 2 + data.dischargeScale ≤
        data.bridgeMassFactor * data.dischargeScale) :
    TypeBBridgeMassStatement data object := by
  refine ⟨?_, ?_, ?_⟩
  · intro _packing _valid piece _inside _connected _charge _positive
    refine ⟨fun centre _member high envelope => ?_, fun component => ?_⟩
    · exact Graph.TypeBEnvelopeCharge.envelopeNegativePart_le _ high massSlack
    · exact Graph.TypeBEnvelopeCharge.bridgeDeficitBound object piece massSlack
        baseline component.1 component.2
  · intro packing _valid route8 route8Surplus components
    exact Graph.TypeBEnvelopeCharge.bridgeResidualMass_le_route8 object _ route8
      massSlack baseline route8Surplus components
  · intro _packing _valid ordinary grouped _ordinaryInside _groupedInside
      ordinaryRoute8 groupedRoute8 ordinarySurplus groupedSurplus
      ordinaryComponents groupedComponents
    exact Graph.TypeBEnvelopeCharge.bridgeResidualMass_le_twice object ordinary
      grouped ordinaryRoute8 groupedRoute8 massSlack baseline ordinarySurplus
      groupedSurplus ordinaryComponents groupedComponents

/-- `prop:typeB-bridge-sublinear`: with no route-`8` core extracted, the bridge
residual mass of both roles is at most twice the assigned surplus, and the
near-cubic spine estimate bounds the surplus. -/
theorem typeBBridgeSublinear
    (bridge : TypeBBridgeMassStatement data object)
    (nearCubic : SurplusAtOrBelowStatement data object) :
    TypeBBridgeSublinearStatement data object := by
  refine ⟨?_, nearCubic⟩
  intro packing valid ordinary grouped ordinaryInside groupedInside
    ordinaryComponents groupedComponents
  have atMostTwice := bridge.2.2 packing valid ordinary grouped
    ordinaryInside groupedInside ∅ ∅ (by simp) (by simp)
    (fun piece pieceMem _pieceNotEmpty => ordinaryComponents piece pieceMem)
    (fun piece pieceMem _pieceNotEmpty => groupedComponents piece pieceMem)
  simpa [Graph.TypeBEnvelopeCharge.route8Deficit] using atMostTwice

end Hypostructure.Graph.Contracts.TypeB
