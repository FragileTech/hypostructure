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
contrapositive form, at every negative positive-surplus canonical piece of
`P₀`: B2 at its own high centres gives its canonical B2 ledger, whose remaining
core stays negative (else the exact refinement would give `N₀ ≥ 0`), with its
post-ledger core closure, or a minimal overlap obstruction. -/
theorem typeBBridgeReduction
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (baseline : ∀ vertex : object.Vertex, data.threshold ≤ object.degree vertex)
    (uncompressible : UncompressibleStatement data object)
    (normalized : RemainderNormalizedStatement data object) :
    TypeBBridgeReductionStatement data object := by
  classical
  intro canonicalPiece negative _surplusPos
  obtain ⟨valid, maximal⟩ :=
    Contracts.RouteEight.canonicalWindowPacking_valid_maximal data object
  rcases Graph.TypeBRefinedSupport.b2_or_overlap object
      data.threshold data.dischargeScale (canonicalWindowPacking data object)
      canonicalPiece.vertices
      (Graph.TypeBRefinedSupport.centres object data.threshold
        canonicalPiece.vertices)
      (Graph.TypeBRefinedSupport.centres_high object data.threshold
        canonicalPiece.vertices) with
    choice | obstruction
  · obtain ⟨ledger, ledgerEq⟩ := canonicalTypeBDisjointChoice_spec
      ⟨choice, Graph.TypeBRefinedSupport.centres_high object data.threshold
        canonicalPiece.vertices, Finset.Subset.refl _⟩
    obtain ⟨components, grouped⟩ := disjointLedgerCoreClosure avoids baseline
      uncompressible normalized valid maximal ledger
    have notClean : ¬ 0 ≤ RemainingCoreCharge data object ledger := by
      intro clean
      exact (object.not_negativeNetCharge_iff canonicalPiece.vertices
        data.threshold data.dischargeScale).mpr
          (Graph.TypeBEnvelopeCharge.nonNegativeNetCharge_of_disjointLedger_remainingCore_nonneg
            (object := object) ledger ledger.exactAugmentedLedgerRefinement clean)
          negative
    exact Or.inl ⟨ledger, ledgerEq, ledger.exactAugmentedLedgerRefinement,
      notClean, components, grouped⟩
  · exact Or.inr obstruction

/-- `def:typeB-residual-mass`, `lem:typeB-bridge-deficit-bound`,
`lem:typeB-bridge-with-route8-core` and `lem:decorated-envelope-with-route8-core`
at the registered mass factor, on `P₀` and on its two canonical role unions. -/
theorem typeBBridgeMass
    (baseline : ∀ vertex : object.Vertex, data.threshold ≤ object.degree vertex)
    (massSlack :
      data.threshold + 2 + data.dischargeScale ≤
        data.bridgeMassFactor * data.dischargeScale) :
    TypeBBridgeMassStatement data object := by
  refine ⟨?_, ?_, ?_⟩
  · intro _component _member _piece _charge _positive
    refine ⟨fun centre _centreMember high => ?_, fun residual => ?_⟩
    · exact Graph.TypeBEnvelopeCharge.envelopeNegativePart_le _ high massSlack
    · exact Graph.TypeBEnvelopeCharge.bridgeDeficitBound object _ massSlack
        baseline residual.1 residual.2
  · intro route8 route8Surplus components
    exact Graph.TypeBEnvelopeCharge.bridgeResidualMass_le_route8 object _ route8
      massSlack baseline route8Surplus components
  · intro ordinaryRoute8 groupedRoute8 ordinarySurplus groupedSurplus
      ordinaryComponents groupedComponents
    exact Graph.TypeBEnvelopeCharge.bridgeResidualMass_le_twice object _ _
      ordinaryRoute8 groupedRoute8 massSlack baseline ordinarySurplus
      groupedSurplus ordinaryComponents groupedComponents

/-- `prop:typeB-bridge-sublinear` at the two canonical role unions of `P₀`:
with no route-`8` core extracted, the bridge residual mass of both roles is at
most twice the assigned surplus, and the near-cubic spine estimate bounds the
surplus. -/
theorem typeBBridgeSublinear
    (bridge : TypeBBridgeMassStatement data object)
    (nearCubic : SurplusAtOrBelowStatement data object) :
    TypeBBridgeSublinearStatement data object := by
  refine ⟨?_, nearCubic⟩
  intro ordinaryComponents groupedComponents
  have atMostTwice := bridge.2.2 ∅ ∅ (by simp) (by simp)
    (fun piece pieceMem _pieceNotEmpty => ordinaryComponents piece pieceMem)
    (fun piece pieceMem _pieceNotEmpty => groupedComponents piece pieceMem)
  simpa [Graph.TypeBEnvelopeCharge.route8Deficit] using atMostTwice

end Hypostructure.Graph.Contracts.TypeB
