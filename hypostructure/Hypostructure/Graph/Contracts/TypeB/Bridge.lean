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
      uncompressible normalized canonicalPiece.vertices_subset_remainder ledger
    have notClean : ¬ 0 ≤ RemainingCoreCharge data object ledger := by
      intro clean
      exact (object.not_negativeNetCharge_iff canonicalPiece.vertices
        data.threshold data.dischargeScale).mpr
          (Graph.TypeBEnvelopeCharge.nonNegativeNetCharge_of_disjointLedger_remainingCore_nonneg
            (object := object) ledger ledger.exactAugmentedLedgerRefinement clean)
          negative
    exact Or.inl ⟨ledger, ledgerEq, ledger.exactAugmentedLedgerRefinement,
      notClean, components, grouped⟩
  · exact Or.inr (canonicalOverlapObstruction_spec obstruction)

/-- G's route-`8` pieces of a support carry exactly the pieces on which the Type A
routing and unsaturation pair fails: off them every piece is a bridge residual
component. -/
theorem bridgeResidual_of_not_mem_route8 {support : Finset object.Vertex}
    {piece : Graph.SupportComponents.Connected.Component object support}
    (member : piece ∈ object.canonicalPieces support)
    (notRoute8 : piece ∉ canonicalBridgeRoute8Pieces data object support) :
    Graph.TypeBEnvelopeCharge.BridgeResidualComponentAt object
      (object.pieceSupport support piece) data.threshold data.dischargeScale := by
  classical
  by_contra failure
  exact notRoute8 (by
    unfold canonicalBridgeRoute8Pieces
    exact Finset.mem_filter.mpr ⟨member, failure⟩)

/-- When every piece of a support is a bridge residual component, G's route-`8`
pieces of it are empty. -/
theorem route8Pieces_eq_empty {support : Finset object.Vertex}
    (components : ∀ piece ∈ object.canonicalPieces support,
      Graph.TypeBEnvelopeCharge.BridgeResidualComponentAt object
        (object.pieceSupport support piece) data.threshold data.dischargeScale) :
    canonicalBridgeRoute8Pieces data object support = ∅ := by
  classical
  unfold canonicalBridgeRoute8Pieces
  exact Finset.filter_eq_empty_iff.mpr fun piece member failure =>
    failure (components piece member)

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
  · intro _remainder _route8 route8Surplus
    exact Graph.TypeBEnvelopeCharge.bridgeResidualMass_le_route8 object _ _
      massSlack baseline route8Surplus
      (fun piece member notRoute8 =>
        bridgeResidual_of_not_mem_route8 member notRoute8)
  · intro _ordinaryRoute8 _groupedRoute8 ordinarySurplus groupedSurplus
    exact Graph.TypeBEnvelopeCharge.bridgeResidualMass_le_twice object _ _
      _ _ massSlack baseline ordinarySurplus groupedSurplus
      (fun piece member notRoute8 =>
        bridgeResidual_of_not_mem_route8 member notRoute8)
      (fun piece member notRoute8 =>
        bridgeResidual_of_not_mem_route8 member notRoute8)

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
  have ordinaryEmpty := route8Pieces_eq_empty ordinaryComponents
  have groupedEmpty := route8Pieces_eq_empty groupedComponents
  have atMostTwice := bridge.2.2
    (by intro piece member; simp [ordinaryEmpty] at member)
    (by intro piece member; simp [groupedEmpty] at member)
  simpa [ordinaryEmpty, groupedEmpty, Graph.TypeBEnvelopeCharge.route8Deficit]
    using atMostTwice

/-- The `[113]`-style test of `prop:typeB-bridge-sublinear`, read after the
bridge-sublinear fact at the same fixed packing `P₀` and the same canonical role
unions: the tested hypotheses hold, or they fail (the Part IX bridge-residual
state). -/
theorem typeBSublinear_split
    (_bridge : TypeBBridgeSublinearStatement data object) :
    TypeBSublinearHypotheses data object ∨
      TypeBSublinearResidualStatement data object := by
  classical
  exact em _

end Hypostructure.Graph.Contracts.TypeB
