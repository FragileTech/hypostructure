import Hypostructure.Graph.Statements.Route8HubPieceMass

/-!
# Contracts: the mass of the negative hub pieces of the remainder (key `9803`)

Per piece, clause (i) of `TypeBSublinearHypotheses` (key `345`) makes every negative hub
piece of the remainder of `P₀` bridge-residual, and the second part of the first conjunct of
`TypeBBridgeMassStatement` (key `85`) then gives `|X| + s·σ_X ≤ s·def⁺(X) + F·s·σ_X`.  The
pieces are disjoint subsets of `R`, so `Σ σ_X ≤ σ(R)`, and on G's minimum-degree baseline
(`MinDegreeBaselineStatement`, key `minDegreeBaseline`) `σ(R) ≤ σ(G)`.
-/

namespace Hypostructure.Graph.Contracts.RouteEight

open Hypostructure
open Hypostructure.Graph
open Hypostructure.Graph.Strategy.Spine
open scoped BigOperators

universe u

/-- **Key `9803`: the hub-piece mass.** -/
theorem route8HubPieceMass (data : Parameters) (object : FiniteObject.{u})
    (h345 : TypeBSublinearHypotheses data object)
    (h85 : TypeBBridgeMassStatement data object)
    (baseline : MinDegreeBaselineStatement data object) :
    Route8HubPieceMassStatement data object := by
  classical
  unfold Route8HubPieceMassStatement
  intro remainder hubs mass
  have perPiece : ∀ component ∈ hubs,
      mass component ≤
        data.bridgeMassFactor * data.dischargeScale *
          object.ambientSurplus (object.pieceSupport remainder component) data.threshold := by
    intro component member
    have member' := member
    simp only [hubs, route8NegativeHubPieces, Finset.mem_filter] at member'
    obtain ⟨present, negative, positive⟩ := member'
    have residual := h345.1 component present negative positive
    have bound := (h85.1 component present negative positive).2 residual
    simp only [mass]
    rw [Nat.sub_le_iff_le_add']
    exact bound
  have summed : ∑ component ∈ hubs, mass component ≤
      data.bridgeMassFactor * data.dischargeScale *
        ∑ component ∈ hubs,
          object.ambientSurplus (object.pieceSupport remainder component) data.threshold := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum perPiece
  have hubSurplus : ∑ component ∈ hubs,
        object.ambientSurplus (object.pieceSupport remainder component) data.threshold ≤
      object.ambientSurplus remainder data.threshold := by
    rw [← object.sum_ambientSurplus_canonicalPieces remainder data.threshold]
    exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  have remainderSurplus :
      object.ambientSurplus remainder data.threshold ≤ object.degreeSurplus data.threshold :=
    object.ambientSurplus_le_degreeSurplus remainder data.threshold
      (fun vertex => le_trans baseline (object.minDegree_le_degree vertex))
  have total : ∑ component ∈ hubs, mass component ≤
      data.bridgeMassFactor * data.dischargeScale * object.degreeSurplus data.threshold :=
    le_trans summed (Nat.mul_le_mul_left _ (le_trans hubSurplus remainderSurplus))
  refine ⟨perPiece, summed, hubSurplus, remainderSurplus, total, ?_⟩
  omega

end Hypostructure.Graph.Contracts.RouteEight
