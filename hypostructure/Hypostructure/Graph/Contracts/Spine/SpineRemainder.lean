import Hypostructure.Graph.Statements.Spine

/-!
# Contracts: the packed-window remainder `[25]`--`[31]`

Proof-agnostic contract lemmas for the remainder a maximal packing leaves:
normalization, relabelling entropy, boundary demand, stub supply, the wedge
lower bound, the curvature target rank, and its finite circuit.  Each lemma is
stated over a `Graph.FiniteObject` with the registered `Parameters` as a
parameter and every hypothesis explicit; its conclusion is exactly the
statement of the fact it proves.  This module imports no strategy, row, or
vocabulary module.
-/

namespace Hypostructure.Graph.Contracts.Spine

open Hypostructure
open Hypostructure.Graph.Strategy.Spine

universe u v

/-- **Nodes `[25]`--`[27]`, `sec:remainder`.**  The remainder `R₀` of G's fixed
maximum packing `P₀` carries no induced window (it would extend the packing), and no subset
of it induces a baseline subgraph: that subgraph would be window-free, so the
cited closure law (`thm:p13free`, read at `G[S]` from `K .spinePresentationLaws`)
gives it an accepted cycle, which is a cycle of the target-avoiding object. -/
theorem remainderNormalized_of_selection
    {BranchState : Graph.FiniteObject.{u} → Type v}
    {Presentation : Type} {presentation : Presentation}
    (data : Parameters) (object : Graph.FiniteObject.{u})
    (freeForcesTarget : ∀ support : Finset object.Vertex,
      Graph.MinimumDegreeAtLeast data.threshold (object.induce support) →
      Graph.InducedPathFree (object.induce support) data.windowOrder →
      Graph.HasCycleWithLength data.LengthOK (object.induce support))
    (selection : SelectionStatement BranchState Presentation presentation data object) :
    RemainderNormalizedStatement data object :=
  fun support inside =>
    ⟨object.not_inducesWindow_of_subset_remainderSupport
        (canonicalWindowPacking_spec data object).2.2 inside,
      fun baseline => selection.1 (object.hasCycleWithLength_of_induce support
        (freeForcesTarget support baseline
          (object.inducedPathFree_induce_of_forall fun _inner contained =>
            object.not_inducesWindow_of_subset_remainderSupport
              (canonicalWindowPacking_spec data object).2.2
              (contained.trans inside))))⟩

/-- **Nodes `[28]`--`[29]`, `lem:surplus-aware-window-stub`.**  On the baseline,
`def⁺(R) ≤ e(R,W)` pointwise-summed, and the boundary incidences plus the
windows' internal mass are bounded by the windows' degree capacity.  No
near-cubic hypothesis is used. -/
theorem boundaryDemand_of_baseline (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (baseline : Graph.MinimumDegreeAtLeast data.threshold object) :
    BoundaryDemandStatement data object :=
  have lower : ∀ vertex : object.Vertex, data.threshold ≤ object.degree vertex :=
    fun vertex => le_trans baseline (object.minDegree_le_degree vertex)
  ⟨object.positiveDeficiency_le_boundaryIncidence
      (object.remainderSupport (canonicalWindowPacking data object))
      data.threshold lower,
    object.boundaryIncidence_add_internal_mass_le
      (canonicalWindowPacking_spec data object).1 lower⟩

/-- **Node `[29]`, `lem:stub-positive`.**  The boundary-demand chain with the
object's own surplus in place of the windows', and the near-cubic ceiling
`σ(G) ≤ T(n)` spent against it. -/
theorem stubSupply_of_boundaryDemand (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (baseline : Graph.MinimumDegreeAtLeast data.threshold object)
    (demand : BoundaryDemandStatement data object)
    (ceiling : SurplusAtOrBelowStatement data object) :
    StubSupplyStatement data object := by
  have lower : ∀ vertex : object.Vertex, data.threshold ≤ object.degree vertex :=
    fun vertex => le_trans baseline (object.minDegree_le_degree vertex)
  have links := demand
  have windowSurplus :=
    object.ambientSurplus_le_degreeSurplus
      (Graph.FiniteObject.windowSupport (canonicalWindowPacking data object))
      data.threshold lower
  have globalSurplus :
      object.degreeSurplus data.threshold ≤
        data.surplusThreshold object.vertexCount := ceiling
  omega

/-- **Node `[30]`, `lem:wedge-lower`.**  Every region `X` of the remainder has
`δ|X| ≤ W₂(X) + 2 def⁺(X)` (for `δ ≥ 3`), and at `X = R` the stub-supply
ceiling turns it into the demand floor of the final collision. -/
theorem wedgeSupply_of_stubSupply (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (three_le_threshold : 3 ≤ data.threshold)
    (stubSupply : StubSupplyStatement data object) :
    WedgeSupplyStatement data object := by
  have supply : ∀ support : Finset object.Vertex,
        data.threshold * support.card ≤
          object.internalWedgeCount support +
            2 * object.positiveDeficiency support data.threshold :=
    fun support =>
      object.baseline_mul_card_le_internalWedgeCount_add_two_mul_positiveDeficiency
        support data.threshold three_le_threshold
  refine ⟨fun support _inside => supply support, ?_⟩
  have wedge := supply
    (object.remainderSupport (canonicalWindowPacking data object))
  have ceiling := stubSupply
  omega

/-- **Node `[31]`, `def:curvature-target-rank`.**  At the remainder of every
maximal packing, the curvature target rank is attained by a surviving
subfamily and bounds every surviving subfamily. -/
theorem curvatureTargetRank_attained (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    CurvatureTargetRankStatement data object :=
  let packing := canonicalWindowPacking data object
  ⟨Graph.FiniteObject.exists_attaining_curvatureTargetRank
        (Graph.MinimumDegreeAtLeast data.threshold)
        (Graph.HasCycleWithLength data.LengthOK) object
        (object.remainderSupport packing),
      fun _candidate subset survives =>
        Graph.FiniteObject.card_le_curvatureTargetRank
          (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) object
          (object.remainderSupport packing) subset survives⟩

/-- **`lem:target-rank-circuit`.**  Adjoining a raw test to a maximal surviving
subfamily breaks survival, so some functional admissible quotient is injective
on the family but not on the extension, and its functional clause supplies a
finite proper determining subfamily; conversely a family with no such
dependence survives. -/
theorem targetRankCircuit_of_curvatureTargetRank (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (rank : CurvatureTargetRankStatement data object) :
    TargetRankCircuitStatement data object :=
  by
    classical
    let packing := canonicalWindowPacking data object
    obtain ⟨_attained, maximal⟩ := rank
    refine ⟨fun independent subset survives maximum test testMem outside => ?_,
      fun noDependence => ?_⟩
    · -- `𝓘 ∪ {a}` does not survive: its size would exceed `r_Ω(R)`.
      have notSurvive : ¬ Graph.FiniteObject.SurvivesCurvatureSystem
          (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) object
          (object.remainderSupport packing)
          (insert test independent) := by
        intro survivesInsert
        have le := maximal (insert test independent)
          (Finset.insert_subset testMem subset) survivesInsert
        rw [Finset.card_insert_of_notMem outside] at le
        omega
      simp only [Graph.FiniteObject.SurvivesCurvatureSystem, not_forall]
        at notSurvive
      obtain ⟨quotient, functional, notInjective⟩ := notSurvive
      have injective := survives quotient functional
      have insertCoe : (↑(insert test independent) :
          Set (object.InternalWedge
            (object.remainderSupport packing))) =
          insert test ↑independent := by simp
      rw [Core.TargetRank.RankQuotient.LabelInjectiveOn, insertCoe] at notInjective
      obtain ⟨determiners, finite, determinersSubset, determines⟩ :=
        functional (Finset.coe_subset.2 subset) testMem
          (by simpa using outside) injective notInjective
      refine ⟨determiners, determinersSubset, finite,
        fun mem => outside (determinersSubset mem), quotient, functional, ?_,
        determines⟩
      intro injectiveFamily
      exact notInjective (injectiveFamily.mono (by
        rw [← insertCoe]
        exact Finset.coe_subset.2 (Finset.insert_subset testMem subset)))
    · exact Graph.FiniteObject.survives_of_no_dependence
        (Graph.MinimumDegreeAtLeast data.threshold)
        (Graph.HasCycleWithLength data.LengthOK) object
        (object.remainderSupport packing) noDependence

end Hypostructure.Graph.Contracts.Spine
