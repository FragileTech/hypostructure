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

/-! ## `lem:target-rank-circuit`: finite proper dependence

For a maximal surviving subfamily `𝓘` and a raw test `a ∉ 𝓘`, adjoining `a`
cannot survive every functional admissible quotient — the maximality clause of
`K .curvatureTargetRank` is what forbids it — so some functional admissible
quotient is label-injective on `𝓘` but not on `𝓘 ∪ {a}`, and its functional
clause supplies the finite determining subfamily `ℬ ⊆ 𝓘`; `a ∉ ℬ`, so the
dependence is proper.  The "in particular" is the contrapositive at a maximal
surviving family. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def targetRankCircuitRow :
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
    `Hypostructure.Graph.Strategy.Spine.targetRankCircuit
    { Requires := [K .curvatureTargetRank]
      Produces := [K .targetRankCircuit]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let rank := (inputs.get (K .curvatureTargetRank)).down
      .cons (key := K .targetRankCircuit)
        (show Value BranchState Presentation presentation data
            .targetRankCircuit inputs.current from
          ⟨fun packing valid card => by
            classical
            obtain ⟨_attained, maximal⟩ := rank packing valid card
            refine ⟨fun independent subset survives maximum test testMem outside => ?_,
              fun noDependence => ?_⟩
            · -- `𝓘 ∪ {a}` does not survive: its size would exceed `r_Ω(R)`.
              have notSurvive : ¬ Graph.FiniteObject.SurvivesCurvatureSystem
                  (Graph.MinimumDegreeAtLeast data.threshold)
                  (Graph.HasCycleWithLength data.LengthOK) inputs.current.object
                  (inputs.current.object.remainderSupport packing)
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
                  Set (inputs.current.object.InternalWedge
                    (inputs.current.object.remainderSupport packing))) =
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
                (Graph.HasCycleWithLength data.LengthOK) inputs.current.object
                (inputs.current.object.remainderSupport packing) noDependence⟩)
        .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
