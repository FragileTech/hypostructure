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

/- Exact finite relabelling-orbit lower bound for every support in a
normalized remainder. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def remainderRelabelingEntropyRow :
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
    `Hypostructure.Graph.Strategy.Spine.remainderRelabelingEntropy
    { Requires := [K .remainderNormalized]
      Produces := [K .remainderRelabelingEntropy]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let normalized := inputs.get (K .remainderNormalized)
      .cons (key := K .remainderRelabelingEntropy)
        (show Value BranchState Presentation presentation data
            .remainderRelabelingEntropy inputs.current from
          ⟨fun packing valid maximal support inside => by
            have windowFree : ∀ inner : Finset inputs.current.object.Vertex,
                inner ⊆ support →
                ¬ inputs.current.object.InducesWindow data.windowOrder inner := by
              intro inner innerInside
              exact (normalized.down packing valid maximal inner
                (innerInside.trans inside)).1
            have coreFree : ∀ inner : Finset inputs.current.object.Vertex,
                inner ⊆ support →
                ¬ Graph.MinimumDegreeAtLeast data.threshold
                  (inputs.current.object.induce inner) := by
              intro inner innerInside
              exact (normalized.down packing valid maximal inner
                (innerInside.trans inside)).2
            have orbit :=
              Graph.LabelledRelabeling.factorial_le_remainderStateCount_mul_stabilizer
                inputs.current.object support data.windowOrder data.threshold
                windowFree coreFree
            dsimp only at orbit
            rw [Graph.FiniteObject.positiveDeficiency_labelledInduce,
              Graph.FiniteObject.card_edgeSet_labelledInduce] at orbit
            exact orbit⟩)
        .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
