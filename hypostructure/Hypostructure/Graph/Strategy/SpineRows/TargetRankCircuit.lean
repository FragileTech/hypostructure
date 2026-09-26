import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.Spine.SpineRemainder

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
      .cons (key := K .targetRankCircuit)
        ⟨Contracts.Spine.targetRankCircuit_of_curvatureTargetRank data.toParameters
          inputs.current.object (inputs.get (K .curvatureTargetRank)).down⟩
        .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
