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

@[reducible] noncomputable def globalBarrierRow
    (data : Data.{u}) :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.globalBarrier
    { Requires := [K .globalDelocalization]
      Produces := [K .globalBarrier]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .globalBarrier)
        (show Value BranchState Presentation presentation data
            .globalBarrier inputs.current from
          ⟨by
            dsimp only [Holds]
            obtain ⟨packing, _valid, quotient, certificate, _complete, _outside,
              covers⟩ := (inputs.get (K .globalDelocalization)).down
            obtain ⟨_test, _determiners, _supportData, certified⟩ := certificate
            have reducing : quotient.toRankQuotient.RankReducingOn
                ↑(remainderCurvatureTests inputs.current.object packing) :=
              certified.2.2.2.2.2.1
            exact quotient.closedRepresentative covers reducing⟩)
        .nil)

end Hypostructure.Graph.Strategy.Spine
