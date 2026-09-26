import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.TypeB.Certificate

/-! Independently compiled spine row declarations. -/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-- Nodes `[76]`/`[85]`: the negative post-ledger residual charged to assigned
surplus. -/
@[reducible] noncomputable def typeBExclusionResidualMassRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.typeBExclusionResidualMass
    { Requires := [K .typeBExclusionResidual]
      Produces := [K .typeBExclusionResidualMass]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .typeBExclusionResidualMass)
        ⟨Contracts.TypeB.typeBExclusionResidualMass data.bridgeMassSlack
          (inputs.get (K .typeBExclusionResidual)).down⟩
        .nil)

end Hypostructure.Graph.Strategy.Spine
