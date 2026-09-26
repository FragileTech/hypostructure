import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.ColdIncrementArithmetic
import Hypostructure.Graph.ColdGermFamily
import Hypostructure.Graph.Strategy.ColdCorridorRows.Basic
import Hypostructure.Graph.Contracts.Spine.ColdMass

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-! ## Node `[153]`, `lem:cold-germ-extraction`: strict positivity

On the linear arm, the selected `9C` mass is strictly larger than the sum of
the non-ambient-window loss and the first-high incidence loss.  The exact
count and charge bound retained above therefore make the candidate family,
and hence its greedy disjoint subfamily, nonempty
(`Contracts.Spine.coldGermFamilyPositive_of_linear`). -/
@[reducible] noncomputable def coldGermFamilyPositiveRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.coldGermFamilyPositive
    { Requires := [K .coldGermCandidates, K .coldMassLinear,
        K .coldSelectedBranchExcess, K .coldStubExcess]
      Produces := [K .coldGermFamilyPositive]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .coldGermFamilyPositive)
        ⟨Contracts.Spine.coldGermFamilyPositive_of_linear data.toParameters
          inputs.current.object (inputs.get (K .coldGermCandidates)).down
          (inputs.get (K .coldMassLinear)).down
          (inputs.get (K .coldSelectedBranchExcess)).down
          (inputs.get (K .coldStubExcess)).down⟩
        .nil)

end Hypostructure.Graph.Strategy.Spine
