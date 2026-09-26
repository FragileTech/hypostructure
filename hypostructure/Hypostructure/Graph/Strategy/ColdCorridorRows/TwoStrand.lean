import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.ColdIncrementArithmetic
import Hypostructure.Graph.ColdGermFamily
import Hypostructure.Graph.Strategy.ColdCorridorRows.Basic
import Hypostructure.Graph.Contracts.Spine.ColdNeutral

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-! ## Node `[167]`, `lem:two-strand-check`: the literal finite check

The genuine arm of `[163]` retains the two ambient strands and the window
segment.  This owner constructs the cycles of lengths `2ℓ` and `ℓ+d` from
those paths.  Either dyadic arm contradicts the selected graph's target
avoidance; the only produced fact is the exact finite-enumeration survivor
consumed by `[168]`. -/
@[reducible] noncomputable def twoStrandSurvivorRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.twoStrandSurvivor
    { Requires := [K .selection, K .coldGenuineSecondStrand]
      Produces := [K .coldTwoStrandSurvivor]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .coldTwoStrandSurvivor)
        ⟨Contracts.Spine.twoStrandSurvivor_of_genuine data.toParameters
          inputs.current.object data.lengthOK_iff_powerOfTwo
          (inputs.get (K .selection)).down.1
          (inputs.get (K .coldGenuineSecondStrand)).down⟩
        .nil)

@[reducible] noncomputable def symmetricPairEndpointExclusionRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.symmetricPairEndpointExclusion
    { Requires := [K .coldWindowStubStructure]
      Produces := [K .coldSymmetricPairExcluded]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .coldSymmetricPairExcluded)
        ⟨Contracts.Spine.coldSymmetricPairExcluded_of_stubStructure
          data.toParameters inputs.current.object data.threshold_eq_three
          (inputs.get (K .coldWindowStubStructure)).down⟩
        .nil)

end Hypostructure.Graph.Strategy.Spine
