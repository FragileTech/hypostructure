import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.TypeB.Local

/-! Independently compiled spine row declarations. -/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-- Node `[69]`, `lem:compatible-pair-fan-closure` at the Type B support of the
node-`[65]` entry, read through `def:fan-closed-port`. -/
@[reducible] noncomputable def compatiblePairFanClosureRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.compatiblePairFanClosure
    { Requires := [K .typeBFanEntry, K .surplusAtOrBelow]
      Produces := [K .compatiblePairFanClosure]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .compatiblePairFanClosure)
        ⟨Contracts.TypeB.compatiblePairFanClosure (inputs.get (K .typeBFanEntry)).down
          (inputs.get (K .surplusAtOrBelow)).down⟩
        .nil)

end Hypostructure.Graph.Strategy.Spine
