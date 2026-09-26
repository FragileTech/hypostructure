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

/-- Node `[69]`, the degree `> 4` local dichotomy on the heavy arm of `[68]`:
`cor:heavy-center-local-dichotomy` at every heavy assigned centre, with the
fan-compatible pair routed by `cor:compatible-pair-typeB-routing` and the
`k - 2` triangular ports routed by `prop:triangular-port-typeB-routing` ---
either alternative gives fan-closed ports. -/
@[reducible] noncomputable def typeBFanLocalDichotomyRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.typeBFanLocalDichotomy
    { Requires := [K .highCentreNormalForm, K .compatiblePairTypeBRouting, K .triangularPortTypeBRouting]
      Produces := [K .typeBFanLocalDichotomy]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .typeBFanLocalDichotomy)
        ⟨Contracts.TypeB.typeBFanLocalDichotomy data.three_le_threshold
          (inputs.get (K .highCentreNormalForm)).down
          (inputs.get (K .compatiblePairTypeBRouting)).down
          (inputs.get (K .triangularPortTypeBRouting)).down⟩
        .nil)

end Hypostructure.Graph.Strategy.Spine
