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

/-- Nodes `[74]`/`[82]`, `prop:typeB-bridge-reduction`: a B2 ledger with
nonnegative remaining core gives `N₀(X) ≥ 0`. -/
@[reducible] noncomputable def typeBExcludedRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.typeBExcluded
    { Requires := []
      Produces := [K .typeBExcluded]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .typeBExcluded)
        ⟨Contracts.TypeB.typeBExcluded⟩
        .nil)

/-- Nodes `[76]`/`[85]`: a Type B support with a canonical core is negative, so its
B2 ledger leaves a negative post-ledger core; Type B carries its deficit only
through the route-`8` residual `[77]`. -/
@[reducible] noncomputable def typeBExclusionResidualRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.typeBExclusionResidual
    { Requires := [K .typeBDisjointLedger, K .typeBExcluded]
      Produces := [K .typeBExclusionResidual]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .typeBExclusionResidual)
        ⟨Contracts.TypeB.typeBExclusionResidual (inputs.get (K .typeBDisjointLedger)).down
          (inputs.get (K .typeBExcluded)).down⟩
        .nil)

end Hypostructure.Graph.Strategy.Spine
