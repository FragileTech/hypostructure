import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.TypeB.Entry

/-! Independently compiled spine row declarations. -/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-- Nodes `[64]`--`[65]`: the ordinary Type B support; `def:canonical-decomp`
assigns its high centres as fan centres, and it enters the common Type B entry. -/
@[reducible] noncomputable def typeBAssignedSupportRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.typeBAssignedSupport
    { Requires := [K .netChargeCap, K .typeBHighSurplus]
      Produces := [K .typeBAssignedSupport]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .typeBAssignedSupport)
        ⟨Contracts.TypeB.typeBAssignedSupport (inputs.get (K .netChargeCap)).down
          (inputs.get (K .typeBHighSurplus)).down⟩
        .nil)

/-- Node `[65]`, the ordinary entry: the Type B entry read from the assigned
support `(X₀, H(X₀))` (`K .typeBAssignedSupport`). -/
@[reducible] noncomputable def typeBAssignedEntryRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.typeBAssignedEntry
    { Requires := [K .typeBAssignedSupport]
      Produces := [K .typeBFanEntry]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .typeBFanEntry)
        ⟨Contracts.TypeB.typeBFanEntry_of_assignedSupport
          (inputs.get (K .typeBAssignedSupport)).down⟩
        .nil)

end Hypostructure.Graph.Strategy.Spine
