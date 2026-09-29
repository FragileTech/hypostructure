import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.Spine.HeavyEntryCorridor

/-!
# The retained cold corridors of G as induced paths, on `[162]`'s residual arm

Type A row over `Graph/Contracts/Spine/HeavyEntryCorridor.lean`.  It reads the retained
first-failure occurrence (`K .coldFirstFailureOccurrence`, whose corridors it speaks about)
and the window-free geometry of `P₀` (`K .windowFreeGeometry`) through `inputs.get`, and
publishes a fact of G; it decides and splits nothing.
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-- `[162]`'s residual arm: G's retained cold corridors are induced paths whose runs in
the remainder are short. -/
@[reducible] noncomputable def coldCorridorInducedRunsRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.coldCorridorInducedRuns
    { Requires := [K .coldFirstFailureOccurrence, K .windowFreeGeometry]
      Produces := [K .coldCorridorInducedRuns]
      requiresUnique := by key_fresh
      producesUnique := by key_fresh
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .coldCorridorInducedRuns)
        ⟨Contracts.Spine.HeavyEntryCorridor.coldCorridorInducedRuns_holds data.toParameters
          inputs.current.object (inputs.get (K .windowFreeGeometry)).down⟩
      .nil)

end Hypostructure.Graph.Strategy.Spine
