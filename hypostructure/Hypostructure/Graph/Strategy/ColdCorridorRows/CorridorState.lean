import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.ColdIncrementArithmetic
import Hypostructure.Graph.ColdGermFamily
import Hypostructure.Graph.Strategy.ColdCorridorRows.Basic
import Hypostructure.Graph.Contracts.Spine.ColdCorridorState

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-! ## Node `[153]`, `lem:cold-corridor-first-failure`: routing

This is the joint owner of `K .coldCorridorState` and
`K .coldFailureRouting`.  It reads the selected-stub partition from
`K .coldReturnCorridors`, constructs the current finite prefix-code
presentation from the literal corridor and its bounded active interface, and
performs the terminal-or-first-repeat construction locally in this atomic
executor.  Its support, offset, relational label, embedded-incidence, and
labelled-degree data are all read from the current graph.  In particular, the
former `(support.card, head ∈ support)` surrogate is absent: equal retained
values mean equal labelled embedded data for the declared coordinate.

The second representative is selected only from the retained finite-state
class: it preserves the inherited boundary-degree profile and baseline, while
the target response is left to the manuscript's (F2)/G2 test.  In particular
the executor does not call `CanonicalPiece.cutStateRepresentative`, whose
all-context `ContextEquivalent` field would circularly erase that alternative.

The separately named (F1)--(F4) consequences are committed in the same atomic
row.  Candidate overlap and mass accounting belong to
`lem:cold-germ-extraction` and are not published under this key
(`Contracts.Spine.coldCorridorState_of_corridors`). -/

@[reducible] noncomputable def coldCorridorStateRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.coldCorridorState
    { Requires := [K .coldReturnCorridors, K .hotColdPartition]
      Produces := [K .coldCorridorState]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .coldCorridorState)
        ⟨Contracts.Spine.coldCorridorState_of_corridors data.toParameters
          inputs.current.object inputs.current.baseline data.five_le_windowOrder
          (inputs.get (K .coldReturnCorridors)).down
          (inputs.get (K .hotColdPartition)).down⟩
        .nil)

end Hypostructure.Graph.Strategy.Spine
