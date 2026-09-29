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
`K .coldReturnCorridors`, reads every corridor through G's own cut-state
presentation `coldCutStatePresentation` (pinned in the published statement),
and performs the terminal-or-first-repeat construction locally in this atomic
executor.  Its support, offset, relational label, embedded-incidence, and
labelled-degree data are all read from the current graph.  In particular, the
former `(support.card, head ∈ support)` surrogate is absent: equal retained
values mean equal labelled embedded data for the declared coordinate.

The second representative is G's canonical representative of the retained
cut-state, read in G's own surroundings `G − Z` (`rowRepresentative`,
`CanonicalPiece.CutStateReadingAt`): the inherited boundary-degree profile, the
baseline of the completion, and the target response there.  The response clause
is the paper's "after excluding (F2), equality of cold corridor states is
equality for every target-response coordinate used by the local replacement",
read at G, where (F2) is decided (`Corridor.not_firstFailureDefect`).  No
context other than `G − Z` is read, so no all-context identification is
imported.

The separately named (F1)--(F4) consequences are committed in the same atomic
row.  Candidate overlap and mass accounting belong to
`lem:cold-germ-extraction` and are not published under this key
(`Contracts.Spine.coldCorridorState_of_corridors`). -/

@[reducible] noncomputable def coldCorridorStateRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.coldCorridorState
    { Requires := [K .coldReturnCorridors, K .hotColdPartition, K .cubicBaseline]
      Produces := [K .coldCorridorState]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .coldCorridorState)
        ⟨Contracts.Spine.coldCorridorState_of_corridors data.toParameters
          inputs.current.object inputs.current.baseline
          (five_le_windowOrder_of_labelCount data.toParameters
            (inputs.get (K .cubicBaseline)).down.1.2.2.2.2.1)
          (inputs.get (K .coldReturnCorridors)).down
          (inputs.get (K .hotColdPartition)).down⟩
        .nil)

end Hypostructure.Graph.Strategy.Spine
