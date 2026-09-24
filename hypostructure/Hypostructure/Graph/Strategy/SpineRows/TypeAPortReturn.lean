import Hypostructure.Graph.Strategy.SpineVocabulary

/-! Independently compiled spine row declarations. -/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

variable [FactSystem (Input BranchState Presentation presentation data)]

/-! ## Nodes `[89]`--`[94]`: `lem:typeA-port-return`, the port non-vacuity

*"Every completion port of a Type A support has at least one anchored return.
A completion port is an oriented edge of `G`.  By `lem:bridgeless`, the
underlying edge lies on a cycle in `G`.  Removing the port edge from that cycle
leaves a simple return path in the required orientation."*

This is the fact the saturated port tests are asked under.  Without it the exit
alternatives at nodes `[95]`--`[107]` — each of the shape "some/no anchored
return of the port has property `p`" — would be satisfied vacuously by a port
carrying no returns at all, and the exit list would discharge itself.

`lem:bridgeless` is the framework's `Graph.EdgeContraction.hasReturn_of_minimal`,
and its two hypotheses are the two halves of the selection statement nodes
`[1]`--`[4]` committed.  The row reads that fact and the selected saturated
Type A support from the literal incoming ledger.  It publishes the conclusion
only for the receivers and completion ports of that selected support. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def typeAPortReturnRow :
    @AtomicStrategy (Input BranchState Presentation presentation data) _
      (instFactSystem (BranchState := BranchState)
        (Presentation := Presentation) (presentation := presentation)
        (data := data)) :=
  letI : FactSystem (Input BranchState Presentation presentation data) :=
    instFactSystem (BranchState := BranchState) (Presentation := Presentation)
      (presentation := presentation) (data := data)
  @factOnly (Input BranchState Presentation presentation data) _
    (instFactSystem (BranchState := BranchState)
      (Presentation := Presentation) (presentation := presentation)
      (data := data))
    `Hypostructure.Graph.Strategy.Spine.typeAPortReturn
    { Requires := [K .typeASaturatedReceiver, K .selection]
      Produces := [K .typeAPortReturn]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let saturated := (show Value BranchState Presentation presentation data
          .typeASaturatedReceiver inputs.current from
        inputs.get (K .typeASaturatedReceiver)).down
      let selection := (show Value BranchState Presentation presentation data
          .selection inputs.current from inputs.get (K .selection)).down
      .cons (key := K .typeAPortReturn)
        (show Value BranchState Presentation presentation data
            .typeAPortReturn inputs.current from
          ⟨by
            obtain ⟨packing, _canonical, valid, maximal, component, present, negative,
              zero, selectedReceiver, selectedIsReceiver,
              selectedSaturated⟩ := saturated
            let piece := inputs.current.object.pieceSupport
              (inputs.current.object.remainderSupport packing) component
            refine ⟨packing, valid, maximal, component, present, negative, zero,
              ⟨selectedReceiver, selectedIsReceiver, selectedSaturated⟩, ?_⟩
            intro receiver _receiverIsReceiver outside port
            exact
              Graph.VisibleEntry.exists_anchoredReturn_of_mem_completionPorts
                (LengthOK := data.LengthOK)
                (by have := data.three_le_threshold; omega)
                inputs.current.baseline selection.1 selection.2
                piece receiver outside port⟩)
        .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
