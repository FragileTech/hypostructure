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

/-! ## `lem:typeA-exit4-finite-descent`, the descent principle on the ledger

`lem:typeA-saturated-handoff`, finite descent part, read at the exact selected
receiver and peeling state committed by the exit entry: whatever the retained
and terminal predicates are, the exit-`(4)` peels terminate at a terminal
retained state or at an unsaturated one.  Node `[102]`'s retest below runs the
same descent for the exit segment; node `[123]`'s large-budget pressure descent
reads this fact for the target-defect entries.  The terminal predicates are not
chosen here. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def typeAExitFourFiniteDescentRow :
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
    `Hypostructure.Graph.Strategy.Spine.typeAExitFourFiniteDescent
    { Requires := [K .typeASaturatedExitEntry]
      Produces := [K .typeAExitFourFiniteDescent]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .typeAExitFourFiniteDescent)
        (show Value BranchState Presentation presentation data
            .typeAExitFourFiniteDescent inputs.current from ⟨by
          classical
          obtain ⟨packing, canonical, valid, maximal, component, present, negative, zero,
            receiver, isReceiver, startPeeled, startInside, startSaturated,
            _startWitnessed⟩ :=
            (inputs.get (K .typeASaturatedExitEntry)).down
          let piece := inputs.current.object.pieceSupport
            (inputs.current.object.remainderSupport packing) component
          refine ⟨packing, canonical, valid, maximal, component, present, negative, zero,
            receiver, isReceiver, startPeeled, startInside, startSaturated,
            ?_⟩
          intro Retained Terminal startRetained step
          exact Graph.ExitFour.terminal_or_unsaturated_from piece
            data.threshold data.dischargeScale receiver startInside
            startRetained step⟩)
        .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
