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

/-! ## Node `[102]`, `lem:typeA-exit4-discharge`: the peel

Node `[101]`'s yes arm charged one exit-`(4)` witness.  The row inserts that
witness's unpeeled routed load into `P₄(w)`: the enlarged set is still a
witnessed peeling set inside `ℒ(w)` and the residual load `L₄(w)` has dropped
by exactly one — the integral form of the manuscript's exact quarter-charge
update. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def typeAExitFourPeelingStepRow :
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
    `Hypostructure.Graph.Strategy.Spine.typeAExitFourPeelingStep
    { Requires := [K .typeASaturatedHandoffExitFour]
      Produces := [K .typeAExitFourPeeled]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .typeAExitFourPeeled)
        (show Value BranchState Presentation presentation data
            .typeAExitFourPeeled inputs.current from ⟨by
          classical
          obtain ⟨packing, canonical, valid, maximal, component, present, negative, zero,
            receiver, isReceiver, peeled, peeledSubset, saturated, witnessed,
            source⟩ :=
            (inputs.get (K .typeASaturatedHandoffExitFour)).down
          let piece := inputs.current.object.pieceSupport
            (inputs.current.object.remainderSupport packing) component
          obtain ⟨witness, unpeeled⟩ :
              ∃ witness : Graph.ExitFour.Witness
                  (Graph.HasCycleWithLength data.LengthOK) piece data.threshold data.dischargeScale
                  receiver peeled,
                witness.load ∈ Graph.ExitFour.unpeeledLoads piece data.threshold
                  receiver peeled := by
            rcases source with visible | silent
            · obtain ⟨_package, witness, _load, _selected, _witnessEq⟩ := visible
              exact ⟨witness, witness.unpeeled⟩
            · obtain ⟨_silent, witness, _supported⟩ := silent
              exact ⟨witness, witness.unpeeled⟩
          exact ⟨packing, canonical, valid, maximal, component, present, negative, zero,
            receiver, isReceiver, peeled, peeledSubset, saturated, witnessed,
            witness, unpeeled,
            Graph.ExitFour.Witness.nextPeeled_subset_routedLoads witness
              peeledSubset,
            Graph.ExitFour.Witness.residualLoad_nextPeeled witness⟩⟩)
        .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
