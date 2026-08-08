import Hypostructure.Graph.Strategy.TypeAExitRun

/-!
# Fixture: selected Type A residual wiring

This fixture instantiates the framework rows at the spine vocabulary without
importing `SpineAssembly`.  It checks the exact selected-support interfaces for
node `[62]`, node `[89]`, node `[93]`, unsaturated discharge, and exits
`(1)`--`(3)`.  It introduces no mathematical carrier or routing operation.
-/

namespace Hypostructure.Fixtures.TypeASelectedResidualWiring

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

noncomputable section

local instance : FactSystem
    (Input BranchState Presentation presentation data) :=
  factSystem BranchState Presentation presentation data

noncomputable abbrev K (keyName : Key) :
    FactKey (Input BranchState Presentation presentation data) :=
  key BranchState Presentation presentation data keyName

abbrev negativeKeys :
    FactKeys (Input BranchState Presentation presentation data) :=
  [K .negativeSupport]

noncomputable def split
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected negativeKeys) :
    Decision (K .typeALowSurplus) (K .typeBHighSurplus) history :=
  typeSplitDichotomy history (K .negativeSupport) (K .typeALowSurplus)
    (K .typeBHighSurplus) (fun fact => fact.down) (fun value => ⟨value⟩)
    (fun value => ⟨value⟩) (by simp [negativeKeys])
    (by simp [negativeKeys])

abbrev lowKeys :
    FactKeys (Input BranchState Presentation presentation data) :=
  [K .typeAReceiverRouting, K .typeALowSurplus]

noncomputable def saturation
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected lowKeys) :
    Decision (K .typeASaturatedReceiver) (K .typeAUnsaturatedReceivers)
      history :=
  typeASaturationDichotomy history (K .typeALowSurplus)
    (K .typeASaturatedReceiver) (K .typeAUnsaturatedReceivers)
    (fun fact => fact.down) (fun value => ⟨value⟩) (fun value => ⟨value⟩)
    (by simp [lowKeys]) (by simp [lowKeys])

abbrev saturatedKeys :
    FactKeys (Input BranchState Presentation presentation data) :=
  [K .typeAPortReturn, K .typeASaturatedReceiver, K .typeAReceiverRouting]

noncomputable def visible
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected saturatedKeys) :
    Decision (K .typeAVisibleEntry) (K .typeAVisibleFirstExcess) history :=
  typeAVisibleEntryDichotomy history (K .typeAReceiverRouting)
    (K .typeASaturatedReceiver) (K .typeAVisibleEntry)
    (K .typeAVisibleFirstExcess) (fun fact => fact.down)
    (fun fact => fact.down) (fun value => ⟨value⟩) (fun value => ⟨value⟩)
    (by simp [saturatedKeys]) (by simp [saturatedKeys])

noncomputable abbrev unsaturatedDischarge :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  typeAUnsaturatedDischargeRow (K .typeAReceiverRouting)
    (K .typeAUnsaturatedReceivers) (K .typeAUnsaturatedDischarge) (by simp)
    (fun _input fact => fact.down) (fun _input fact => fact.down)
    (fun _input value => ⟨value⟩)

example :
    (unsaturatedDischarge (BranchState := BranchState)
      (presentation := presentation) (data := data)).manifest.Requires =
      [K .typeAReceiverRouting, K .typeAUnsaturatedReceivers] :=
  rfl

example :
    (unsaturatedDischarge (BranchState := BranchState)
      (presentation := presentation) (data := data)).manifest.Produces =
      [K .typeAUnsaturatedDischarge] :=
  rfl

abbrev visibleExitKeys :
    FactKeys (Input BranchState Presentation presentation data) :=
  [K .typeAVisibleEntryClause, K .typeAVisibleEntry,
    K .returnAvoidance, K .selection]

end

end Hypostructure.Fixtures.TypeASelectedResidualWiring
