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

/-! ## Node `[109]` preserves the full incoming ledger prefix

The route-8 arm is an ordinary one-fact append.  These checks pin the exact
index shape: `[109]` adds `route8Residual` on top of the no-exit-`(7)` ledger
and leaves every incoming fact in the prefix available downstream.  The row's
manifest requires the finite descent, silent residual, and no-exit facts; the
framework carries them through this prefix, not through a custom payload.
-/

example {known : FactKeys (Input BranchState Presentation presentation data)} :
    route8ResidualKeys (BranchState := BranchState) (presentation := presentation)
      (data := data) known =
      K .route8Residual ::
        typeAExitSevenFreeKeys (BranchState := BranchState)
          (presentation := presentation) (data := data) known := rfl

example {known : FactKeys (Input BranchState Presentation presentation data)} :
    route8ResidualProfileKeys (BranchState := BranchState)
      (presentation := presentation) (data := data) known =
      K .route8ResidualProfile ::
        route8ResidualKeys (BranchState := BranchState)
          (presentation := presentation) (data := data) known := rfl

example {known : FactKeys (Input BranchState Presentation presentation data)} :
    route8GlobalSqueezeKeys (BranchState := BranchState)
      (presentation := presentation) (data := data) known =
      K .route8GlobalSqueeze ::
        route8ResidualProfileKeys (BranchState := BranchState)
          (presentation := presentation) (data := data) known := rfl

example {known : FactKeys (Input BranchState Presentation presentation data)} :
    route8BurdenAndDeficitKeys (BranchState := BranchState)
      (presentation := presentation) (data := data) known =
      K .route8BasinBurden :: K .route8LargeBudgetDeficit ::
        route8GlobalSqueezeKeys (BranchState := BranchState)
          (presentation := presentation) (data := data) known := rfl

example {known : FactKeys (Input BranchState Presentation presentation data)} :
    route8CarrierCoreKeys (BranchState := BranchState)
      (presentation := presentation) (data := data) known =
      K .route8CarrierCore ::
        route8BurdenAndDeficitKeys (BranchState := BranchState)
          (presentation := presentation) (data := data) known := rfl

example {known : FactKeys (Input BranchState Presentation presentation data)} :
    route8SmallCoreCollapseKeys (BranchState := BranchState)
      (presentation := presentation) (data := data) known =
      K .route8SmallCoreCollapse ::
        route8CarrierCoreKeys (BranchState := BranchState)
          (presentation := presentation) (data := data) known := rfl

example {known : FactKeys (Input BranchState Presentation presentation data)}
    {fact : FactKey (Input BranchState Presentation presentation data)}
    (member : fact ∈ known) :
    fact ∈ route8ResidualKeys (BranchState := BranchState)
      (presentation := presentation) (data := data) known := by
  simp [route8ResidualKeys, typeAExitSevenFreeKeys, typeAExitSixFreeKeys,
    member]

example {known : FactKeys (Input BranchState Presentation presentation data)}
    {fact : FactKey (Input BranchState Presentation presentation data)}
    (member : fact ∈ known) :
    fact ∈ route8ResidualProfileKeys (BranchState := BranchState)
      (presentation := presentation) (data := data) known := by
  simp [route8ResidualProfileKeys, route8ResidualKeys, typeAExitSevenFreeKeys,
    typeAExitSixFreeKeys, member]

example {known : FactKeys (Input BranchState Presentation presentation data)}
    {fact : FactKey (Input BranchState Presentation presentation data)}
    (member : fact ∈ known) :
    fact ∈ route8GlobalSqueezeKeys (BranchState := BranchState)
      (presentation := presentation) (data := data) known := by
  simp [route8GlobalSqueezeKeys, route8ResidualProfileKeys,
    route8ResidualKeys, typeAExitSevenFreeKeys, typeAExitSixFreeKeys, member]

example {known : FactKeys (Input BranchState Presentation presentation data)}
    {fact : FactKey (Input BranchState Presentation presentation data)}
    (member : fact ∈ known) :
    fact ∈ route8BurdenAndDeficitKeys (BranchState := BranchState)
      (presentation := presentation) (data := data) known := by
  simp [route8BurdenAndDeficitKeys, route8GlobalSqueezeKeys,
    route8ResidualProfileKeys, route8ResidualKeys, typeAExitSevenFreeKeys,
    typeAExitSixFreeKeys, member]

example {known : FactKeys (Input BranchState Presentation presentation data)}
    {fact : FactKey (Input BranchState Presentation presentation data)}
    (member : fact ∈ known) :
    fact ∈ route8CarrierCoreKeys (BranchState := BranchState)
      (presentation := presentation) (data := data) known := by
  simp [route8CarrierCoreKeys, route8BurdenAndDeficitKeys,
    route8GlobalSqueezeKeys, route8ResidualProfileKeys, route8ResidualKeys,
    typeAExitSevenFreeKeys, typeAExitSixFreeKeys, member]

example {known : FactKeys (Input BranchState Presentation presentation data)}
    {fact : FactKey (Input BranchState Presentation presentation data)}
    (member : fact ∈ known) :
    fact ∈ route8SmallCoreCollapseKeys (BranchState := BranchState)
      (presentation := presentation) (data := data) known := by
  simp [route8SmallCoreCollapseKeys, route8CarrierCoreKeys,
    route8BurdenAndDeficitKeys, route8GlobalSqueezeKeys,
    route8ResidualProfileKeys, route8ResidualKeys, typeAExitSevenFreeKeys,
    typeAExitSixFreeKeys, member]

example {known : FactKeys (Input BranchState Presentation presentation data)} :
    K .typeAExitSevenFree ∈
      route8ResidualKeys (BranchState := BranchState)
        (presentation := presentation) (data := data) known := by
  simp [route8ResidualKeys, typeAExitSevenFreeKeys]

example {known : FactKeys (Input BranchState Presentation presentation data)} :
    K .route8Residual ∈
      route8ResidualProfileKeys (BranchState := BranchState)
        (presentation := presentation) (data := data) known := by
  simp [route8ResidualProfileKeys]

example {known : FactKeys (Input BranchState Presentation presentation data)} :
    K .route8ResidualProfile ∈
      route8GlobalSqueezeKeys (BranchState := BranchState)
        (presentation := presentation) (data := data) known := by
  simp [route8GlobalSqueezeKeys]

example {known : FactKeys (Input BranchState Presentation presentation data)}
    (member : K .largeBudgetResidual ∈ known) :
    K .largeBudgetResidual ∈
      route8GlobalSqueezeKeys (BranchState := BranchState)
        (presentation := presentation) (data := data) known := by
  simp [route8GlobalSqueezeKeys, route8ResidualProfileKeys,
    route8ResidualKeys, typeAExitSevenFreeKeys, typeAExitSixFreeKeys, member]

example {known : FactKeys (Input BranchState Presentation presentation data)} :
    K .route8GlobalSqueeze ∈
      route8BurdenAndDeficitKeys (BranchState := BranchState)
        (presentation := presentation) (data := data) known := by
  simp [route8BurdenAndDeficitKeys]

example {known : FactKeys (Input BranchState Presentation presentation data)} :
    K .route8LargeBudgetDeficit ∈
      route8CarrierCoreKeys (BranchState := BranchState)
        (presentation := presentation) (data := data) known := by
  simp [route8CarrierCoreKeys, route8BurdenAndDeficitKeys]

example {known : FactKeys (Input BranchState Presentation presentation data)} :
    K .route8CarrierCore ∈
      route8SmallCoreCollapseKeys (BranchState := BranchState)
        (presentation := presentation) (data := data) known := by
  simp [route8SmallCoreCollapseKeys]

example {known : FactKeys (Input BranchState Presentation presentation data)} :
    K .route8LargeBudgetDeficit ∈
      route8SmallCoreCollapseKeys (BranchState := BranchState)
        (presentation := presentation) (data := data) known := by
  simp [route8SmallCoreCollapseKeys, route8CarrierCoreKeys,
    route8BurdenAndDeficitKeys]

example {known : FactKeys (Input BranchState Presentation presentation data)} :
    K .route8BasinBurden ∈
      route8CarrierCoreKeys (BranchState := BranchState)
        (presentation := presentation) (data := data) known := by
  simp [route8CarrierCoreKeys, route8BurdenAndDeficitKeys]

example {known : FactKeys (Input BranchState Presentation presentation data)} :
    K .route8BasinBurden ∈
      route8SmallCoreCollapseKeys (BranchState := BranchState)
        (presentation := presentation) (data := data) known := by
  simp [route8SmallCoreCollapseKeys, route8CarrierCoreKeys,
    route8BurdenAndDeficitKeys]

example {known : FactKeys (Input BranchState Presentation presentation data)}
    (member : K .typeAVisibleFirstExcess ∈ known) :
    K .typeAVisibleFirstExcess ∈
      route8BurdenAndDeficitKeys (BranchState := BranchState)
        (presentation := presentation) (data := data) known := by
  simp [route8BurdenAndDeficitKeys, route8GlobalSqueezeKeys,
    route8ResidualProfileKeys, route8ResidualKeys, typeAExitSevenFreeKeys,
    typeAExitSixFreeKeys, member]

example {known : FactKeys (Input BranchState Presentation presentation data)}
    (member : K .typeAVisibleFirstExcess ∈ known) :
    K .typeAVisibleFirstExcess ∈
      route8CarrierCoreKeys (BranchState := BranchState)
        (presentation := presentation) (data := data) known := by
  simp [route8CarrierCoreKeys, route8BurdenAndDeficitKeys,
    route8GlobalSqueezeKeys, route8ResidualProfileKeys, route8ResidualKeys,
    typeAExitSevenFreeKeys, typeAExitSixFreeKeys, member]

example {known : FactKeys (Input BranchState Presentation presentation data)}
    (member : K .typeAVisibleFirstExcess ∈ known) :
    K .typeAVisibleFirstExcess ∈
      route8SmallCoreCollapseKeys (BranchState := BranchState)
        (presentation := presentation) (data := data) known := by
  simp [route8SmallCoreCollapseKeys, route8CarrierCoreKeys,
    route8BurdenAndDeficitKeys, route8GlobalSqueezeKeys,
    route8ResidualProfileKeys, route8ResidualKeys, typeAExitSevenFreeKeys,
    typeAExitSixFreeKeys, member]

example {known : FactKeys (Input BranchState Presentation presentation data)} :
    K .typeAExitSixFree ∈
      route8ResidualKeys (BranchState := BranchState)
        (presentation := presentation) (data := data) known := by
  simp [route8ResidualKeys, typeAExitSevenFreeKeys, typeAExitSixFreeKeys]

example {known : FactKeys (Input BranchState Presentation presentation data)}
    (member : K .typeAExitFourFiniteDescent ∈ known) :
    K .typeAExitFourFiniteDescent ∈
      route8ResidualKeys (BranchState := BranchState)
        (presentation := presentation) (data := data) known := by
  simp [route8ResidualKeys, typeAExitSevenFreeKeys, typeAExitSixFreeKeys,
    member]

example {known : FactKeys (Input BranchState Presentation presentation data)}
    (member : K .typeASaturatedHandoffSilent ∈ known) :
    K .typeASaturatedHandoffSilent ∈
      route8ResidualKeys (BranchState := BranchState)
        (presentation := presentation) (data := data) known := by
  simp [route8ResidualKeys, typeAExitSevenFreeKeys, typeAExitSixFreeKeys,
    member]

example {known : FactKeys (Input BranchState Presentation presentation data)}
    (member : K .typeASaturatedHandoffExitFourFree ∈ known) :
    K .typeASaturatedHandoffExitFourFree ∈
      route8ResidualKeys (BranchState := BranchState)
        (presentation := presentation) (data := data) known := by
  simp [route8ResidualKeys, typeAExitSevenFreeKeys, typeAExitSixFreeKeys,
    member]

example {known : FactKeys (Input BranchState Presentation presentation data)}
    (member : K .typeAExitFiveFree ∈ known) :
    K .typeAExitFiveFree ∈
      route8ResidualKeys (BranchState := BranchState)
        (presentation := presentation) (data := data) known := by
  simp [route8ResidualKeys, typeAExitSevenFreeKeys, typeAExitSixFreeKeys,
    member]

end

end Hypostructure.Fixtures.TypeASelectedResidualWiring
