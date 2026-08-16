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

/-! ## Nodes `[109]`--`[110]`: routing and the first route-8 fact

Node `[109]` is the identity routing edge on the literal no-exit-`(7)` ledger
and appends no key. Node `[110]` runs directly on that ledger and appends only
the silent-core profile. The literal list checks below expose the exact output
types of the canonical rows and the ancestry retained by `AtomicCT.run`.
-/

example {known : FactKeys (Input BranchState Presentation presentation data)} :
    (typeAExitSevenFreeKeys (BranchState := BranchState) (presentation := presentation) (data := data) known) =
      K .typeAExitSevenFree ::
        typeAExitSixFreeKeys (BranchState := BranchState)
          (presentation := presentation) (data := data) known := rfl

example {known : FactKeys (Input BranchState Presentation presentation data)} :
    (K .route8ResidualProfile :: typeAExitSevenFreeKeys (BranchState := BranchState) (presentation := presentation) (data := data) known) =
      K .route8ResidualProfile ::
        (typeAExitSevenFreeKeys (BranchState := BranchState) (presentation := presentation) (data := data) known) := rfl

example {known : FactKeys (Input BranchState Presentation presentation data)} :
    (K .route8GlobalSqueeze :: K .route8ResidualProfile :: typeAExitSevenFreeKeys (BranchState := BranchState) (presentation := presentation) (data := data) known) =
      K .route8GlobalSqueeze ::
        (K .route8ResidualProfile :: typeAExitSevenFreeKeys (BranchState := BranchState) (presentation := presentation) (data := data) known) := rfl

example {known : FactKeys (Input BranchState Presentation presentation data)} :
    (K .route8BasinBurden :: K .route8LargeBudgetDeficit :: K .route8GlobalSqueeze :: K .route8ResidualProfile :: typeAExitSevenFreeKeys (BranchState := BranchState) (presentation := presentation) (data := data) known) =
      K .route8BasinBurden :: K .route8LargeBudgetDeficit ::
        (K .route8GlobalSqueeze :: K .route8ResidualProfile :: typeAExitSevenFreeKeys (BranchState := BranchState) (presentation := presentation) (data := data) known) := rfl

example {known : FactKeys (Input BranchState Presentation presentation data)} :
    (K .route8CarrierCore :: K .route8BasinBurden :: K .route8LargeBudgetDeficit :: K .route8GlobalSqueeze :: K .route8ResidualProfile :: typeAExitSevenFreeKeys (BranchState := BranchState) (presentation := presentation) (data := data) known) =
      K .route8CarrierCore ::
        (K .route8BasinBurden :: K .route8LargeBudgetDeficit :: K .route8GlobalSqueeze :: K .route8ResidualProfile :: typeAExitSevenFreeKeys (BranchState := BranchState) (presentation := presentation) (data := data) known) := rfl

example {known : FactKeys (Input BranchState Presentation presentation data)} :
    (K .route8SmallCoreCollapse :: K .route8CarrierCore :: K .route8BasinBurden :: K .route8LargeBudgetDeficit :: K .route8GlobalSqueeze :: K .route8ResidualProfile :: typeAExitSevenFreeKeys (BranchState := BranchState) (presentation := presentation) (data := data) known) =
      K .route8SmallCoreCollapse ::
        (K .route8CarrierCore :: K .route8BasinBurden :: K .route8LargeBudgetDeficit :: K .route8GlobalSqueeze :: K .route8ResidualProfile :: typeAExitSevenFreeKeys (BranchState := BranchState) (presentation := presentation) (data := data) known) := rfl

example {known : FactKeys (Input BranchState Presentation presentation data)} :
    (K .route8TwoCarrierReduction :: K .route8SmallCoreCollapse :: K .route8CarrierCore :: K .route8BasinBurden :: K .route8LargeBudgetDeficit :: K .route8GlobalSqueeze :: K .route8ResidualProfile :: typeAExitSevenFreeKeys (BranchState := BranchState) (presentation := presentation) (data := data) known) =
      K .route8TwoCarrierReduction ::
        (K .route8SmallCoreCollapse :: K .route8CarrierCore :: K .route8BasinBurden :: K .route8LargeBudgetDeficit :: K .route8GlobalSqueeze :: K .route8ResidualProfile :: typeAExitSevenFreeKeys (BranchState := BranchState) (presentation := presentation) (data := data) known) := rfl

example {known : FactKeys (Input BranchState Presentation presentation data)} :
    (K .route8CarrierDeletionWitnesses :: K .route8TwoCarrierReduction :: K .route8SmallCoreCollapse :: K .route8CarrierCore :: K .route8BasinBurden :: K .route8LargeBudgetDeficit :: K .route8GlobalSqueeze :: K .route8ResidualProfile :: typeAExitSevenFreeKeys (BranchState := BranchState) (presentation := presentation) (data := data) known) =
      K .route8CarrierDeletionWitnesses ::
        (K .route8TwoCarrierReduction :: K .route8SmallCoreCollapse :: K .route8CarrierCore :: K .route8BasinBurden :: K .route8LargeBudgetDeficit :: K .route8GlobalSqueeze :: K .route8ResidualProfile :: typeAExitSevenFreeKeys (BranchState := BranchState) (presentation := presentation) (data := data) known) := rfl

example {known : FactKeys (Input BranchState Presentation presentation data)} :
    (K .route8PrivateCarrierBudget :: K .route8NoTwoCarrierContradiction :: K .route8CarrierDeletionWitnesses :: K .route8TwoCarrierReduction :: K .route8SmallCoreCollapse :: K .route8CarrierCore :: K .route8BasinBurden :: K .route8LargeBudgetDeficit :: K .route8GlobalSqueeze :: K .route8ResidualProfile :: typeAExitSevenFreeKeys (BranchState := BranchState) (presentation := presentation) (data := data) known) =
      K .route8PrivateCarrierBudget :: K .route8NoTwoCarrierContradiction ::
        (K .route8CarrierDeletionWitnesses :: K .route8TwoCarrierReduction :: K .route8SmallCoreCollapse :: K .route8CarrierCore :: K .route8BasinBurden :: K .route8LargeBudgetDeficit :: K .route8GlobalSqueeze :: K .route8ResidualProfile :: typeAExitSevenFreeKeys (BranchState := BranchState) (presentation := presentation) (data := data) known) := rfl

example {known : FactKeys (Input BranchState Presentation presentation data)} :
    (K .route8PressureDescent :: K .route8PrivateCarrierBudget :: K .route8NoTwoCarrierContradiction :: K .route8CarrierDeletionWitnesses :: K .route8TwoCarrierReduction :: K .route8SmallCoreCollapse :: K .route8CarrierCore :: K .route8BasinBurden :: K .route8LargeBudgetDeficit :: K .route8GlobalSqueeze :: K .route8ResidualProfile :: typeAExitSevenFreeKeys (BranchState := BranchState) (presentation := presentation) (data := data) known) =
      K .route8PressureDescent ::
        (K .route8PrivateCarrierBudget :: K .route8NoTwoCarrierContradiction :: K .route8CarrierDeletionWitnesses :: K .route8TwoCarrierReduction :: K .route8SmallCoreCollapse :: K .route8CarrierCore :: K .route8BasinBurden :: K .route8LargeBudgetDeficit :: K .route8GlobalSqueeze :: K .route8ResidualProfile :: typeAExitSevenFreeKeys (BranchState := BranchState) (presentation := presentation) (data := data) known) := rfl

example {known : FactKeys (Input BranchState Presentation presentation data)} :
    (K .route8TerminalNoGo :: K .route8PressureDescent :: K .route8PrivateCarrierBudget :: K .route8NoTwoCarrierContradiction :: K .route8CarrierDeletionWitnesses :: K .route8TwoCarrierReduction :: K .route8SmallCoreCollapse :: K .route8CarrierCore :: K .route8BasinBurden :: K .route8LargeBudgetDeficit :: K .route8GlobalSqueeze :: K .route8ResidualProfile :: typeAExitSevenFreeKeys (BranchState := BranchState) (presentation := presentation) (data := data) known) =
      K .route8TerminalNoGo ::
        (K .route8PressureDescent :: K .route8PrivateCarrierBudget :: K .route8NoTwoCarrierContradiction :: K .route8CarrierDeletionWitnesses :: K .route8TwoCarrierReduction :: K .route8SmallCoreCollapse :: K .route8CarrierCore :: K .route8BasinBurden :: K .route8LargeBudgetDeficit :: K .route8GlobalSqueeze :: K .route8ResidualProfile :: typeAExitSevenFreeKeys (BranchState := BranchState) (presentation := presentation) (data := data) known) := rfl

example {known : FactKeys (Input BranchState Presentation presentation data)}
    {fact : FactKey (Input BranchState Presentation presentation data)}
    (member : fact ∈ known) :
    fact ∈ (typeAExitSevenFreeKeys (BranchState := BranchState) (presentation := presentation) (data := data) known) := by
  simp [typeAExitSevenFreeKeys, typeAExitSixFreeKeys,
    member]

example {known : FactKeys (Input BranchState Presentation presentation data)}
    {fact : FactKey (Input BranchState Presentation presentation data)}
    (member : fact ∈ known) :
    fact ∈ (K .route8ResidualProfile :: typeAExitSevenFreeKeys (BranchState := BranchState) (presentation := presentation) (data := data) known) := by
  simp [typeAExitSevenFreeKeys,
    typeAExitSixFreeKeys, member]

example {known : FactKeys (Input BranchState Presentation presentation data)}
    {fact : FactKey (Input BranchState Presentation presentation data)}
    (member : fact ∈ known) :
    fact ∈ (K .route8GlobalSqueeze :: K .route8ResidualProfile :: typeAExitSevenFreeKeys (BranchState := BranchState) (presentation := presentation) (data := data) known) := by
  simp [typeAExitSevenFreeKeys, typeAExitSixFreeKeys, member]

example {known : FactKeys (Input BranchState Presentation presentation data)}
    {fact : FactKey (Input BranchState Presentation presentation data)}
    (member : fact ∈ known) :
    fact ∈ (K .route8BasinBurden :: K .route8LargeBudgetDeficit :: K .route8GlobalSqueeze :: K .route8ResidualProfile :: typeAExitSevenFreeKeys (BranchState := BranchState) (presentation := presentation) (data := data) known) := by
  simp [typeAExitSevenFreeKeys,
    typeAExitSixFreeKeys, member]

example {known : FactKeys (Input BranchState Presentation presentation data)}
    {fact : FactKey (Input BranchState Presentation presentation data)}
    (member : fact ∈ known) :
    fact ∈ (K .route8CarrierCore :: K .route8BasinBurden :: K .route8LargeBudgetDeficit :: K .route8GlobalSqueeze :: K .route8ResidualProfile :: typeAExitSevenFreeKeys (BranchState := BranchState) (presentation := presentation) (data := data) known) := by
  simp [typeAExitSevenFreeKeys, typeAExitSixFreeKeys, member]

example {known : FactKeys (Input BranchState Presentation presentation data)}
    {fact : FactKey (Input BranchState Presentation presentation data)}
    (member : fact ∈ known) :
    fact ∈ (K .route8SmallCoreCollapse :: K .route8CarrierCore :: K .route8BasinBurden :: K .route8LargeBudgetDeficit :: K .route8GlobalSqueeze :: K .route8ResidualProfile :: typeAExitSevenFreeKeys (BranchState := BranchState) (presentation := presentation) (data := data) known) := by
  simp [typeAExitSevenFreeKeys,
    typeAExitSixFreeKeys, member]

example {known : FactKeys (Input BranchState Presentation presentation data)}
    {fact : FactKey (Input BranchState Presentation presentation data)}
    (member : fact ∈ known) :
    fact ∈ (K .route8TwoCarrierReduction :: K .route8SmallCoreCollapse :: K .route8CarrierCore :: K .route8BasinBurden :: K .route8LargeBudgetDeficit :: K .route8GlobalSqueeze :: K .route8ResidualProfile :: typeAExitSevenFreeKeys (BranchState := BranchState) (presentation := presentation) (data := data) known) := by
  simp [typeAExitSevenFreeKeys, typeAExitSixFreeKeys, member]

example {known : FactKeys (Input BranchState Presentation presentation data)}
    {fact : FactKey (Input BranchState Presentation presentation data)}
    (member : fact ∈ known) :
    fact ∈ (K .route8CarrierDeletionWitnesses :: K .route8TwoCarrierReduction :: K .route8SmallCoreCollapse :: K .route8CarrierCore :: K .route8BasinBurden :: K .route8LargeBudgetDeficit :: K .route8GlobalSqueeze :: K .route8ResidualProfile :: typeAExitSevenFreeKeys (BranchState := BranchState) (presentation := presentation) (data := data) known) := by
  simp [typeAExitSevenFreeKeys,
    typeAExitSixFreeKeys, member]

example {known : FactKeys (Input BranchState Presentation presentation data)}
    {fact : FactKey (Input BranchState Presentation presentation data)}
    (member : fact ∈ known) :
    fact ∈ (K .route8PrivateCarrierBudget :: K .route8NoTwoCarrierContradiction :: K .route8CarrierDeletionWitnesses :: K .route8TwoCarrierReduction :: K .route8SmallCoreCollapse :: K .route8CarrierCore :: K .route8BasinBurden :: K .route8LargeBudgetDeficit :: K .route8GlobalSqueeze :: K .route8ResidualProfile :: typeAExitSevenFreeKeys (BranchState := BranchState) (presentation := presentation) (data := data) known) := by
  simp [typeAExitSevenFreeKeys,
    typeAExitSixFreeKeys, member]

example {known : FactKeys (Input BranchState Presentation presentation data)}
    {fact : FactKey (Input BranchState Presentation presentation data)}
    (member : fact ∈ known) :
    fact ∈ (K .route8PressureDescent :: K .route8PrivateCarrierBudget :: K .route8NoTwoCarrierContradiction :: K .route8CarrierDeletionWitnesses :: K .route8TwoCarrierReduction :: K .route8SmallCoreCollapse :: K .route8CarrierCore :: K .route8BasinBurden :: K .route8LargeBudgetDeficit :: K .route8GlobalSqueeze :: K .route8ResidualProfile :: typeAExitSevenFreeKeys (BranchState := BranchState) (presentation := presentation) (data := data) known) := by
  simp [typeAExitSevenFreeKeys,
    typeAExitSixFreeKeys, member]

example {known : FactKeys (Input BranchState Presentation presentation data)}
    {fact : FactKey (Input BranchState Presentation presentation data)}
    (member : fact ∈ known) :
    fact ∈ (K .route8TerminalNoGo :: K .route8PressureDescent :: K .route8PrivateCarrierBudget :: K .route8NoTwoCarrierContradiction :: K .route8CarrierDeletionWitnesses :: K .route8TwoCarrierReduction :: K .route8SmallCoreCollapse :: K .route8CarrierCore :: K .route8BasinBurden :: K .route8LargeBudgetDeficit :: K .route8GlobalSqueeze :: K .route8ResidualProfile :: typeAExitSevenFreeKeys (BranchState := BranchState) (presentation := presentation) (data := data) known) := by
  simp [typeAExitSevenFreeKeys, typeAExitSixFreeKeys, member]

example {known : FactKeys (Input BranchState Presentation presentation data)} :
    K .typeAExitSevenFree ∈
      (typeAExitSevenFreeKeys (BranchState := BranchState) (presentation := presentation) (data := data) known) := by
  simp [typeAExitSevenFreeKeys]

example {known : FactKeys (Input BranchState Presentation presentation data)} :
    K .typeAExitSevenFree ∈
      (K .route8ResidualProfile :: typeAExitSevenFreeKeys (BranchState := BranchState) (presentation := presentation) (data := data) known) := by
  simp

example {known : FactKeys (Input BranchState Presentation presentation data)} :
    K .route8ResidualProfile ∈
      (K .route8GlobalSqueeze :: K .route8ResidualProfile :: typeAExitSevenFreeKeys (BranchState := BranchState) (presentation := presentation) (data := data) known) := by
  simp

example {known : FactKeys (Input BranchState Presentation presentation data)}
    (member : K .largeBudgetResidual ∈ known) :
    K .largeBudgetResidual ∈
      (K .route8GlobalSqueeze :: K .route8ResidualProfile :: typeAExitSevenFreeKeys (BranchState := BranchState) (presentation := presentation) (data := data) known) := by
  simp [typeAExitSevenFreeKeys, typeAExitSixFreeKeys, member]

example {known : FactKeys (Input BranchState Presentation presentation data)} :
    K .route8GlobalSqueeze ∈
      (K .route8BasinBurden :: K .route8LargeBudgetDeficit :: K .route8GlobalSqueeze :: K .route8ResidualProfile :: typeAExitSevenFreeKeys (BranchState := BranchState) (presentation := presentation) (data := data) known) := by
  simp

example {known : FactKeys (Input BranchState Presentation presentation data)} :
    K .route8LargeBudgetDeficit ∈
      (K .route8CarrierCore :: K .route8BasinBurden :: K .route8LargeBudgetDeficit :: K .route8GlobalSqueeze :: K .route8ResidualProfile :: typeAExitSevenFreeKeys (BranchState := BranchState) (presentation := presentation) (data := data) known) := by
  simp

example {known : FactKeys (Input BranchState Presentation presentation data)} :
    K .route8CarrierCore ∈
      (K .route8SmallCoreCollapse :: K .route8CarrierCore :: K .route8BasinBurden :: K .route8LargeBudgetDeficit :: K .route8GlobalSqueeze :: K .route8ResidualProfile :: typeAExitSevenFreeKeys (BranchState := BranchState) (presentation := presentation) (data := data) known) := by
  simp

example {known : FactKeys (Input BranchState Presentation presentation data)} :
    K .route8SmallCoreCollapse ∈
      (K .route8TwoCarrierReduction :: K .route8SmallCoreCollapse :: K .route8CarrierCore :: K .route8BasinBurden :: K .route8LargeBudgetDeficit :: K .route8GlobalSqueeze :: K .route8ResidualProfile :: typeAExitSevenFreeKeys (BranchState := BranchState) (presentation := presentation) (data := data) known) := by
  simp

example {known : FactKeys (Input BranchState Presentation presentation data)} :
    K .route8TwoCarrierReduction ∈
      (K .route8CarrierDeletionWitnesses :: K .route8TwoCarrierReduction :: K .route8SmallCoreCollapse :: K .route8CarrierCore :: K .route8BasinBurden :: K .route8LargeBudgetDeficit :: K .route8GlobalSqueeze :: K .route8ResidualProfile :: typeAExitSevenFreeKeys (BranchState := BranchState) (presentation := presentation) (data := data) known) := by
  simp

example {known : FactKeys (Input BranchState Presentation presentation data)} :
    K .route8CarrierDeletionWitnesses ∈
      (K .route8CarrierDeletionWitnesses :: K .route8TwoCarrierReduction :: K .route8SmallCoreCollapse :: K .route8CarrierCore :: K .route8BasinBurden :: K .route8LargeBudgetDeficit :: K .route8GlobalSqueeze :: K .route8ResidualProfile :: typeAExitSevenFreeKeys (BranchState := BranchState) (presentation := presentation) (data := data) known) := by
  simp

example {known : FactKeys (Input BranchState Presentation presentation data)} :
    K .route8PrivateCarrierBudget ∈
      (K .route8PrivateCarrierBudget :: K .route8NoTwoCarrierContradiction :: K .route8CarrierDeletionWitnesses :: K .route8TwoCarrierReduction :: K .route8SmallCoreCollapse :: K .route8CarrierCore :: K .route8BasinBurden :: K .route8LargeBudgetDeficit :: K .route8GlobalSqueeze :: K .route8ResidualProfile :: typeAExitSevenFreeKeys (BranchState := BranchState) (presentation := presentation) (data := data) known) := by
  simp

example {known : FactKeys (Input BranchState Presentation presentation data)} :
    K .route8NoTwoCarrierContradiction ∈
      (K .route8PrivateCarrierBudget :: K .route8NoTwoCarrierContradiction :: K .route8CarrierDeletionWitnesses :: K .route8TwoCarrierReduction :: K .route8SmallCoreCollapse :: K .route8CarrierCore :: K .route8BasinBurden :: K .route8LargeBudgetDeficit :: K .route8GlobalSqueeze :: K .route8ResidualProfile :: typeAExitSevenFreeKeys (BranchState := BranchState) (presentation := presentation) (data := data) known) := by
  simp

example {known : FactKeys (Input BranchState Presentation presentation data)} :
    K .route8PressureDescent ∈
      (K .route8PressureDescent :: K .route8PrivateCarrierBudget :: K .route8NoTwoCarrierContradiction :: K .route8CarrierDeletionWitnesses :: K .route8TwoCarrierReduction :: K .route8SmallCoreCollapse :: K .route8CarrierCore :: K .route8BasinBurden :: K .route8LargeBudgetDeficit :: K .route8GlobalSqueeze :: K .route8ResidualProfile :: typeAExitSevenFreeKeys (BranchState := BranchState) (presentation := presentation) (data := data) known) := by
  simp

example {known : FactKeys (Input BranchState Presentation presentation data)} :
    K .route8TerminalNoGo ∈
      (K .route8TerminalNoGo :: K .route8PressureDescent :: K .route8PrivateCarrierBudget :: K .route8NoTwoCarrierContradiction :: K .route8CarrierDeletionWitnesses :: K .route8TwoCarrierReduction :: K .route8SmallCoreCollapse :: K .route8CarrierCore :: K .route8BasinBurden :: K .route8LargeBudgetDeficit :: K .route8GlobalSqueeze :: K .route8ResidualProfile :: typeAExitSevenFreeKeys (BranchState := BranchState) (presentation := presentation) (data := data) known) := by
  simp

example {known : FactKeys (Input BranchState Presentation presentation data)} :
    K .route8PressureDescent ∈
      (K .route8TerminalNoGo :: K .route8PressureDescent :: K .route8PrivateCarrierBudget :: K .route8NoTwoCarrierContradiction :: K .route8CarrierDeletionWitnesses :: K .route8TwoCarrierReduction :: K .route8SmallCoreCollapse :: K .route8CarrierCore :: K .route8BasinBurden :: K .route8LargeBudgetDeficit :: K .route8GlobalSqueeze :: K .route8ResidualProfile :: typeAExitSevenFreeKeys (BranchState := BranchState) (presentation := presentation) (data := data) known) := by
  simp

example {known : FactKeys (Input BranchState Presentation presentation data)} :
    K .route8NoTwoCarrierContradiction ∈
      (K .route8PressureDescent :: K .route8PrivateCarrierBudget :: K .route8NoTwoCarrierContradiction :: K .route8CarrierDeletionWitnesses :: K .route8TwoCarrierReduction :: K .route8SmallCoreCollapse :: K .route8CarrierCore :: K .route8BasinBurden :: K .route8LargeBudgetDeficit :: K .route8GlobalSqueeze :: K .route8ResidualProfile :: typeAExitSevenFreeKeys (BranchState := BranchState) (presentation := presentation) (data := data) known) := by
  simp

example {known : FactKeys (Input BranchState Presentation presentation data)} :
    K .route8CarrierDeletionWitnesses ∈
      (K .route8PrivateCarrierBudget :: K .route8NoTwoCarrierContradiction :: K .route8CarrierDeletionWitnesses :: K .route8TwoCarrierReduction :: K .route8SmallCoreCollapse :: K .route8CarrierCore :: K .route8BasinBurden :: K .route8LargeBudgetDeficit :: K .route8GlobalSqueeze :: K .route8ResidualProfile :: typeAExitSevenFreeKeys (BranchState := BranchState) (presentation := presentation) (data := data) known) := by
  simp

example {known : FactKeys (Input BranchState Presentation presentation data)} :
    K .route8CarrierDeletionWitnesses ∈
      (K .route8PressureDescent :: K .route8PrivateCarrierBudget :: K .route8NoTwoCarrierContradiction :: K .route8CarrierDeletionWitnesses :: K .route8TwoCarrierReduction :: K .route8SmallCoreCollapse :: K .route8CarrierCore :: K .route8BasinBurden :: K .route8LargeBudgetDeficit :: K .route8GlobalSqueeze :: K .route8ResidualProfile :: typeAExitSevenFreeKeys (BranchState := BranchState) (presentation := presentation) (data := data) known) := by
  simp

example {known : FactKeys (Input BranchState Presentation presentation data)} :
    K .route8CarrierCore ∈
      (K .route8TwoCarrierReduction :: K .route8SmallCoreCollapse :: K .route8CarrierCore :: K .route8BasinBurden :: K .route8LargeBudgetDeficit :: K .route8GlobalSqueeze :: K .route8ResidualProfile :: typeAExitSevenFreeKeys (BranchState := BranchState) (presentation := presentation) (data := data) known) := by
  simp

example {known : FactKeys (Input BranchState Presentation presentation data)} :
    K .route8CarrierCore ∈
      (K .route8CarrierDeletionWitnesses :: K .route8TwoCarrierReduction :: K .route8SmallCoreCollapse :: K .route8CarrierCore :: K .route8BasinBurden :: K .route8LargeBudgetDeficit :: K .route8GlobalSqueeze :: K .route8ResidualProfile :: typeAExitSevenFreeKeys (BranchState := BranchState) (presentation := presentation) (data := data) known) := by
  simp

example {known : FactKeys (Input BranchState Presentation presentation data)} :
    K .route8CarrierCore ∈
      (K .route8PrivateCarrierBudget :: K .route8NoTwoCarrierContradiction :: K .route8CarrierDeletionWitnesses :: K .route8TwoCarrierReduction :: K .route8SmallCoreCollapse :: K .route8CarrierCore :: K .route8BasinBurden :: K .route8LargeBudgetDeficit :: K .route8GlobalSqueeze :: K .route8ResidualProfile :: typeAExitSevenFreeKeys (BranchState := BranchState) (presentation := presentation) (data := data) known) := by
  simp

example {known : FactKeys (Input BranchState Presentation presentation data)} :
    K .route8LargeBudgetDeficit ∈
      (K .route8SmallCoreCollapse :: K .route8CarrierCore :: K .route8BasinBurden :: K .route8LargeBudgetDeficit :: K .route8GlobalSqueeze :: K .route8ResidualProfile :: typeAExitSevenFreeKeys (BranchState := BranchState) (presentation := presentation) (data := data) known) := by
  simp

example {known : FactKeys (Input BranchState Presentation presentation data)} :
    K .route8BasinBurden ∈
      (K .route8CarrierCore :: K .route8BasinBurden :: K .route8LargeBudgetDeficit :: K .route8GlobalSqueeze :: K .route8ResidualProfile :: typeAExitSevenFreeKeys (BranchState := BranchState) (presentation := presentation) (data := data) known) := by
  simp

example {known : FactKeys (Input BranchState Presentation presentation data)} :
    K .route8BasinBurden ∈
      (K .route8SmallCoreCollapse :: K .route8CarrierCore :: K .route8BasinBurden :: K .route8LargeBudgetDeficit :: K .route8GlobalSqueeze :: K .route8ResidualProfile :: typeAExitSevenFreeKeys (BranchState := BranchState) (presentation := presentation) (data := data) known) := by
  simp

example {known : FactKeys (Input BranchState Presentation presentation data)}
    (member : K .typeAVisibleFirstExcess ∈ known) :
    K .typeAVisibleFirstExcess ∈
      (K .route8BasinBurden :: K .route8LargeBudgetDeficit :: K .route8GlobalSqueeze :: K .route8ResidualProfile :: typeAExitSevenFreeKeys (BranchState := BranchState) (presentation := presentation) (data := data) known) := by
  simp [typeAExitSevenFreeKeys,
    typeAExitSixFreeKeys, member]

example {known : FactKeys (Input BranchState Presentation presentation data)}
    (member : K .typeAVisibleFirstExcess ∈ known) :
    K .typeAVisibleFirstExcess ∈
      (K .route8CarrierCore :: K .route8BasinBurden :: K .route8LargeBudgetDeficit :: K .route8GlobalSqueeze :: K .route8ResidualProfile :: typeAExitSevenFreeKeys (BranchState := BranchState) (presentation := presentation) (data := data) known) := by
  simp [typeAExitSevenFreeKeys, typeAExitSixFreeKeys, member]

example {known : FactKeys (Input BranchState Presentation presentation data)}
    (member : K .typeAVisibleFirstExcess ∈ known) :
    K .typeAVisibleFirstExcess ∈
      (K .route8SmallCoreCollapse :: K .route8CarrierCore :: K .route8BasinBurden :: K .route8LargeBudgetDeficit :: K .route8GlobalSqueeze :: K .route8ResidualProfile :: typeAExitSevenFreeKeys (BranchState := BranchState) (presentation := presentation) (data := data) known) := by
  simp [typeAExitSevenFreeKeys,
    typeAExitSixFreeKeys, member]

example {known : FactKeys (Input BranchState Presentation presentation data)}
    (member : K .typeAVisibleFirstExcess ∈ known) :
    K .typeAVisibleFirstExcess ∈
      (K .route8TwoCarrierReduction :: K .route8SmallCoreCollapse :: K .route8CarrierCore :: K .route8BasinBurden :: K .route8LargeBudgetDeficit :: K .route8GlobalSqueeze :: K .route8ResidualProfile :: typeAExitSevenFreeKeys (BranchState := BranchState) (presentation := presentation) (data := data) known) := by
  simp [typeAExitSevenFreeKeys, typeAExitSixFreeKeys, member]

example {known : FactKeys (Input BranchState Presentation presentation data)}
    (member : K .typeAVisibleFirstExcess ∈ known) :
    K .typeAVisibleFirstExcess ∈
      (K .route8CarrierDeletionWitnesses :: K .route8TwoCarrierReduction :: K .route8SmallCoreCollapse :: K .route8CarrierCore :: K .route8BasinBurden :: K .route8LargeBudgetDeficit :: K .route8GlobalSqueeze :: K .route8ResidualProfile :: typeAExitSevenFreeKeys (BranchState := BranchState) (presentation := presentation) (data := data) known) := by
  simp [typeAExitSevenFreeKeys,
    typeAExitSixFreeKeys, member]

example {known : FactKeys (Input BranchState Presentation presentation data)}
    (member : K .typeAVisibleFirstExcess ∈ known) :
    K .typeAVisibleFirstExcess ∈
      (K .route8PrivateCarrierBudget :: K .route8NoTwoCarrierContradiction :: K .route8CarrierDeletionWitnesses :: K .route8TwoCarrierReduction :: K .route8SmallCoreCollapse :: K .route8CarrierCore :: K .route8BasinBurden :: K .route8LargeBudgetDeficit :: K .route8GlobalSqueeze :: K .route8ResidualProfile :: typeAExitSevenFreeKeys (BranchState := BranchState) (presentation := presentation) (data := data) known) := by
  simp [typeAExitSevenFreeKeys,
    typeAExitSixFreeKeys, member]

example {known : FactKeys (Input BranchState Presentation presentation data)}
    (member : K .typeAVisibleFirstExcess ∈ known) :
    K .typeAVisibleFirstExcess ∈
      (K .route8PressureDescent :: K .route8PrivateCarrierBudget :: K .route8NoTwoCarrierContradiction :: K .route8CarrierDeletionWitnesses :: K .route8TwoCarrierReduction :: K .route8SmallCoreCollapse :: K .route8CarrierCore :: K .route8BasinBurden :: K .route8LargeBudgetDeficit :: K .route8GlobalSqueeze :: K .route8ResidualProfile :: typeAExitSevenFreeKeys (BranchState := BranchState) (presentation := presentation) (data := data) known) := by
  simp [typeAExitSevenFreeKeys,
    typeAExitSixFreeKeys, member]

example {known : FactKeys (Input BranchState Presentation presentation data)}
    (member : K .typeAVisibleFirstExcess ∈ known) :
    K .typeAVisibleFirstExcess ∈
      (K .route8TerminalNoGo :: K .route8PressureDescent :: K .route8PrivateCarrierBudget :: K .route8NoTwoCarrierContradiction :: K .route8CarrierDeletionWitnesses :: K .route8TwoCarrierReduction :: K .route8SmallCoreCollapse :: K .route8CarrierCore :: K .route8BasinBurden :: K .route8LargeBudgetDeficit :: K .route8GlobalSqueeze :: K .route8ResidualProfile :: typeAExitSevenFreeKeys (BranchState := BranchState) (presentation := presentation) (data := data) known) := by
  simp [typeAExitSevenFreeKeys, typeAExitSixFreeKeys, member]

example {known : FactKeys (Input BranchState Presentation presentation data)} :
    K .typeAExitSixFree ∈
      (typeAExitSevenFreeKeys (BranchState := BranchState) (presentation := presentation) (data := data) known) := by
  simp [typeAExitSevenFreeKeys, typeAExitSixFreeKeys]

example {known : FactKeys (Input BranchState Presentation presentation data)}
    (member : K .typeAExitFourFiniteDescent ∈ known) :
    K .typeAExitFourFiniteDescent ∈
      (typeAExitSevenFreeKeys (BranchState := BranchState) (presentation := presentation) (data := data) known) := by
  simp [typeAExitSevenFreeKeys, typeAExitSixFreeKeys,
    member]

example {known : FactKeys (Input BranchState Presentation presentation data)}
    (member : K .typeASaturatedHandoffSilent ∈ known) :
    K .typeASaturatedHandoffSilent ∈
      (typeAExitSevenFreeKeys (BranchState := BranchState) (presentation := presentation) (data := data) known) := by
  simp [typeAExitSevenFreeKeys, typeAExitSixFreeKeys,
    member]

example {known : FactKeys (Input BranchState Presentation presentation data)}
    (member : K .typeASaturatedHandoffExitFourFree ∈ known) :
    K .typeASaturatedHandoffExitFourFree ∈
      (typeAExitSevenFreeKeys (BranchState := BranchState) (presentation := presentation) (data := data) known) := by
  simp [typeAExitSevenFreeKeys, typeAExitSixFreeKeys,
    member]

example {known : FactKeys (Input BranchState Presentation presentation data)}
    (member : K .typeAExitFiveFree ∈ known) :
    K .typeAExitFiveFree ∈
      (typeAExitSevenFreeKeys (BranchState := BranchState) (presentation := presentation) (data := data) known) := by
  simp [typeAExitSevenFreeKeys, typeAExitSixFreeKeys,
    member]

end

end Hypostructure.Fixtures.TypeASelectedResidualWiring
