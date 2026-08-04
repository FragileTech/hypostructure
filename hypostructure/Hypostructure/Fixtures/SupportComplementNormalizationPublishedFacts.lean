import Hypostructure.Core.Strategy.SupportComplementNormalization
import Hypostructure.Core.Strategy.FiniteDensityBudgetSemantics

namespace Hypostructure.Fixtures.SupportComplementNormalizationPublishedFacts

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy.FiniteDensityBudget
open Hypostructure.Core.Strategy.SupportComplementNormalization

universe uStage uResidual uAmbient uPiece uAdded

variable {Stage : Type uStage} {Residual : Type uResidual}
variable [HasResidual Stage Residual]
variable {AmbientItem : Stage → Type uAmbient}
variable (ledger : ExactLedger Stage Residual AmbientItem)
variable {Added : Stage → Type uAdded}
variable (capLedger : Hypostructure.Core.Strategy.FiniteDensityBudget.CapLedger Stage)

theorem preserve_previous (stage : Stage) (added : Added stage) :
    (Ledger.extend stage added).previous = stage := rfl

theorem preserve_residual (stage : Stage) (added : Added stage) :
    residualOf (Ledger.extend stage added) = residualOf stage := rfl

theorem preserve_summary (stage : Stage) (added : Added stage) :
    (ledger.preserve (Added := Added)).summary.read (Ledger.extend stage added) =
      ledger.summary.read stage := rfl

theorem preserve_partitionExact (stage : Stage) (added : Added stage) :
    (ledger.preserve (Added := Added)).partitionExact.read
        (Ledger.extend stage added) =
      ledger.partitionExact.read stage := rfl

theorem preserve_selectedUniform (stage : Stage) (added : Added stage) :
    (ledger.preserve (Added := Added)).selectedUniform.read
        (Ledger.extend stage added) =
      ledger.selectedUniform.read stage := rfl

theorem preserve_complementExact (stage : Stage) (added : Added stage) :
    (ledger.preserve (Added := Added)).complementExact.read
        (Ledger.extend stage added) =
      ledger.complementExact.read stage := rfl

theorem preserve_ambient (stage : Stage) (added : Added stage) :
    (ledger.preserve (Added := Added)).ambient.read (Ledger.extend stage added) =
      ledger.ambient.read stage := rfl

theorem preserve_selected (stage : Stage) (added : Added stage) :
    (ledger.preserve (Added := Added)).selected.read (Ledger.extend stage added) =
      ledger.selected.read stage := rfl

theorem preserve_blocks (stage : Stage) (added : Added stage) :
    (ledger.preserve (Added := Added)).blocks.read (Ledger.extend stage added) =
      ledger.blocks.read stage := rfl

theorem preserve_coverCardExact (stage : Stage) (added : Added stage) :
    (ledger.preserve (Added := Added)).coverCardExact.read
      (Ledger.extend stage added) = ledger.coverCardExact.read stage := rfl

theorem preserve_entropyCap (stage : Stage) (added : Added stage) :
    (Hypostructure.Core.Strategy.FiniteDensityBudget.CapLedger.preserve capLedger (Added := Added)).entropyCap.read
        (Ledger.extend stage added) = capLedger.entropyCap.read stage := rfl

end Hypostructure.Fixtures.SupportComplementNormalizationPublishedFacts
