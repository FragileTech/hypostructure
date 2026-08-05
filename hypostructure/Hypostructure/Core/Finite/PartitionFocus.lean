import Hypostructure.Core.Finite.Partition
import Hypostructure.Core.Residual.Focus

/-!
# Finite partitions: the legacy focused executor

**Legacy.**  `Core/Finite/Partition.lean` holds the finite partition
mathematics.  This file holds the focused-stage executor that used to drive it,
which reaches `Core.Residual.Focus` and through it the legacy
`Core.Residual.Ledger`.

Separated so that the support-component decomposition -- and through it the
spine's row `[11]`--`[14]` -- can use partitions without importing the legacy
stage stack.
-/

namespace Hypostructure.Core.Finite.Partition

open Hypostructure.Core.Residual

/-! ## Focused residual executor -/

/-- Residual-owned finite partition contract.  Consumers provide only the
active schedule, predicate, and predicate decider.  Core runs the lossless
partition and stores the exact accepted/rejected schedules in the ledger. -/
structure FocusedContract {Previous : Sort uPrevious}
    (focus : Focus.Profile Previous) where
  Item : Type u
  schedule : Focus.ActiveQuery focus fun _previous _active =>
    Enumeration Item
  predicate : (previous : Previous) -> focus.Active previous -> Item -> Prop
  decidePredicate : (previous : Previous) -> (active : focus.Active previous) ->
    (item : Item) -> Decidable (predicate previous active item)

namespace FocusedContract

variable {Previous : Sort uPrevious} {focus : Focus.Profile Previous}
variable (contract : FocusedContract focus)

/-- Pure finite partition seen at one active predecessor. -/
def partitionAt (previous : Previous) (active : focus.Active previous) :
    Result (contract.schedule previous active)
      (contract.predicate previous active) :=
  run (contract.schedule previous active)
    (contract.predicate previous active)
    (contract.decidePredicate previous active)

/-- Focused stage carrying exactly one Core-owned partition result. -/
abbrev Stage :=
  Focus.Stage focus fun previous active =>
    Result (contract.schedule previous active)
      (contract.predicate previous active)

/-- Execute the partition and register the accepted/rejected schedules. -/
def executeCounted (previous : Previous) : Counted contract.Stage :=
  Focus.runCounted focus previous fun active _checks _exact =>
    contract.partitionAt previous active

/-- Uncounted public executor. -/
def execute (previous : Previous) : contract.Stage :=
  (contract.executeCounted previous).value

/-- Public CT-style executor spelling. -/
abbrev runStage (previous : Previous) : contract.Stage :=
  contract.execute previous

@[simp] theorem execute_previous (previous : Previous) :
    (contract.execute previous).previous = previous :=
  Focus.runCounted_previous focus previous _

@[simp] theorem runStage_previous (previous : Previous) :
    (contract.runStage previous).previous = previous :=
  contract.execute_previous previous

theorem executeCounted_checks (previous : Previous) :
    (contract.executeCounted previous).checks =
      focus.selectionBudget.checks previous :=
  Focus.runCounted_checks focus previous _

abbrev successor : Focus.Profile contract.Stage :=
  Focus.successor focus fun previous active =>
    Result (contract.schedule previous active)
      (contract.predicate previous active)

/-- Read the complete partition result from the newest ledger extension. -/
def latestResult :
    Focus.ActiveQuery contract.successor fun stage active =>
      Result (contract.schedule stage.previous active)
        (contract.predicate stage.previous active) :=
  Focus.ActiveQuery.latest

/-- Read the accepted exact schedule from the newest ledger extension. -/
def latestAccepted :
    Focus.ActiveQuery contract.successor fun stage active =>
      Enumeration {value // contract.predicate stage.previous active value} :=
  contract.latestResult.map fun _stage _active result =>
    result.accepted

/-- Read the rejected exact schedule from the newest ledger extension. -/
def latestRejected :
    Focus.ActiveQuery contract.successor fun stage active =>
      Enumeration {value // Not (contract.predicate stage.previous active value)} :=
  contract.latestResult.map fun _stage _active result =>
    result.rejected

/-- Read the lossless cardinality identity from the newest ledger extension. -/
def latestCardPartition :
    Focus.ActiveQuery contract.successor fun stage active =>
      (contract.latestAccepted stage active).card +
          (contract.latestRejected stage active).card =
        ((contract.schedule.preserve) stage active).card :=
  fun stage active =>
    (contract.latestResult stage active).card_partition

end FocusedContract

end Hypostructure.Core.Finite.Partition
