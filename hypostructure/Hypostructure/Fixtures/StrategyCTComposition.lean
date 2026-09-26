import Hypostructure
import Hypostructure.Core.Strategy

/-!
# Core CT composition boundary

This fixture checks that the public CT automation surfaces are available to
the Core strategy layer and that a dependent two-CT composition executes the
second contract on the literal first ledger stage.  The fixture is framework
code; no application strategy or output is exposed.
-/

namespace Hypostructure.Fixtures.StrategyCTComposition

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

def firstContract : Contract Unit where
  Terminal := CompletedTerminal
  Payload := fun _ _ => Unit
  produce _ := ⟨.completed, ()⟩
  exhaustive _ := ⟨⟨.completed, ()⟩⟩

def firstExecution : CTExecution Unit where
  Terminal := CompletedTerminal
  Output := fun _ => Unit
  run := fun _ => ()
  terminal := fun _ _ => .completed
  checks := fun _ => 1
  work := fun _ => 1

def first : CTAdapter Unit := firstExecution.toAdapter

def secondExecution : CTExecution
    (Ledger.Extension Unit (fun _ => Sigma (first.execution.Payload ()))) where
  Terminal := CompletedTerminal
  Output := fun _ => Unit
  run := fun _ => ()
  terminal := fun _ _ => .completed
  checks := fun _ => 2
  work := fun _ => 3

def second : CTAdapter
    (Ledger.Extension Unit (fun _ => Sigma (first.execution.Payload ()))) :=
  secondExecution.toAdapter

def secondGeneric : CTExecution
    (Ledger.Extension Unit (fun _ => Unit)) where
  Terminal := CompletedTerminal
  Output := fun _ => Bool
  run := fun _ => true
  terminal := fun _ _ => .completed
  checks := fun _ => 5
  work := fun _ => 6

def genericComposition := firstExecution.compose secondGeneric

def composition : _root_.Hypostructure.Core.Strategy.CTComposition Unit where
  first := first
  next := second

def singleStrategy : DomainStrategy Unit :=
  first.toDomainStrategy

def firstFromContract : CTExecution Unit :=
  first.execution.toCTExecution first.checks first.work

def thirdExecution : CTExecution
    (Ledger.Extension Unit
      (fun previous => Sigma (composition.execution.Payload previous))) where
  Terminal := CompletedTerminal
  Output := fun _ => Unit
  run := fun _ => ()
  terminal := fun _ _ => .completed
  checks := fun _ => 4
  work := fun _ => 4

def threeComposition := composition.then thirdExecution.toAdapter

theorem composition_preserves_first_stage (previous : Unit) :
    (composition.run previous).previous.previous = previous := by
  rfl

theorem composition_work :
    composition.work.work () = 4 := by
  rfl

theorem nested_composition_work :
    threeComposition.work.work () = 8 := by
  rfl

theorem single_strategy_preserves_work :
    singleStrategy.work.work () = 1 := by
  rfl

theorem adapter_execution_roundtrip :
    (first.toExecution.run ()).fst = CompletedTerminal.completed := by
  rfl

theorem generic_composition_work :
    genericComposition.work () = 7 := by
  rfl

theorem contract_execution_roundtrip :
    firstFromContract.work () = 1 := by
  rfl

#check Hypostructure.CT1.execute
#check Hypostructure.CT2.execute
#check Hypostructure.CT3.execute
#check Hypostructure.CT4.execute
#check Hypostructure.CT5.execute
#check Hypostructure.CT6.execute
#check Hypostructure.CT7.execute
#check Hypostructure.CT8.execute
#check Hypostructure.CT9.execute
#check Hypostructure.CT10.execute
#check Hypostructure.CT11.execute
#check Hypostructure.CT12.execute
#check Hypostructure.CT13.execute
#check Hypostructure.CT14.execute
#check Hypostructure.CT15.execute
#check Hypostructure.CT16.execute
#check Hypostructure.CT17.execute
#check Hypostructure.Graph.Strategy.WitnessScan.toCore
#check Hypostructure.Graph.Strategy.ResponseProfile.toCore
#check Hypostructure.Graph.Strategy.ChargeProfile.toCore
#check Hypostructure.Graph.Strategy.ConnectedSupportProfile.toCore
#check Hypostructure.Graph.Strategy.targetAvoiding
#check Hypostructure.Graph.Strategy.rankBudget
#check Hypostructure.Graph.Strategy.dichotomy
#check Hypostructure.Core.Strategy.CTAdapter.toDomainStrategy
#check Hypostructure.Core.Strategy.CTAdapter.toExecution
#check Hypostructure.Core.Strategy.CTExecution.compose
#check Hypostructure.Core.Strategy.CTExecution.toContract
#check Hypostructure.Core.Strategy.Contract.toCTExecution
#check Hypostructure.Core.Strategy.OrderedWitnessScan.toCTExecution
#check Hypostructure.Core.Strategy.ResponseClassifier.toCTExecution
#check Hypostructure.Core.Strategy.CapacityLedger.toCTExecution
#check Hypostructure.Core.Strategy.SupportLocalization.toCTExecution
#check Hypostructure.Core.Strategy.TargetAvoidingContinuation.toCTExecution
#check Hypostructure.Core.Strategy.RankBudgetSplit.toCTExecution
#check Hypostructure.Core.Strategy.ClosedCodeExhaustion.toCTExecution
#check Hypostructure.CTAdapters.ct1
#check Hypostructure.CTAdapters.ct2
#check Hypostructure.CTAdapters.ct3
#check Hypostructure.CTAdapters.ct4
#check Hypostructure.CTAdapters.ct5
#check Hypostructure.CTAdapters.ct6
#check Hypostructure.CTAdapters.ct7
#check Hypostructure.CTAdapters.ct8
#check Hypostructure.CTAdapters.ct9
#check Hypostructure.CTAdapters.ct10
#check Hypostructure.CTAdapters.ct11
#check Hypostructure.CTAdapters.ct12
#check Hypostructure.CTAdapters.ct13
#check Hypostructure.CTAdapters.ct14
#check Hypostructure.CTAdapters.ct15
#check Hypostructure.CTAdapters.ct16
#check Hypostructure.CTAdapters.ct17

#print axioms composition_preserves_first_stage
#print axioms composition_work
#print axioms nested_composition_work
#print axioms single_strategy_preserves_work
#print axioms adapter_execution_roundtrip
#print axioms generic_composition_work
#print axioms contract_execution_roundtrip

end Hypostructure.Fixtures.StrategyCTComposition
