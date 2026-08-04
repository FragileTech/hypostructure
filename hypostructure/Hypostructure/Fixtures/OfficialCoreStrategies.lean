import Hypostructure.Core.Strategy.Official.Schema
import Hypostructure.Core.Strategy.Official.Strategies
import Hypostructure.Core.Strategy.Official.Strategies.Dispatcher

namespace Hypostructure.Fixtures.OfficialCoreStrategies

open Core.Strategy.Official
open Core.Strategy.Official.Strategies
open Core.Strategy.OfficialRegistry

def carrier : FiniteCarrier where
  Carrier := Bool
  finite := inferInstance
  decidableEq := inferInstance

def zero : carrier.Carrier := false
def one : carrier.Carrier := true

def schedule : ScheduleSlot where
  carrier := carrier
  rows := [zero, one]
  covers := by intro x; cases x <;> simp [zero, one]

def functionTable : FunctionTableSlot where
  left := carrier
  right := carrier
  rows := [(zero, one), (one, one)]
  total := by
    intro x
    cases x
    · exact ⟨one, by simp [zero, one]⟩
    · exact ⟨one, by simp [zero, one]⟩
  functional := by
    intro x y z hy hz
    cases x <;> simp [zero, one] at hy hz ⊢
    · exact hy.trans hz.symm
    · exact hy.trans hz.symm

def natTable : NatTableSlot where
  key := carrier
  rows := [(zero, 2), (one, 3)]
  total := by
    intro x
    cases x
    · exact ⟨2, by simp [zero, one]⟩
    · exact ⟨3, by simp [zero, one]⟩
  functional := by
    intro x m n hm hn
    cases x <;> simp [zero, one] at hm hn
    · omega
    · omega

def relation : RelationSlot where
  left := carrier
  right := carrier
  rows := [(zero, one), (one, zero)]

def schema : ProblemSchema where
  core := {
    schedules := [schedule]
    responseTables := [functionTable]
    capacityTables := [natTable]
    supportRelations := [relation]
    rankTables := [natTable]
    closedCodeTables := [functionTable]
  }

example : (OrderedExhaustion.execute schedule).trace = [zero, one] := rfl
example : (OrderedExhaustion.execute schedule).work.bound = 2 := rfl

example : (ResponseClassification.execute functionTable).graph =
    [(zero, one), (one, one)] := rfl
example : (ResponseClassification.execute functionTable).work.bound = 2 := rfl

example : (CapacityAccounting.execute natTable).aggregate = 5 := rfl
example : (CapacityAccounting.execute natTable).work.bound = 2 := rfl

example : (SupportLocalization.execute relation).support = [zero, one] := rfl
example : (SupportLocalization.execute relation).work.bound = 2 := rfl

example : (RankBudget.execute natTable).maxRank = 3 := rfl
example : (RankBudget.execute natTable).work.bound = 2 := rfl

example : (ClosedCodeExhaustion.execute functionTable).repetitions.length = 2 := by
  native_decide
example : (ClosedCodeExhaustion.execute functionTable).work.bound = 4 := rfl

example : Strategies.Dispatcher.supports .orderedExhaustion = true := rfl
example : Strategies.Dispatcher.supports .responseClassification = true := rfl
example : Strategies.Dispatcher.supports .capacityAccounting = true := rfl
example : Strategies.Dispatcher.supports .supportLocalization = true := rfl
example : Strategies.Dispatcher.supports .rankBudget = true := rfl
example : Strategies.Dispatcher.supports .closedCodeExhaustion = true := rfl
example : (Strategies.Dispatcher.resolve schema ⟨.orderedExhaustion, 0⟩).isSome :=
  by native_decide
example : (Strategies.Dispatcher.resolve schema ⟨.responseClassification, 0⟩).isSome :=
  by native_decide
example : (Strategies.Dispatcher.resolve schema ⟨.capacityAccounting, 0⟩).isSome :=
  by native_decide
example : (Strategies.Dispatcher.resolve schema ⟨.supportLocalization, 0⟩).isSome :=
  by native_decide
example : (Strategies.Dispatcher.resolve schema ⟨.rankBudget, 0⟩).isSome :=
  by native_decide
example : (Strategies.Dispatcher.resolve schema ⟨.closedCodeExhaustion, 0⟩).isSome :=
  by native_decide
example : Strategies.Dispatcher.resolve schema ⟨.targetDecision, 0⟩ = none :=
  Strategies.Dispatcher.rejects_unsupported _ _ rfl

#print axioms OrderedExhaustion.execute
#print axioms ResponseClassification.execute
#print axioms CapacityAccounting.execute
#print axioms SupportLocalization.execute
#print axioms RankBudget.execute
#print axioms ClosedCodeExhaustion.execute

end Hypostructure.Fixtures.OfficialCoreStrategies
