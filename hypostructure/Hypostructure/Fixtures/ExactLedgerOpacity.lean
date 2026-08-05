import Hypostructure.Core.Strategy.ExactExecution

namespace Hypostructure.Fixtures.ExactLedgerOpacity

open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

structure Residual where value : Nat

instance : RefinementSystem Residual where
  Subject := Unit
  subject := fun _ => ()
  Refines new old := new.value ≤ old.value
  refl := fun _ => Nat.le_refl _
  trans := Nat.le_trans
  subject_eq := fun _ => rfl

inductive Key where
  | unitFact
  | contradiction
  deriving DecidableEq

instance : FactSystem Residual where
  Key := Key
  keyDecidableEq := inferInstance
  name
    | .unitFact => `ExactLedgerOpacity.unitFact
    | .contradiction => closureFactName
  name_injective := by
    intro left right same
    cases left <;> cases right <;> simp_all [closureFactName]
  Value
    | .unitFact, _ => Unit
    | .contradiction, _ => ClosureEvidence
  transport := by
    intro key new old refinement value
    cases key <;> exact value
  transport_refl := by
    intro key residual value
    cases key with
    | unitFact => rfl
    | contradiction => exact False.elim value.contradiction
  transport_trans := by
    intro key new middle old newMiddle middleOld value
    cases key with
    | unitFact => rfl
    | contradiction => exact False.elim value.contradiction
  closureKey := .contradiction
  closure_name := rfl
  closureValue _ evidence := evidence
  closureEvidence _ evidence := evidence

def unitFact : FactKey Residual := .unitFact

/-! Application code cannot invoke either private ledger constructor or the
private atomic-executor constructor. -/

/-- error: Unknown constant `Hypostructure.Core.Residual.ExactLedger.seed` -/
#guard_msgs (error) in
#check ExactLedger.seed

/-- error: Unknown constant `Hypostructure.Core.Residual.ExactLedger.step` -/
#guard_msgs (error) in
#check ExactLedger.step

/-- error: Unknown constant `Hypostructure.Core.Residual.ExactLedger.scope` -/
#guard_msgs (error) in
#check ExactLedger.scope

/-- error: Unknown constant `Hypostructure.Core.Strategy.AtomicCT.mk` -/
#guard_msgs (error) in
#check AtomicCT.mk

/-- error: Unknown constant `Hypostructure.Core.Residual.ExactLedger.materialize` -/
#guard_msgs (error) in
#check ExactLedger.materialize

/-- error: Unknown constant `Hypostructure.Core.Residual.ExactLedger.commitTrail` -/
#guard_msgs (error) in
#check ExactLedger.commitTrail

/-- error: Unknown constant `Hypostructure.Core.Strategy.FactKeys.Available.mk` -/
#guard_msgs (error) in
#check Core.Strategy.FactKeys.Available.mk

/-- error: Unknown constant `Hypostructure.Core.Strategy.FactKeys.Available.values` -/
#guard_msgs (error) in
#check Core.Strategy.FactKeys.Available.values

/-- error: Unknown constant `Hypostructure.Core.Strategy.FactInputs.mk` -/
#guard_msgs (error) in
#check FactInputs.mk

/-- error: Unknown constant `Hypostructure.Core.Strategy.FactInputs.facts` -/
#guard_msgs (error) in
#check FactInputs.facts

/-- error: Unknown constant `Hypostructure.Core.Strategy.AtomicCT.next` -/
#guard_msgs (error) in
#check AtomicCT.next

/-- error: Unknown constant `Hypostructure.Core.Strategy.AtomicCT.refines` -/
#guard_msgs (error) in
#check AtomicCT.refines

/-- error: Unknown constant `Hypostructure.Core.Strategy.AtomicCT.execute` -/
#guard_msgs (error) in
#check AtomicCT.execute

/-- error: Unknown constant `Hypostructure.Core.Residual.FactKeys.Values.getAt` -/
#guard_msgs (error) in
#check FactKeys.Values.getAt

/-- error: Unknown constant `Hypostructure.Core.Residual.FactKeys.Values.transport` -/
#guard_msgs (error) in
#check FactKeys.Values.transport

/-- error: Unknown constant `Hypostructure.Core.Residual.FactKeys.Values.append` -/
#guard_msgs (error) in
#check FactKeys.Values.append

/-! A fact key has no public structure constructor: the domain's closed key
type and sole `FactSystem` determine every schema. -/

/-- error: Unknown constant `Hypostructure.Core.Residual.FactKey.mk` -/
#guard_msgs (error) in
#check FactKey.mk

/-- error: Unknown constant `Hypostructure.Core.Strategy.RoutedTask.dispatch` -/
#guard_msgs (error) in
#check RoutedTask.dispatch

/-- error: Unknown constant `Hypostructure.Core.Strategy.RoutedTask.selectReady` -/
#guard_msgs (error) in
#check RoutedTask.selectReady

end Hypostructure.Fixtures.ExactLedgerOpacity
