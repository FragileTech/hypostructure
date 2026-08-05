import Hypostructure.Core.Strategy.ExactExecution

namespace Hypostructure.Fixtures.ExactExecutionDroppedFact

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
  | first
  | second
  | contradiction
  deriving DecidableEq

instance : FactSystem Residual where
  Key := Key
  keyDecidableEq := inferInstance
  name
    | .first => `DroppedFact.first
    | .second => `DroppedFact.second
    | .contradiction => closureFactName
  name_injective := by
    intro left right same
    cases left <;> cases right <;> simp_all [closureFactName]
  Value
    | .first, _ => Unit
    | .second, _ => Unit
    | .contradiction, _ => ClosureEvidence
  transport := by
    intro key new old refinement value
    cases key <;> exact value
  transport_refl := by
    intro key residual value
    cases key with
    | first | second => rfl
    | contradiction => exact False.elim value.contradiction
  transport_trans := by
    intro key new middle old newMiddle middleOld value
    cases key with
    | first | second => rfl
    | contradiction => exact False.elim value.contradiction
  closureKey := .contradiction
  closure_name := rfl
  closureValue _ evidence := evidence
  closureEvidence _ evidence := evidence

def first : FactKey Residual := .first
def second : FactKey Residual := .second

abbrev manifest : FactManifest Residual where
  Requires := []
  Produces := [first, second]
  requiresUnique := by simp
  producesUnique := by simp [first, second]
  producesNonempty := by simp

/--
error: Application type mismatch: The argument
  FactKeys.Values.nil
has type
  FactKeys.Values ?m.17 []
but is expected to have type
  FactKeys.Values residual [second]
in the application
  FactKeys.Values.cons () FactKeys.Values.nil
-/
#guard_msgs (error) in
def cannotDropSecond (residual : Residual) : AtomicResult manifest residual :=
  { facts := .cons (key := first) () .nil }

end Hypostructure.Fixtures.ExactExecutionDroppedFact
