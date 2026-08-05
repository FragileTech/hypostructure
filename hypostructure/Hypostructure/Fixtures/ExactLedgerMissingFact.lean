import Hypostructure.Core.Residual.ExactLedger

namespace Hypostructure.Fixtures.ExactLedgerMissingFact

open Hypostructure.Core.Residual

structure Residual where value : Nat

instance : RefinementSystem Residual where
  Subject := Unit
  subject := fun _ => ()
  Refines new old := new.value ≤ old.value
  refl := fun _ => Nat.le_refl _
  trans := Nat.le_trans
  subject_eq := fun _ => rfl

inductive Key where
  | missing
  | contradiction
  deriving DecidableEq

instance : FactSystem Residual where
  Key := Key
  keyDecidableEq := inferInstance
  name
    | .missing => `Missing
    | .contradiction => closureFactName
  name_injective := by
    intro left right same
    cases left <;> cases right <;> simp_all [closureFactName]
  Value
    | .missing, _ => Unit
    | .contradiction, _ => ClosureEvidence
  transport := by
    intro key new old refinement value
    cases key <;> exact value
  transport_refl := by
    intro key residual value
    cases key with
    | missing => rfl
    | contradiction => exact False.elim value.contradiction
  transport_trans := by
    intro key new middle old newMiddle middleOld value
    cases key with
    | missing => rfl
    | contradiction => exact False.elim value.contradiction
  closureKey := .contradiction
  closure_name := rfl
  closureValue _ evidence := evidence
  closureEvidence _ evidence := evidence

def missing : FactKey Residual := .missing
def history := ExactLedger.root exactLedgerInternal% ({ value := 1 } : Residual)

/--
error: failed to synthesize instance of type class
  FactKeys.Has missing []

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs (error) in
example : missing.At (ExactLedger.currentOf history) :=
  ExactLedger.get history missing

end Hypostructure.Fixtures.ExactLedgerMissingFact
