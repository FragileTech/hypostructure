import Hypostructure.Core.Residual.ExactLedger

namespace Hypostructure.Fixtures.ExactLedgerDuplicateFact

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
  | bound
  | contradiction
  deriving DecidableEq

instance : FactSystem Residual where
  Key := Key
  keyDecidableEq := inferInstance
  name
    | .bound => `Bound
    | .contradiction => closureFactName
  name_injective := by
    intro left right same
    cases left <;> cases right <;> simp_all [closureFactName]
  Value
    | .bound, residual => PLift (residual.value ≤ 1)
    | .contradiction, _ => ClosureEvidence
  transport := by
    intro key new old refinement value
    cases key with
    | bound => exact ⟨refinement.trans value.down⟩
    | contradiction => exact value
  transport_refl := by
    intro key residual value
    cases key with
    | bound => exact Subsingleton.elim _ _
    | contradiction => exact False.elim value.contradiction
  transport_trans := by
    intro key new middle old newMiddle middleOld value
    cases key with
    | bound => exact Subsingleton.elim _ _
    | contradiction => exact False.elim value.contradiction
  closureKey := .contradiction
  closure_name := rfl
  closureValue _ evidence := evidence
  closureEvidence _ evidence := evidence

def bound : FactKey Residual := .bound
def rootHistory := ExactLedger.root exactLedgerInternal% ({ value := 1 } : Residual)
def once := ExactLedger.publishFact exactLedgerInternal% rootHistory bound ⟨by decide⟩

/--
error: could not synthesize default value for parameter 'fresh' using tactics
---
error: Tactic `decide` proved that the proposition
  bound ∉ [bound]
is false
-/
#guard_msgs (error) in
def duplicate := ExactLedger.publishFact exactLedgerInternal% once bound ⟨by decide⟩

end Hypostructure.Fixtures.ExactLedgerDuplicateFact
