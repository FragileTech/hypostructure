import Hypostructure.Core.Strategy.ExactExecution

namespace Hypostructure.Fixtures.ExactLedgerEmptinessClosure

open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

structure Residual where
  candidates : Finset Nat
  nonempty : candidates.Nonempty

instance : RefinementSystem Residual where
  Subject := Unit
  subject := fun _ => ()
  Refines new old := new.candidates ⊆ old.candidates
  refl := fun _ => Finset.Subset.rfl
  trans := fun newMiddle middleOld => newMiddle.trans middleOld
  subject_eq := fun _ => rfl

inductive Key where
  | contradiction
  deriving DecidableEq

instance : FactSystem Residual where
  Key := Key
  keyDecidableEq := inferInstance
  name | .contradiction => closureFactName
  name_injective := by intro left right same; cases left; cases right; rfl
  Value | .contradiction, _ => ClosureEvidence
  transport := by intro key new old refinement value; exact value
  transport_refl := by
    intro key residual value
    exact False.elim value.contradiction
  transport_trans := by
    intro key new middle old newMiddle middleOld value
    exact False.elim value.contradiction
  closureKey := .contradiction
  closure_name := rfl
  closureValue _ evidence := evidence
  closureEvidence _ evidence := evidence

instance : EmptinessOracle Residual where
  Empty residual := residual.candidates = ∅
  decideEmpty _ := inferInstance
  impossible residual empty := residual.nonempty.ne_empty empty

def rootHistory := ExactLedger.root exactLedgerInternal% ({
  candidates := {0}
  nonempty := ⟨0, by simp⟩
} : Residual)

theorem oracle_keeps_nonempty_branch_open :
    match closeIfEmpty rootHistory with
    | .open => True
    | .closed _ => False := by
  cases result : closeIfEmpty rootHistory with
  | «open» => trivial
  | closed ledger =>
      exact (ExactLedger.get ledger
        (FactSystem.closureKey (Residual := Residual))).contradiction

end Hypostructure.Fixtures.ExactLedgerEmptinessClosure
