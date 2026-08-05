import Hypostructure.Core.Residual.ExactLedger

namespace Hypostructure.Fixtures.ExactLedger

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
  | upperFive
  | upperThree
  | contradiction
  deriving DecidableEq

instance : FactSystem Residual where
  Key := Key
  keyDecidableEq := inferInstance
  name
    | .upperFive => `UpperFive
    | .upperThree => `UpperThree
    | .contradiction => closureFactName
  name_injective := by
    intro left right same
    cases left <;> cases right <;> simp_all [closureFactName]
  Value
    | .upperFive, residual => PLift (residual.value ≤ 5)
    | .upperThree, residual => PLift (residual.value ≤ 3)
    | .contradiction, _ => ClosureEvidence
  transport := by
    intro key new old refinement value
    cases key with
    | upperFive => exact ⟨refinement.trans value.down⟩
    | upperThree => exact ⟨refinement.trans value.down⟩
    | contradiction => exact value
  transport_refl := by
    intro key residual value
    cases key with
    | upperFive | upperThree => exact Subsingleton.elim _ _
    | contradiction => exact False.elim value.contradiction
  transport_trans := by
    intro key new middle old newMiddle middleOld value
    cases key with
    | upperFive | upperThree => exact Subsingleton.elim _ _
    | contradiction => exact False.elim value.contradiction
  closureKey := .contradiction
  closure_name := rfl
  closureValue _ evidence := evidence
  closureEvidence _ evidence := evidence

def upperFive : FactKey Residual := .upperFive
def upperThree : FactKey Residual := .upperThree

def rootHistory := ExactLedger.root exactLedgerInternal% ({ value := 5 } : Residual)

def withBound := ExactLedger.publishFact exactLedgerInternal% rootHistory upperFive ⟨by decide⟩

def advanced :
    ExactLedger Residual ({ value := 3 } : Residual)
      [upperThree, upperFive] :=
  ExactLedger.append exactLedgerInternal% withBound { value := 3 } (by
      change (3 : Nat) ≤ 5
      decide)
    (.cons (key := upperThree) ⟨Nat.le_refl 3⟩ .nil)
    (by simp) (by simp) (by simp [upperThree, upperFive])
    { producer := `ExactLedgerFixture.advance }

noncomputable def inheritedBound : upperFive.At (ExactLedger.currentOf advanced) :=
  ExactLedger.get advanced upperFive

theorem transition_is_auditable : (ExactLedger.currentOf advanced).value = 3 :=
  rfl

theorem transition_fact_is_indexed :
    (ExactLedger.currentOf advanced).value ≤ 3 :=
  (ExactLedger.get advanced upperThree).down

theorem prior_fact_is_found_without_a_path :
    (ExactLedger.currentOf advanced).value ≤ 5 :=
  inheritedBound.down

theorem audit_lists_every_available_fact :
    (ExactLedger.audit advanced).facts = [`UpperThree, `UpperFive] :=
  rfl

theorem audit_retains_every_commit_in_root_order :
    (ExactLedger.audit advanced).commits.map (fun record => record.info.producer) =
      [`UpperFive, `ExactLedgerFixture.advance] :=
  rfl

theorem audit_fact_names_are_unique :
    (ExactLedger.audit advanced).facts.Nodup :=
  ExactLedger.audit_facts_unique advanced

theorem audit_has_no_empty_commit :
    (ExactLedger.audit advanced).commits.Forall
      (fun record => record.produced ≠ []) :=
  ExactLedger.audit_commits_nonempty advanced

end Hypostructure.Fixtures.ExactLedger
