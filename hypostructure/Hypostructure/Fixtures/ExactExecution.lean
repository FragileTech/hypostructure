import Hypostructure.Core.Strategy.ExactExecution

namespace Hypostructure.Fixtures.ExactExecution

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
  | atMostTwo
  | atMostThree
  | auditTag
  | contradiction
  deriving DecidableEq

instance : FactSystem Residual where
  Key := Key
  keyDecidableEq := inferInstance
  name
    | .atMostTwo => `AtMostTwo
    | .atMostThree => `AtMostThree
    | .auditTag => `AuditTag
    | .contradiction => closureFactName
  name_injective := by
    intro left right same
    cases left <;> cases right <;> simp_all [closureFactName]
  Value
    | .atMostTwo, residual => PLift (residual.value ≤ 2)
    | .atMostThree, residual => PLift (residual.value ≤ 3)
    | .auditTag, _ => Unit
    | .contradiction, _ => ClosureEvidence
  value_subsingleton := by
    intro key residual
    cases key <;>
      exact ⟨fun left right => by
        first
          | exact left.contradiction.elim
          | (cases left; cases right; rfl)⟩
  transport := by
    intro key new old refinement value
    cases key with
    | atMostTwo => exact ⟨refinement.trans value.down⟩
    | atMostThree => exact ⟨refinement.trans value.down⟩
    | auditTag | contradiction => exact value
  closureKey := .contradiction
  closure_name := rfl
  closureValue _ evidence := evidence
  closureEvidence _ evidence := evidence

def atMostTwo : FactKey Residual := .atMostTwo
def atMostThree : FactKey Residual := .atMostThree
def auditTag : FactKey Residual := .auditTag

def rootHistory := ExactLedger.root exactLedgerInternal% ({ value := 3 } : Residual)
def taggedRoot := ExactLedger.publishFact exactLedgerInternal% rootHistory auditTag ()

abbrev ctManifest : FactManifest Residual where
  Requires := []
  Produces := [atMostTwo]
  requiresUnique := by simp
  producesUnique := by simp
  producesNonempty := by simp

abbrev ct : AtomicCT Residual :=
  AtomicCT.create exactLedgerInternal% `ExactExecutionFixture.ct ctManifest
    (fun inputs => { value := min inputs.current.value 2 })
    (fun inputs => Nat.min_le_left inputs.current.value 2)
    (fun inputs => {
      facts := .cons (key := atMostTwo)
        ⟨Nat.min_le_right inputs.current.value 2⟩ .nil
      checks := 1
      work := 1 })

noncomputable def afterCT := ct.run rootHistory (by simp)

/-- The same CT runs after an unrelated fact whenever its exact manifest is
ready. -/
noncomputable def afterTagThenCT := ct.run taggedRoot (by
  simp [atMostTwo, auditTag])

theorem order_independent_run_preserves_unrelated_fact :
    ExactLedger.get afterTagThenCT auditTag = () := rfl

abbrev strategyManifest : FactManifest Residual where
  Requires := [atMostTwo]
  Produces := [atMostThree]
  requiresUnique := by simp
  producesUnique := by simp
  producesNonempty := by simp

abbrev strategy : AtomicStrategy Residual :=
  AtomicCT.create exactLedgerInternal% `ExactExecutionFixture.strategy strategyManifest
    FactInputs.current
    (fun inputs => RefinementSystem.refl inputs.current)
    (fun inputs => {
      facts := .cons (key := atMostThree) ⟨by
        exact Nat.le_trans (inputs.get atMostTwo).down (by decide)⟩ .nil })

noncomputable def afterStrategy := AtomicCT.run strategy afterCT (by
  simp [atMostThree, atMostTwo])

theorem no_fact_was_dropped :
    (ExactLedger.currentOf afterStrategy).value ≤ 2 :=
  (ExactLedger.get afterStrategy atMostTwo).down

theorem strategy_fact_is_retrievable :
    (ExactLedger.currentOf afterStrategy).value ≤ 3 :=
  (ExactLedger.get afterStrategy atMostThree).down

end Hypostructure.Fixtures.ExactExecution
