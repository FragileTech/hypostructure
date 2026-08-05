import Hypostructure.Core.Strategy.ExactExecution

/-! A Strategy consumes one CT fact by exact key and appends a derived theorem
without changing the residual or opening a second transport channel. -/

namespace Hypostructure.Fixtures.DerivedFactPublication

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
  | nonnegative
  | selfEqual
  | contradiction
  deriving DecidableEq

instance : FactSystem Residual where
  Key := Key
  keyDecidableEq := inferInstance
  name
    | .nonnegative => `DerivedFactPublication.nonnegative
    | .selfEqual => `DerivedFactPublication.selfEqual
    | .contradiction => closureFactName
  name_injective := by
    intro left right same
    cases left <;> cases right <;> simp_all [closureFactName]
  Value
    | .nonnegative, residual => PLift (0 ≤ residual.value)
    | .selfEqual, residual => PLift (residual.value = residual.value)
    | .contradiction, _ => ClosureEvidence
  transport := by
    intro key new old refinement value
    cases key with
    | nonnegative => exact ⟨Nat.zero_le _⟩
    | selfEqual => exact ⟨rfl⟩
    | contradiction => exact value
  transport_refl := by
    intro key residual value
    cases key with
    | nonnegative | selfEqual => exact Subsingleton.elim _ _
    | contradiction => exact False.elim value.contradiction
  transport_trans := by
    intro key new middle old newMiddle middleOld value
    cases key with
    | nonnegative | selfEqual => exact Subsingleton.elim _ _
    | contradiction => exact False.elim value.contradiction
  closureKey := .contradiction
  closure_name := rfl
  closureValue _ evidence := evidence
  closureEvidence _ evidence := evidence

def nonnegative : FactKey Residual := .nonnegative
def selfEqual : FactKey Residual := .selfEqual

abbrev ctManifest : FactManifest Residual where
  Requires := []
  Produces := [nonnegative]
  requiresUnique := by simp
  producesUnique := by simp
  producesNonempty := by simp

abbrev atomic : AtomicCT Residual :=
  AtomicCT.create exactLedgerInternal% `DerivedFactPublication.ct ctManifest
    FactInputs.current
    (fun inputs => RefinementSystem.refl inputs.current)
    (fun inputs => {
      facts := .cons (key := nonnegative)
        ⟨Nat.zero_le inputs.current.value⟩ .nil
      checks := 1
      work := 1 })

def rootHistory := ExactLedger.root exactLedgerInternal% ({ value := 7 } : Residual)
noncomputable def afterCT := atomic.run rootHistory (by simp)

abbrev strategyManifest : FactManifest Residual where
  Requires := [nonnegative]
  Produces := [selfEqual]
  requiresUnique := by simp
  producesUnique := by simp
  producesNonempty := by simp

abbrev certified : AtomicStrategy Residual :=
  AtomicCT.create exactLedgerInternal% `DerivedFactPublication.strategy strategyManifest
    FactInputs.current
    (fun inputs => RefinementSystem.refl inputs.current)
    (fun _inputs => {
      facts := .cons (key := selfEqual) ⟨rfl⟩ .nil })

noncomputable def afterStrategy := AtomicCT.run certified afterCT (by
  simp [selfEqual, nonnegative])

theorem residual_retained :
    ExactLedger.currentOf afterStrategy = ExactLedger.currentOf afterCT := rfl

theorem atomic_fact_retained :
    0 ≤ (ExactLedger.currentOf afterStrategy).value :=
  (ExactLedger.get afterStrategy nonnegative).down

theorem published_fact_readable :
    (ExactLedger.currentOf afterStrategy).value =
      (ExactLedger.currentOf afterStrategy).value :=
  (ExactLedger.get afterStrategy selfEqual).down

end Hypostructure.Fixtures.DerivedFactPublication
