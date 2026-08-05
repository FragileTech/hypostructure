import Hypostructure.Core.Strategy.ExactExecution

namespace Hypostructure.Fixtures.ExactExecutionMissingRequirement

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
  | required
  | produced
  | contradiction
  deriving DecidableEq

instance : FactSystem Residual where
  Key := Key
  keyDecidableEq := inferInstance
  name
    | .required => `MissingRequirement.required
    | .produced => `MissingRequirement.produced
    | .contradiction => closureFactName
  name_injective := by
    intro left right same
    cases left <;> cases right <;> simp_all [closureFactName]
  Value
    | .required, _ => Unit
    | .produced, _ => Unit
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
    cases key <;> exact value
  closureKey := .contradiction
  closure_name := rfl
  closureValue _ evidence := evidence
  closureEvidence _ evidence := evidence

def required : FactKey Residual := .required
def produced : FactKey Residual := .produced

abbrev manifest : FactManifest Residual where
  Requires := [required]
  Produces := [produced]
  requiresUnique := by simp
  producesUnique := by simp
  producesNonempty := by simp

abbrev ct : AtomicCT Residual :=
  AtomicCT.create exactLedgerInternal% `MissingRequirement.ct manifest
    FactInputs.current
    (fun inputs => RefinementSystem.refl inputs.current)
    (fun _ => {
      facts := .cons (key := produced) () .nil })

def history := ExactLedger.root exactLedgerInternal% ({ value := 0 } : Residual)

/--
error: failed to synthesize instance of type class
  FactKeys.Available ct.manifest.Requires []

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs (error) in
noncomputable def cannotRun := ct.run history (by simp)

end Hypostructure.Fixtures.ExactExecutionMissingRequirement
