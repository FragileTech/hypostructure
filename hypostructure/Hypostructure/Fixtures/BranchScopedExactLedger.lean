import Hypostructure.Core.Residual.ExactLedger

namespace Hypostructure.Fixtures.BranchScopedExactLedger

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
  | upstream
  | leftOnly
  | rightOnly
  | contradiction
  deriving DecidableEq

instance : FactSystem Residual where
  Key := Key
  keyDecidableEq := inferInstance
  name
    | .upstream => `Upstream
    | .leftOnly => `LeftOnly
    | .rightOnly => `RightOnly
    | .contradiction => closureFactName
  name_injective := by
    intro left right same
    cases left <;> cases right <;> simp_all [closureFactName]
  Value
    | .upstream, residual => PLift (residual.value ≤ 4)
    | .leftOnly, _ => Unit
    | .rightOnly, _ => Unit
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
    | upstream => exact ⟨refinement.trans value.down⟩
    | leftOnly | rightOnly | contradiction => exact value
  closureKey := .contradiction
  closure_name := rfl
  closureValue _ evidence := evidence
  closureEvidence _ evidence := evidence

def upstream : FactKey Residual := .upstream
def leftOnly : FactKey Residual := .leftOnly
def rightOnly : FactKey Residual := .rightOnly

def rootHistory := ExactLedger.root exactLedgerInternal% ({ value := 4 } : Residual)
def sharedPrefix := ExactLedger.publishFact exactLedgerInternal% rootHistory upstream ⟨Nat.le_refl 4⟩

/-- Both branches extend the same immutable canonical prefix. -/
def leftCursor := ExactLedger.publishFact exactLedgerInternal% sharedPrefix leftOnly ()
def rightCursor := ExactLedger.publishFact exactLedgerInternal% sharedPrefix rightOnly ()

theorem upstream_visible_on_left :
    (ExactLedger.currentOf leftCursor).value ≤ 4 :=
  (ExactLedger.get leftCursor upstream).down

theorem upstream_visible_on_right :
    (ExactLedger.currentOf rightCursor).value ≤ 4 :=
  (ExactLedger.get rightCursor upstream).down

/--
error: failed to synthesize instance of type class
  FactKeys.Has leftOnly [rightOnly, upstream]

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs (error) in
example : leftOnly.At (ExactLedger.currentOf rightCursor) :=
  ExactLedger.get rightCursor leftOnly

end Hypostructure.Fixtures.BranchScopedExactLedger
