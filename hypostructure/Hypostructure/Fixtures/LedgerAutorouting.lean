import Hypostructure.Core.Strategy.ExactExecution

namespace Hypostructure.Fixtures.LedgerAutorouting

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
  | a
  | b
  | readyResult
  | blockedResult
  | contradiction
  deriving DecidableEq

instance : FactSystem Residual where
  Key := Key
  keyDecidableEq := inferInstance
  name
    | .a => `A
    | .b => `B
    | .readyResult => `ReadyResult
    | .blockedResult => `BlockedResult
    | .contradiction => closureFactName
  name_injective := by
    intro left right same
    cases left <;> cases right <;> simp_all [closureFactName]
  Value
    | .a, residual => PLift (residual.value ≤ 2)
    | .b, _ => Unit
    | .readyResult, _ => Unit
    | .blockedResult, _ => Unit
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
    | a => exact ⟨refinement.trans value.down⟩
    | b | readyResult | blockedResult | contradiction => exact value
  closureKey := .contradiction
  closure_name := rfl
  closureValue _ evidence := evidence
  closureEvidence _ evidence := evidence

def factA : FactKey Residual := .a
def factB : FactKey Residual := .b
def readyResult : FactKey Residual := .readyResult
def blockedResult : FactKey Residual := .blockedResult

def rootHistory := ExactLedger.root exactLedgerInternal% ({ value := 2 } : Residual)
def history := ExactLedger.publishFact exactLedgerInternal% rootHistory factA ⟨by decide⟩

abbrev requiresA : FactManifest Residual where
  Requires := [factA]
  Produces := [readyResult]
  requiresUnique := by simp
  producesUnique := by simp
  producesNonempty := by simp

abbrev requiresB : FactManifest Residual where
  Requires := [factB]
  Produces := [blockedResult]
  requiresUnique := by simp
  producesUnique := by simp
  producesNonempty := by simp

def blocked : RoutedTask Residual where
  id := `blocked
  order := 0
  manifest := requiresB

def ready : RoutedTask Residual where
  id := `ready
  order := 1
  manifest := requiresA

def selected := RoutedTask.selectFor history [ready, blocked]

theorem earliest_ready_is_selected : selected.map RoutedTask.id = some `ready := by
  native_decide

theorem closure_marker_stops_autorouting (impossible : False) :
    let closed := ExactLedger.publishFact exactLedgerInternal% history
      (FactSystem.closureKey (Residual := Residual))
      (FactSystem.closureValue (Residual := Residual)
        (ExactLedger.currentOf history) {
          reason := .emptyResidual
          contradiction := impossible })
    match RoutedTask.dispatchFor closed [ready, blocked] with
    | .closed => True
    | .run _ => False
    | .deadlock _ => False := by
  exact True.intro

theorem closure_marker_stops_selection (impossible : False) :
    let closed := ExactLedger.publishFact exactLedgerInternal% history
      (FactSystem.closureKey (Residual := Residual))
      (FactSystem.closureValue (Residual := Residual)
        (ExactLedger.currentOf history) {
          reason := .emptyResidual
          contradiction := impossible })
    RoutedTask.selectFor closed [ready, blocked] = none := by
  exact rfl

noncomputable def inputs := FactInputs.ofLedger exactLedgerInternal% requiresA history

noncomputable def readDeclared : factA.At inputs.current :=
  inputs.get factA

/--
error: failed to synthesize instance of type class
  FactKeys.Has factB requiresA.Requires

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs (error) in
example : factB.At (ExactLedger.currentOf history) :=
  inputs.get factB

end Hypostructure.Fixtures.LedgerAutorouting
