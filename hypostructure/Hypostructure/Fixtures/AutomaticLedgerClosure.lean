import Hypostructure.Core.Strategy.ExactExecution

namespace Hypostructure.Fixtures.AutomaticLedgerClosure

open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

structure Subject where
  Cold : Prop
  Hot : Prop
  exclusive : Cold -> Hot -> False

structure Residual where
  subject : Subject
  rank : Nat

instance : RefinementSystem Residual where
  Subject := Subject
  subject := Residual.subject
  Refines new old := new.subject = old.subject ∧ new.rank ≤ old.rank
  refl := fun residual => ⟨rfl, Nat.le_refl residual.rank⟩
  trans := fun newMiddle middleOld =>
    ⟨newMiddle.1.trans middleOld.1, newMiddle.2.trans middleOld.2⟩
  subject_eq := And.left

inductive Key where
  | cold
  | hot
  | contradiction
  deriving DecidableEq

instance : FactSystem Residual where
  Key := Key
  keyDecidableEq := inferInstance
  name
    | .cold => `Cold
    | .hot => `Hot
    | .contradiction => closureFactName
  name_injective := by
    intro left right same
    cases left <;> cases right <;> simp_all [closureFactName]
  Value
    | .cold, residual => PLift residual.subject.Cold
    | .hot, residual => PLift residual.subject.Hot
    | .contradiction, _ => ClosureEvidence
  transport := by
    intro key new old refinement value
    cases key with
    | cold =>
        constructor
        rw [refinement.1]
        exact value.down
    | hot =>
        constructor
        rw [refinement.1]
        exact value.down
    | contradiction => exact value
  transport_refl := by
    intro key residual value
    cases key with
    | cold | hot => exact Subsingleton.elim _ _
    | contradiction => exact False.elim value.contradiction
  transport_trans := by
    intro key new middle old newMiddle middleOld value
    cases key with
    | cold | hot => exact Subsingleton.elim _ _
    | contradiction => exact False.elim value.contradiction
  closureKey := .contradiction
  closure_name := rfl
  closureValue _ evidence := evidence
  closureEvidence _ evidence := evidence

def coldFact : FactKey Residual := .cold
def hotFact : FactKey Residual := .hot
def contradictionFact : FactKey Residual := .contradiction

instance : Incompatible Residual coldFact hotFact where
  contradiction residual cold hot :=
    residual.subject.exclusive cold.down hot.down

def rootHistory (subject : Subject) :=
  ExactLedger.root exactLedgerInternal% ({ subject, rank := 10 } : Residual)

def coldHistory (subject : Subject) (cold : subject.Cold) :=
  ExactLedger.publishFact exactLedgerInternal% (rootHistory subject) coldFact ⟨cold⟩

abbrev hotManifest : FactManifest Residual where
  Requires := [coldFact]
  Produces := [hotFact]
  requiresUnique := by simp
  producesUnique := by simp
  producesNonempty := by simp

abbrev publishHot (subject : Subject) (cold : subject.Cold)
    (hot : subject.Hot) : AtomicCT Residual :=
  AtomicCT.create exactLedgerInternal% `AutomaticLedgerClosure.publishHot hotManifest
    FactInputs.current
    (fun inputs => RefinementSystem.refl inputs.current)
    (fun _ => False.elim (subject.exclusive cold hot))

noncomputable def closedHistory (subject : Subject)
    (cold : subject.Cold) (hot : subject.Hot) :=
  (publishHot subject cold hot).runAndCloseIncompatible
    (coldHistory subject cold) coldFact hotFact
    (by simp [hotFact, coldFact])
    (by simp [hotFact, coldFact])

theorem cold_remains_retrievable_after_closure (subject : Subject)
    (cold : subject.Cold) (hot : subject.Hot) :
    (ExactLedger.currentOf (closedHistory subject cold hot)).subject.Cold :=
  (ExactLedger.get (closedHistory subject cold hot) coldFact).down

theorem hot_remains_retrievable_after_closure (subject : Subject)
    (cold : subject.Cold) (hot : subject.Hot) :
    (ExactLedger.currentOf (closedHistory subject cold hot)).subject.Hot :=
  (ExactLedger.get (closedHistory subject cold hot) hotFact).down

theorem branch_is_closed (subject : Subject)
    (cold : subject.Cold) (hot : subject.Hot) : False :=
  (ExactLedger.get (closedHistory subject cold hot)
    (FactSystem.closureKey (Residual := Residual))).contradiction

end Hypostructure.Fixtures.AutomaticLedgerClosure
