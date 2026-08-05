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
  /-- The alternative a branch test has to offer and no residual can realize. -/
  | both
  | contradiction
  deriving DecidableEq

instance : FactSystem Residual where
  Key := Key
  keyDecidableEq := inferInstance
  name
    | .cold => `Cold
    | .hot => `Hot
    | .both => `Both
    | .contradiction => closureFactName
  name_injective := by
    intro left right same
    cases left <;> cases right <;> simp_all [closureFactName]
  Value
    | .cold, residual => PLift residual.subject.Cold
    | .hot, residual => PLift residual.subject.Hot
    | .both, residual => PLift (residual.subject.Cold ∧ residual.subject.Hot)
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
    | cold =>
        constructor
        rw [refinement.1]
        exact value.down
    | hot =>
        constructor
        rw [refinement.1]
        exact value.down
    | both =>
        constructor
        rw [refinement.1]
        exact value.down
    | contradiction => exact value
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

/-! ## Single-fact closure

A branch test must offer every alternative its domain admits, and some of them
are realized by no object at all.  `Impossible` registers that, and
`closeImpossible` closes the arm the moment it is taken, without a second fact
having to be manufactured to record the contradiction.

The fixture below is the generic witness for that operation: the residual keeps
its subject, every earlier fact is still retrievable through
`ExactLedger.get` after the closure, and the branch carries Core's reserved
closure entry naming the impossible fact and nothing else. -/

/-- A fact no residual of this domain can carry: it asserts both halves of the
subject's own exclusion. -/
def bothFact : FactKey Residual := .both

instance : Impossible Residual bothFact where
  contradiction residual value :=
    residual.subject.exclusive value.down.1 value.down.2

noncomputable def impossibleHistory (subject : Subject)
    (cold : subject.Cold) (both : subject.Cold ∧ subject.Hot) :=
  closeImpossible
    (ExactLedger.publishFact exactLedgerInternal% (coldHistory subject cold)
      bothFact ⟨both⟩ (by simp [bothFact, coldFact]))
    bothFact (by simp [bothFact, coldFact])

/-- **Predecessor preservation.**  The fact committed before the closure is
still retrievable by exact key afterwards. -/
theorem cold_remains_retrievable_after_impossible (subject : Subject)
    (cold : subject.Cold) (both : subject.Cold ∧ subject.Hot) :
    (ExactLedger.currentOf (impossibleHistory subject cold both)).subject.Cold :=
  (ExactLedger.get (impossibleHistory subject cold both) coldFact).down

/-- **Residual behaviour.**  A single-fact closure changes no residual: the
subject the branch argues about is the one it started with. -/
theorem subject_unchanged_after_impossible (subject : Subject)
    (cold : subject.Cold) (both : subject.Cold ∧ subject.Hot) :
    (ExactLedger.currentOf (impossibleHistory subject cold both)).subject =
      subject := rfl

/-- **The advertised theorem.**  The branch is closed. -/
theorem impossible_branch_is_closed (subject : Subject)
    (cold : subject.Cold) (both : subject.Cold ∧ subject.Hot) : False :=
  (ExactLedger.get (impossibleHistory subject cold both)
    (FactSystem.closureKey (Residual := Residual))).contradiction

/-- **Ledger availability.**  The closure entry names the impossible fact, and
`AutomaticClosureReason.impossibleFact` is what distinguishes it from a
two-fact incompatibility. -/
theorem impossible_closure_names_the_fact (subject : Subject)
    (cold : subject.Cold) (both : subject.Cold ∧ subject.Hot) :
    (ExactLedger.get (impossibleHistory subject cold both)
      (FactSystem.closureKey (Residual := Residual))).reason =
      .impossibleFact (FactSystem.name bothFact) := rfl

end Hypostructure.Fixtures.AutomaticLedgerClosure
