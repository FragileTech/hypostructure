import Hypostructure.Core.Strategy.ClosingProgram

/-!
# Total strategy closure fixture

This non-graph fixture exercises the complete public theorem path.  A
framework-owned scope selects a minimal counterexample, an atomic CT publishes
a prerequisite, an exhaustive decision commits one of two branch-local facts,
and both branches close against the retained target-avoidance fact.  Core alone
turns those local closures into the registered global statement.
-/

namespace Hypostructure.Fixtures.ClosingProgram

open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

abbrev problem : Core.Problem.{0, 0} where
  Ambient := Bool
  Baseline := fun _ => True
  BranchState := fun _ => Unit

abbrev target : Core.Target problem where
  Predicate := fun object => object = true ∨ object = false
  Statement := ∀ object : Bool, object = true ∨ object = false
  statement_to_target := fun statement object _baseline => statement object
  target_to_statement := fun closure object => closure object trivial

abbrev progress : Core.Progress.{0, 0, 0} problem where
  Measure := Nat
  lt := (· < ·)
  wellFounded := Nat.lt_wfRel.wf
  measure := fun object => if object then 1 else 0

inductive Key where
  | selection
  | prepared
  | isTrue
  | isFalse
  deriving DecidableEq

abbrev vocabulary : FactVocabulary.{0, 0, 0, 0} problem where
  Key := Key
  keyDecidableEq := inferInstance
  name
    | .selection => `ClosingProgramFixture.selection
    | .prepared => `ClosingProgramFixture.prepared
    | .isTrue => `ClosingProgramFixture.isTrue
    | .isFalse => `ClosingProgramFixture.isFalse
  name_injective := by
    intro left right same
    cases left <;> cases right <;> simp_all
  name_ne_closure := by
    intro key
    cases key <;> decide
  Value
    | .selection, input =>
        PLift (¬ (input.object = true ∨ input.object = false))
    | .prepared, _ => Unit
    | .isTrue, input => PLift (input.object = true)
    | .isFalse, input => PLift (input.object = false)
  value_subsingleton := by
    intro key input
    cases key <;> infer_instance
  transport := by
    intro key new old refinement value
    cases key with
    | selection =>
        exact ⟨by
          rw [refinement]
          exact value.down⟩
    | prepared => exact ()
    | isTrue =>
        exact ⟨by
          rw [refinement]
          exact value.down⟩
    | isFalse =>
        exact ⟨by
          rw [refinement]
          exact value.down⟩

noncomputable instance : FactSystem (ProblemInput problem) :=
  problemInputFactSystem vocabulary

noncomputable def selection : FactKey (ProblemInput problem) :=
  FactVocabulary.WithClosure.fact .selection

noncomputable def prepared : FactKey (ProblemInput problem) :=
  FactVocabulary.WithClosure.fact .prepared

noncomputable def isTrue : FactKey (ProblemInput problem) :=
  FactVocabulary.WithClosure.fact .isTrue

noncomputable def isFalse : FactKey (ProblemInput problem) :=
  FactVocabulary.WithClosure.fact .isFalse

noncomputable abbrev prepareManifest : FactManifest (ProblemInput problem) where
  Requires := [selection]
  Produces := [prepared]
  requiresUnique := by simp
  producesUnique := by simp
  producesNonempty := by simp

noncomputable abbrev prepare : AtomicCT (ProblemInput problem) :=
  factOnly `ClosingProgramFixture.prepare prepareManifest
    (fun _inputs => .cons (key := prepared) () .nil)

noncomputable abbrev splitManifest : DecisionManifest (ProblemInput problem) where
  Requires := [prepared]
  requiresUnique := by simp
  left := isTrue
  right := isFalse
  distinct := by decide
  left_ne_closure := by decide
  right_ne_closure := by decide

noncomputable abbrev split : AtomicDecision (ProblemInput problem) :=
  AtomicDecision.create exactLedgerInternal% `ClosingProgramFixture.split
    splitManifest fun inputs => by
      cases h : inputs.current.object with
      | false => exact .inr ⟨h⟩
      | true => exact .inl ⟨h⟩

instance : Incompatible (ProblemInput problem) selection isTrue where
  contradiction := fun _input avoids trueFact =>
    avoids.down (Or.inl trueFact.down)

instance : Incompatible (ProblemInput problem) selection isFalse where
  contradiction := fun _input avoids falseFact =>
    avoids.down (Or.inr falseFact.down)

noncomputable abbrev leftProgram :
    ClosingProgram (ProblemInput problem) [isTrue, prepared, selection] :=
  ClosingProgram.closeIncompatible selection isTrue

noncomputable abbrev rightProgram :
    ClosingProgram (ProblemInput problem) [isFalse, prepared, selection] :=
  ClosingProgram.closeIncompatible selection isFalse

noncomputable abbrev afterPreparation :
    ClosingProgram (ProblemInput problem) [prepared, selection] :=
  ClosingProgram.branch split leftProgram rightProgram

noncomputable abbrev program : ClosingProgram (ProblemInput problem) [selection] :=
  ClosingProgram.atomic prepare afterPreparation
    (fresh := by
      rw [List.singleton_disjoint]
      simp only [List.mem_singleton]
      intro same
      change FactVocabulary.WithClosure.fact (vocabulary := vocabulary) Key.prepared =
        FactVocabulary.WithClosure.fact (vocabulary := vocabulary) Key.selection at same
      injection same with key_eq
      cases key_eq)

noncomputable def scope : CounterexampleScope target :=
  CounterexampleScope.createMinimal target exactLedgerInternal% progress
    (fun _ => ()) selection (fun context => ⟨context.avoids⟩)

noncomputable def dag : ClosingDag target :=
  ClosingDag.ofCounterexampleScope target scope program

/-- The global result is obtained only from the registered target and sealed
DAG. -/
theorem certified_statement : target.Statement :=
  dag.statement

/-! ## Isolation pins -/

/-- error: Unknown constant `Hypostructure.Core.Strategy.AtomicDecision.mk` -/
#guard_msgs (error) in
#check AtomicDecision.mk

/-- error: Unknown constant `Hypostructure.Core.Strategy.AtomicDecision.decide` -/
#guard_msgs (error) in
#check AtomicDecision.decide

/-- error: Unknown constant `Hypostructure.Core.Strategy.ClosingProgram.mk` -/
#guard_msgs (error) in
#check ClosingProgram.mk

/-- error: Unknown constant `Hypostructure.Core.Strategy.ClosingProgram.body` -/
#guard_msgs (error) in
#check ClosingProgram.body

/-- error: Unknown constant `Hypostructure.Core.Strategy.CounterexampleScope.mk` -/
#guard_msgs (error) in
#check CounterexampleScope.mk

/-- error: Unknown constant `Hypostructure.Core.Strategy.CounterexampleScope.openScope` -/
#guard_msgs (error) in
#check CounterexampleScope.openScope

/-- error: Unknown constant `Hypostructure.Core.Strategy.ClosingDag.mk` -/
#guard_msgs (error) in
#check ClosingDag.mk

/-- error: Unknown constant `Hypostructure.Core.Strategy.ClosingDag.program` -/
#guard_msgs (error) in
#check ClosingDag.program

/-- error: Unknown constant `Hypostructure.Core.Strategy.ClosingProgram.open` -/
#guard_msgs (error) in
#check ClosingProgram.open

/--
error: failed to synthesize instance of type class
  FactKeys.Has isTrue [isFalse, prepared, selection]

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs (error) in
noncomputable def siblingFactLeak :
    ClosingProgram (ProblemInput problem) [isFalse, prepared, selection] :=
  ClosingProgram.closeIncompatible selection isTrue

/--
error: Type mismatch
  fun right => ClosingProgram.branch split leftProgram right ⋯ ⋯ ⋯
has type
  ClosingProgram (ProblemInput problem) [split.manifest.right, prepared, selection] →
    ClosingProgram (ProblemInput problem) [prepared, selection]
but is expected to have type
  ClosingProgram (ProblemInput problem) [prepared, selection]
-/
#guard_msgs (error) in
noncomputable def missingDecisionArm :
    ClosingProgram (ProblemInput problem) [prepared, selection] :=
  ClosingProgram.branch split leftProgram

-- Application topology cannot replace an `AtomicDecision` with a callback.
def trueInput : ProblemInput problem :=
  { object := true, baseline := trivial, branchState := () }

noncomputable def routeCallback
    (history : ExactLedger (ProblemInput problem) trueInput [prepared, selection]) :
    Decision isTrue isFalse history :=
  Decision.run history isTrue isFalse `ClosingProgramFixture.callback
    (.inl ⟨rfl⟩)

/--
error: Type mismatch
  routeCallback
has type
  (history : ExactLedger (ProblemInput problem) trueInput [prepared, selection]) → Decision isTrue isFalse history
but is expected to have type
  AtomicDecision (ProblemInput problem)
-/
#guard_msgs (error) in
example : AtomicDecision (ProblemInput problem) := routeCallback

#print axioms certified_statement

end Hypostructure.Fixtures.ClosingProgram
