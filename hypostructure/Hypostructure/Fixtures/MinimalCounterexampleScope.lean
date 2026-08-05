import Hypostructure.Core.Strategy.MinimalCounterexampleScope

/-! Positive enforcement fixture for the problem-input residual domain and for
framework-owned first-scope initialization.

It proves, on a concrete problem, that opening the minimal-counterexample scope
(a) moves the residual to the selected object, (b) commits the manuscript's own
selection fact, and (c) makes that fact retrievable from the canonical ledger by
its exact semantic key — with no wrapper, payload, or side channel. -/

namespace Hypostructure.Fixtures.MinimalCounterexampleScope

open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

/-- Ambient objects are naturals; every object satisfies the baseline. -/
abbrev problem : Core.Problem.{0, 0} where
  Ambient := Nat
  Baseline := fun _ => True
  BranchState := fun _ => Unit

/-- The target is "the object is zero", so a counterexample is a nonzero
object and the minimal counterexample is `1`. -/
abbrev target : Core.Target problem where
  Predicate := fun object => object = 0
  Statement := ∀ object : Nat, True → object = 0
  statement_to_target := fun statement object baseline => statement object baseline
  target_to_statement := fun proof => proof

abbrev progress : Core.Progress.{0, 0, 0} problem where
  Measure := Nat
  lt := (· < ·)
  wellFounded := Nat.lt_wfRel.wf
  measure := id

/-- One semantic fact: the residual object is a counterexample and every
strictly smaller baseline object is not.  This is the manuscript's selection
statement, not a paraphrase of it. -/
inductive Key where
  | selection
  deriving DecidableEq

abbrev vocabulary : FactVocabulary.{0, 0, 0, 0} problem where
  Key := Key
  keyDecidableEq := inferInstance
  name := fun _ => `MinimalCounterexampleScopeFixture.selection
  name_injective := by intro left right _; cases left; cases right; rfl
  name_ne_closure := by intro key; cases key; decide
  Value := fun _ input =>
    PLift (input.object ≠ 0 ∧ ∀ smaller, smaller < input.object → smaller = 0)
  value_subsingleton := fun _ _ => ⟨fun left right => by
    cases left; cases right; rfl⟩
  transport := by
    intro _ new old refinement value
    exact ⟨refinement ▸ value.down⟩

noncomputable instance : FactSystem (Core.Strategy.ProblemInput problem) :=
  problemInputFactSystem vocabulary

/-- The exact semantic key, as callers name it. -/
def selection : FactKey (Core.Strategy.ProblemInput problem) :=
  FactVocabulary.WithClosure.fact Key.selection

/-- The scope opened from the counterexample `7`. -/
noncomputable def opened :
    OpenedScope (P := problem) selection :=
  openMinimalCounterexampleScope target progress (fun _ => ())
    selection
    (fun context => ⟨context.avoids, fun smaller below =>
      context.minimal smaller below trivial⟩)
    { object := 7, baseline := trivial, branchState := () }
    (by decide)

/-- **The committed fact is retrievable by its exact key.**  No producer, row,
predecessor depth, or display name is named. -/
theorem selection_fact_retrievable :
    (ExactLedger.currentOf opened.history).object ≠ 0 ∧
      ∀ smaller, smaller < (ExactLedger.currentOf opened.history).object →
        smaller = 0 :=
  (ExactLedger.get opened.history selection).down

/-- **The residual moved to the selected object**, and the selected object is
the one the fact speaks about. -/
theorem residual_is_selected :
    ExactLedger.currentOf opened.history = opened.selected := rfl

/-- **The scope is the branch's first and only commit**, so nothing was
archived or rebased to make room for it. -/
theorem audit_is_exactly_the_selection :
    (ExactLedger.audit opened.history).facts =
      [`MinimalCounterexampleScopeFixture.selection] := rfl

/-- Every fact is accounted for by a chronological commit. -/
theorem audit_accounts_for_every_fact :
    (ExactLedger.audit opened.history).facts =
      (ExactLedger.audit opened.history).commits.reverse.flatMap
        (fun record => record.produced) :=
  ExactLedger.audit_complete opened.history

end Hypostructure.Fixtures.MinimalCounterexampleScope
