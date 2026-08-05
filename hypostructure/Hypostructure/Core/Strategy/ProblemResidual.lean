import Hypostructure.Core.Strategy.ExactExecution
import Hypostructure.Core.Strategy.ProblemInput
import Hypostructure.Core.Context

/-!
# The problem-input residual domain

`Core.Residual.ExactLedger` needs one `RefinementSystem` and one `FactSystem`
per residual domain.  This module supplies both for the residual every
structural spine actually argues about: a `Strategy.ProblemInput P`, i.e. an
ambient object together with its baseline hypothesis and branch state.

The refinement relation is *object equality*.  That is the honest relation for
this domain: after the initial minimal-counterexample scope is opened, no later
step of the spine replaces the object it argues about, and a step may only add
facts (`RefinementSystem.refl`) or move branch state while the object stays
fixed.  Because `Subject` is the object itself, `subject_eq` is exactly the
statement that a refinement never changes what the run is proving a target
about, which is what `Strategy.closeTarget` decodes against.

Fact keys are supplied by the caller as an abstract vocabulary
(`FactVocabulary`).  A structural spine therefore quantifies over its semantic
keys instead of naming a fixed enumeration, and a problem instantiates the
vocabulary with the exact facts its manuscript proves.
-/

namespace Hypostructure.Core.Strategy

open Hypostructure.Core.Residual

universe uAmbient uBranch uKey uValue

variable {P : Core.Problem.{uAmbient, uBranch}}

/-! ## Refinement -/

/-- Object equality is the refinement relation of the problem-input domain.
A fact-only step is `refl`; a step that rewrites branch state keeps the object
and therefore keeps every established fact applicable. -/
instance problemInputRefinement (P : Core.Problem.{uAmbient, uBranch}) :
    RefinementSystem.{max uAmbient uBranch, uAmbient} (Strategy.ProblemInput P) where
  Subject := P.Ambient
  subject input := input.object
  Refines new old := new.object = old.object
  refl _ := rfl
  trans new_middle middle_old := new_middle.trans middle_old
  subject_eq refinement := refinement

/-! ## Fact vocabulary

A vocabulary is the closed set of semantic keys one problem's manuscript
proves, together with the value schema of each key and its transport along a
refinement.  Core owns the distinguished closure key, so no vocabulary can
forget it or give it a second schema. -/

/-- The semantic facts of one problem, excluding the closure key Core adds. -/
structure FactVocabulary (P : Core.Problem.{uAmbient, uBranch}) where
  Key : Type uKey
  keyDecidableEq : DecidableEq Key
  /-- Audit names.  They are diagnostics; routing always compares keys. -/
  name : Key → Lean.Name
  name_injective : Function.Injective name
  /-- No vocabulary key may impersonate the reserved closure name. -/
  name_ne_closure : ∀ key, name key ≠ Core.Residual.closureFactName
  Value : Key → Strategy.ProblemInput P → Sort (uValue + 1)
  /-- Every fact stays applicable on a descendant residual. -/
  transport : {key : Key} → {new old : Strategy.ProblemInput P} →
    new.object = old.object → Value key old → Value key new
  /-- Transport is functorial, so a fact carried along a chain of refinements
  is the fact carried along their composite.  Only the vocabulary author can
  prove this: a value may be data rather than a proposition. -/
  transport_refl : ∀ (key : Key) (input : Strategy.ProblemInput P)
    (value : Value key input), transport rfl value = value
  transport_trans : ∀ (key : Key) {new middle old : Strategy.ProblemInput P}
    (new_middle : new.object = middle.object)
    (middle_old : middle.object = old.object) (value : Value key old),
    transport (new_middle.trans middle_old) value =
      transport new_middle (transport middle_old value)

namespace FactVocabulary

variable (vocabulary : FactVocabulary.{uAmbient, uBranch, uKey, uValue} P)

/-- Core's fact keys: the problem's own vocabulary plus the reserved closure
key.  Adding the closure key here, rather than asking a vocabulary to carry it,
is what makes `closureFactName` unforgeable by an application. -/
inductive WithClosure where
  | fact (key : vocabulary.Key)
  | closed

instance : DecidableEq vocabulary.WithClosure := by
  intro left right
  cases left <;> cases right
  · rename_i leftKey rightKey
    letI := vocabulary.keyDecidableEq
    exact decidable_of_iff (leftKey = rightKey) (by constructor <;> intro h <;> simp_all)
  · exact .isFalse (by intro h; cases h)
  · exact .isFalse (by intro h; cases h)
  · exact .isTrue rfl

end FactVocabulary

/-- The sole `FactSystem` of the problem-input domain, built from one
problem's vocabulary. -/
@[reducible] def problemInputFactSystem
    (vocabulary : FactVocabulary.{uAmbient, uBranch, uKey, uValue} P) :
    FactSystem.{max uAmbient uBranch, uAmbient, uKey, uValue}
      (Strategy.ProblemInput P) where
  Key := vocabulary.WithClosure
  keyDecidableEq := inferInstance
  name
    | .fact key => vocabulary.name key
    | .closed => Core.Residual.closureFactName
  name_injective := by
    intro left right same
    cases left <;> cases right
    · exact congrArg _ (vocabulary.name_injective same)
    · exact absurd same (vocabulary.name_ne_closure _)
    · exact absurd same.symm (vocabulary.name_ne_closure _)
    · rfl
  Value
    | .fact key, input => vocabulary.Value key input
    | .closed, _ => ULift.{uValue, 0} ClosureEvidence
  transport := by
    intro key new old refinement value
    cases key with
    | fact key => exact vocabulary.transport refinement value
    | closed => exact value
  transport_refl := by
    intro key input value
    cases key with
    | fact key => exact vocabulary.transport_refl key input value
    | closed => rfl
  transport_trans := by
    intro key _ _ _ new_middle middle_old value
    cases key with
    | fact key => exact vocabulary.transport_trans key new_middle middle_old value
    | closed => rfl
  closureKey := .closed
  closure_name := rfl
  closureValue _ evidence := ULift.up evidence
  closureEvidence _ value := value.down

end Hypostructure.Core.Strategy
