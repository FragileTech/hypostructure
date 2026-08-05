import Hypostructure.Core.Strategy.FactOnlyStrategy
import Hypostructure.Core.Strategy.MinimalCounterexampleScope
import Hypostructure.Graph.RootedReturn
import Hypostructure.Graph.Minimality
import Hypostructure.Graph.DeletionCriticality

/-!
# The minimum-degree cycle spine: fact vocabulary

The entry spine of a minimum-degree cycle problem proves a fixed sequence of
theorems about one selected minimal counterexample.  This module names them as
the closed semantic vocabulary of that residual domain, so each is a fact of
the one canonical `ExactLedger` rather than a payload, summary, or wrapper.

Nothing here is specialized to one manuscript.  The baseline threshold and the
accepted cycle-length predicate are parameters, so the same vocabulary serves
any minimum-degree cycle problem; a problem supplies its threshold through its
own presentation and never spells a numeral at a node.
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

/-- The problem this spine argues about: a minimum-degree baseline at the
registered threshold, with the problem's own presentation attached. -/
abbrev problem (BranchState : Graph.FiniteObject.{u} → Type v)
    (Presentation : Type) (presentation : Presentation) (threshold : Nat) :
    Core.Problem.{u + 1, v} :=
  Graph.problemWithPresentation (Graph.MinimumDegreeAtLeast threshold)
    BranchState Presentation presentation

/-- The registered progress order: vertex count, then edge count. -/
abbrev progress (BranchState : Graph.FiniteObject.{u} → Type v)
    (Presentation : Type) (presentation : Presentation) (threshold : Nat) :
    Core.Progress.{u + 1, v, 0}
      (problem BranchState Presentation presentation threshold) :=
  (Graph.CanonicalProgress.progress
    (P := problem BranchState Presentation presentation threshold))

/-- The semantic facts the entry spine proves.

Each constructor is one manuscript statement.  A key determines exactly one
value schema, so two unrelated facts cannot impersonate one another. -/
inductive Key where
  /-- Nodes `[1]`--`[4]`: the selected object avoids the target and every
  strictly smaller baseline object does not. -/
  | selection
  /-- Nodes `[5]`--`[7]`: the return-length set is disjoint from the shifted
  accepted set at every oriented edge.  This is the return-set form of target
  avoidance, the standing invariant the rest of the spine consumes. -/
  | returnAvoidance
  /-- Node `[8]`: no proper subgraph satisfies the baseline. -/
  | noProperBaseline
  /-- Node `[9]`: every oriented edge has an endpoint exactly at the
  threshold. -/
  | tightEndpoint
  /-- Node `[10]`: vertices strictly above the threshold are pairwise
  nonadjacent. -/
  | slackIndependent
  deriving DecidableEq

/-- The value schema of each spine fact, stated of the *object* alone.

Every spine fact is a statement about the selected graph, never about the
branch state carried beside it.  Making that explicit is what lets a fact
transport along a refinement by a rewrite: refinement is object equality. -/
def Holds (BranchState : Graph.FiniteObject.{u} → Type v)
    (Presentation : Type) (presentation : Presentation)
    (threshold : Nat) (LengthOK : Nat → Prop) :
    Key → Graph.FiniteObject.{u} → Prop
  | .selection, object =>
      (¬ Graph.HasCycleWithLength LengthOK object ∧
        ∀ smaller : Graph.FiniteObject.{u},
          (progress BranchState Presentation presentation threshold).Smaller
            smaller object →
          Graph.MinimumDegreeAtLeast threshold smaller →
          Graph.HasCycleWithLength LengthOK smaller)
  | .returnAvoidance, object =>
      (∀ dart : object.graph.Dart,
        Disjoint (Graph.returnLengthSet object dart)
          (Graph.shiftedAcceptedSet LengthOK))
  | .noProperBaseline, object =>
      (∀ subgraph : Graph.ProperSubgraph object,
        ¬ Graph.MinimumDegreeAtLeast threshold subgraph.value)
  | .tightEndpoint, object =>
      (∀ dart : object.graph.Dart,
        object.degree dart.fst = threshold ∨
          object.degree dart.snd = threshold)
  | .slackIndependent, object =>
      (∀ left right : object.Vertex,
        threshold < object.degree left →
        threshold < object.degree right →
        ¬ object.graph.Adj left right)

/-- Audit names.  They are diagnostics; every routing and lookup decision
compares exact keys. -/
def name : Key → Lean.Name
  | .selection => `Hypostructure.Graph.Strategy.Spine.selection
  | .returnAvoidance => `Hypostructure.Graph.Strategy.Spine.returnAvoidance
  | .noProperBaseline => `Hypostructure.Graph.Strategy.Spine.noProperBaseline
  | .tightEndpoint => `Hypostructure.Graph.Strategy.Spine.tightEndpoint
  | .slackIndependent => `Hypostructure.Graph.Strategy.Spine.slackIndependent

/-- The value schema at a residual: the object-level statement, read at the
residual's own object. -/
def Value (BranchState : Graph.FiniteObject.{u} → Type v)
    (Presentation : Type) (presentation : Presentation)
    (threshold : Nat) (LengthOK : Nat → Prop)
    (k : Key)
    (input : Core.Strategy.ProblemInput
      (problem BranchState Presentation presentation threshold)) : Type :=
  PLift (Holds BranchState Presentation presentation threshold LengthOK k
    input.object)

theorem name_injective : Function.Injective name := by
  intro left right same
  cases left <;> cases right <;> simp_all [name]

/-- The spine's closed fact vocabulary.  Every value depends on the residual
only through its object, so transport along a refinement is a rewrite. -/
def vocabulary (BranchState : Graph.FiniteObject.{u} → Type v)
    (Presentation : Type) (presentation : Presentation)
    (threshold : Nat) (LengthOK : Nat → Prop) :
    FactVocabulary.{u + 1, v, 0, 0}
      (problem BranchState Presentation presentation threshold) where
  Key := Key
  keyDecidableEq := inferInstance
  name := name
  name_injective := name_injective
  name_ne_closure := by intro key; cases key <;> decide
  Value := Value BranchState Presentation presentation threshold LengthOK
  transport := fun {_key} {_new _old} refinement value =>
    ⟨by rw [show _new.object = _old.object from refinement]; exact value.down⟩
  transport_refl := by
    intro _ _ value; cases value; rfl
  transport_trans := by
    intro _ _ _ _ _ _ value; cases value; rfl

/-- The spine's sole `FactSystem`.  It is a definition rather than an
instance because the accepted length predicate is a parameter of the spine,
not of the problem; a caller installs it with `letI` for the run it is
compiling. -/
noncomputable def factSystem
    (BranchState : Graph.FiniteObject.{u} → Type v)
    (Presentation : Type) (presentation : Presentation)
    (threshold : Nat) (LengthOK : Nat → Prop) :
    FactSystem
      (Core.Strategy.ProblemInput
        (problem BranchState Presentation presentation threshold)) :=
  problemInputFactSystem
    (vocabulary BranchState Presentation presentation threshold LengthOK)

/-- The exact semantic keys, as callers name them. -/
abbrev key (BranchState : Graph.FiniteObject.{u} → Type v)
    (Presentation : Type) (presentation : Presentation)
    (threshold : Nat) (LengthOK : Nat → Prop) (k : Key) :
    @FactKey _ _
      (factSystem BranchState Presentation presentation threshold LengthOK) :=
  FactVocabulary.WithClosure.fact k

end Hypostructure.Graph.Strategy.Spine
