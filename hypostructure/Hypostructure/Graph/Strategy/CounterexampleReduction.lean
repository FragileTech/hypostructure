import Hypostructure.Core.Strategy.Data
import Hypostructure.Graph.CT1
import Hypostructure.Graph.DeletionCriticality
import Hypostructure.Graph.Strategy.InterfaceReplacement

/-!
# Canonical graph counterexample reduction data

Graph derives the semantic inputs for Core's standard structural continuation
from a minimum-degree problem and a cycle target.  The result contains no
executor, route, branch selector, terminal, or ledger operation.

The atomic-modification block -- `Atomic`, `Carrier`, `Related`, `Critical`,
`atomicSubobject`, `baseline_of_not_critical`, `noncritical_of_related` -- is
manuscript nodes `[9]`--`[10]`, and every one of those fields is
`Graph.minimumDegreeDeletionCriticalityProfile k`'s own, so the spine and
`Graph.DeletionCriticalityCertificate` speak about the same criticality
predicate rather than two copies of it.
-/

namespace Hypostructure.Graph.Strategy

open Hypostructure

universe u v

/-- Framework-derived semantic bundle for a minimum-degree graph problem and
an arbitrary accepted cycle-length predicate. -/
noncomputable def minimumDegreeCycleCounterexampleReduction
    (k : Nat)
    (BranchState : FiniteObject.{u} → Type v)
    (Presentation : Type)
    (presentation : Presentation)
    (LengthOK : Nat → Prop)
    (T : Core.Target
      (problemWithPresentation (MinimumDegreeAtLeast k) BranchState
        Presentation presentation))
    (targetBridge : ∀ object, T.Predicate object ↔
      HasCycleWithLength LengthOK object)
    (stateOf : ∀ object, BranchState object) :
    Core.CounterexampleReductionData.{u + 1, v, 0}
      (problemWithPresentation (MinimumDegreeAtLeast k) BranchState
        Presentation presentation) T where
  selection :=
    Core.MinimalCounterexampleSelectionData.ofProgress
      (CanonicalProgress.progress
        (P := problemWithPresentation (MinimumDegreeAtLeast k) BranchState
          Presentation presentation))
  Code := fun object =>
    ULift.{u + 1, u}
      (EdgeRootedReturn object (ShiftedCycleLength LengthOK))
  Accepts := fun _object _return => True
  target_iff_code := by
    intro object
    rw [targetBridge object, hasCycleWithLength_iff_hasEdgeRootedReturn]
    constructor
    · rintro ⟨certificate⟩
      exact ⟨ULift.up certificate, trivial⟩
    · rintro ⟨⟨certificate⟩, _⟩
      exact ⟨certificate⟩
  acceptsDecidable := fun _object _return => .isTrue trivial
  Subobject := ProperSubgraph
  subobjectProfile := {
    toAmbient := fun subgraph => subgraph.value
    smaller := by
      intro source subgraph
      exact subgraph.decreases
    targetMonotone := by
      intro source subgraph target
      apply (targetBridge source).mpr
      exact (cycleProperSubgraphTargetMonotone LengthOK).map subgraph
        ((targetBridge subgraph.value).mp target)
    stateOf := stateOf
  }
  Atomic := fun object => ULift.{u + 1, u} object.graph.Dart
  Carrier := fun object =>
    ULift.{u + 1, u}
      ((minimumDegreeDeletionCriticalityProfile k).Carrier object)
  Related := fun object left right =>
    object.graph.Adj left.down.1 right.down.1
  Critical := fun object dart =>
    (minimumDegreeDeletionCriticalityProfile k).Critical object dart.down
  atomicSubobject := fun {object} dart =>
    ProperSubgraph.deleteEdge object (object.edgeOfDart dart.down)
  baseline_of_not_critical := fun baseline dart notCritical =>
    (minimumDegreeDeletionCriticalityProfile k).baseline_of_not_critical
      baseline dart.down notCritical
  atomic_of_related := fun left right adjacent =>
    ULift.up ⟨(left.down.1, right.down.1), adjacent⟩
  noncritical_of_related := fun left right adjacent =>
    (minimumDegreeDeletionCriticalityProfile k).noncritical_of_related
      left.down right.down adjacent
  interfaceReplacement := by
    let baselineInvariant :
        FiniteObject.IsomorphismInvariant (MinimumDegreeAtLeast k) := {
      iff_of_iso := by
        intro left right equivalent
        unfold MinimumDegreeAtLeast
        rw [FiniteObject.minDegree_eq_of_isomorphic equivalent]
    }
    let semantics :=
      isomorphismEquivalenceWithPresentation
        (MinimumDegreeAtLeast k) BranchState Presentation presentation
        baselineInvariant
    let targetInvariant : Core.TargetInvariant semantics T.Predicate := {
      target_iff := by
        intro left right equivalent
        rw [targetBridge left, targetBridge right]
        rcases equivalent with ⟨iso⟩
        exact hasCycleWithLength_iff_of_iso iso LengthOK
    }
    exact
      InterfaceReplacement.profileWithPresentation
        (MinimumDegreeAtLeast k) BranchState baselineInvariant
        Presentation presentation targetInvariant

end Hypostructure.Graph.Strategy
