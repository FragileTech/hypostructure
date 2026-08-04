import Hypostructure.Graph.Target
import Hypostructure.Graph.DeletionCriticality

/-!
# Minimum-degree cycle targets and their pinned public statements

A minimum-degree cycle problem states its public theorem in Mathlib's own
`SimpleGraph` vocabulary, with the accepted cycle length presented through a
free exponent rather than through the executable length predicate the strategy
layer consumes.  Graph owns both directions of that bridge, so an application
registers only

* its baseline threshold `k`,
* its executable length predicate `LengthOK`,
* the exponent presentation `Index`/`lengthOf` of the pinned statement, and
* the completeness theorem tying the two together,

and supplies no proof.
-/

namespace Hypostructure.Graph

open Hypostructure

universe u v

/-- The public shape of a minimum-degree cycle theorem, written in Mathlib's
`SimpleGraph` vocabulary with the accepted length presented by a free
exponent.  This is exactly the form in which such statements are pinned
externally. -/
def IndexedCycleStatement (k : Nat) (Index : Nat → Prop)
    (lengthOf : Nat → Nat) : Prop :=
  ∀ (V : Type u) (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj],
    G.minDegree ≥ k →
      ∃ (index : Nat) (vertex : V) (cycle : G.Walk vertex vertex),
        Index index ∧ cycle.IsCycle ∧ cycle.length = lengthOf index

/-- The packed cycle target is exactly the conclusion of the pinned statement
for the same underlying graph. -/
theorem hasCycleWithLength_iff_indexed
    {LengthOK Index : Nat → Prop} {lengthOf : Nat → Nat}
    (bridge : ∀ length, LengthOK length ↔
      ∃ index, Index index ∧ length = lengthOf index)
    (object : FiniteObject.{u}) :
    HasCycleWithLength LengthOK object ↔
      ∃ (index : Nat) (vertex : object.Vertex)
        (cycle : object.graph.Walk vertex vertex),
        Index index ∧ cycle.IsCycle ∧ cycle.length = lengthOf index := by
  constructor
  · rintro ⟨certificate⟩
    obtain ⟨index, indexed, lengthEq⟩ :=
      (bridge certificate.walk.length).mp certificate.length_ok
    exact ⟨index, certificate.vertex, certificate.walk, indexed,
      certificate.isCycle, lengthEq⟩
  · rintro ⟨index, vertex, cycle, indexed, isCycle, lengthEq⟩
    exact ⟨{
      vertex := vertex
      walk := cycle
      isCycle := isCycle
      length_ok := (bridge cycle.length).mpr ⟨index, indexed, lengthEq⟩
    }⟩

/-- The minimum-degree baseline descends through packed graph isomorphism. -/
def minimumDegreeAtLeast_isomorphismInvariant (k : Nat) :
    FiniteObject.IsomorphismInvariant (MinimumDegreeAtLeast.{u} k) where
  iff_of_iso := by
    intro left right equivalent
    unfold MinimumDegreeAtLeast
    rw [FiniteObject.minDegree_eq_of_isomorphic equivalent]

/-- The Core target of a minimum-degree cycle problem, whose `Statement` is
the pinned public proposition and whose `Predicate` is the packed executable
cycle target.  Both transport directions are framework-owned. -/
def minimumDegreeCycleTarget
    (k : Nat)
    (BranchState : FiniteObject.{u} → Type v)
    (Presentation : Type) (presentation : Presentation)
    (LengthOK Index : Nat → Prop) (lengthOf : Nat → Nat)
    (bridge : ∀ length, LengthOK length ↔
      ∃ index, Index index ∧ length = lengthOf index) :
    Core.Target
      (problemWithPresentation (MinimumDegreeAtLeast.{u} k) BranchState
        Presentation presentation) where
  Predicate := HasCycleWithLength LengthOK
  Statement := IndexedCycleStatement.{u} k Index lengthOf
  statement_to_target := by
    intro statement object baseline
    letI : Fintype object.Vertex := @FinEnum.instFintype _ object.vertices
    letI : DecidableRel object.graph.Adj := object.decideAdj
    apply (hasCycleWithLength_iff_indexed bridge object).mpr
    simpa [MinimumDegreeAtLeast] using
      statement object.Vertex object.graph baseline
  target_to_statement := by
    intro closure V G _ _ minimumDegree
    let vertices : FinEnum V :=
      FinEnum.ofEquiv (Fin (Fintype.card V)) (Fintype.equivFin V)
    let object : FiniteObject.{u} := FiniteObject.of G vertices inferInstance
    have baseline : MinimumDegreeAtLeast.{u} k object := by
      have fintype_eq :
          (inferInstance : Fintype V) = @FinEnum.instFintype _ vertices :=
        Subsingleton.elim _ _
      have decide_eq :
          (inferInstance : DecidableRel G.Adj) = object.decideAdj :=
        Subsingleton.elim _ _
      unfold MinimumDegreeAtLeast
      change k ≤ @SimpleGraph.minDegree V G
        (@FinEnum.instFintype _ vertices) object.decideAdj
      rw [← fintype_eq, ← decide_eq]
      exact minimumDegree
    rcases (hasCycleWithLength_iff_indexed bridge object).mp
      (closure object baseline) with
      ⟨index, vertex, cycle, indexed, isCycle, lengthEq⟩
    exact ⟨index, vertex, cycle, indexed, isCycle, lengthEq⟩

/-- Core semantics of a minimum-degree cycle problem, obtained from the graph
layer's own isomorphism invariance. -/
def minimumDegreeIsomorphismSemantics
    (k : Nat)
    (BranchState : FiniteObject.{u} → Type v)
    (Presentation : Type) (presentation : Presentation) :
    Core.SemanticEquivalence
      (problemWithPresentation (MinimumDegreeAtLeast.{u} k) BranchState
        Presentation presentation) :=
  isomorphismEquivalenceWithPresentation (MinimumDegreeAtLeast.{u} k)
    BranchState Presentation presentation
    (minimumDegreeAtLeast_isomorphismInvariant k)

/-- Core target invariance for a minimum-degree cycle problem. -/
def minimumDegreeCycleTargetInvariant
    (k : Nat)
    (BranchState : FiniteObject.{u} → Type v)
    (Presentation : Type) (presentation : Presentation)
    (LengthOK : Nat → Prop) :
    Core.TargetInvariant
      (minimumDegreeIsomorphismSemantics k BranchState Presentation
        presentation)
      (HasCycleWithLength LengthOK) :=
  (cycleTargetInterface LengthOK).coreInvariantWithPresentation
    (MinimumDegreeAtLeast.{u} k) BranchState Presentation presentation
    (minimumDegreeAtLeast_isomorphismInvariant k)

end Hypostructure.Graph
