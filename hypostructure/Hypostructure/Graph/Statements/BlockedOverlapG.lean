import Hypostructure.Graph.Statements.Spine

/-!
# Statements: the overlap support of G's own completions (`def:barrier-overlap-system`, `[172a]`)

For G's own skeleton (the member of `𝓑(𝒫)` given by `K .blockedClassMember`) and each
exposure coordinate (window `P` of the packing, scale `2^j`, barrier row `(a,b)`), the canonical
completion support of `def:barrier-overlap-system` is the one the barrier state reads
(`Graph/BarrierOverlapSystem.lean`, `barrierState`: the fixed choice `support.some`).  Its
vertex set is the support of the closed walk *first arm, second arm, completion* through `P`.
Two windows of the same scale and row *overlap* when their supports meet outside the two
root-window interiors; the overlap support of a coordinate is the union of the supports over the
overlap component of the coordinate.  Everything is a construction on G's own graph.

This module imports no strategy, row, or vocabulary module.
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure

universe u

/-- The completion supports of a member of `𝓑(𝒫)` at a coordinate. -/
abbrev BlockedCompletionSupport (data : Parameters) (object : Graph.FiniteObject.{u})
    (member : blockedClassAt data object) (coordinate : blockedCoordinate data object) : Type :=
  Graph.BarrierSystem.CompletionSupport data.windowOrder member.1.1.1
    ((blockedWindowLabels data object).biUnion id) coordinate.1.1.1
    (barrierLegs data coordinate.2).1 (barrierLegs data coordinate.2).2
    (2 ^ coordinate.1.2.1)

/-- The closed walk of a completion support: first arm, second arm, completion. -/
def blockedSupportWalk (data : Parameters) (object : Graph.FiniteObject.{u})
    (member : blockedClassAt data object) (coordinate : blockedCoordinate data object)
    (support : BlockedCompletionSupport data object member coordinate) :
    member.1.1.1.graph.Walk support.source support.source :=
  (support.firstArm.append support.secondArm).append support.completion

/-- The vertex set of the canonical completion support of a coordinate (empty when the
barrier state is absent). -/
noncomputable def blockedSupportVertices (data : Parameters)
    (object : Graph.FiniteObject.{u}) (member : blockedClassAt data object)
    (coordinate : blockedCoordinate data object) : Finset (Fin object.vertexCount) := by
  classical
  exact if h : Nonempty (BlockedCompletionSupport data object member coordinate) then
    (blockedSupportWalk data object member coordinate h.some).support.toFinset
  else ∅

/-- Two coordinates of the same scale and row, on different windows, overlap: their completion
supports meet outside the two root-window interiors. -/
def blockedOverlapAdj (data : Parameters) (object : Graph.FiniteObject.{u})
    (member : blockedClassAt data object)
    (left right : blockedCoordinate data object) : Prop :=
  left.1.2 = right.1.2 ∧ left.2 = right.2 ∧ left.1.1 ≠ right.1.1 ∧
    ((blockedSupportVertices data object member left ∩
        blockedSupportVertices data object member right) \
      (left.1.1.1 ∪ right.1.1.1)).Nonempty

/-- The overlap support of a coordinate: the union of the completion supports over its overlap
component. -/
def blockedOverlapUnion (data : Parameters) (object : Graph.FiniteObject.{u})
    (member : blockedClassAt data object) (coordinate : blockedCoordinate data object) :
    Set (Fin object.vertexCount) :=
  {vertex | ∃ other, Relation.ReflTransGen (blockedOverlapAdj data object member)
      coordinate other ∧ vertex ∈ blockedSupportVertices data object member other}

/-- **G's overlap support.**  For G's own skeleton, at every coordinate: each completion support
has at most `2^j + 1` vertices; a present one is the support of a closed walk of length `2^j`
in G through a vertex of the root window which is not a cycle (G has no accepted cycle
through a window, so the completion retraces or self-overlaps); and the overlap support of the
coordinate is connected in G. -/
def BlockedOverlapSupportStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∃ own : blockedClassAt data object,
    own.1.1 = Graph.BlockedClass.objectSkeletonMember object ∧
    (∀ coordinate : blockedCoordinate data object,
      (blockedSupportVertices data object own coordinate).card ≤
        2 ^ coordinate.1.2.1 + 1) ∧
    (∀ coordinate : blockedCoordinate data object,
      (blockedSupportVertices data object own coordinate).Nonempty →
        ∃ (start : Fin object.vertexCount) (walk : own.1.1.1.graph.Walk start start),
          walk.length = 2 ^ coordinate.1.2.1 ∧ ¬ walk.IsCycle ∧
          blockedSupportVertices data object own coordinate = walk.support.toFinset ∧
          ∃ vertex ∈ walk.support, vertex ∈ coordinate.1.1.1) ∧
    ∀ (coordinate : blockedCoordinate data object)
      (u v : Fin object.vertexCount),
      u ∈ blockedOverlapUnion data object own coordinate →
      v ∈ blockedOverlapUnion data object own coordinate →
      own.1.1.1.graph.Reachable u v

end Hypostructure.Graph.Strategy.Spine
