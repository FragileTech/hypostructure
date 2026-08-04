/-!
DEPRECATED: migrated to canonical CT composition strategy
(Producer/view: predecessor support query).
This detached feature executor is retained only as a parity oracle until
its CT-ledger equivalence theorem is kernel-checked.  It must not be
registered or executed by the framework.
-/
import Hypostructure.Graph.InducedPathMaximalPacking

/-! Exact support selected by a finite induced-path packing. -/

namespace Hypostructure.Graph.Strategy.Official.Features.PackedSupport

open Hypostructure.Graph

universe u

def union (object : FiniteObject.{u}) [DecidableEq object.Vertex]
    (order : Nat) :
    List (InducedPathMaximalPacking.Window object order) →
      Finset object.Vertex
  | [] => ∅
  | window :: tail =>
      InducedPathMaximalPacking.support object order window ∪
        union object order tail

def selected (object : FiniteObject.{u}) [DecidableEq object.Vertex]
    (order : Nat)
    (profile : InducedPathMaximalPacking.Profile object order) :
    Finset object.Vertex :=
  union object order profile.selected

theorem support_subset_union
    (object : FiniteObject.{u}) [DecidableEq object.Vertex]
    (order : Nat)
    (windows : List (InducedPathMaximalPacking.Window object order))
    {window : InducedPathMaximalPacking.Window object order}
    (member : window ∈ windows) :
    InducedPathMaximalPacking.support object order window ⊆
      union object order windows := by
  intro vertex vertex_mem
  induction windows generalizing window with
  | nil => simp only [List.not_mem_nil] at member
  | cons head tail ih =>
      rw [union, Finset.mem_union]
      rcases List.mem_cons.mp member with rfl | member
      · exact Or.inl vertex_mem
      · exact Or.inr (ih member vertex_mem)

theorem support_subset_selected
    (object : FiniteObject.{u}) [DecidableEq object.Vertex]
    (order : Nat)
    (profile : InducedPathMaximalPacking.Profile object order)
    {window : InducedPathMaximalPacking.Window object order}
    (member : window ∈ profile.selected) :
    InducedPathMaximalPacking.support object order window ⊆
      selected object order profile :=
  support_subset_union object order profile.selected member

theorem selected_subset_vertices
    (object : FiniteObject.{u}) [DecidableEq object.Vertex]
    (order : Nat)
    (profile : InducedPathMaximalPacking.Profile object order) :
    selected object order profile ⊆ object.vertexFinset := by
  intro vertex _
  exact object.mem_vertexFinset vertex

end Hypostructure.Graph.Strategy.Official.Features.PackedSupport
