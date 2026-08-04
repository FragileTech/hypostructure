/-!
DEPRECATED: migrated to canonical CT composition strategy
(CT17 compatibility or CT7 exact contexts).
This detached feature executor is retained only as a parity oracle until
its CT-ledger equivalence theorem is kernel-checked.  It must not be
registered or executed by the framework.
-/
import Hypostructure.Graph.InducedPathMaximalPacking

/-!
# Exact attachment semantics on a packed induced-path family

Labels are reconstructed from the graph: the label of a vertex at a selected
window is exactly the set of path coordinates adjacent to that vertex.  The
safety relation is reconstructed from the registered cycle-length predicate,
so neither a label index nor a compatibility outcome is supplied by an
application.
-/

namespace Hypostructure.Graph.Strategy.Official.Features.PackedWindowAttachmentSemantics

open Hypostructure.Graph

noncomputable section

universe u

variable (object : FiniteObject.{u}) (order : Nat)
variable (packing : InducedPathMaximalPacking.Profile object order)

local instance vertexDecEq : DecidableEq object.Vertex :=
  object.vertices.decEq

/-- Literal attachment set of an ambient vertex to one induced path window. -/
def label
    (window : InducedPathMaximalPacking.Window object order)
    (vertex : object.Vertex) : Finset (Fin order) := by
  classical
  exact Finset.univ.filter fun index =>
    object.graph.Adj vertex (window index)

@[simp] theorem mem_label_iff
    (window : InducedPathMaximalPacking.Window object order)
    (vertex : object.Vertex) (index : Fin order) :
    index ∈ label object order window vertex ↔
      object.graph.Adj vertex (window index) := by
  classical
  simp [label]

def coordinateDistance (left right : Fin order) : Nat :=
  Nat.dist left.1 right.1

/-- Exact two-label safety relation through an outside connector of the
specified length. -/
def Compatible
    (CycleLengthOK : Nat → Prop) (connectorLength : Nat)
    (left right : Finset (Fin order)) : Prop :=
  ∀ leftIndex ∈ left, ∀ rightIndex ∈ right,
    ¬ CycleLengthOK
      (connectorLength + 2 + coordinateDistance order leftIndex rightIndex)

/-- Every selected window is checked in the exact packing order. -/
def SafeAcrossPacking
    (CycleLengthOK : Nat → Prop) (connectorLength : Nat)
    (left right : object.Vertex) : Prop :=
  ∀ window ∈ packing.selected,
    Compatible order CycleLengthOK connectorLength
      (label object order window left) (label object order window right)

structure Collision
    (CycleLengthOK : Nat → Prop) (connectorLength : Nat)
    (left right : object.Vertex) where
  window : InducedPathMaximalPacking.Window object order
  window_mem : window ∈ packing.selected
  leftIndex : Fin order
  left_mem : leftIndex ∈ label object order window left
  rightIndex : Fin order
  right_mem : rightIndex ∈ label object order window right
  accepted :
    CycleLengthOK
      (connectorLength + 2 +
        coordinateDistance order leftIndex rightIndex)

structure Safe
    (CycleLengthOK : Nat → Prop) (connectorLength : Nat)
    (left right : object.Vertex) where
  proof :
    SafeAcrossPacking object order packing CycleLengthOK connectorLength
      left right

inductive Result
    (CycleLengthOK : Nat → Prop) (connectorLength : Nat)
    (left right : object.Vertex)
  | collision
      (residual :
        Collision object order packing CycleLengthOK connectorLength left right)
  | safe
      (residual :
        Safe object order packing CycleLengthOK connectorLength left right)

/-- Exhaustive framework-owned semantic classification. -/
noncomputable def execute
    (CycleLengthOK : Nat → Prop)
    (cycleLengthDecidable : ∀ length, Decidable (CycleLengthOK length))
    (connectorLength : Nat) (left right : object.Vertex) :
    Result object order packing CycleLengthOK connectorLength left right := by
  classical
  letI (length : Nat) : Decidable (CycleLengthOK length) :=
    cycleLengthDecidable length
  by_cases safe :
      SafeAcrossPacking object order packing CycleLengthOK connectorLength
        left right
  · exact .safe ⟨safe⟩
  · simp only [SafeAcrossPacking, Compatible] at safe
    push Not at safe
    let window := Classical.choose safe
    have windowData := Classical.choose_spec safe
    let leftIndex := Classical.choose windowData.2
    have leftData := Classical.choose_spec windowData.2
    let rightIndex := Classical.choose leftData.2
    have rightData := Classical.choose_spec leftData.2
    exact .collision
      { window := window
        window_mem := windowData.1
        leftIndex := leftIndex
        left_mem := leftData.1
        rightIndex := rightIndex
        right_mem := rightData.1
        accepted := rightData.2 }

end

end Hypostructure.Graph.Strategy.Official.Features.PackedWindowAttachmentSemantics
