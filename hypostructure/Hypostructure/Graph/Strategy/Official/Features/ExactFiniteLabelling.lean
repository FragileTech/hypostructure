/-!
DEPRECATED: migrated to canonical CT composition strategy
(Producer/view: CT9 -> CT16).
This detached feature executor is retained only as a parity oracle until
its CT-ledger equivalence theorem is kernel-checked.  It must not be
registered or executed by the framework.
-/
import Hypostructure.Core.Strategy.Official.Schema
import Hypostructure.Graph.InducedPathMaximalPacking

/-!
# Exact finite labelling of a canonical packing

This adapter is graph-generic.  It combines a framework-owned maximal packing
with a complete finite label schedule and a total finite relation table.
Neither table can choose a route or assert a target; they only present the
finite coordinate language inspected by later Core strategies.
-/

namespace Hypostructure.Graph.Strategy.Official.Features.ExactFiniteLabelling

open Hypostructure
open Hypostructure.Core.Strategy.Official
open Hypostructure.Graph

universe u

structure Presentation
    (object : FiniteObject.{u}) (order : Nat)
    (packing : InducedPathMaximalPacking.Profile object order) where
  labels : ScheduleSlot
  relation : FunctionTableSlot

namespace Presentation

variable {object : FiniteObject.{u}} {order : Nat}
variable {packing : InducedPathMaximalPacking.Profile object order}
variable (presentation :
  Presentation object order packing)

/-- Exact labelled coordinates: one generated label at one selected window. -/
abbrev Coordinate :=
  {window // window ∈ packing.selected} × presentation.labels.carrier.Carrier

/-- Canonical enumeration of every labelled coordinate. -/
def coordinates : List presentation.Coordinate :=
  packing.selected.attach.flatMap fun window =>
    presentation.labels.rows.map fun label => (window, label)

/-- Every exact coordinate occurs in the generated schedule. -/
theorem mem_coordinates (coordinate : presentation.Coordinate) :
    coordinate ∈ presentation.coordinates := by
  rw [coordinates, List.mem_flatMap]
  refine ⟨coordinate.1, List.mem_attach _ _, ?_⟩
  rw [List.mem_map]
  exact ⟨coordinate.2, presentation.labels.covers coordinate.2, rfl⟩

/-- The relation table is read only through its certified total functional
graph; no caller-supplied lookup or classifier is exposed. -/
theorem relation_value (key : presentation.relation.left.Carrier) :
    ∃! value : presentation.relation.right.Carrier,
      (key, value) ∈ presentation.relation.rows := by
  obtain ⟨value, member⟩ := presentation.relation.total key
  exact ⟨value, member, fun other otherMember =>
    presentation.relation.functional otherMember member⟩

end Presentation

end Hypostructure.Graph.Strategy.Official.Features.ExactFiniteLabelling
