import Hypostructure.Core.Problem
import Hypostructure.Core.Strategy.OfficialRegistry

/-!
# Callback-free official problem schemas

An official presentation is finite mathematical data.  Its fields may name
carriers, relations, rows, and bounds, but never executable strategy code.
In particular, none of the structures below has a field returning a route,
branch, transition, terminal, or target proof.
-/

namespace Hypostructure.Core.Strategy.Official

universe u v

/-- A finite carrier presented extensionally. -/
structure FiniteCarrier where
  Carrier : Type u
  finite : Fintype Carrier
  decidableEq : DecidableEq Carrier := Classical.decEq Carrier

attribute [instance] FiniteCarrier.finite
attribute [instance] FiniteCarrier.decidableEq

namespace FiniteCarrier

/-- Canonical carrier wrapper; no extensional rows or outcomes are authored. -/
def ofFintype (α : Type) [Fintype α] [DecidableEq α] : FiniteCarrier where
  Carrier := α
  finite := inferInstance
  decidableEq := inferInstance

end FiniteCarrier

/-- A finite schedule is data, not an iterator or transition function. -/
structure ScheduleSlot where
  carrier : FiniteCarrier
  rows : List carrier.Carrier
  covers : ∀ x, x ∈ rows

namespace ScheduleSlot

/-- Complete canonical schedule of a finite type. -/
noncomputable def ofFintype
    (α : Type) [Fintype α] [DecidableEq α] : ScheduleSlot where
  carrier := FiniteCarrier.ofFintype α
  rows := Finset.univ.toList
  covers := by simp

end ScheduleSlot

/-- A finite relation presented by its complete list of rows. -/
structure RelationSlot where
  left : FiniteCarrier
  right : FiniteCarrier
  rows : List (left.Carrier × right.Carrier)

/-- A total single-valued finite observation table.

`total` and `functional` certify only the extensional table.  They cannot
choose a strategy branch: framework code performs lookup and interprets the
official strategy identifier. -/
structure FunctionTableSlot extends RelationSlot where
  total : ∀ x, ∃ y, (x, y) ∈ rows
  functional : ∀ {x y z}, (x, y) ∈ rows -> (x, z) ∈ rows -> y = z

namespace FunctionTableSlot

/-- Total extensional table generated from a mathematical finite function. -/
noncomputable def ofFunction (α : Type) (β : Type)
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (function : α → β) : FunctionTableSlot where
  left := FiniteCarrier.ofFintype α
  right := FiniteCarrier.ofFintype β
  rows := Finset.univ.toList.map fun input => (input, function input)
  total := by
    intro input
    exact ⟨function input, by simp⟩
  functional := by
    intro input leftValue rightValue leftMem rightMem
    simp at leftMem rightMem
    exact leftMem.symm.trans rightMem

end FunctionTableSlot

/-- A finite family of natural-number resources or costs. -/
structure NatTableSlot where
  key : FiniteCarrier
  rows : List (key.Carrier × Nat)
  total : ∀ x, ∃ n, (x, n) ∈ rows
  functional : ∀ {x m n}, (x, m) ∈ rows -> (x, n) ∈ rows -> m = n

/-- A certified finite bound.  The proposition talks only about the inert
table and cannot close a target. -/
structure BoundSlot where
  values : List Nat
  bound : Nat
  bounded : ∀ n, n ∈ values -> n ≤ bound

/-- Presentation slots understood by framework-owned Core strategies. -/
structure CoreSchema where
  schedules : List ScheduleSlot := []
  responseTables : List FunctionTableSlot := []
  capacityTables : List NatTableSlot := []
  supportRelations : List RelationSlot := []
  rankTables : List NatTableSlot := []
  closedCodeTables : List FunctionTableSlot := []
  bounds : List BoundSlot := []

/-- Graph-owned mathematical slots.  They contain graph-independent finite
relations here; the Graph framework layer supplies their canonical semantics
and executor. -/
structure GraphSchema where
  rootedReturnTables : List RelationSlot := []
  targetDefectTables : List RelationSlot := []
  decoratedFanTables : List RelationSlot := []

/-- PDE-owned represented mathematical slots.  The PDE framework layer,
rather than an application, supplies their analytic interpretation. -/
structure PDESchema where
  representedSupports : List RelationSlot := []
  representedFluxTables : List NatTableSlot := []
  representedDefectTables : List RelationSlot := []

/-- The complete callback-free presentation visible to official strategies. -/
structure ProblemSchema where
  core : CoreSchema := {}
  graph : GraphSchema := {}
  pde : PDESchema := {}

end Hypostructure.Core.Strategy.Official
