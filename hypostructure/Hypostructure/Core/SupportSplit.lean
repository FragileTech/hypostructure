import Hypostructure.Core.Finite.Enumeration
import Hypostructure.Core.Residual.Query

namespace Hypostructure.Core.SupportSplit

universe u

/-! Domain-neutral negative-support split.  A graph or PDE adapter supplies
the carrier, a finite ordered schedule, and the local charge semantics. -/

structure Parameters where
  baseline : Nat
  scale : Nat

structure Source (Carrier : Type u) where
  core : Finset Carrier
  cells : Finite.Enumeration Carrier
  cells_toFinset : cells.toFinset = core
  charge : Carrier -> Int
  negative : (cells.values.map charge).sum < 0

@[simp] theorem cells_mem_iff {Carrier : Type u} (source : Source Carrier)
    (carrier : Carrier) :
    carrier ∈ source.cells.values ↔ carrier ∈ source.core := by
  rw [← Finite.Enumeration.mem_toFinset source.cells carrier]
  rw [source.cells_toFinset]

/-- **A negatively charged source is nonempty.**

The sum over an empty cell list is `0`, so `negative` already rules the empty
support out.  `def:net-charge`'s selection of a support with `No(X) < 0` carries
this implicitly; it is published here, at the node that records the negative
charge, so every later stage retrieves it from the ledger instead of
re-deriving it. -/
theorem core_nonempty {Carrier : Type u} (source : Source Carrier) :
    source.core.Nonempty := by
  by_contra empty
  rw [Finset.not_nonempty_iff_eq_empty] at empty
  have values_nil : source.cells.values = [] := by
    rw [List.eq_nil_iff_forall_not_mem]
    intro carrier member
    have inCore : carrier ∈ source.core := (cells_mem_iff source carrier).mp member
    rw [empty] at inCore
    simp at inCore
  have negative := source.negative
  rw [values_nil] at negative
  simp at negative

/-- The cardinality form of `core_nonempty`, in the shape a member-count ledger
entry reads. -/
theorem card_core_pos {Carrier : Type u} (source : Source Carrier) :
    0 < source.core.card :=
  Finset.card_pos.mpr (core_nonempty source)

structure HighSplit (Carrier : Type u) (source : Source Carrier) where
  high : Carrier -> Prop
  high_decidable : ∀ carrier, Decidable (high carrier)

def highValues {Carrier : Type u} {source : Source Carrier}
    (split : HighSplit Carrier source) : List Carrier :=
  letI : ∀ carrier, Decidable (split.high carrier) := split.high_decidable
  source.cells.values.filter (fun carrier => decide (split.high carrier))

inductive Outcome (Carrier : Type u) (source : Source Carrier)
    (split : HighSplit Carrier source) where
  | high (value : Carrier) (member : value ∈ highValues split) : Outcome Carrier source split
  | low (none : highValues split = []) : Outcome Carrier source split

def execute {Carrier : Type u} {source : Source Carrier}
    (split : HighSplit Carrier source) : Outcome Carrier source split := by
  classical
  cases h : highValues split with
  | nil => exact .low h
  | cons value rest => exact .high value (by simp [h])

theorem outcome_cases {Carrier : Type u} {source : Source Carrier}
    {split : HighSplit Carrier source} (outcome : Outcome Carrier source split) :
    (∃ value, ∃ member, outcome = .high value member) ∨
      (∃ none, outcome = .low none) := by
  cases outcome with
  | high value member => exact Or.inl ⟨value, member, rfl⟩
  | low none => exact Or.inr ⟨none, rfl⟩

/-! ## Predecessor-query projections -/

namespace QuerySurface

universe uPrevious

variable {Previous : Sort uPrevious}

open Hypostructure.Core.Residual

abbrev SourceQuery (Carrier : Type u) :=
  Query Previous (fun _previous => Source Carrier)

def highValuesQuery {Carrier : Type u}
    (source : SourceQuery (Previous := Previous) Carrier)
    (split : Query Previous (fun previous =>
      HighSplit Carrier (source previous))) :
    Query Previous (fun _previous => List Carrier) :=
  split.map fun _previous activeSplit => highValues activeSplit

def outcomeQuery {Carrier : Type u}
    (source : SourceQuery (Previous := Previous) Carrier)
    (split : Query Previous (fun previous =>
      HighSplit Carrier (source previous))) :
    Query Previous (fun previous =>
      Outcome Carrier (source previous) (split previous)) :=
  split.dependentMap fun _previous activeSplit => execute activeSplit

def stageNode {Carrier : Type u}
    (source : SourceQuery (Previous := Previous) Carrier)
    (split : Query Previous (fun previous =>
      HighSplit Carrier (source previous))) :
    StageNode Previous (fun previous =>
      Outcome Carrier (source previous) (split previous)) :=
  StageNode.derive (outcomeQuery source split)
    (fun _previous outcome => outcome)

end QuerySurface

end Hypostructure.Core.SupportSplit
