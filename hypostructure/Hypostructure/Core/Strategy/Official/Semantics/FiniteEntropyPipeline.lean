import Hypostructure.Core.FiniteEntropy
import Mathlib.Data.Finset.Card

/-!
# Residual-owned finite entropy pipeline

This kernel computes packedness, state demand, curvature cost, realization,
ambient capacity, and the entropy-cap comparison from finite tables.  It is
domain-neutral: Graph and PDE adapters need only expose the same raw finite
observations.
-/

namespace Hypostructure.Core.Strategy.Official.Semantics.FiniteEntropyPipeline

/-- One packed-window candidate and its raw local state/cost table. -/
structure Window where
  support : Finset Nat
  stateCodes : List Nat
  curvatureCosts : List Nat

namespace Window

def stateCount (window : Window) : Nat :=
  window.stateCodes.eraseDups.length

def curvatureCost (window : Window) : Nat :=
  window.curvatureCosts.sum

end Window

/-- All fields are literal residual tables.  Repetition is harmless:
capacities and local state counts are computed after duplicate removal. -/
structure Input where
  windows : List Window
  realizedCodes : List Nat
  ambientCodes : List Nat

def packed (input : Input) : Prop :=
  input.windows.Pairwise fun left right => Disjoint left.support right.support

instance (input : Input) : Decidable (packed input) :=
  inferInstanceAs (Decidable
    (input.windows.Pairwise fun left right =>
      Disjoint left.support right.support))

def stateDemand (input : Input) : Nat :=
  (input.windows.map Window.stateCount).prod

def curvatureCost (input : Input) : Nat :=
  (input.windows.map Window.curvatureCost).sum

def ambientCapacity (input : Input) : Nat :=
  input.ambientCodes.toFinset.card

/-- A table realizes the complete demanded state family exactly when it lists
one distinct ambient code per computed joint state. -/
def Realizes (input : Input) : Prop :=
  input.realizedCodes.Nodup ∧
  input.realizedCodes.length = stateDemand input ∧
  input.ambientCodes.Nodup ∧
  ∀ code ∈ input.realizedCodes, code ∈ input.ambientCodes

instance (input : Input) : Decidable (Realizes input) :=
  inferInstanceAs (Decidable
    (input.realizedCodes.Nodup ∧
      input.realizedCodes.length = stateDemand input ∧
      input.ambientCodes.Nodup ∧
      ∀ code ∈ input.realizedCodes, code ∈ input.ambientCodes))

inductive PackedTerminal (input : Input) where
  | independent (proof : packed input)
  | overlap (proof : ¬ packed input)

def classifyPacked (input : Input) : PackedTerminal input :=
  if h : packed input then .independent h else .overlap h

inductive RealizationTerminal (input : Input) where
  | realized (proof : Realizes input)
  | incomplete (proof : ¬ Realizes input)

def classifyRealization (input : Input) : RealizationTerminal input :=
  if h : Realizes input then .realized h else .incomplete h

theorem nodup_length_mono_of_subset
    {left right : List Nat}
    (leftNodup : left.Nodup)
    (rightNodup : right.Nodup)
    (subset : ∀ code ∈ left, code ∈ right) :
    left.length ≤ right.length := by
  rw [← List.toFinset_card_of_nodup leftNodup,
    ← List.toFinset_card_of_nodup rightNodup]
  apply Finset.card_le_card
  intro code member
  simp only [List.mem_toFinset] at member ⊢
  exact subset code member

theorem demand_le_capacity (input : Input) (realizes : Realizes input) :
    stateDemand input ≤ ambientCapacity input := by
  rcases realizes with ⟨realizedNodup, count, ambientNodup, subset⟩
  rw [← count, ambientCapacity,
    List.toFinset_card_of_nodup ambientNodup]
  exact nodup_length_mono_of_subset realizedNodup ambientNodup subset

/-- The entropy-cap contradiction.  Both numerical sides are definitions
computed from the input tables; neither is supplied as a theorem parameter. -/
theorem entropyCapContradiction (input : Input)
    (realizes : Realizes input)
    (overflow : ambientCapacity input < stateDemand input) :
    False :=
  (Nat.not_lt_of_ge (demand_le_capacity input realizes)) overflow

/-- Exhaustive framework-owned cap comparison. -/
inductive EntropyCapTerminal (input : Input) where
  | withinCap (proof : stateDemand input ≤ ambientCapacity input)
  | exceedsCap (proof : ambientCapacity input < stateDemand input)

def classifyEntropyCap (input : Input) : EntropyCapTerminal input :=
  if h : stateDemand input ≤ ambientCapacity input then .withinCap h
  else .exceedsCap (lt_of_not_ge h)

/-- One immutable execution report for S07. -/
structure Report (input : Input) where
  packedness : PackedTerminal input
  realization : RealizationTerminal input
  cap : EntropyCapTerminal input
  demand : Nat
  demand_eq : demand = stateDemand input
  cost : Nat
  cost_eq : cost = curvatureCost input
  capacity : Nat
  capacity_eq : capacity = ambientCapacity input
  checks : Nat
  checks_eq :
    checks =
      input.windows.length * input.windows.length +
      input.realizedCodes.length + input.ambientCodes.length

def execute (input : Input) : Report input where
  packedness := classifyPacked input
  realization := classifyRealization input
  cap := classifyEntropyCap input
  demand := stateDemand input
  demand_eq := rfl
  cost := curvatureCost input
  cost_eq := rfl
  capacity := ambientCapacity input
  capacity_eq := rfl
  checks :=
    input.windows.length * input.windows.length +
      input.realizedCodes.length + input.ambientCodes.length
  checks_eq := rfl

end Hypostructure.Core.Strategy.Official.Semantics.FiniteEntropyPipeline
