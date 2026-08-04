import Mathlib.Data.Int.Basic
import Mathlib.Data.List.Defs

/-!
# Residual-owned sparse-surplus and hot/cold refinement

The input is one finite table of raw observations.  All classifications and
all numerical ledger entries are computed from that table.  In particular,
there is no selector, threshold callback, route, or authored aggregate.
-/

namespace Hypostructure.Core.Strategy.Official.Semantics.SparseSurplusRefinement

/-- One residual-owned observation.  Every numerical parameter, including the
acceptance requirement, is a column of the finite presentation table. -/
structure Row where
  baseline : Nat
  observed : Nat
  attempts : Nat
  successes : Nat
  requiredSuccesses : Nat
  deriving DecidableEq, Repr

namespace Row

def surplus (row : Row) : Int :=
  Int.ofNat row.observed - Int.ofNat row.baseline

def isSparse (row : Row) : Bool :=
  row.observed ≤ row.baseline

def isHot (row : Row) : Bool :=
  row.requiredSuccesses ≤ row.successes

end Row

/-- A well-formed finite residual table.  The proof only certifies that the
raw success counter came from the represented attempts; it chooses no route. -/
structure Input where
  rows : List Row
  successes_le_attempts :
    ∀ row ∈ rows, row.successes ≤ row.attempts
  required_le_attempts :
    ∀ row ∈ rows, row.requiredSuccesses ≤ row.attempts

def sparseRows (input : Input) : List Row :=
  input.rows.filter Row.isSparse

def denseRows (input : Input) : List Row :=
  input.rows.filter fun row => !row.isSparse

def hotRows (input : Input) : List Row :=
  input.rows.filter Row.isHot

def coldRows (input : Input) : List Row :=
  input.rows.filter fun row => !row.isHot

def totalSurplus (input : Input) : Int :=
  (input.rows.map Row.surplus).sum

def sparseSurplus (input : Input) : Int :=
  ((sparseRows input).map Row.surplus).sum

def denseSurplus (input : Input) : Int :=
  ((denseRows input).map Row.surplus).sum

private theorem sum_filter_add_sum_filter_not
    (rows : List Row) (classify : Row → Bool) (value : Row → Int) :
    ((rows.filter classify).map value).sum +
        ((rows.filter fun row => !classify row).map value).sum =
      (rows.map value).sum := by
  induction rows with
  | nil => simp
  | cons row tail ih =>
      cases h : classify row <;> simp [h] at ih ⊢ <;> omega

private theorem length_filter_add_length_filter_not
    (rows : List Row) (classify : Row → Bool) :
    (rows.filter classify).length +
        (rows.filter fun row => !classify row).length =
      rows.length := by
  induction rows with
  | nil => simp
  | cons row tail ih =>
      cases h : classify row <;> simp [h] at ih ⊢ <;> omega

/-- The complete computed S04 ledger. -/
structure Ledger (input : Input) where
  sparse : List Row
  sparse_eq : sparse = sparseRows input
  dense : List Row
  dense_eq : dense = denseRows input
  hot : List Row
  hot_eq : hot = hotRows input
  cold : List Row
  cold_eq : cold = coldRows input
  total : Int
  total_eq : total = totalSurplus input
  sparseTotal : Int
  sparseTotal_eq : sparseTotal = sparseSurplus input
  denseTotal : Int
  denseTotal_eq : denseTotal = denseSurplus input
  surplus_split : total = sparseTotal + denseTotal
  row_split : sparse.length + dense.length = input.rows.length
  temperature_split : hot.length + cold.length = input.rows.length
  checks : Nat
  checks_eq : checks = 2 * input.rows.length

def execute (input : Input) : Ledger input where
  sparse := sparseRows input
  sparse_eq := rfl
  dense := denseRows input
  dense_eq := rfl
  hot := hotRows input
  hot_eq := rfl
  cold := coldRows input
  cold_eq := rfl
  total := totalSurplus input
  total_eq := rfl
  sparseTotal := sparseSurplus input
  sparseTotal_eq := rfl
  denseTotal := denseSurplus input
  denseTotal_eq := rfl
  surplus_split :=
    (sum_filter_add_sum_filter_not input.rows Row.isSparse Row.surplus).symm
  row_split := by
    simpa [sparseRows, denseRows] using
      length_filter_add_length_filter_not input.rows Row.isSparse
  temperature_split := by
    simpa [hotRows, coldRows] using
      length_filter_add_length_filter_not input.rows Row.isHot
  checks := 2 * input.rows.length
  checks_eq := rfl

/-- Exhaustive sign classification of the computed sparse-surplus ledger. -/
inductive SparseSurplusTerminal (input : Input) (ledger : Ledger input) where
  | nonpositive (proof : ledger.sparseTotal ≤ 0)
  | positive (proof : 0 < ledger.sparseTotal)

def classifySparseSurplus (input : Input) (ledger : Ledger input) :
    SparseSurplusTerminal input ledger :=
  if h : ledger.sparseTotal ≤ 0 then .nonpositive h
  else .positive (by omega)

end Hypostructure.Core.Strategy.Official.Semantics.SparseSurplusRefinement
