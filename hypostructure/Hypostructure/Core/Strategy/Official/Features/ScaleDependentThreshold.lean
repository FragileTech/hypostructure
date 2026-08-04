import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic

/-!
# Scale-dependent threshold classification

This file provides a domain-neutral decision strategy whose threshold is
computed from a certified finite table.  A table contains natural fixed
charges and nonnegative rational coefficients paired with a member of a
closed framework-owned scale basis.  At the current natural size, each basis
and rational contribution is rounded upward and the resulting finite charges
are summed.

The caller supplies observations (`size` and `load`) and literal table data,
but cannot supply a threshold, comparison result, or route.  `execute`
computes an exhaustive proof-relevant terminal.
-/

namespace Hypostructure.Core.Strategy.Official.Features.ScaleDependentThreshold

/-- A nonnegative rational coefficient represented by certified natural data.
The positive-denominator proof is mathematical table certification, not an
execution choice. -/
structure RationalCoefficient where
  numerator : Nat
  denominator : Nat
  denominator_pos : 0 < denominator

namespace RationalCoefficient

/-- The rational represented by the certified row. -/
def value (coefficient : RationalCoefficient) : ℚ :=
  coefficient.numerator / coefficient.denominator

/-- Exact natural ceiling of `numerator * size / denominator`.

The quotient form avoids floating point evaluation and is executable on the
literal certified table. -/
def contribution (coefficient : RationalCoefficient) (size : Nat) : Nat :=
  let scaled := coefficient.numerator * size
  scaled / coefficient.denominator +
    if scaled % coefficient.denominator = 0 then 0 else 1

@[simp] theorem contribution_zero (coefficient : RationalCoefficient) :
    coefficient.contribution 0 = 0 := by
  simp [contribution]

theorem scaled_le_denominator_mul_contribution
    (coefficient : RationalCoefficient) (size : Nat) :
    coefficient.numerator * size ≤
      coefficient.denominator * coefficient.contribution size := by
  let scaled := coefficient.numerator * size
  change scaled ≤ coefficient.denominator *
    (scaled / coefficient.denominator +
      if scaled % coefficient.denominator = 0 then 0 else 1)
  have decomposition :
      scaled % coefficient.denominator +
          coefficient.denominator * (scaled / coefficient.denominator) =
        scaled := by
    simpa [Nat.mul_comm] using Nat.mod_add_div scaled coefficient.denominator
  by_cases exactDivision : scaled % coefficient.denominator = 0
  · rw [if_pos exactDivision, Nat.add_zero]
    calc
      scaled =
          scaled % coefficient.denominator +
            coefficient.denominator * (scaled / coefficient.denominator) :=
        decomposition.symm
      _ = coefficient.denominator *
            (scaled / coefficient.denominator) := by simp [exactDivision]
      _ ≤ coefficient.denominator *
            (scaled / coefficient.denominator) := le_rfl
  · have remainder_lt :
        scaled % coefficient.denominator < coefficient.denominator :=
      Nat.mod_lt _ coefficient.denominator_pos
    rw [if_neg exactDivision]
    calc
      scaled =
          scaled % coefficient.denominator +
            coefficient.denominator * (scaled / coefficient.denominator) :=
        decomposition.symm
      _ ≤ coefficient.denominator +
            coefficient.denominator * (scaled / coefficient.denominator) :=
        Nat.add_le_add_right (Nat.le_of_lt remainder_lt) _
      _ = coefficient.denominator *
            (scaled / coefficient.denominator + 1) := by
        simp [Nat.mul_add, Nat.add_comm]

end RationalCoefficient

/-- Closed scale basis supported by the framework.  Applications select a
mathematical basis in each certified row; they cannot provide an evaluator. -/
inductive ScaleBasis
  | linear
  | squareRoot
  deriving DecidableEq, Repr

namespace ScaleBasis

/-- Integer ceiling of the square root, computed from Lean's certified
integer square root. -/
def ceilSqrt (size : Nat) : Nat :=
  if Nat.sqrt size ^ 2 = size then Nat.sqrt size else Nat.sqrt size + 1

@[simp] theorem ceilSqrt_zero : ceilSqrt 0 = 0 := by
  simp [ceilSqrt]

/-- The computed ceiling square root really covers the source size. -/
theorem le_ceilSqrt_sq (size : Nat) :
    size ≤ ceilSqrt size ^ 2 := by
  by_cases perfect : Nat.sqrt size ^ 2 = size
  · simp [ceilSqrt, perfect]
  · rw [ceilSqrt, if_neg perfect]
    exact Nat.le_of_lt (Nat.lt_succ_sqrt' size)

/-- Evaluate one official basis at the current size. -/
def evaluate : ScaleBasis → Nat → Nat
  | .linear, size => size
  | .squareRoot, size => ceilSqrt size

@[simp] theorem evaluate_linear (size : Nat) :
    evaluate .linear size = size := rfl

@[simp] theorem evaluate_squareRoot (size : Nat) :
    evaluate .squareRoot size = ceilSqrt size := rfl

@[simp] theorem evaluate_zero (basis : ScaleBasis) :
    basis.evaluate 0 = 0 := by
  cases basis <;> simp [evaluate]

end ScaleBasis

/-- One certified scale row.  Both its coefficient and its scale semantics
come from closed data constructors. -/
structure ScaleRow where
  basis : ScaleBasis
  coefficient : RationalCoefficient

namespace ScaleRow

/-- Exact ceiling-rounded contribution of this row at the current size. -/
def contribution (row : ScaleRow) (size : Nat) : Nat :=
  row.coefficient.contribution (row.basis.evaluate size)

@[simp] theorem contribution_zero (row : ScaleRow) :
    row.contribution 0 = 0 := by
  simp [contribution]

end ScaleRow

/-- Certified finite data defining a scale-dependent threshold.

`fixedRows` and `scaleRows` are retained separately so audit tools can recover
the literal Nat, rational, and closed-basis sources of every contribution. -/
structure Table where
  fixedRows : List Nat
  scaleRows : List ScaleRow

namespace Table

/-- Per-row scale charges computed at the current size. -/
def scaleContributions (table : Table) (size : Nat) : List Nat :=
  table.scaleRows.map fun row => row.contribution size

/-- The threshold computed from all finite table rows at the current size. -/
def threshold (table : Table) (size : Nat) : Nat :=
  table.fixedRows.sum + (table.scaleContributions size).sum

/-- Number of literal rows inspected by threshold execution. -/
def work (table : Table) : Nat :=
  table.fixedRows.length + table.scaleRows.length

@[simp] theorem threshold_zero (table : Table) :
    table.threshold 0 = table.fixedRows.sum := by
  simp [threshold, scaleContributions]

theorem fixed_sum_le_threshold (table : Table) (size : Nat) :
    table.fixedRows.sum ≤ table.threshold size := by
  simp [threshold]

end Table

/-- Literal predecessor observations consumed by the strategy. -/
structure Input where
  table : Table
  size : Nat
  load : Nat

namespace Input

/-- Framework-computed threshold for these exact predecessor observations. -/
def threshold (input : Input) : Nat :=
  input.table.threshold input.size

/-- Proof-relevant terminal evidence.  These are the only two routes and they
are exhaustive: strict overload, or load at/below the computed threshold. -/
inductive Terminal (input : Input) : Type
  | above (evidence : input.threshold < input.load)
  | atOrBelow (evidence : input.load ≤ input.threshold)

namespace Terminal

def isAbove {input : Input} : input.Terminal → Bool
  | .above _ => true
  | .atOrBelow _ => false

theorem above_evidence {input : Input} (terminal : input.Terminal)
    (h : terminal.isAbove = true) :
    input.threshold < input.load := by
  cases terminal <;> simp_all [isAbove]

theorem atOrBelow_evidence {input : Input} (terminal : input.Terminal)
    (h : terminal.isAbove = false) :
    input.load ≤ input.threshold := by
  cases terminal <;> simp_all [isAbove]

end Terminal

/-- Proof-relevant execution ledger.  Every numerical field is definitionally
derived from the literal predecessor input. -/
structure Execution (input : Input) where
  computedThreshold : Nat
  computedThreshold_eq : computedThreshold = input.threshold
  fixedContributions : List Nat
  fixedContributions_eq : fixedContributions = input.table.fixedRows
  scaleContributions : List Nat
  scaleContributions_eq :
    scaleContributions = input.table.scaleContributions input.size
  terminal : input.Terminal
  checks : Nat
  checks_eq : checks = input.table.work

/-- Framework-owned exhaustive threshold decision. -/
def execute (input : Input) : input.Execution :=
  let terminal : input.Terminal :=
    if h : input.threshold < input.load then
      .above h
    else
      .atOrBelow (Nat.le_of_not_gt h)
  {
    computedThreshold := input.threshold
    computedThreshold_eq := rfl
    fixedContributions := input.table.fixedRows
    fixedContributions_eq := rfl
    scaleContributions := input.table.scaleContributions input.size
    scaleContributions_eq := rfl
    terminal
    checks := input.table.work
    checks_eq := rfl
  }

theorem execute_exhaustive (input : Input) :
    input.threshold < input.load ∨ input.load ≤ input.threshold := by
  cases (execute input).terminal with
  | above evidence => exact Or.inl evidence
  | atOrBelow evidence => exact Or.inr evidence

theorem execute_above_iff (input : Input) :
    (execute input).terminal.isAbove = true ↔
      input.threshold < input.load := by
  simp only [execute]
  split <;> simp_all [Terminal.isAbove]

theorem execute_atOrBelow_iff (input : Input) :
    (execute input).terminal.isAbove = false ↔
      input.load ≤ input.threshold := by
  rw [Bool.eq_false_iff]
  simp [execute_above_iff]

end Input

end Hypostructure.Core.Strategy.Official.Features.ScaleDependentThreshold
