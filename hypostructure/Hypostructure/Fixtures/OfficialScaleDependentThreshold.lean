import Hypostructure.Core.Strategy.Official.Features.ScaleDependentThreshold

/-!
Focused Core fixture for table-derived scale thresholds.  The examples supply
only finite source rows and observations; execution computes both the
threshold and its exhaustive terminal.
-/

namespace Hypostructure.Fixtures.OfficialScaleDependentThreshold

open Core.Strategy.Official.Features.ScaleDependentThreshold

def half : RationalCoefficient where
  numerator := 1
  denominator := 2
  denominator_pos := by decide

def threeHalves : RationalCoefficient where
  numerator := 3
  denominator := 2
  denominator_pos := by decide

def linearHalf : ScaleRow where
  basis := .linear
  coefficient := half

def squareRootThreeHalves : ScaleRow where
  basis := .squareRoot
  coefficient := threeHalves

def sourceTable : Table where
  fixedRows := [2, 1]
  scaleRows := [linearHalf, squareRootThreeHalves]

def overloaded : Input where
  table := sourceTable
  size := 4
  load := 9

def controlled : Input where
  table := sourceTable
  size := 4
  load := 8

example : ScaleBasis.ceilSqrt 4 = 2 := by native_decide
example : ScaleBasis.ceilSqrt 5 = 3 := by native_decide
example : ScaleBasis.ceilSqrt 8 = 3 := by native_decide
example : ScaleBasis.ceilSqrt 9 = 3 := by native_decide
example : sourceTable.scaleContributions 4 = [2, 3] := by native_decide
example : overloaded.threshold = 8 := by native_decide
example : (overloaded.execute).terminal.isAbove = true := by native_decide
example : (controlled.execute).terminal.isAbove = false := by native_decide
example : (overloaded.execute).checks = 4 := rfl

example : overloaded.threshold < overloaded.load :=
  (overloaded.execute).terminal.above_evidence (by native_decide)

example : controlled.load ≤ controlled.threshold :=
  (controlled.execute).terminal.atOrBelow_evidence (by native_decide)

#print axioms RationalCoefficient.scaled_le_denominator_mul_contribution
#print axioms ScaleBasis.le_ceilSqrt_sq
#print axioms Input.execute
#print axioms Input.execute_exhaustive

end Hypostructure.Fixtures.OfficialScaleDependentThreshold
