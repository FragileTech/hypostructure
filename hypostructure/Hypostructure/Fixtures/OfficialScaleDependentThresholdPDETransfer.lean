import Hypostructure.Core.Strategy.Official.Features.ScaleDependentThreshold

/-!
PDE-transfer fixture.  Spectral resolution is the current scale and an
integrated dissipation count is the current load.  The strategy itself knows
nothing about PDEs and imports no Graph module.
-/

namespace Hypostructure.Fixtures.OfficialScaleDependentThresholdPDETransfer

open Core.Strategy.Official.Features.ScaleDependentThreshold

/-- Certified coefficients read from a finite analytic estimate table. -/
def fluxCoefficient : RationalCoefficient where
  numerator := 5
  denominator := 4
  denominator_pos := by decide

def commutatorCoefficient : RationalCoefficient where
  numerator := 1
  denominator := 2
  denominator_pos := by decide

def squareRootFlux : ScaleRow where
  basis := .squareRoot
  coefficient := fluxCoefficient

def linearCommutator : ScaleRow where
  basis := .linear
  coefficient := commutatorCoefficient

def spectralBudgetTable : Table where
  fixedRows := [1, 2]
  scaleRows := [squareRootFlux, linearCommutator]

/-- A represented PDE residual contributes observations, never a route. -/
structure SpectralResidual where
  resolution : Nat
  dissipationLoad : Nat

def thresholdInput (residual : SpectralResidual) : Input where
  table := spectralBudgetTable
  size := residual.resolution
  load := residual.dissipationLoad

def highDissipation : SpectralResidual where
  resolution := 8
  dissipationLoad := 12

def controlledDissipation : SpectralResidual where
  resolution := 8
  dissipationLoad := 11

example : ScaleBasis.ceilSqrt 8 = 3 := by native_decide
example : spectralBudgetTable.scaleContributions 8 = [4, 4] := by native_decide
example : (thresholdInput highDissipation).threshold = 11 := by native_decide

example :
    ((thresholdInput highDissipation).execute).terminal.isAbove = true := by
  native_decide

example :
    ((thresholdInput controlledDissipation).execute).terminal.isAbove = false := by
  native_decide

example :
    (thresholdInput highDissipation).threshold <
      (thresholdInput highDissipation).load :=
  ((thresholdInput highDissipation).execute).terminal.above_evidence
    (by native_decide)

example :
    (thresholdInput controlledDissipation).load ≤
      (thresholdInput controlledDissipation).threshold :=
  ((thresholdInput controlledDissipation).execute).terminal.atOrBelow_evidence
    (by native_decide)

#print axioms Input.execute
#print axioms Input.execute_above_iff
#print axioms Input.execute_atOrBelow_iff

end Hypostructure.Fixtures.OfficialScaleDependentThresholdPDETransfer
