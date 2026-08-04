import Hypostructure.Core.Strategy.Official.Features.ScaleDependentThreshold

/-!
# Residual-owned scale-threshold semantics

This registration contains only the finite coefficient table and the two
observations read from a residual.  The threshold, comparison, route,
terminal, ledger output, checks, and work are all computed by Core.
-/

namespace Hypostructure.Core.Strategy.ScaleThresholdDichotomy

open Hypostructure.Core.Strategy.Official.Features

universe uResidual

structure Registration (Residual : Type uResidual) where
  table : Residual → ScaleDependentThreshold.Table
  size : Residual → Nat
  load : Residual → Nat

end Hypostructure.Core.Strategy.ScaleThresholdDichotomy
