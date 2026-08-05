import Hypostructure.Core.Strategy.Official.Schema
import Hypostructure.Core.Strategy.Official.ProblemDefinition
import Hypostructure.Core.Strategy.Official.Availability
import Hypostructure.Core.Strategy.Official.Syntax
import Hypostructure.Core.Strategy.Official.FiniteTableKernel
import Hypostructure.Core.Strategy.Official.Strategies.Dispatcher
import Hypostructure.Core.Strategy.Official.Strategies.MeasuredFiniteRouting
import Hypostructure.Core.Strategy.Official.Features.DeletionFanAccounting
import Hypostructure.Core.Strategy.Official.Features.ScaleDependentThreshold

/-!
Public entry point for reusable official strategy data, schemas, and
mathematics. Proof declarations and execution are provided solely by the
sealed `Core.Strategy.Dag` API.
-/
