import Hypostructure.Graph.Strategy.ColdCorridorRows
import Hypostructure.Graph.Strategy.HomogeneousBottleneckRows
import Hypostructure.Graph.Strategy.SurplusRun

/-!
# Spine continuation surface

Continuation transport is owned by the framework ledger/router.  This module is
the stable import surface for end-to-end composition over the existing rows; it
declares no custom continuation or result carrier.
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

end Hypostructure.Graph.Strategy.Spine
