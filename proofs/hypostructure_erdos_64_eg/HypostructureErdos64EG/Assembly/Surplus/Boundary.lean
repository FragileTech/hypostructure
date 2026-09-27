import HypostructureErdos64EG.Assembly.Residuals

/-!
# Assembly: Surplus / Boundary

Part of the dependency-separated Erdős–Gyárfás assembly.
-/

namespace HypostructureErdos64EG

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u w

/-- The strict-surplus branch returns exactly the three root outcomes it can
reach, as the literal disjunction the root boundary lists: the node-`[144a]`
handoff, a `[179]`/`[180]` Type B entry, or the open node-`[182]` residual. -/
abbrev StrictSurplusBoundaryResult (selected : EGInput.{u}) : Prop :=
  Node144aOutcome selected ∨ PairTypeBOutcome selected ∨
    PairConditionalFactorizationOutcome selected

end HypostructureErdos64EG
