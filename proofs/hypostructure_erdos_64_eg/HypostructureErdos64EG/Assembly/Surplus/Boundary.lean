import HypostructureErdos64EG.Assembly.Residuals
import HypostructureErdos64EG.Assembly.Residuals.Node144aOutcome
import HypostructureErdos64EG.Assembly.Residuals.PairTypeBOutcome
import HypostructureErdos64EG.Assembly.Residuals.PairConditionalFactorizationOutcome

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
  (Node144aOutcome_windowHandoff selected ∨ Node144aOutcome_windowFails selected ∨
    Node144aOutcome_remainderHandoff selected ∨
    Node144aOutcome_remainderFails selected ∨
    Node144aOutcome_primitiveHandoff selected ∨
    Node144aOutcome_primitiveFails selected) ∨
  (PairTypeBOutcome_independentSystem selected ∨
      PairTypeBOutcome_dependentSystem selected) ∨
    (PairConditionalFactorizationOutcome_freeFactorizationFails selected ∨
      PairConditionalFactorizationOutcome_freeRealizabilityFails selected ∨
      PairConditionalFactorizationOutcome_freeIncrementFails selected ∨
      PairConditionalFactorizationOutcome_blockedFactorizationFails selected ∨
      PairConditionalFactorizationOutcome_blockedRealizabilityFails selected ∨
      PairConditionalFactorizationOutcome_blockedIncrementFails selected)

end HypostructureErdos64EG
