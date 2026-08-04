import Hypostructure.Graph.Strategy.Official.Features.HighCenterFanClosure

/-!
Focused fixture for graph-owned high-centre fan accounting and closure.
It is polymorphic in the baseline, branch state, and target, so it cannot
encode an application-specific route or numerical outcome.
-/

namespace Hypostructure.Fixtures.OfficialHighCenterFanClosureGraph

open Hypostructure.Graph
open Hypostructure.Graph.Strategy.Official.Features

universe u v

variable
    {Baseline : FiniteObject.{u} → Prop}
    {BranchState : FiniteObject.{u} → Type v}
    {Target : FiniteObject.{u} → Prop}
    {profile : DeletionCriticalityProfile Baseline}
    {ctx : Core.MinimalCounterexampleContext
      (problem Baseline BranchState) Target
      (lexicographicProgress Baseline BranchState)}
    (criticality : DeletionCriticalityCertificate profile ctx)

private def deletionResidual :
    DeletionFanIncidence.Residual profile ctx :=
  DeletionFanIncidence.deriveResidual criticality

example :
    (HighCenterFanClosure.deriveLedger
      (deletionResidual criticality)).claims =
      HighCenterFanClosure.carrierClaims (deletionResidual criticality) :=
  rfl

example :
    (HighCenterFanClosure.deriveLedger
      (deletionResidual criticality)).surplusMass =
      HighCenterFanClosure.centerSurplusMass (deletionResidual criticality) :=
  rfl

example :
    HighCenterFanClosure.centerSurplusMass (deletionResidual criticality) =
      ((deletionResidual criticality).centers.flatMap
        DeletionFanIncidence.HighCenterRow.excess).length :=
  HighCenterFanClosure.centerSurplusMass_eq_excess_ports _

noncomputable example :
    let residual := deletionResidual criticality
    let ledger := HighCenterFanClosure.deriveLedger residual
    HighCenterFanClosure.Terminal residual ledger :=
  HighCenterFanClosure.execute (deletionResidual criticality)

#print axioms HighCenterFanClosure.execute
#print axioms HighCenterFanClosure.centerSurplusMass_eq_excess_ports

end Hypostructure.Fixtures.OfficialHighCenterFanClosureGraph
