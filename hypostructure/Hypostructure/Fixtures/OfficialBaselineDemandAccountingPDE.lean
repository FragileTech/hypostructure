import Hypostructure.Core.Strategy.BaselineDemandAccounting
import Hypostructure.PDE.CT5

namespace Hypostructure.Fixtures.OfficialBaselineDemandAccountingPDE

open Hypostructure
open Hypostructure.Core.Strategy

universe uPrevious uModel uSite uWitness uResource

/-- Every capability produced by the PDE CT5 adapter is accepted directly by
the domain-neutral Strategy, without translating or copying its data. -/
noncomputable def strategy
    {Previous : Type uPrevious}
    (M : PDE.LocalModel.{uModel})
    (state : Core.Residual.Query Previous fun _ => M.problem.Ambient)
    (budget : Core.ResourceBudget.{uResource})
    (Site : Previous → Type uSite)
    (Witness : (previous : Previous) → Site previous → Type uWitness)
    (Active : (previous : Previous) → M.problem.Ambient →
      Site previous → Prop)
    (Supports : (previous : Previous) → M.problem.Ambient →
      (site : Site previous) → Witness previous site → Prop)
    (contribution : (previous : Previous) → M.problem.Ambient →
      (site : Site previous) → Witness previous site → budget.Resource)
    (required capacity : (previous : Previous) → M.problem.Ambient →
      budget.Resource)
    (accounting : CT5.Capability
      (PDE.CT5.localWitnessSpec M state budget Site Witness Active Supports
        contribution required capacity)) :
    CTExecution Previous :=
  BaselineDemandAccounting.execution accounting

end Hypostructure.Fixtures.OfficialBaselineDemandAccountingPDE
