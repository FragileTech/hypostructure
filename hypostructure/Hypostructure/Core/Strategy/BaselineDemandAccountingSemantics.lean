import Hypostructure.Core.Budget.Resource
import Hypostructure.Core.Finite.Enumeration

/-!
# Baseline demand accounting semantics

The registration contains only residual-owned local-witness mathematics.
Core constructs and executes CT5 from this presentation.
-/

namespace Hypostructure.Core.Strategy.BaselineDemandAccounting

universe uResidual uSite uWitness uResource

structure Registration (Residual : Type uResidual) where
  budget : Core.ResourceBudget.{uResource}
  Site : Residual → Type uSite
  Witness : (residual : Residual) → Site residual → Type uWitness
  family : (residual : Residual) →
    Core.Finite.DependentEnumeration (Site residual) (Witness residual)
  Active : (residual : Residual) → Site residual → Prop
  Supports : (residual : Residual) → (site : Site residual) →
    Witness residual site → Prop
  contribution : (residual : Residual) → (site : Site residual) →
    Witness residual site → budget.Resource
  required : Residual → budget.Resource
  capacity : Residual → budget.Resource
  activeDecidable : (residual : Residual) → (site : Site residual) →
    Decidable (Active residual site)
  supportsDecidable : (residual : Residual) → (site : Site residual) →
    (witness : Witness residual site) →
      Decidable (Supports residual site witness)
  resourceLEDecidable : (left right : budget.Resource) →
    Decidable (left ≤ right)

end Hypostructure.Core.Strategy.BaselineDemandAccounting
