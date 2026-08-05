import Hypostructure.CTAdapters
import Hypostructure.Core.Residual.Stage
import Hypostructure.Core.Strategy.BaselineDemandAccountingSemantics

/-!
# Baseline demand accounting

The strategy is the canonical CT5 execution over the exact incoming
predecessor.  The supplied capability owns the typed ledger query; Core owns
the scan, output, ledger extension, and work accounting.
-/

namespace Hypostructure.Core.Strategy.BaselineDemandAccounting

open Hypostructure
open Hypostructure.Core.Residual

universe uPrevious uResidual uSite uWitness uResource

/-- Record the baseline demand and its exact accounting output through CT5. -/
noncomputable def execution
    {Previous : Type uPrevious}
    {accountingSpec : CT5.Spec Previous}
    (accounting : CT5.Capability accountingSpec) :
    CTExecution Previous :=
  CTAdapters.ct5 accounting

/-- Residual presentation lifted through Core's stable-residual query. -/
structure Profile (Previous : Type uPrevious) (Residual : Type uResidual)
    [HasResidual Previous Residual] where
  registration :
    Registration.{uResidual, uSite, uWitness, uResource} Residual
  /-- The object this accounting audits.  It defaults to the incoming
  residual; a compiler that has already rebased onto a selected minimal
  counterexample passes that query instead, so the demand family and the
  capacity comparison speak about the same object as the strategies that
  produced this node's inputs. -/
  current : Query Previous (fun _ => Residual) := Query.residual

namespace Profile

variable [HasResidual Previous Residual]
variable (profile :
  Profile.{uPrevious, uResidual, uSite, uWitness, uResource}
    Previous Residual)

def spec : CT5.Spec Previous where
  budget := profile.registration.budget
  Site := fun previous =>
    profile.registration.Site (profile.current previous)
  Witness := fun previous =>
    profile.registration.Witness (profile.current previous)
  Active := fun previous =>
    profile.registration.Active (profile.current previous)
  Supports := fun previous =>
    profile.registration.Supports (profile.current previous)
  contribution := fun previous =>
    profile.registration.contribution (profile.current previous)
  required := fun previous =>
    profile.registration.required (profile.current previous)
  capacity := fun previous =>
    profile.registration.capacity (profile.current previous)

def family : Query Previous fun previous =>
    Core.Finite.DependentEnumeration
      (profile.spec.Site previous) (profile.spec.Witness previous) :=
  profile.current.dependentMap fun _ residual =>
    profile.registration.family residual

def capability : CT5.Capability profile.spec where
  family := profile.family
  activeDecidable := fun previous =>
    profile.registration.activeDecidable (profile.current previous)
  supportsDecidable := fun previous =>
    profile.registration.supportsDecidable (profile.current previous)
  resourceLEDecidable := profile.registration.resourceLEDecidable

noncomputable def execution : CTExecution Previous :=
  BaselineDemandAccounting.execution profile.capability

end Profile

end Hypostructure.Core.Strategy.BaselineDemandAccounting
