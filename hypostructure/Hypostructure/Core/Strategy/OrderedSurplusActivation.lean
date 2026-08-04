import Hypostructure.CTAdapters
import Hypostructure.Core.Residual.Stage
import Hypostructure.Core.Strategy.BaselineDemandAccounting
import Hypostructure.Core.Strategy.OrderedSurplusActivationSemantics

/-!
# Ordered surplus activation

The strategy is the dependent composition of an ordered exhaustion (CT6)
with capacity accounting (CT5).  CT5 receives the exact ledger extension
produced by CT6; all execution, ledger access, and work accounting remain in
Core.
-/

namespace Hypostructure.Core.Strategy.OrderedSurplusActivation

open Hypostructure
open Hypostructure.Core.Residual

universe uPrevious uResidual uIndex uData uSite uWitness uResource

/-- Run CT6 and then CT5 on CT6's exact retained output. -/
noncomputable def execution
    {Previous : Type uPrevious}
    {activitySpec : CT6.Spec Previous}
    (activity : CT6.Capability activitySpec)
    {accountingSpec : CT5.Spec
      (Ledger.Extension Previous (CTAdapters.ct6 activity).Output)}
    (accounting : CT5.Capability accountingSpec) :
    CTExecution Previous :=
  (CTAdapters.ct6 activity).compose (CTAdapters.ct5 accounting)

structure Profile (Previous : Type uPrevious) (Residual : Type uResidual)
    [HasResidual Previous Residual] where
  registration :
    Registration.{
      uResidual, uIndex, uData, uSite, uWitness, uResource} Residual
  /-- The object this activation scans.  It defaults to the incoming residual;
  a compiler that has already rebased onto a selected minimal counterexample
  passes that query instead, so the ordered scan and the accounting it feeds
  speak about the same object as the strategies that produced this node's
  inputs. -/
  current : Query Previous (fun _ => Residual) := Query.residual

namespace Profile

variable [HasResidual Previous Residual]
variable (profile :
  Profile.{
    uPrevious, uResidual, uIndex, uData, uSite, uWitness, uResource}
    Previous Residual)

def activitySpec : CT6.Spec Previous where
  Index := fun previous =>
    profile.registration.Index (profile.current.read previous)
  FailureData := fun previous =>
    profile.registration.FailureData (profile.current.read previous)
  Failure := fun previous =>
    profile.registration.Failure (profile.current.read previous)
  failureData := fun previous =>
    profile.registration.failureData (profile.current.read previous)
  contribution := fun previous =>
    profile.registration.contribution (profile.current.read previous)

def activityOrder : Query Previous fun previous =>
    Core.Finite.Enumeration (profile.activitySpec.Index previous) :=
  profile.current.dependentMap fun _ residual =>
    profile.registration.order residual

def activityCapability : CT6.Capability profile.activitySpec where
  failureOrder := profile.activityOrder
  failureDecidable := fun previous =>
    profile.registration.failureDecidable (profile.current.read previous)
  inputSize := fun previous => (profile.activityOrder.read previous).card
  workCoefficient := Fintype.card Unit
  workDegree := Fintype.card Unit
  workBound := by
    intro previous
    simp only [CT6.localCheckBound, Fintype.card_unit, Nat.pow_one,
      Nat.one_mul]
    exact Nat.le_succ _

abbrev ActivityStage :=
  Ledger.Extension Previous (CTAdapters.ct6 profile.activityCapability).Output

def accountingProfile :
    BaselineDemandAccounting.Profile.{
      max uPrevious (max uIndex uData), uResidual, uSite, uWitness, uResource}
      profile.ActivityStage Residual where
  registration := profile.registration.accounting
  current := profile.current.preserve

noncomputable def execution : CTExecution Previous :=
  OrderedSurplusActivation.execution profile.activityCapability
    profile.accountingProfile.capability

end Profile

end Hypostructure.Core.Strategy.OrderedSurplusActivation
