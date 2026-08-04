import Hypostructure.CTAdapters
import Hypostructure.Core.Residual.Stage
import Hypostructure.Core.Strategy.CanonicalPairResponseAccountingSemantics

/-!
# Canonical pair-response accounting

This Strategy is exactly CT15 followed by CT9.  Both CT capabilities are
constructed from stable residual queries; CT9 receives the literal ledger
extension produced by CT15 and transports the pair and role schedules only
through `Query.preserve`.
-/

namespace Hypostructure.Core.Strategy.CanonicalPairResponseAccounting

open Hypostructure
open Hypostructure.Core.Residual

universe uPrevious uResidual uPair uBlocker

/-- Residual presentation lifted to one arbitrary incoming ledger stage. -/
structure Profile (Previous : Type uPrevious) (Residual : Type uResidual)
    [HasResidual Previous Residual] where
  registration :
    Registration.{uResidual, uPair, uBlocker} Residual
  /-- The object this accounting audits.  It defaults to the incoming
  residual; a compiler that has already rebased onto a selected minimal
  counterexample passes that query instead, so the pair schedule, the
  dependence decision and the role fibres all speak about the same object as
  the strategies that produced this node's inputs. -/
  current : Query Previous (fun _ => Residual) := Query.residual

namespace Profile

variable [HasResidual Previous Residual]
variable (profile :
  Profile.{uPrevious, uResidual, uPair, uBlocker} Previous Residual)

/-- The one stable read of the audited object. -/
def residualQuery : Query Previous (fun _ => Residual) :=
  profile.current

/-- Primitive target-relative dependence semantics for CT15. -/
def dependenceSpec : CT15.Spec Previous where
  Coordinate := fun previous =>
    profile.registration.Pair (profile.current.read previous)
  TargetDependent := fun previous pair =>
    profile.registration.Dependent (profile.current.read previous) pair
  charge := fun previous pair =>
    profile.registration.pairCharge (profile.current.read previous) pair
  capacity := fun previous =>
    profile.registration.pairCapacity (profile.current.read previous)

/-- The exact residual-owned pair schedule. -/
def pairQuery :
    Query Previous fun previous =>
      Core.Finite.Enumeration
        (profile.dependenceSpec.Coordinate previous) :=
  profile.residualQuery.dependentMap fun _ residual =>
    profile.registration.pairSchedule residual

/-- The complete role alphabet derived from the residual's blocker kinds. -/
def completeRoleQuery :
    Query Previous fun previous =>
      Core.Finite.CompleteEnumeration
        (Role
          (profile.registration.BlockerKind
            (profile.current.read previous))) :=
  profile.residualQuery.dependentMap fun _ residual =>
    profile.registration.completeRoles residual

/-- CT15 receives only the residual-owned pair query and primitive dependence
decision. -/
def dependenceCapability : CT15.Capability profile.dependenceSpec where
  coordinates := profile.pairQuery
  targetDependentDecidable := fun previous pair =>
    profile.registration.dependentDecidable
      (profile.current.read previous) pair
  inputSize := fun previous =>
    CT15.localCheckBound (profile.pairQuery.read previous)
  workCoefficient := Fintype.card Unit
  workDegree := Fintype.card Unit
  workBound := by
    intro previous
    simp only [Fintype.card_unit, Nat.pow_one, Nat.one_mul]
    exact Nat.le_succ _

/-- The first exact CT execution. -/
noncomputable def dependenceExecution : Core.Strategy.CTExecution Previous :=
  CTAdapters.ct15 profile.dependenceCapability

/-- The literal stage Core constructs by retaining CT15's exact result. -/
abbrev AfterDependence :=
  Ledger.Extension Previous profile.dependenceExecution.Output

/-- The audited object transported through the CT15 extension. -/
def currentAfterDependence :
    Query profile.AfterDependence fun _ => Residual :=
  profile.current.preserve

/-- Transport the exact pair schedule through the CT15 extension. -/
def inheritedPairs :
    Query profile.AfterDependence fun stage =>
      Core.Finite.Enumeration
        (profile.registration.Pair
          (profile.currentAfterDependence.read stage)) :=
  profile.pairQuery.preserve

/-- Transport the exact complete role schedule through the CT15 extension. -/
def inheritedRoles :
    Query profile.AfterDependence fun stage =>
      Core.Finite.CompleteEnumeration
        (Role (profile.registration.BlockerKind
          (profile.currentAfterDependence.read stage))) :=
  profile.completeRoleQuery.preserve

/-- Primitive role-fibre semantics for CT9 on CT15's exact extension. -/
def roleSpec : CT9.Spec profile.AfterDependence where
  Item := fun stage =>
    profile.registration.Pair (profile.currentAfterDependence.read stage)
  Label := fun stage =>
    Role (profile.registration.BlockerKind
      (profile.currentAfterDependence.read stage))
  label := fun stage pair =>
    profile.registration.roleOf
      (profile.currentAfterDependence.read stage) pair
  capacity := fun stage role =>
    profile.registration.roleCapacity
      (profile.currentAfterDependence.read stage) role

/-- CT9 consumes only the two schedules preserved through CT15. -/
def roleCapability : CT9.Capability profile.roleSpec where
  items := profile.inheritedPairs
  labels := fun stage =>
    profile.inheritedRoles.read stage
  inputSize := fun stage =>
    CT9.localCheckBound
      (profile.inheritedPairs.read stage)
      (profile.inheritedRoles.read stage).toEnumeration
  workCoefficient := Fintype.card Unit
  workDegree := Fintype.card Unit
  workBound := by
    intro stage
    simp only [Fintype.card_unit, Nat.pow_one, Nat.one_mul]
    exact Nat.le_succ _

/-- The entire executable Strategy: CT15 followed by CT9, with both exact
results retained by Core's dependent composition. -/
noncomputable def roleExecution :
    Core.Strategy.CTExecution profile.AfterDependence :=
  CTAdapters.ct9 profile.roleCapability

noncomputable def execution : Core.Strategy.CTExecution Previous :=
  profile.dependenceExecution.compose profile.roleExecution

/-- Literal ledger stage after the composed CT15 → CT9 execution. -/
abbrev AfterExecution :=
  Ledger.Extension Previous profile.execution.Output

/-- Direct read of the exact composed output written by the Strategy. -/
noncomputable def executionResult :
    Query profile.AfterExecution
      (fun stage => profile.execution.Output stage.previous) :=
  Query.latest

/-- Direct projection of the exact CT15 payload from the composed ledger
entry.  The value remains indexed by the literal predecessor. -/
noncomputable def dependenceOutput :
    Query profile.AfterExecution
      (fun stage => profile.dependenceExecution.Output stage.previous) :=
  profile.executionResult.map fun _ output => output.fst

/-- Direct projection of the exact CT9 payload from the same composed ledger
entry.  Its predecessor is the literal CT15 extension retained in `output`. -/
noncomputable def roleOutput :
    Query profile.AfterExecution fun stage =>
      let output := profile.executionResult.read stage
      profile.roleExecution.Output
        (Ledger.extend stage.previous output.fst) :=
  profile.executionResult.dependentMap fun stage output => output.snd

/-- The CT15 terminal read directly from the retained composed output. -/
noncomputable def dependenceTerminal :
    Query profile.AfterExecution (fun _ => CT15.Terminal) :=
  profile.dependenceOutput.map fun _ output => output.terminal

/-- The CT9 terminal read directly from the retained composed output. -/
noncomputable def roleTerminal :
    Query profile.AfterExecution (fun _ => CT9.Terminal) :=
  profile.roleOutput.map fun _ output => output.terminal

end Profile

end Hypostructure.Core.Strategy.CanonicalPairResponseAccounting
