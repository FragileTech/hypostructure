import Hypostructure.CTAdapters
import Hypostructure.Core.Residual.Stage
import Hypostructure.Core.Strategy.CoupledHomogeneousFibrePressure
import Hypostructure.Core.Strategy.FiniteBottleneckClassificationSemantics

/-!
# Finite bottleneck classification

This strategy is exactly the right-associated composition
CT9 → CT14 → CT10 → CT6.  Primitive schedules come from the stable residual;
CT14 reads CT9's exact partition through the ledger API; and later
residual-owned schedules are transported only with `Query.preserve`.
-/

namespace Hypostructure.Core.Strategy.FiniteBottleneckClassification

open Hypostructure
open Hypostructure.Core.Residual

universe uPrevious uResidual uPatternItem uCoarseCode uPressureLabel
  uDatum uSemanticTag uPromotion uSeparatorIndex uSeparatorData
  uAmbient uBranch uLiveData uInputItem uToken uRole uInputLabel uPayer
  uObstruction uResource uMember uAggregateLabel

structure Profile (Previous : Type uPrevious) (Residual : Type uResidual)
    [HasResidual Previous Residual] where
  registration :
    Registration.{
      uResidual, uPatternItem, uCoarseCode, uPressureLabel, uDatum,
      uSemanticTag, uPromotion, uSeparatorIndex, uSeparatorData} Residual
  current : Query Previous fun _ => Residual := Query.residual

/-- Producer-indexed continuation profile.  Its CT execution remains the
existing finite-bottleneck composition, while the incoming pressure overload
is retained as an exact typed ledger rather than an untracked side condition. -/
structure ContinuationProfile
    (Previous : Type uPrevious) (Residual : Type uResidual)
    [HasResidual Previous Residual]
    (pressureRegistration :
      CoupledHomogeneousFibrePressure.Registration.{
        uResidual, uInputItem, uToken, uRole, uInputLabel, uPayer,
        uObstruction, uResource, uMember, uAggregateLabel} Residual) where
  registration :
    Registration.{
      uResidual, uPatternItem, uCoarseCode, uPressureLabel, uDatum,
      uSemanticTag, uPromotion, uSeparatorIndex, uSeparatorData} Residual
  overload : CoupledHomogeneousFibrePressure.OverloadLedger
    Previous Residual pressureRegistration

namespace ContinuationProfile

variable [HasResidual Previous Residual]

def base
    (profile : ContinuationProfile Previous Residual pressureRegistration) :
    Profile Previous Residual :=
  { registration := profile.registration
    current := profile.overload.current }

noncomputable def selectedOverload
    (profile : ContinuationProfile Previous Residual pressureRegistration) :=
  profile.overload.selected

end ContinuationProfile

/-- Internal exact claim transported as one dependent value.  Public
consumers see only the three projections below. -/
private abbrev SeparatorClaim
    (registration : Registration.{
      uResidual, uPatternItem, uCoarseCode, uPressureLabel, uDatum,
      uSemanticTag, uPromotion, uSeparatorIndex, uSeparatorData} Residual)
    (residual : Residual) :=
  Option (Σ separator : registration.SeparatorIndex residual,
    PLift
      (separator ∈ (registration.separatorOrder residual).values ∧
        registration.SeparatorFailure residual separator))

/-- Query-only view of CT6's exact selected separator.  Its constructor and
combined claim are private; witness and soundness are exposed only through
the individual dependent queries below. -/
structure SeparatorLedger (Stage : Type uPrevious) (Residual : Type uResidual)
    [HasResidual Stage Residual]
    (registration : Registration.{
      uResidual, uPatternItem, uCoarseCode, uPressureLabel, uDatum,
      uSemanticTag, uPromotion, uSeparatorIndex, uSeparatorData} Residual) where
  private mk ::
  current : Query Stage fun _ => Residual
  private claim : Query Stage fun stage =>
    SeparatorClaim registration (current.read stage)

namespace SeparatorLedger

universe uNew

variable {Stage : Type uPrevious} {Residual : Type uResidual}
variable [HasResidual Stage Residual]

variable {registration : Registration.{
  uResidual, uPatternItem, uCoarseCode, uPressureLabel, uDatum,
  uSemanticTag, uPromotion, uSeparatorIndex, uSeparatorData} Residual}

private def ofClaim
    (current : Query Stage fun _ => Residual)
    (claim : Query Stage fun stage =>
      SeparatorClaim registration (current.read stage)) :
    SeparatorLedger Stage Residual registration :=
  .mk current claim

/-- Exact CT6-selected separator, or `none` on the active-ledger terminal. -/
def selected (ledger : SeparatorLedger Stage Residual registration) :
    Query Stage fun stage =>
      Option (registration.SeparatorIndex (ledger.current.read stage)) :=
  ledger.claim.map fun _ value => value.map Sigma.fst

/-- Schedule membership indexed by the exact selected separator. -/
def member (ledger : SeparatorLedger Stage Residual registration) :
    Query Stage fun stage =>
      match ledger.selected.read stage with
      | none => PUnit
      | some separator =>
          PLift (separator ∈
            (registration.separatorOrder (ledger.current.read stage)).values) :=
  Query.ofFunction fun stage => by
    change match (ledger.claim.read stage).map Sigma.fst with
      | none => PUnit
      | some separator =>
          PLift (separator ∈
            (registration.separatorOrder (ledger.current.read stage)).values)
    cases value_eq : ledger.claim.read stage with
    | none => exact PUnit.unit
    | some selected => exact PLift.up selected.snd.down.1

/-- Failure soundness indexed by the exact selected separator. -/
def failure (ledger : SeparatorLedger Stage Residual registration) :
    Query Stage fun stage =>
      match ledger.selected.read stage with
      | none => PUnit
      | some separator =>
          PLift (registration.SeparatorFailure
            (ledger.current.read stage) separator) :=
  Query.ofFunction fun stage => by
    change match (ledger.claim.read stage).map Sigma.fst with
      | none => PUnit
      | some separator =>
          PLift (registration.SeparatorFailure
            (ledger.current.read stage) separator)
    cases value_eq : ledger.claim.read stage with
    | none => exact PUnit.unit
    | some selected => exact PLift.up selected.snd.down.2

/-- Reindex the exact separator queries along a residual-preserving stage
projection. -/
def comap {NewStage : Type uNew} [HasResidual NewStage Residual]
    (ledger : SeparatorLedger Stage Residual registration)
    (project : NewStage → Stage)
    (current : Query NewStage fun _ => Residual)
    (current_eq : ∀ stage,
      ledger.current.read (project stage) = current.read stage) :
    SeparatorLedger NewStage Residual registration :=
  ofClaim current (Query.ofFunction fun stage =>
    Eq.mp (congrArg (SeparatorClaim registration) (current_eq stage))
      (ledger.claim.read (project stage)))

end SeparatorLedger

namespace Profile

variable [HasResidual Previous Residual]
variable (profile :
  Profile.{
    uPrevious, uResidual, uPatternItem, uCoarseCode, uPressureLabel, uDatum,
    uSemanticTag, uPromotion, uSeparatorIndex, uSeparatorData}
    Previous Residual)

def residualQuery : Query Previous fun _ => Residual :=
  profile.current

def patternItemQuery : Query Previous fun previous =>
    Core.Finite.Enumeration
      (profile.registration.PatternItem (profile.current.read previous)) :=
  profile.residualQuery.dependentMap fun _ residual =>
    profile.registration.patternItems residual

def coarseCodeQuery : Query Previous fun previous =>
    Core.Finite.CompleteEnumeration
      (profile.registration.CoarseCode (profile.current.read previous)) :=
  profile.residualQuery.dependentMap fun _ residual =>
    profile.registration.completeCoarseCodes residual

def dataQuery : Query Previous fun previous =>
    Core.Finite.Enumeration
      (profile.registration.Datum (profile.current.read previous)) :=
  profile.residualQuery.dependentMap fun _ residual =>
    profile.registration.data residual

def semanticTagQuery : Query Previous fun previous =>
    Core.Finite.CompleteEnumeration
      (profile.registration.SemanticTag (profile.current.read previous)) :=
  profile.residualQuery.dependentMap fun _ residual =>
    profile.registration.completeSemanticTags residual

def separatorOrderQuery : Query Previous fun previous =>
    Core.Finite.Enumeration
      (profile.registration.SeparatorIndex (profile.current.read previous)) :=
  profile.residualQuery.dependentMap fun _ residual =>
    profile.registration.separatorOrder residual

def collisionSpec : CT9.Spec Previous where
  Item := fun previous =>
    profile.registration.PatternItem (profile.current.read previous)
  Label := fun previous =>
    profile.registration.CoarseCode (profile.current.read previous)
  label := fun previous item =>
    profile.registration.coarseCodeOf (profile.current.read previous) item
  capacity := fun _previous _code => Fintype.card Unit

def collisionCapability : CT9.Capability profile.collisionSpec where
  items := profile.patternItemQuery
  labels := fun previous => profile.coarseCodeQuery.read previous
  inputSize := fun previous =>
    CT9.localCheckBound
      (profile.patternItemQuery.read previous)
      (profile.coarseCodeQuery.read previous).toEnumeration
  workCoefficient := Fintype.card Unit
  workDegree := Fintype.card Unit
  workBound := by
    intro previous
    simp only [Fintype.card_unit, Nat.pow_one, Nat.one_mul]
    exact Nat.le_succ _

noncomputable def collisionExecution : Core.Strategy.CTExecution Previous :=
  CTAdapters.ct9 profile.collisionCapability

abbrev AfterCollision :=
  Ledger.Extension Previous profile.collisionExecution.Output

def currentAfterCollision : Query profile.AfterCollision fun _ => Residual :=
  profile.current.preserve

def collisionResult :
    Query profile.AfterCollision
      (fun stage => profile.collisionExecution.Output stage.previous) :=
  Query.latest

def collisionPartition :
    Query profile.AfterCollision fun stage =>
      let result := profile.collisionResult.read stage
      CT9.Partition profile.collisionCapability result.stage.previous :=
  profile.collisionResult.dependentMap fun _stage result =>
    match result.terminal, result.outcome with
    | .overloaded, .overloaded partition _ => partition
    | .bounded, .bounded certificate => certificate.partition

def pressureMembers :
    Query profile.AfterCollision fun stage =>
      let result := profile.collisionResult.read stage
      Core.Finite.Enumeration
        (profile.collisionSpec.Label result.stage.previous) :=
  profile.collisionResult.dependentMap fun _stage result =>
    profile.collisionCapability.labelScheduleAt result.stage.previous

def pressureSpec : CT14.Spec profile.AfterCollision where
  Member := fun stage =>
    profile.collisionSpec.Label
      (profile.collisionResult.read stage).stage.previous
  Label := fun stage =>
    let result := profile.collisionResult.read stage
    profile.registration.PressureLabel
      (profile.current.read result.stage.previous)
  memberLowerMass := fun stage code =>
    (profile.collisionPartition.read stage).count code
  memberCapacity := fun stage code =>
    let result := profile.collisionResult.read stage
    profile.registration.pressureCapacity
      (profile.current.read result.stage.previous) code
  memberLabel := fun stage code =>
    let result := profile.collisionResult.read stage
    profile.registration.pressureLabel
      (profile.current.read result.stage.previous) code

def pressureCapability : CT14.Capability profile.pressureSpec where
  members := profile.pressureMembers
  labelDecidableEq := fun stage =>
    let result := profile.collisionResult.read stage
    profile.registration.pressureLabelDecidableEq
      (profile.current.read result.stage.previous)
  inputSize := fun stage =>
    CT14.localCheckBound (profile.pressureMembers.read stage)
  workCoefficient := Fintype.card Unit
  workDegree := Fintype.card Unit
  workBound := by
    intro stage
    simp only [Fintype.card_unit, Nat.pow_one, Nat.one_mul]
    exact Nat.le_succ _

noncomputable def pressureExecution :
    Core.Strategy.CTExecution profile.AfterCollision :=
  CTAdapters.ct14 profile.pressureCapability

abbrev AfterPressure :=
  Ledger.Extension profile.AfterCollision profile.pressureExecution.Output

def currentAfterPressure : Query profile.AfterPressure fun _ => Residual :=
  profile.currentAfterCollision.preserve

def dataAfterPressure : Query profile.AfterPressure fun stage =>
    Core.Finite.Enumeration
      (profile.registration.Datum (profile.currentAfterPressure.read stage)) :=
  profile.dataQuery.preserve.preserve

def semanticTagsAfterPressure : Query profile.AfterPressure fun stage =>
    Core.Finite.CompleteEnumeration
      (profile.registration.SemanticTag
        (profile.currentAfterPressure.read stage)) :=
  profile.semanticTagQuery.preserve.preserve

def classificationSpec : CT10.Spec profile.AfterPressure where
  Datum := fun stage =>
    profile.registration.Datum (profile.currentAfterPressure.read stage)
  Class := fun stage =>
    profile.registration.SemanticTag (profile.currentAfterPressure.read stage)
  Promotion := fun stage =>
    profile.registration.Promotion (profile.currentAfterPressure.read stage)
  classOf := fun stage datum =>
    profile.registration.classOf (profile.currentAfterPressure.read stage) datum
  Direct := fun stage tag =>
    profile.registration.Direct (profile.currentAfterPressure.read stage) tag
  promote := fun stage tag =>
    profile.registration.promote (profile.currentAfterPressure.read stage) tag

def classificationCapability :
    CT10.Capability profile.classificationSpec where
  data := profile.dataAfterPressure
  classes := profile.semanticTagsAfterPressure
  directDecidable := fun stage tag =>
    profile.registration.directDecidable
      (profile.currentAfterPressure.read stage) tag
  inputSize := fun stage =>
    CT10.localCheckBound profile.classificationSpec
      profile.dataAfterPressure profile.semanticTagsAfterPressure stage
  workCoefficient := Fintype.card Unit
  workDegree := Fintype.card Unit
  workBound := by
    intro stage
    simp only [Fintype.card_unit, Nat.pow_one, Nat.one_mul]
    exact Nat.le_succ _

noncomputable def classificationExecution :
    Core.Strategy.CTExecution profile.AfterPressure :=
  CTAdapters.ct10 profile.classificationCapability

abbrev AfterClassification :=
  Ledger.Extension profile.AfterPressure
    profile.classificationExecution.Output

def currentAfterClassification :
    Query profile.AfterClassification fun _ => Residual :=
  profile.currentAfterPressure.preserve

def separatorOrderAfterClassification :
    Query profile.AfterClassification fun stage =>
      Core.Finite.Enumeration
        (profile.registration.SeparatorIndex
          (profile.currentAfterClassification.read stage)) :=
  profile.separatorOrderQuery.preserve.preserve.preserve

def separatorSpec : CT6.Spec profile.AfterClassification where
  Index := fun stage =>
    profile.registration.SeparatorIndex
      (profile.currentAfterClassification.read stage)
  FailureData := fun stage =>
    profile.registration.SeparatorData
      (profile.currentAfterClassification.read stage)
  Failure := fun stage =>
    profile.registration.SeparatorFailure
      (profile.currentAfterClassification.read stage)
  failureData := fun stage =>
    profile.registration.separatorFailureData
      (profile.currentAfterClassification.read stage)
  contribution := fun stage =>
    profile.registration.separatorContribution
      (profile.currentAfterClassification.read stage)

def separatorCapability : CT6.Capability profile.separatorSpec where
  failureOrder := profile.separatorOrderAfterClassification
  failureDecidable := fun stage =>
    profile.registration.separatorFailureDecidable
      (profile.currentAfterClassification.read stage)
  inputSize := fun stage =>
    CT6.localCheckBound
      (profile.separatorOrderAfterClassification.read stage)
  workCoefficient := Fintype.card Unit
  workDegree := Fintype.card Unit
  workBound := by
    intro stage
    simp only [Fintype.card_unit, Nat.pow_one, Nat.one_mul]
    exact Nat.le_succ _

noncomputable def separatorExecution :
    Core.Strategy.CTExecution profile.AfterClassification :=
  CTAdapters.ct6 profile.separatorCapability

noncomputable def execution : Core.Strategy.CTExecution Previous :=
  profile.collisionExecution.compose
    (profile.pressureExecution.compose
      (profile.classificationExecution.compose profile.separatorExecution))

/-- Literal ledger stage after the composed CT9 → CT14 → CT10 → CT6
execution. -/
abbrev AfterExecution :=
  Ledger.Extension Previous profile.execution.Output

/-- Direct read of the exact composed output written by the Strategy. -/
noncomputable def executionResult :
    Query profile.AfterExecution
      (fun stage => profile.execution.Output stage.previous) :=
  Query.latest

/-- Exact CT9 payload projected from the composed ledger entry. -/
noncomputable def collisionOutput :
    Query profile.AfterExecution
      (fun stage => profile.collisionExecution.Output stage.previous) :=
  profile.executionResult.map fun _ output => output.fst

/-- Exact CT14 payload projected from the composed ledger entry. -/
noncomputable def pressureOutput :
    Query profile.AfterExecution fun stage =>
      let output := profile.executionResult.read stage
      profile.pressureExecution.Output
        (Ledger.extend stage.previous output.fst) :=
  profile.executionResult.dependentMap fun _ output => output.snd.fst

/-- Exact CT10 payload projected from the composed ledger entry. -/
noncomputable def classificationOutput :
    Query profile.AfterExecution fun stage =>
      let output := profile.executionResult.read stage
      let collisionStage := Ledger.extend stage.previous output.fst
      profile.classificationExecution.Output
        (Ledger.extend collisionStage output.snd.fst) :=
  profile.executionResult.dependentMap fun _ output => output.snd.snd.fst

/-- Exact CT6 payload projected from the composed ledger entry. -/
noncomputable def separatorOutput :
    Query profile.AfterExecution fun stage =>
      let output := profile.executionResult.read stage
      let collisionStage := Ledger.extend stage.previous output.fst
      let pressureStage := Ledger.extend collisionStage output.snd.fst
      profile.separatorExecution.Output
        (Ledger.extend pressureStage output.snd.snd.fst) :=
  profile.executionResult.dependentMap fun _ output => output.snd.snd.snd

/-- The CT9 terminal read directly from the retained composed output. -/
noncomputable def collisionTerminal :
    Query profile.AfterExecution (fun _ => CT9.Terminal) :=
  profile.collisionOutput.map fun _ output => output.terminal

/-- The CT14 terminal read directly from the retained composed output. -/
noncomputable def pressureTerminal :
    Query profile.AfterExecution (fun _ => CT14.Terminal) :=
  profile.pressureOutput.map fun _ output => output.terminal

/-- The CT10 terminal read directly from the retained composed output. -/
noncomputable def classificationTerminal :
    Query profile.AfterExecution (fun _ => CT10.Terminal) :=
  profile.classificationOutput.map fun _ output => output.terminal

/-- The CT6 terminal read directly from the retained composed output. -/
noncomputable def separatorTerminal :
    Query profile.AfterExecution (fun _ => CT6.Terminal) :=
  profile.separatorOutput.map fun _ output => output.terminal

/-- The exact separator selected by CT6, if that scan found a first failure.
The query reads the literal output appended by the compiled Strategy.  Its
membership and failure proofs are transported across CT6's predecessor law;
the scan is never reconstructed or rerun. -/
private noncomputable def selectedSeparatorClaimLive
    {P : Core.Problem.{uAmbient, uBranch}} {T : Core.Target P}
    {Previous : Type (max uAmbient uBranch uLiveData)}
    [HasResidual Previous (Core.Strategy.ProblemInput P)]
    (profile : Profile.{
      max uAmbient uBranch uLiveData, max uAmbient uBranch,
      uLiveData, uLiveData, uLiveData, uLiveData, uLiveData, uLiveData,
      uLiveData, uLiveData} Previous (Core.Strategy.ProblemInput P))
    (certify : (stage : Previous) →
      Sigma (profile.execution.toContract.Payload stage) →
        Option (PLift (T.Predicate (residualOf stage).object))) :
    Query
      (Core.Strategy.HaltingProgram.LiveExtension T Previous
        profile.execution.toContract certify)
      (fun live =>
        Option (Σ separator :
            profile.registration.SeparatorIndex
              ((Core.Strategy.HaltingProgram.LiveExtension.preserveQuery
                (T := T) profile.current).read live),
          PLift
            (separator ∈
                (profile.registration.separatorOrder
                  ((Core.Strategy.HaltingProgram.LiveExtension.preserveQuery
                    (T := T) profile.current).read live)).values ∧
              profile.registration.SeparatorFailure
                ((Core.Strategy.HaltingProgram.LiveExtension.preserveQuery
                  (T := T) profile.current).read live) separator))) :=
  Query.ofFunction fun live => by
    let composed :=
      (profile.execution.liveOutputQuery certify).read live
    let collisionOutput := composed.fst
    let collisionStage := Ledger.extend live.previous collisionOutput
    let pressureOutput := composed.snd.fst
    let pressureStage := Ledger.extend collisionStage pressureOutput
    let classificationOutput := composed.snd.snd.fst
    let separatorInput := Ledger.extend pressureStage classificationOutput
    let separatorOutput := composed.snd.snd.snd
    have composed_eq : composed = profile.execution.run live.previous :=
      Core.Strategy.CTExecution.read_liveOutputQuery
        profile.execution certify live
    have previous_eq : separatorOutput.stage.previous = separatorInput := by
      change composed.snd.snd.snd.stage.previous =
        Ledger.extend
          (Ledger.extend
            (Ledger.extend live.previous composed.fst) composed.snd.fst)
          composed.snd.snd.fst
      rw [composed_eq]
      exact CT6.run_previous profile.separatorSpec
        profile.separatorCapability _
    match terminal : separatorOutput.terminal,
        outcome : separatorOutput.outcome with
    | .firstFailure, .firstFailure failure =>
        have current_eq :
            profile.currentAfterClassification.read
                separatorOutput.stage.previous =
              (Core.Strategy.HaltingProgram.LiveExtension.preserveQuery
                (T := T) profile.current).read live := by
          rw [previous_eq]
          rfl
        exact Eq.mp
          (congrArg (SeparatorClaim profile.registration) current_eq)
          (some ⟨failure.hit.value,
            PLift.up ⟨failure.hit.member, failure.hit.holds⟩⟩)
    | .activeLedger, .activeLedger _ => exact none

/-- Public exact-ledger package assembled from the three literal dependent
queries above. -/
noncomputable def separatorLedgerLive
    {P : Core.Problem.{uAmbient, uBranch}} {T : Core.Target P}
    {Previous : Type (max uAmbient uBranch uLiveData)}
    [HasResidual Previous (Core.Strategy.ProblemInput P)]
    (profile : Profile.{
      max uAmbient uBranch uLiveData, max uAmbient uBranch,
      uLiveData, uLiveData, uLiveData, uLiveData, uLiveData, uLiveData,
      uLiveData, uLiveData} Previous (Core.Strategy.ProblemInput P))
    (certify : (stage : Previous) →
      Sigma (profile.execution.toContract.Payload stage) →
        Option (PLift (T.Predicate (residualOf stage).object))) :
    SeparatorLedger
      (Core.Strategy.HaltingProgram.LiveExtension T Previous
        profile.execution.toContract certify)
      (Core.Strategy.ProblemInput P) profile.registration :=
  SeparatorLedger.ofClaim
    (Core.Strategy.HaltingProgram.LiveExtension.preserveQuery
      (T := T) profile.current)
    (profile.selectedSeparatorClaimLive certify)

end Profile

namespace ContinuationProfile

variable [HasResidual Previous Residual]

noncomputable def execution
    (continuation :
      ContinuationProfile Previous Residual pressureRegistration) :
    Core.Strategy.CTExecution Previous :=
  continuation.base.execution

end ContinuationProfile

end Hypostructure.Core.Strategy.FiniteBottleneckClassification
