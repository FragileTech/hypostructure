import Hypostructure.CTAdapters
import Hypostructure.Core.Strategy.HomogeneousBottleneckSemantics

/-!
# Homogeneous-bottleneck exhaustion

This reusable Core Strategy is exactly

`CT9 → CT14 → CT10 → CT6 → CT3 → CT6 → CT1 → CT5 → CT14`.

All primitive schedules are queried from the stable incoming residual.  The
first CT14 alone consumes CT9's exact generated partition through
`Query.latest`; every other root query is transported through the exact
number of Core-owned ledger extensions.  The implementation contains no
application classifier, custom executor, direct ledger write, or domain
concept.
-/

namespace Hypostructure.Core.Strategy.HomogeneousBottleneck

open Hypostructure
open Hypostructure.Core.Residual

universe uPrevious uResidual uData

/-- One inert registration lifted to an arbitrary literal predecessor. -/
structure Profile (Previous : Type uPrevious) (Residual : Type uResidual)
    [HasResidual Previous Residual] (Target : Residual → Prop) where
  registration : Registration.{uResidual, uData} Residual Target
  /-- The object this bottleneck audits.  It defaults to the incoming
  residual; a compiler that has already rebased onto a selected minimal
  counterexample passes that query instead, so every schedule, capacity and
  comparison below speaks about the same object as the strategies that
  produced this node's inputs. -/
  current : Query Previous (fun _ => Residual) := Query.residual

namespace Registration

variable {Residual : Type uResidual} {Target : Residual → Prop}

/-- Exact registered load compared by the final CT14 of the homogeneous
bottleneck: the registered `boundedLowerMass` summed over the residual's own
bounded member schedule. -/
def boundedLoad (registration : Registration.{uResidual, uData} Residual Target)
    (residual : Residual) : Nat :=
  ((registration.boundedMembers residual).values.map fun member =>
    registration.boundedLowerMass residual member).sum

/-- Exact registered capacity compared by the same final CT14: the registered
`boundedCapacity` summed over the same schedule.  Every entry is genuinely
finite by `boundedCapacityTotal`, so the `getD` default is never reached on a
scheduled member. -/
def boundedCap (registration : Registration.{uResidual, uData} Residual Target)
    (residual : Residual) : Nat :=
  ((registration.boundedMembers residual).values.map fun member =>
    (registration.boundedCapacity residual member).getD 0).sum

end Registration

namespace Profile

variable [HasResidual Previous Residual]
variable {Target : Residual → Prop}
variable (profile :
  Profile.{uPrevious, uResidual, uData} Previous Residual Target)

/-! ## Stable root queries -/

/-- The one stable read of the audited object. -/
def residualQuery : Query Previous (fun _ => Residual) :=
  profile.current

def itemQuery :=
  profile.residualQuery.dependentMap fun _ residual =>
    profile.registration.items residual

def homogeneityCodeQuery :=
  profile.residualQuery.dependentMap fun _ residual =>
    profile.registration.completeHomogeneityCodes residual

def dataQuery :=
  profile.residualQuery.dependentMap fun _ residual =>
    profile.registration.data residual

def localClassQuery :=
  profile.residualQuery.dependentMap fun _ residual =>
    profile.registration.completeLocalClasses residual

def localOrderQuery :=
  profile.residualQuery.dependentMap fun _ residual =>
    profile.registration.localOrder residual

def responseSourceQuery :=
  profile.residualQuery.dependentMap fun _ residual =>
    profile.registration.responseSource residual

def responseCoordinateQuery :=
  profile.residualQuery.dependentMap fun _ residual =>
    profile.registration.responseCoordinates residual

def responseCandidateQuery :=
  profile.residualQuery.dependentMap fun _ residual =>
    profile.registration.responseCandidates residual

def responseRowQuery :=
  profile.residualQuery.dependentMap fun _ residual =>
    profile.registration.responseRows residual

def admissibilityOrderQuery :=
  profile.residualQuery.dependentMap fun _ residual =>
    profile.registration.admissibilityOrder residual

def outcomeCandidateQuery :=
  profile.residualQuery.dependentMap fun _ residual =>
    profile.registration.outcomeCandidates residual

def supportFamilyQuery :=
  profile.residualQuery.dependentMap fun _ residual =>
    profile.registration.supportFamily residual

def boundedMemberQuery :=
  profile.residualQuery.dependentMap fun _ residual =>
    profile.registration.boundedMembers residual

/-! ## CT9: exact homogeneous fibres -/

def collisionSpec : CT9.Spec Previous where
  Item := fun previous =>
    profile.registration.Item (profile.current.read previous)
  Label := fun previous =>
    profile.registration.HomogeneityCode (profile.current.read previous)
  label := fun previous item =>
    profile.registration.homogeneityCodeOf (profile.current.read previous) item
  capacity := fun previous code =>
    profile.registration.homogeneityCapacity (profile.current.read previous) code

def collisionCapability : CT9.Capability profile.collisionSpec where
  items := profile.itemQuery
  labels := fun previous =>
    profile.homogeneityCodeQuery.read previous
  inputSize := fun previous =>
    CT9.localCheckBound
      (profile.itemQuery.read previous)
      (profile.homogeneityCodeQuery.read previous).toEnumeration
  workCoefficient := Fintype.card Unit
  workDegree := Fintype.card Unit
  workBound := by
    intro previous
    simp only [Fintype.card_unit, Nat.pow_one, Nat.one_mul]
    exact Nat.le_succ _

noncomputable def collisionExecution : CTExecution Previous :=
  CTAdapters.ct9 profile.collisionCapability

abbrev AfterCollision :=
  Ledger.Extension Previous profile.collisionExecution.Output

def collisionResult :
    Query profile.AfterCollision
      (fun stage => profile.collisionExecution.Output stage.previous) :=
  Query.latest

def collisionPartition :
    Query profile.AfterCollision fun stage =>
      let result := profile.collisionResult.read stage
      CT9.Partition profile.collisionCapability result.stage.previous :=
  profile.collisionResult.dependentMap fun _ result =>
    match result.terminal, result.outcome with
    | .overloaded, .overloaded partition _ => partition
    | .bounded, .bounded certificate => certificate.partition

def codeMembers :
    Query profile.AfterCollision fun stage =>
      let result := profile.collisionResult.read stage
      Core.Finite.Enumeration
        (profile.collisionSpec.Label result.stage.previous) :=
  profile.collisionResult.dependentMap fun _ result =>
    profile.collisionCapability.labelScheduleAt result.stage.previous

/-! ## First CT14: exact code-capacity accounting -/

def codeCapacitySpec : CT14.Spec profile.AfterCollision where
  Member := fun stage =>
    profile.collisionSpec.Label
      (profile.collisionResult.read stage).stage.previous
  Label := fun stage =>
    profile.registration.CapacityLabel
      (profile.current.read (profile.collisionResult.read stage).stage.previous)
  memberLowerMass := fun stage code =>
    (profile.collisionPartition.read stage).count code
  memberCapacity := fun stage code =>
    profile.registration.codeCapacity
      (profile.current.read (profile.collisionResult.read stage).stage.previous) code
  memberLabel := fun stage code =>
    profile.registration.codeLabel
      (profile.current.read (profile.collisionResult.read stage).stage.previous) code

def codeCapacityCapability : CT14.Capability profile.codeCapacitySpec where
  members := profile.codeMembers
  labelDecidableEq := fun stage =>
    profile.registration.codeLabelDecidableEq
      (profile.current.read (profile.collisionResult.read stage).stage.previous)
  inputSize := fun stage =>
    CT14.localCheckBound (profile.codeMembers.read stage)
  workCoefficient := Fintype.card Unit
  workDegree := Fintype.card Unit
  workBound := by
    intro stage
    simp only [Fintype.card_unit, Nat.pow_one, Nat.one_mul]
    exact Nat.le_succ _

noncomputable def codeCapacityExecution :
    CTExecution profile.AfterCollision :=
  CTAdapters.ct14 profile.codeCapacityCapability

abbrev AfterCodeCapacity :=
  Ledger.Extension profile.AfterCollision
    profile.codeCapacityExecution.Output

/-! ## CT10: exact finite local classification -/

def currentAfterCollision :=
  profile.current.preserve
    (Added := profile.collisionExecution.Output)

def currentAfterCodeCapacity :=
  profile.currentAfterCollision.preserve
    (Added := profile.codeCapacityExecution.Output)

def dataAfterCodeCapacity :=
  (profile.dataQuery.preserve
    (Added := profile.collisionExecution.Output)).preserve
      (Added := profile.codeCapacityExecution.Output)

def localClassesAfterCodeCapacity :=
  (profile.localClassQuery.preserve
    (Added := profile.collisionExecution.Output)).preserve
      (Added := profile.codeCapacityExecution.Output)

def classificationSpec : CT10.Spec profile.AfterCodeCapacity where
  Datum := fun stage =>
    profile.registration.Datum (profile.currentAfterCodeCapacity.read stage)
  Class := fun stage =>
    profile.registration.LocalClass (profile.currentAfterCodeCapacity.read stage)
  Promotion := fun stage =>
    profile.registration.Promotion (profile.currentAfterCodeCapacity.read stage)
  classOf := fun stage datum =>
    profile.registration.classOf (profile.currentAfterCodeCapacity.read stage) datum
  Direct := fun stage localClass =>
    profile.registration.Direct (profile.currentAfterCodeCapacity.read stage) localClass
  promote := fun stage localClass =>
    profile.registration.promote (profile.currentAfterCodeCapacity.read stage) localClass

def classificationCapability :
    CT10.Capability profile.classificationSpec where
  data := profile.dataAfterCodeCapacity
  classes := profile.localClassesAfterCodeCapacity
  directDecidable := fun stage localClass =>
    profile.registration.directDecidable (profile.currentAfterCodeCapacity.read stage) localClass
  inputSize := fun stage =>
    CT10.localCheckBound profile.classificationSpec
      profile.dataAfterCodeCapacity
      profile.localClassesAfterCodeCapacity stage
  workCoefficient := Fintype.card Unit
  workDegree := Fintype.card Unit
  workBound := by
    intro stage
    simp only [Fintype.card_unit, Nat.pow_one, Nat.one_mul]
    exact Nat.le_succ _

noncomputable def classificationExecution :
    CTExecution profile.AfterCodeCapacity :=
  CTAdapters.ct10 profile.classificationCapability

abbrev AfterClassification :=
  Ledger.Extension profile.AfterCodeCapacity
    profile.classificationExecution.Output

/-! ## First CT6: ordered local-failure audit -/

def currentAfterClassification :=
  profile.currentAfterCodeCapacity.preserve
    (Added := profile.classificationExecution.Output)

def localOrderAfterClassification :=
  ((profile.localOrderQuery.preserve
    (Added := profile.collisionExecution.Output)).preserve
      (Added := profile.codeCapacityExecution.Output)).preserve
        (Added := profile.classificationExecution.Output)

def localFailureSpec : CT6.Spec profile.AfterClassification where
  Index := fun stage =>
    profile.registration.LocalIndex (profile.currentAfterClassification.read stage)
  FailureData := fun stage index =>
    profile.registration.LocalFailureData (profile.currentAfterClassification.read stage) index
  Failure := fun stage index =>
    profile.registration.LocalFailure (profile.currentAfterClassification.read stage) index
  failureData := fun stage index failure =>
    profile.registration.localFailureData
      (profile.currentAfterClassification.read stage) index failure
  contribution := fun stage index =>
    profile.registration.localContribution (profile.currentAfterClassification.read stage) index

def localFailureCapability : CT6.Capability profile.localFailureSpec where
  failureOrder := profile.localOrderAfterClassification
  failureDecidable := fun stage index =>
    profile.registration.localFailureDecidable
      (profile.currentAfterClassification.read stage) index
  inputSize := fun stage =>
    CT6.localCheckBound (profile.localOrderAfterClassification.read stage)
  workCoefficient := Fintype.card Unit
  workDegree := Fintype.card Unit
  workBound := by
    intro stage
    simp only [Fintype.card_unit, Nat.pow_one, Nat.one_mul]
    exact Nat.le_succ _

noncomputable def localFailureExecution :
    CTExecution profile.AfterClassification :=
  CTAdapters.ct6 profile.localFailureCapability

abbrev AfterLocalFailure :=
  Ledger.Extension profile.AfterClassification
    profile.localFailureExecution.Output

/-! ## CT3: exact response table -/

def currentAfterLocalFailure :=
  profile.currentAfterClassification.preserve
    (Added := profile.localFailureExecution.Output)

def responseSourceAfterFinite :=
  (((profile.responseSourceQuery.preserve
    (Added := profile.collisionExecution.Output)).preserve
      (Added := profile.codeCapacityExecution.Output)).preserve
        (Added := profile.classificationExecution.Output)).preserve
          (Added := profile.localFailureExecution.Output)

def responseCoordinatesAfterFinite :=
  (((profile.responseCoordinateQuery.preserve
    (Added := profile.collisionExecution.Output)).preserve
      (Added := profile.codeCapacityExecution.Output)).preserve
        (Added := profile.classificationExecution.Output)).preserve
          (Added := profile.localFailureExecution.Output)

def responseCandidatesAfterFinite :=
  (((profile.responseCandidateQuery.preserve
    (Added := profile.collisionExecution.Output)).preserve
      (Added := profile.codeCapacityExecution.Output)).preserve
        (Added := profile.classificationExecution.Output)).preserve
          (Added := profile.localFailureExecution.Output)

def responseRowsAfterFinite :=
  (((profile.responseRowQuery.preserve
    (Added := profile.collisionExecution.Output)).preserve
      (Added := profile.codeCapacityExecution.Output)).preserve
        (Added := profile.classificationExecution.Output)).preserve
          (Added := profile.localFailureExecution.Output)

def responseSpec : CT3.Spec profile.AfterLocalFailure where
  Representative := profile.registration.Representative
  Candidate := profile.registration.ResponseCandidate
  Row := profile.registration.ResponseRow
  system := profile.registration.responseSystem
  semantics := profile.registration.targetSemantics
  candidatePiece := profile.registration.candidatePiece
  rowPiece := profile.registration.rowPiece
  rowResponse := profile.registration.rowResponse
  Admissible := fun stage =>
    profile.registration.ResponseAdmissible (profile.currentAfterLocalFailure.read stage)
  StrictlySmaller := fun stage =>
    profile.registration.ResponseStrictlySmaller (profile.currentAfterLocalFailure.read stage)

def responseCapability : CT3.Capability profile.responseSpec where
  source := profile.responseSourceAfterFinite
  coordinates := profile.responseCoordinatesAfterFinite
  candidates := profile.responseCandidatesAfterFinite
  rows := profile.responseRowsAfterFinite
  valueDecEq := profile.registration.responseValueDecEq
  admissibleDecidable := fun stage source candidate =>
    profile.registration.responseAdmissibleDecidable
      (profile.currentAfterLocalFailure.read stage) source candidate
  smallerDecidable := fun stage source candidate =>
    profile.registration.responseSmallerDecidable
      (profile.currentAfterLocalFailure.read stage) source candidate
  candidateCoverage := fun stage candidate member =>
    profile.registration.responseCandidateCoverage
      (profile.currentAfterLocalFailure.read stage) candidate member
  rowCoverage := fun stage row member =>
    profile.registration.responseRowCoverage
      (profile.currentAfterLocalFailure.read stage) row member
  inputSize := fun stage =>
    CT3.localCheckBound
      (profile.responseCoordinatesAfterFinite.read stage)
      (profile.responseCandidatesAfterFinite.read stage)
      (profile.responseRowsAfterFinite.read stage)
  workCoefficient := Fintype.card Unit
  workDegree := Fintype.card Unit
  workBound := by
    intro stage
    simp only [Fintype.card_unit, Nat.pow_one, Nat.one_mul]
    exact Nat.le_succ _

noncomputable def responseExecution :
    CTExecution profile.AfterLocalFailure :=
  CTAdapters.ct3 profile.responseCapability

abbrev AfterResponse :=
  Ledger.Extension profile.AfterLocalFailure
    profile.responseExecution.Output

/-! ## Second CT6: ordered admissibility audit -/

def currentAfterResponse :=
  profile.currentAfterLocalFailure.preserve
    (Added := profile.responseExecution.Output)

def admissibilityOrderAfterResponse :=
  ((((profile.admissibilityOrderQuery.preserve
    (Added := profile.collisionExecution.Output)).preserve
      (Added := profile.codeCapacityExecution.Output)).preserve
        (Added := profile.classificationExecution.Output)).preserve
          (Added := profile.localFailureExecution.Output)).preserve
            (Added := profile.responseExecution.Output)

def admissibilitySpec : CT6.Spec profile.AfterResponse where
  Index := fun stage =>
    profile.registration.AdmissibilityField (profile.currentAfterResponse.read stage)
  FailureData := fun stage field =>
    profile.registration.AdmissibilityFailureData
      (profile.currentAfterResponse.read stage) field
  Failure := fun stage field =>
    profile.registration.AdmissibilityFailure (profile.currentAfterResponse.read stage) field
  failureData := fun stage field failure =>
    profile.registration.admissibilityFailureData
      (profile.currentAfterResponse.read stage) field failure
  contribution := fun stage field =>
    profile.registration.admissibilityContribution
      (profile.currentAfterResponse.read stage) field

def admissibilityCapability : CT6.Capability profile.admissibilitySpec where
  failureOrder := profile.admissibilityOrderAfterResponse
  failureDecidable := fun stage field =>
    profile.registration.admissibilityFailureDecidable
      (profile.currentAfterResponse.read stage) field
  inputSize := fun stage =>
    CT6.localCheckBound
      (profile.admissibilityOrderAfterResponse.read stage)
  workCoefficient := Fintype.card Unit
  workDegree := Fintype.card Unit
  workBound := by
    intro stage
    simp only [Fintype.card_unit, Nat.pow_one, Nat.one_mul]
    exact Nat.le_succ _

noncomputable def admissibilityExecution :
    CTExecution profile.AfterResponse :=
  CTAdapters.ct6 profile.admissibilityCapability

abbrev AfterAdmissibility :=
  Ledger.Extension profile.AfterResponse
    profile.admissibilityExecution.Output

/-! ## CT1: target-or-exception realization -/

def currentAfterAdmissibility :=
  profile.currentAfterResponse.preserve
    (Added := profile.admissibilityExecution.Output)

def outcomeCandidatesAfterAdmissibility :=
  (((((profile.outcomeCandidateQuery.preserve
    (Added := profile.collisionExecution.Output)).preserve
      (Added := profile.codeCapacityExecution.Output)).preserve
        (Added := profile.classificationExecution.Output)).preserve
          (Added := profile.localFailureExecution.Output)).preserve
            (Added := profile.responseExecution.Output)).preserve
              (Added := profile.admissibilityExecution.Output)

def outcomeSpec : CT1.Spec profile.AfterAdmissibility where
  Candidate := fun stage =>
    Sum
      (profile.registration.TargetCandidate (profile.currentAfterAdmissibility.read stage))
      (profile.registration.ExceptionalCandidate (profile.currentAfterAdmissibility.read stage))
  Realizes := fun stage candidate =>
    match candidate with
    | .inl target =>
        profile.registration.RealizesTarget (profile.currentAfterAdmissibility.read stage) target
    | .inr exceptional =>
        profile.registration.RealizesException (profile.currentAfterAdmissibility.read stage) exceptional

def outcomeCapability : CT1.Capability profile.outcomeSpec where
  schedule := profile.outcomeCandidatesAfterAdmissibility
  realizesDecidable := fun stage candidate =>
    match candidate with
    | .inl target =>
        profile.registration.targetRealizationDecidable
          (profile.currentAfterAdmissibility.read stage) target
    | .inr exceptional =>
        profile.registration.exceptionRealizationDecidable
          (profile.currentAfterAdmissibility.read stage) exceptional
  inputSize := fun stage =>
    CT1.searchCheckBound profile.outcomeSpec
      profile.outcomeCandidatesAfterAdmissibility stage
  workCoefficient := Fintype.card Unit
  workDegree := Fintype.card Unit
  workBound := by
    intro stage
    simp only [Fintype.card_unit, Nat.pow_one, Nat.one_mul]
    exact Nat.le_succ _

noncomputable def outcomeExecution :
    CTExecution profile.AfterAdmissibility :=
  CTAdapters.ct1 profile.outcomeCapability

abbrev AfterOutcome :=
  Ledger.Extension profile.AfterAdmissibility
    profile.outcomeExecution.Output

/-! ## CT5: exact structured-support accounting -/

def currentAfterOutcome :=
  profile.currentAfterAdmissibility.preserve
    (Added := profile.outcomeExecution.Output)

def supportFamilyAfterOutcome :=
  ((((((profile.supportFamilyQuery.preserve
    (Added := profile.collisionExecution.Output)).preserve
      (Added := profile.codeCapacityExecution.Output)).preserve
        (Added := profile.classificationExecution.Output)).preserve
          (Added := profile.localFailureExecution.Output)).preserve
            (Added := profile.responseExecution.Output)).preserve
              (Added := profile.admissibilityExecution.Output)).preserve
                (Added := profile.outcomeExecution.Output)

def supportSpec : CT5.Spec profile.AfterOutcome where
  budget := profile.registration.supportBudget
  Site := fun stage =>
    profile.registration.SupportSite (profile.currentAfterOutcome.read stage)
  Witness := fun stage site =>
    profile.registration.SupportWitness (profile.currentAfterOutcome.read stage) site
  Active := fun stage site =>
    profile.registration.SupportActive (profile.currentAfterOutcome.read stage) site
  Supports := fun stage site witness =>
    profile.registration.SupportRelation
      (profile.currentAfterOutcome.read stage) site witness
  contribution := fun stage site witness =>
    profile.registration.supportContribution
      (profile.currentAfterOutcome.read stage) site witness
  required := fun stage =>
    profile.registration.supportRequired (profile.currentAfterOutcome.read stage)
  capacity := fun stage =>
    profile.registration.supportCapacity (profile.currentAfterOutcome.read stage)

def supportCapability : CT5.Capability profile.supportSpec where
  family := profile.supportFamilyAfterOutcome
  activeDecidable := fun stage site =>
    profile.registration.supportActiveDecidable
      (profile.currentAfterOutcome.read stage) site
  supportsDecidable := fun stage site witness =>
    profile.registration.supportRelationDecidable
      (profile.currentAfterOutcome.read stage) site witness
  resourceLEDecidable :=
    profile.registration.supportResourceLEDecidable

noncomputable def supportExecution :
    CTExecution profile.AfterOutcome :=
  CTAdapters.ct5 profile.supportCapability

abbrev AfterSupport :=
  Ledger.Extension profile.AfterOutcome
    profile.supportExecution.Output

/-! ## Final CT14: bounded homogeneous capacity -/

def currentAfterSupport :=
  profile.currentAfterOutcome.preserve
    (Added := profile.supportExecution.Output)

def boundedMembersAfterSupport :=
  (((((((profile.boundedMemberQuery.preserve
    (Added := profile.collisionExecution.Output)).preserve
      (Added := profile.codeCapacityExecution.Output)).preserve
        (Added := profile.classificationExecution.Output)).preserve
          (Added := profile.localFailureExecution.Output)).preserve
            (Added := profile.responseExecution.Output)).preserve
              (Added := profile.admissibilityExecution.Output)).preserve
                (Added := profile.outcomeExecution.Output)).preserve
                  (Added := profile.supportExecution.Output)

def boundedSpec : CT14.Spec profile.AfterSupport where
  Member := fun stage =>
    profile.registration.BoundedMember (profile.currentAfterSupport.read stage)
  Label := fun stage =>
    profile.registration.BoundedLabel (profile.currentAfterSupport.read stage)
  memberLowerMass := fun stage member =>
    profile.registration.boundedLowerMass (profile.currentAfterSupport.read stage) member
  memberCapacity := fun stage member =>
    profile.registration.boundedCapacity (profile.currentAfterSupport.read stage) member
  memberLabel := fun stage member =>
    profile.registration.boundedLabel (profile.currentAfterSupport.read stage) member

def boundedCapability : CT14.Capability profile.boundedSpec where
  members := profile.boundedMembersAfterSupport
  labelDecidableEq := fun stage =>
    profile.registration.boundedLabelDecidableEq (profile.currentAfterSupport.read stage)
  inputSize := fun stage =>
    CT14.localCheckBound (profile.boundedMembersAfterSupport.read stage)
  workCoefficient := Fintype.card Unit
  workDegree := Fintype.card Unit
  workBound := by
    intro stage
    simp only [Fintype.card_unit, Nat.pow_one, Nat.one_mul]
    exact Nat.le_succ _

noncomputable def boundedExecution :
    CTExecution profile.AfterSupport :=
  CTAdapters.ct14 profile.boundedCapability

/-! ## Complete exact composition -/

noncomputable def execution : CTExecution Previous :=
  (CTAdapters.ct9 profile.collisionCapability).compose
    ((CTAdapters.ct14 profile.codeCapacityCapability).compose
      ((CTAdapters.ct10 profile.classificationCapability).compose
        ((CTAdapters.ct6 profile.localFailureCapability).compose
          ((CTAdapters.ct3 profile.responseCapability).compose
            ((CTAdapters.ct6 profile.admissibilityCapability).compose
              ((CTAdapters.ct1 profile.outcomeCapability).compose
                ((CTAdapters.ct5 profile.supportCapability).compose
                  (CTAdapters.ct14 profile.boundedCapability))))))))

/-! ## Exact output projections and provenance -/

def collisionOutput {previous : Previous}
    (output : profile.execution.Output previous) :=
  output.fst

def codeCapacityOutput {previous : Previous}
    (output : profile.execution.Output previous) :=
  output.snd.fst

def classificationOutput {previous : Previous}
    (output : profile.execution.Output previous) :=
  output.snd.snd.fst

def localFailureOutput {previous : Previous}
    (output : profile.execution.Output previous) :=
  output.snd.snd.snd.fst

def responseOutput {previous : Previous}
    (output : profile.execution.Output previous) :=
  output.snd.snd.snd.snd.fst

def admissibilityOutput {previous : Previous}
    (output : profile.execution.Output previous) :=
  output.snd.snd.snd.snd.snd.fst

def outcomeOutput {previous : Previous}
    (output : profile.execution.Output previous) :=
  output.snd.snd.snd.snd.snd.snd.fst

def supportOutput {previous : Previous}
    (output : profile.execution.Output previous) :=
  output.snd.snd.snd.snd.snd.snd.snd.fst

def boundedOutput {previous : Previous}
    (output : profile.execution.Output previous) :=
  output.snd.snd.snd.snd.snd.snd.snd.snd

/-- The one literal nested output plus the stable residual laws of its nine
Core-owned CT writes.  Each law is stated at the immediate CT predecessor;
clients never traverse the nested ledger representation. -/
structure ExactOutput (previous : Previous) where
  output : profile.execution.Output previous
  collisionResidual :
    profile.current.read (profile.collisionOutput output).stage.previous =
      profile.current.read previous
  codeCapacityResidual :
    profile.currentAfterCollision.read (profile.codeCapacityOutput output).stage.previous =
      profile.current.read previous
  classificationResidual :
    profile.currentAfterCodeCapacity.read (profile.classificationOutput output).stage.previous =
      profile.current.read previous
  localFailureResidual :
    profile.currentAfterClassification.read (profile.localFailureOutput output).stage.previous =
      profile.current.read previous
  responseResidual :
    profile.currentAfterLocalFailure.read (profile.responseOutput output).stage.previous =
      profile.current.read previous
  admissibilityResidual :
    profile.currentAfterResponse.read (profile.admissibilityOutput output).stage.previous =
      profile.current.read previous
  outcomeResidual :
    profile.currentAfterAdmissibility.read (profile.outcomeOutput output).stage.previous =
      profile.current.read previous
  supportResidual :
    profile.currentAfterOutcome.read (profile.supportOutput output).stage.previous =
      profile.current.read previous
  boundedResidual :
    profile.currentAfterSupport.read (profile.boundedOutput output).stage.previous =
      profile.current.read previous

/-- Terminal-specific implications derived from one inert registration.
These fields consume exact CT evidence; none returns a route or result. -/
structure Semantics where
  Target : Previous → Prop
  targetOfRealization : ∀ previous (exact : profile.ExactOutput previous)
    (candidate :
      profile.registration.TargetCandidate
        (profile.currentAfterAdmissibility.read (profile.outcomeOutput exact.output).stage.previous)),
      profile.registration.RealizesTarget
        (profile.currentAfterAdmissibility.read (profile.outcomeOutput exact.output).stage.previous)
        candidate → Target previous
  localFailureAvoidingImpossible :
    ∀ previous (exact : profile.ExactOutput previous),
      (profile.localFailureOutput exact.output).terminal = .firstFailure →
      (profile.outcomeOutput exact.output).terminal = .avoiding → False
  responseDefectAvoidingImpossible :
    ∀ previous (exact : profile.ExactOutput previous),
      (profile.responseOutput exact.output).terminal = .distinguishing →
      (profile.outcomeOutput exact.output).terminal = .avoiding → False
  admissibilityFailureAvoidingImpossible :
    ∀ previous (exact : profile.ExactOutput previous),
      (profile.admissibilityOutput exact.output).terminal = .firstFailure →
      (profile.outcomeOutput exact.output).terminal = .avoiding → False
  supportDeficitAvoidingImpossible :
    ∀ previous (exact : profile.ExactOutput previous),
      (profile.outcomeOutput exact.output).terminal = .avoiding →
      (profile.supportOutput exact.output).terminal = .deficit → False
  supportCapacityAvoidingImpossible :
    ∀ previous (exact : profile.ExactOutput previous),
      (profile.outcomeOutput exact.output).terminal = .avoiding →
      (profile.supportOutput exact.output).terminal = .c4 → False
  boundedCapacityComplete :
    ∀ previous (exact : profile.ExactOutput previous),
      (profile.boundedOutput exact.output).terminal = .unboundedMember → False
  boundedLabelComplete :
    ∀ previous (exact : profile.ExactOutput previous),
      (profile.boundedOutput exact.output).terminal = .missingLabel → False

/-- Proposition-only identification of CT1's exact exceptional hit. -/
def ExceptionalSelected {previous : Previous}
    (exact : profile.ExactOutput previous) : Prop :=
  ∃ candidate :
      profile.registration.ExceptionalCandidate
        (profile.currentAfterAdmissibility.read (profile.outcomeOutput exact.output).stage.previous),
    ∃ hasHit :
        (profile.outcomeOutput exact.output).stage.added.previous.HasHit,
      (Core.Finite.Search.Execution.hitOfHasHit
        (profile.outcomeOutput exact.output).stage.added.previous
        hasHit).value = Sum.inr candidate

/-- A registration whose exceptional candidate family is uninhabited refutes
any CT1 exceptional identification.  This is the whole mathematical content of
the vacuity closure: `ExceptionalSelected` produces the candidate, and the
registered fact rejects it. -/
theorem exceptionalSelected_false {previous : Previous}
    {exact : profile.ExactOutput previous}
    (impossible : ∀ residual,
      profile.registration.ExceptionalCandidate residual → False)
    (identified : profile.ExceptionalSelected exact) : False :=
  identified.elim fun candidate _ => impossible _ candidate

/-- The four exhaustive routes of the homogeneous-bottleneck composition. -/
inductive Terminal where
  | target
  | exceptional
  | structured
  | bounded
  deriving DecidableEq, Repr

/-- Exhaustive terminal-indexed successor.  Every constructor retains the
same literal nine-CT output; every additional field is propositional. -/
inductive RoutedResidual (semantics : profile.Semantics)
    (previous : Previous) : Terminal → Type (max uPrevious uResidual uData) where
  | target
      (exact : profile.ExactOutput previous)
      (proof : semantics.Target previous) :
      RoutedResidual semantics previous .target
  | exceptional
      (exact : profile.ExactOutput previous)
      (selected :
        (profile.outcomeOutput exact.output).terminal = .c1)
      (identified : profile.ExceptionalSelected exact) :
      RoutedResidual semantics previous .exceptional
  | structured
      (exact : profile.ExactOutput previous)
      (outcomeAvoiding :
        (profile.outcomeOutput exact.output).terminal = .avoiding)
      (supportSelected :
        (profile.supportOutput exact.output).terminal = .aggregate ∨
        ((profile.supportOutput exact.output).terminal = .chargeLedger ∧
          (profile.boundedOutput exact.output).terminal = .aggregate)) :
      RoutedResidual semantics previous .structured
  | bounded
      (exact : profile.ExactOutput previous)
      (outcomeAvoiding :
        (profile.outcomeOutput exact.output).terminal = .avoiding)
      (supportSelected :
        (profile.supportOutput exact.output).terminal = .chargeLedger)
      (capacitySelected :
        (profile.boundedOutput exact.output).terminal = .capacity) :
      RoutedResidual semantics previous .bounded

/-- Under the registered exceptional-vacuity fact, the exceptional route of
`RoutedResidual` is uninhabited.

The exceptional constructor retains `ExceptionalSelected`, which asserts the
existence of an `ExceptionalCandidate` that CT1's search actually hit.  A
registration whose exceptional schedule has no inhabitant therefore refutes
its own exceptional output; nothing else about the composed execution is
consulted. -/
theorem exceptional_false {semantics : profile.Semantics} {previous : Previous}
    (impossible : ∀ residual,
      profile.registration.ExceptionalCandidate residual → False)
    (witness : profile.RoutedResidual semantics previous .exceptional) :
    False := by
  cases witness with
  | exceptional _ _ identified =>
      exact profile.exceptionalSelected_false impossible identified

/-- Public projection from the exact final CT14 capacity residual retained by
the bounded terminal to the literal registered comparison it was executed on.
Consumers do not unfold the composed nine-CT ledger.

This is the branch fact recorded by the bounded route of the homogeneous
bottleneck: the registered homogeneous load, read on the residual's own
bounded member schedule, is at most the registered capacity on that same
schedule.  A continuation nested inside the bounded branch may read the
numeric estimate from here instead of assuming it.

Mirrors `ScaleThresholdDichotomy.Profile.AtOrBelowResidual.load_le_threshold`.
`RoutedResidual.bounded` is the only constructor that *retains* the CT14
`.capacity` terminal as a field, which is why only it can be eliminated into
this comparison; the composition runs all nine CTs on every route, so the
other three constructors say nothing either way about that terminal. -/
theorem bounded_load_le_cap {semantics : profile.Semantics}
    {previous : Previous}
    (witness : profile.RoutedResidual semantics previous .bounded) :
    profile.registration.boundedLoad (profile.current.read previous) ≤
      profile.registration.boundedCap (profile.current.read previous) := by
  cases witness with
  | bounded exact _ _ capacitySelected =>
      have outcome := (profile.boundedOutput exact.output).outcome
      rw [capacitySelected] at outcome
      cases outcome with
      | capacity ledger residual =>
          change ledger.lower.total ≤ ledger.capacity.total at residual
          rw [ledger.lower.total_exact, ledger.capacity.total_exact] at residual
          rw [← exact.boundedResidual]
          simp only [CT14.lowerMass, CT14.lowerMassEntries, CT14.upperCapacity,
            CT14.capacityEntries, List.map_map, Function.comp_def] at residual
          exact residual

/-- Fixed terminal elimination over the one exact composed execution. -/
noncomputable def route (semantics : profile.Semantics)
    (previous : Previous) :
    Sigma (profile.RoutedResidual semantics previous) :=
  let output := profile.execution.run previous
  let exact : profile.ExactOutput previous :=
    ⟨output, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  match outcomeTerminal :
      (profile.outcomeOutput output).terminal with
  | .c1 =>
      match branch :
          (profile.outcomeOutput output).stage.added.added with
      | .noBranch _ =>
          have avoiding :
              (profile.outcomeOutput output).terminal = .avoiding := by
            simp [CT1.ExecutionResult.terminal, CT1.terminalOfRoute, branch]
          (CT1.Terminal.noConfusion (outcomeTerminal.symm.trans avoiding))
      | .yesBranch hasHit =>
          let hit := Core.Finite.Search.Execution.hitOfHasHit
            (profile.outcomeOutput output).stage.added.previous hasHit
          match selected : hit.value with
          | .inl candidate =>
              ⟨.target,
                .target exact
                  (semantics.targetOfRealization previous exact candidate (by
                    have realized := hit.sound
                    rw [selected] at realized
                    exact realized))⟩
          | .inr candidate =>
              ⟨.exceptional,
                .exceptional exact outcomeTerminal
                  ⟨candidate, hasHit, selected⟩⟩
  | .avoiding =>
      match localTerminal :
          (profile.localFailureOutput output).terminal with
      | .firstFailure =>
          (semantics.localFailureAvoidingImpossible previous exact
            localTerminal outcomeTerminal).elim
      | .activeLedger =>
          match responseTerminal :
              (profile.responseOutput output).terminal with
          | .distinguishing =>
              (semantics.responseDefectAvoidingImpossible previous exact
                responseTerminal outcomeTerminal).elim
          | .compression | .knownRow | .novelRow =>
              match admissibilityTerminal :
                  (profile.admissibilityOutput output).terminal with
              | .firstFailure =>
                  (semantics.admissibilityFailureAvoidingImpossible previous
                    exact admissibilityTerminal outcomeTerminal).elim
              | .activeLedger =>
                  match supportTerminal :
                      (profile.supportOutput output).terminal with
                  | .deficit =>
                      (semantics.supportDeficitAvoidingImpossible previous
                        exact outcomeTerminal supportTerminal).elim
                  | .c4 =>
                      (semantics.supportCapacityAvoidingImpossible previous
                        exact outcomeTerminal supportTerminal).elim
                  | .aggregate =>
                      ⟨.structured,
                        .structured exact outcomeTerminal
                          (Or.inl supportTerminal)⟩
                  | .chargeLedger =>
                      match boundedResultTerminal :
                          (profile.boundedOutput output).terminal with
                      | .unboundedMember =>
                          (semantics.boundedCapacityComplete previous exact
                            boundedResultTerminal).elim
                      | .missingLabel =>
                          (semantics.boundedLabelComplete previous exact
                            boundedResultTerminal).elim
                      | .aggregate =>
                          ⟨.structured,
                            .structured exact outcomeTerminal
                              (Or.inr
                                ⟨supportTerminal, boundedResultTerminal⟩)⟩
                      | .capacity =>
                          ⟨.bounded,
                            .bounded exact outcomeTerminal supportTerminal
                              boundedResultTerminal⟩

/-- Four-terminal Strategy boundary over the exact routed execution. -/
noncomputable def contract (semantics : profile.Semantics) :
    Core.Strategy.Contract Previous where
  Terminal := Terminal
  Payload := fun previous terminal =>
    profile.RoutedResidual semantics previous terminal
  produce := fun previous => profile.route semantics previous
  exhaustive := fun previous =>
    ⟨profile.route semantics previous⟩

end Profile

/-! ## Registration-driven construction -/

def Profile.ofRegistration
    {Previous : Type uPrevious} {Residual : Type uResidual}
    [HasResidual Previous Residual] {Target : Residual → Prop}
    (registration :
      Registration.{uResidual, uData} Residual Target) :
    Profile.{uPrevious, uResidual, uData} Previous Residual Target :=
  { registration }

/-- The same registration lowered at an explicit audited-object query. -/
def Profile.ofRegistrationAt
    {Previous : Type uPrevious} {Residual : Type uResidual}
    [HasResidual Previous Residual] {Target : Residual → Prop}
    (registration :
      Registration.{uResidual, uData} Residual Target)
    (current : Query Previous (fun _ => Residual)) :
    Profile.{uPrevious, uResidual, uData} Previous Residual Target :=
  { registration, current }

namespace Profile

variable [HasResidual Previous Residual]
variable {Target : Residual → Prop}

/-! The proof that the inert registration laws imply the exact terminal laws
is intentionally kept separate from execution. -/
def semanticsOfProfile
    (profile :
      Profile.{uPrevious, uResidual, uData} Previous Residual Target) :
    profile.Semantics := by
  let registration := profile.registration
  refine
    { Target := fun previous => Target (profile.current.read previous)
      targetOfRealization := ?_
      localFailureAvoidingImpossible := ?_
      responseDefectAvoidingImpossible := ?_
      admissibilityFailureAvoidingImpossible := ?_
      supportDeficitAvoidingImpossible := ?_
      supportCapacityAvoidingImpossible := ?_
      boundedCapacityComplete := ?_
      boundedLabelComplete := ?_ }
  · intro previous exact candidate realizes
    have target :=
      registration.targetOfRealization
        (profile.currentAfterAdmissibility.read (profile.outcomeOutput exact.output).stage.previous)
        candidate realizes
    have residual_eq :
        profile.currentAfterAdmissibility.read (profile.outcomeOutput exact.output).stage.previous =
          profile.current.read previous :=
      exact.outcomeResidual
    exact residual_eq ▸ target
  · intro previous exact localTerminal outcomeTerminal
    have outcome := (profile.localFailureOutput exact.output).outcome
    rw [localTerminal] at outcome
    cases outcome with
    | firstFailure failure =>
        have forcedAtOutcome :
            ∃ candidate :
                registration.ExceptionalCandidate
                  (profile.currentAfterAdmissibility.read
                    (profile.outcomeOutput exact.output).stage.previous),
              Sum.inr candidate ∈
                  (registration.outcomeCandidates
                    (profile.currentAfterAdmissibility.read
                      (profile.outcomeOutput exact.output).stage.previous)).values ∧
                registration.RealizesException
                  (profile.currentAfterAdmissibility.read
                    (profile.outcomeOutput exact.output).stage.previous)
                  candidate := by
          have localResidual :
              profile.currentAfterClassification.read
                  (profile.localFailureOutput exact.output).stage.previous =
                profile.current.read previous :=
            exact.localFailureResidual
          have outcomeResidual :
              profile.currentAfterAdmissibility.read (profile.outcomeOutput exact.output).stage.previous =
                profile.current.read previous :=
            exact.outcomeResidual
          exact localResidual.trans outcomeResidual.symm ▸
            registration.localFailureScheduled
              (profile.currentAfterClassification.read
                (profile.localFailureOutput exact.output).stage.previous)
              failure.hit.value failure.hit.member failure.hit.holds
        obtain ⟨candidate, scheduled, realizes⟩ := forcedAtOutcome
        have ctScheduled :
            Sum.inr candidate ∈
              (profile.outcomeCapability.scheduleAt
                (profile.outcomeOutput exact.output).stage.previous).values := by
          change Sum.inr candidate ∈
            (registration.outcomeCandidates
              (profile.currentAfterAdmissibility.read
                (profile.outcomeOutput exact.output).stage.previous)).values
          exact scheduled
        cases branch :
            (profile.outcomeOutput exact.output).stage.added.added with
        | yesBranch _ =>
            have selected :
                (profile.outcomeOutput exact.output).terminal = .c1 := by
              simp [CT1.ExecutionResult.terminal, CT1.terminalOfRoute, branch]
            exact CT1.Terminal.noConfusion
              (selected.symm.trans outcomeTerminal)
        | noBranch avoids =>
            exact (CT1.AvoidingState.noRealization avoids
              (Sum.inr candidate) ctScheduled) realizes
  · intro previous exact responseTerminal outcomeTerminal
    have outcome := (profile.responseOutput exact.output).outcome
    rw [responseTerminal] at outcome
    cases outcome with
    | distinguishing _ certificate =>
        have rowScheduled :
            certificate.row ∈
              (registration.responseRows
                (profile.currentAfterLocalFailure.read
                  (profile.responseOutput exact.output).stage.previous)).values := by
          change certificate.row ∈
            (profile.responseCapability.rowsAt
              (profile.responseOutput exact.output).stage.previous).values
          exact certificate.row_member
        have coordinateScheduled :
            certificate.coordinate ∈
              (registration.responseCoordinates
                (profile.currentAfterLocalFailure.read
                  (profile.responseOutput exact.output).stage.previous)).values := by
          change certificate.coordinate ∈
            (profile.responseCapability.coordinatesAt
              (profile.responseOutput exact.output).stage.previous).values
          exact certificate.coordinate_member
        have forcedAtOutcome :
            ∃ candidate :
                registration.ExceptionalCandidate
                  (profile.currentAfterAdmissibility.read
                    (profile.outcomeOutput exact.output).stage.previous),
              Sum.inr candidate ∈
                  (registration.outcomeCandidates
                    (profile.currentAfterAdmissibility.read
                      (profile.outcomeOutput exact.output).stage.previous)).values ∧
                registration.RealizesException
                  (profile.currentAfterAdmissibility.read
                    (profile.outcomeOutput exact.output).stage.previous)
                  candidate := by
          have responseResidual :
              profile.currentAfterLocalFailure.read
                  (profile.responseOutput exact.output).stage.previous =
                profile.current.read previous :=
            exact.responseResidual
          have outcomeResidual :
              profile.currentAfterAdmissibility.read (profile.outcomeOutput exact.output).stage.previous =
                profile.current.read previous :=
            exact.outcomeResidual
          exact responseResidual.trans outcomeResidual.symm ▸
            registration.responseDefectScheduled
              (profile.currentAfterLocalFailure.read
                (profile.responseOutput exact.output).stage.previous)
              certificate.row certificate.coordinate rowScheduled
              coordinateScheduled certificate.differs
        obtain ⟨candidate, scheduled, realizes⟩ := forcedAtOutcome
        have ctScheduled :
            Sum.inr candidate ∈
              (profile.outcomeCapability.scheduleAt
                (profile.outcomeOutput exact.output).stage.previous).values := by
          change Sum.inr candidate ∈
            (registration.outcomeCandidates
              (profile.currentAfterAdmissibility.read
                (profile.outcomeOutput exact.output).stage.previous)).values
          exact scheduled
        cases branch :
            (profile.outcomeOutput exact.output).stage.added.added with
        | yesBranch _ =>
            have selected :
                (profile.outcomeOutput exact.output).terminal = .c1 := by
              simp [CT1.ExecutionResult.terminal, CT1.terminalOfRoute, branch]
            exact CT1.Terminal.noConfusion
              (selected.symm.trans outcomeTerminal)
        | noBranch avoids =>
            exact (CT1.AvoidingState.noRealization avoids
              (Sum.inr candidate) ctScheduled) realizes
  · intro previous exact admissibilityTerminal outcomeTerminal
    have outcome := (profile.admissibilityOutput exact.output).outcome
    rw [admissibilityTerminal] at outcome
    cases outcome with
    | firstFailure failure =>
        have forcedAtOutcome :
            ∃ candidate :
                registration.ExceptionalCandidate
                  (profile.currentAfterAdmissibility.read
                    (profile.outcomeOutput exact.output).stage.previous),
              Sum.inr candidate ∈
                  (registration.outcomeCandidates
                    (profile.currentAfterAdmissibility.read
                      (profile.outcomeOutput exact.output).stage.previous)).values ∧
                registration.RealizesException
                  (profile.currentAfterAdmissibility.read
                    (profile.outcomeOutput exact.output).stage.previous)
                  candidate := by
          have admissibilityResidual :
              profile.currentAfterResponse.read
                  (profile.admissibilityOutput exact.output).stage.previous =
                profile.current.read previous :=
            exact.admissibilityResidual
          have outcomeResidual :
              profile.currentAfterAdmissibility.read (profile.outcomeOutput exact.output).stage.previous =
                profile.current.read previous :=
            exact.outcomeResidual
          exact admissibilityResidual.trans outcomeResidual.symm ▸
            registration.admissibilityFailureScheduled
              (profile.currentAfterResponse.read
                (profile.admissibilityOutput exact.output).stage.previous)
              failure.hit.value failure.hit.member failure.hit.holds
        obtain ⟨candidate, scheduled, realizes⟩ := forcedAtOutcome
        have ctScheduled :
            Sum.inr candidate ∈
              (profile.outcomeCapability.scheduleAt
                (profile.outcomeOutput exact.output).stage.previous).values := by
          change Sum.inr candidate ∈
            (registration.outcomeCandidates
              (profile.currentAfterAdmissibility.read
                (profile.outcomeOutput exact.output).stage.previous)).values
          exact scheduled
        cases branch :
            (profile.outcomeOutput exact.output).stage.added.added with
        | yesBranch _ =>
            have selected :
                (profile.outcomeOutput exact.output).terminal = .c1 := by
              simp [CT1.ExecutionResult.terminal, CT1.terminalOfRoute, branch]
            exact CT1.Terminal.noConfusion
              (selected.symm.trans outcomeTerminal)
        | noBranch avoids =>
            exact (CT1.AvoidingState.noRealization avoids
              (Sum.inr candidate) ctScheduled) realizes
  · intro previous exact outcomeTerminal supportTerminal
    have outcome := (profile.supportOutput exact.output).outcome
    rw [supportTerminal] at outcome
    cases outcome with
    | deficit deficit =>
        have siteScheduled :
            deficit.value ∈
              (registration.supportFamily
                (profile.currentAfterOutcome.read
                  (profile.supportOutput exact.output).stage.previous)).indices.values := by
          change deficit.value ∈
            (profile.supportCapability.sitesAt
              (profile.supportOutput exact.output).stage.previous).values
          exact deficit.scheduled
        have active :
            registration.SupportActive
              (profile.currentAfterOutcome.read
                (profile.supportOutput exact.output).stage.previous)
              deficit.value := by
          change profile.supportSpec.Active
            (profile.supportOutput exact.output).stage.previous deficit.value
          exact deficit.active
        have noSupport :
            ∀ index : Fin
                ((registration.supportFamily
                  (profile.currentAfterOutcome.read
                    (profile.supportOutput exact.output).stage.previous)).fibres
                      deficit.value).card,
              ¬ registration.SupportRelation
                (profile.currentAfterOutcome.read
                  (profile.supportOutput exact.output).stage.previous)
                deficit.value
                (((registration.supportFamily
                  (profile.currentAfterOutcome.read
                    (profile.supportOutput exact.output).stage.previous)).fibres
                      deficit.value).get index) := by
          change CT5.NoSupportingWitness profile.supportCapability
            (profile.supportOutput exact.output).stage.previous deficit.value
          exact deficit.noSupportingWitness
        have forcedAtOutcome :
            ∃ candidate :
                registration.ExceptionalCandidate
                  (profile.currentAfterAdmissibility.read
                    (profile.outcomeOutput exact.output).stage.previous),
              Sum.inr candidate ∈
                  (registration.outcomeCandidates
                    (profile.currentAfterAdmissibility.read
                      (profile.outcomeOutput exact.output).stage.previous)).values ∧
                registration.RealizesException
                  (profile.currentAfterAdmissibility.read
                    (profile.outcomeOutput exact.output).stage.previous)
                  candidate := by
          have supportResidual :
              profile.currentAfterOutcome.read (profile.supportOutput exact.output).stage.previous =
                profile.current.read previous :=
            exact.supportResidual
          have outcomeResidual :
              profile.currentAfterAdmissibility.read (profile.outcomeOutput exact.output).stage.previous =
                profile.current.read previous :=
            exact.outcomeResidual
          exact supportResidual.trans outcomeResidual.symm ▸
            registration.supportDeficitScheduled
              (profile.currentAfterOutcome.read
                (profile.supportOutput exact.output).stage.previous)
              deficit.value siteScheduled active noSupport
        obtain ⟨candidate, scheduled, realizes⟩ := forcedAtOutcome
        have ctScheduled :
            Sum.inr candidate ∈
              (profile.outcomeCapability.scheduleAt
                (profile.outcomeOutput exact.output).stage.previous).values := by
          change Sum.inr candidate ∈
            (registration.outcomeCandidates
              (profile.currentAfterAdmissibility.read
                (profile.outcomeOutput exact.output).stage.previous)).values
          exact scheduled
        cases branch :
            (profile.outcomeOutput exact.output).stage.added.added with
        | yesBranch _ =>
            have selected :
                (profile.outcomeOutput exact.output).terminal = .c1 := by
              simp [CT1.ExecutionResult.terminal, CT1.terminalOfRoute, branch]
            exact CT1.Terminal.noConfusion
              (selected.symm.trans outcomeTerminal)
        | noBranch avoids =>
            exact (CT1.AvoidingState.noRealization avoids
              (Sum.inr candidate) ctScheduled) realizes
  · intro previous exact outcomeTerminal supportTerminal
    have outcome := (profile.supportOutput exact.output).outcome
    rw [supportTerminal] at outcome
    cases outcome with
    | c4 certificate =>
        have capacityFailure :
            ¬ registration.supportRequired
                (profile.currentAfterOutcome.read
                  (profile.supportOutput exact.output).stage.previous) ≤
              registration.supportCapacity
                (profile.currentAfterOutcome.read
                  (profile.supportOutput exact.output).stage.previous) := by
          change ¬ profile.supportSpec.required
              (profile.supportOutput exact.output).stage.previous ≤
            profile.supportSpec.capacity
              (profile.supportOutput exact.output).stage.previous
          exact certificate.capacityFailure
        have forcedAtOutcome :
            ∃ candidate :
                registration.ExceptionalCandidate
                  (profile.currentAfterAdmissibility.read
                    (profile.outcomeOutput exact.output).stage.previous),
              Sum.inr candidate ∈
                  (registration.outcomeCandidates
                    (profile.currentAfterAdmissibility.read
                      (profile.outcomeOutput exact.output).stage.previous)).values ∧
                registration.RealizesException
                  (profile.currentAfterAdmissibility.read
                    (profile.outcomeOutput exact.output).stage.previous)
                  candidate := by
          have supportResidual :
              profile.currentAfterOutcome.read (profile.supportOutput exact.output).stage.previous =
                profile.current.read previous :=
            exact.supportResidual
          have outcomeResidual :
              profile.currentAfterAdmissibility.read (profile.outcomeOutput exact.output).stage.previous =
                profile.current.read previous :=
            exact.outcomeResidual
          exact supportResidual.trans outcomeResidual.symm ▸
            registration.supportCapacityFailureScheduled
              (profile.currentAfterOutcome.read
                (profile.supportOutput exact.output).stage.previous)
              capacityFailure
        obtain ⟨candidate, scheduled, realizes⟩ := forcedAtOutcome
        have ctScheduled :
            Sum.inr candidate ∈
              (profile.outcomeCapability.scheduleAt
                (profile.outcomeOutput exact.output).stage.previous).values := by
          change Sum.inr candidate ∈
            (registration.outcomeCandidates
              (profile.currentAfterAdmissibility.read
                (profile.outcomeOutput exact.output).stage.previous)).values
          exact scheduled
        cases branch :
            (profile.outcomeOutput exact.output).stage.added.added with
        | yesBranch _ =>
            have selected :
                (profile.outcomeOutput exact.output).terminal = .c1 := by
              simp [CT1.ExecutionResult.terminal, CT1.terminalOfRoute, branch]
            exact CT1.Terminal.noConfusion
              (selected.symm.trans outcomeTerminal)
        | noBranch avoids =>
            exact (CT1.AvoidingState.noRealization avoids
              (Sum.inr candidate) ctScheduled) realizes
  · intro previous exact boundedTerminal
    have outcome := (profile.boundedOutput exact.output).outcome
    rw [boundedTerminal] at outcome
    cases outcome with
    | unboundedMember _ residual =>
        obtain ⟨capacity, capacityEq⟩ :=
          registration.boundedCapacityTotal
            (profile.currentAfterSupport.read
              (profile.boundedOutput exact.output).stage.previous)
            residual.value residual.member
        have missing := residual.holds
        change registration.boundedCapacity
            (profile.currentAfterSupport.read
              (profile.boundedOutput exact.output).stage.previous)
            residual.value = none at missing
        rw [capacityEq] at missing
        cases missing
  · intro previous exact boundedTerminal
    have outcome := (profile.boundedOutput exact.output).outcome
    rw [boundedTerminal] at outcome
    cases outcome with
    | missingLabel _ _ residual =>
        obtain ⟨label, labelEq⟩ :=
          registration.boundedLabelTotal
            (profile.currentAfterSupport.read
              (profile.boundedOutput exact.output).stage.previous)
            residual.value residual.member
        have missing := residual.holds
        change registration.boundedLabel
            (profile.currentAfterSupport.read
              (profile.boundedOutput exact.output).stage.previous)
            residual.value = none at missing
        rw [labelEq] at missing
        cases missing

end Profile

end Hypostructure.Core.Strategy.HomogeneousBottleneck
