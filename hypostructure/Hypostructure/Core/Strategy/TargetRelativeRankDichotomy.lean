import Hypostructure.CTAdapters
import Hypostructure.Core.Residual.Stage
import Hypostructure.Core.Strategy.LocalSupplyLowerBound
import Hypostructure.Core.Strategy.SupportComplementNormalization
import Hypostructure.Core.Strategy.TargetRelativeRankDichotomySemantics

/-!
# Target-relative rank dichotomy

This reusable Strategy is exactly the dependent composition

```text
CT10 → CT15 → CT16
```

CT10 classifies the predecessor-owned observation table. CT15 consumes the
literal CT10 ledger extension and computes target-relative rank. CT16 consumes
the literal CT10–CT15 ledger extension and checks the resulting whole-support
code. All inherited data are typed `Core.Residual.Query` values; every
intermediate result is recovered with `Query.latest`; and all ledger writes
are owned by `CTExecution.compose`.
-/

namespace Hypostructure.Core.Strategy.TargetRelativeRankDichotomy

open Hypostructure
open Hypostructure.Core.Residual

universe uPrevious uResidual uResponse uSupply uDatum uClass uPromotion
  uCoordinate uCode uAmbient uPiece

/-- Primitive finite-response semantics and the exact predecessor-owned
observation queries consumed by CT10. No execution result, terminal, route,
or classifier output is accepted. -/
structure ClassificationProfile
    (Previous : Type uPrevious) (Residual : Type uResidual)
    [HasResidual Previous Residual] where
  Response : Previous → Type uResponse
  exactResponsePresentation : Query Previous Response
  Datum : Previous → Type uDatum
  Class : Previous → Type uClass
  Promotion : Previous → Type uPromotion
  observationData : Query Previous fun previous =>
    Core.Finite.Enumeration (Datum previous)
  completeClasses : Query Previous fun previous =>
    Core.Finite.CompleteEnumeration (Class previous)
  classOf : (previous : Previous) → Response previous →
    Datum previous → Class previous
  Direct : (previous : Previous) → Response previous →
    Class previous → Prop
  promote : (previous : Previous) → Response previous →
    Class previous → Promotion previous
  directDecidable : (previous : Previous) →
    (response : Response previous) → (cls : Class previous) →
      Decidable (Direct previous response cls)

namespace ClassificationProfile

variable [HasResidual Previous Residual]
variable (profile :
  ClassificationProfile.{
    uPrevious, uResidual, uResponse, uDatum, uClass, uPromotion}
    Previous Residual)

/-- The stable residual read remains available independently of ledger depth. -/
def residualQuery :
    Query Previous fun _ => Residual :=
  Query.residual

/-- The two finite schedules are read from the same literal predecessor. -/
def observationsAndClasses :
    Query Previous fun previous =>
      PProd
        (Core.Finite.Enumeration (profile.Datum previous))
        (Core.Finite.CompleteEnumeration (profile.Class previous)) :=
  profile.observationData.and profile.completeClasses

/-- Exact observation schedule projected from the combined predecessor read. -/
def observations :
    Query Previous fun previous =>
      Core.Finite.Enumeration (profile.Datum previous) :=
  profile.observationsAndClasses.map fun _ inputs => inputs.fst

/-- Exact complete class schedule projected from the same predecessor read. -/
def classes :
    Query Previous fun previous =>
      Core.Finite.CompleteEnumeration (profile.Class previous) :=
  profile.observationsAndClasses.dependentMap fun _ inputs => inputs.snd

/-- CT10 semantics read only the exact response presentation retained by the
predecessor ledger. -/
def classificationSpec : CT10.Spec Previous where
  Datum := profile.Datum
  Class := profile.Class
  Promotion := profile.Promotion
  classOf := fun previous datum =>
    profile.classOf previous
      (profile.exactResponsePresentation.read previous) datum
  Direct := fun previous cls =>
    profile.Direct previous
      (profile.exactResponsePresentation.read previous) cls
  promote := fun previous cls =>
    profile.promote previous
      (profile.exactResponsePresentation.read previous) cls

/-- Canonical CT10 capability. Its polynomial envelope is derived uniformly
from CT10's own exact local check schedule. -/
def classificationCapability :
    CT10.Capability profile.classificationSpec where
  data := profile.observations
  classes := profile.classes
  directDecidable := fun previous cls =>
    profile.directDecidable previous
      (profile.exactResponsePresentation.read previous) cls
  inputSize := fun previous =>
    CT10.localCheckBound profile.classificationSpec
      profile.observations profile.classes previous
  workCoefficient := Fintype.card Unit
  workDegree := Fintype.card Unit
  workBound := by
    intro previous
    simp only [Fintype.card_unit, Nat.pow_one, Nat.one_mul]
    exact Nat.le_succ _

/-- The first atomic execution is the canonical CT10 adapter. -/
noncomputable def classificationExecution :
    Core.Strategy.CTExecution Previous :=
  CTAdapters.ct10 profile.classificationCapability

/-- Literal accumulated-ledger stage after CT10. -/
abbrev AfterClassification :=
  Ledger.Extension Previous profile.classificationExecution.Output

/-- Exact CT10 result stored in the newest ledger entry. -/
def classificationResult :
    Query profile.AfterClassification fun stage =>
      profile.classificationExecution.Output stage.previous :=
  Query.latest

end ClassificationProfile

/-- Primitive target-relative rank semantics over CT10's literal output.
Local supply, coordinates, and responses remain exact inherited queries. -/
structure RankProfile
    {Previous : Type uPrevious} {Residual : Type uResidual}
    [HasResidual Previous Residual]
    (classification :
      ClassificationProfile.{
        uPrevious, uResidual, uResponse, uDatum, uClass, uPromotion}
        Previous Residual) where
  Supply : Previous → Type uSupply
  localSupply : Query Previous Supply
  Coordinate : Previous → Type uCoordinate
  coordinateSchedule : Query Previous fun previous =>
    Core.Finite.Enumeration (Coordinate previous)
  TargetDependent :
    (previous : Previous) →
    classification.Response previous →
    classification.classificationExecution.Output previous →
    Coordinate previous → Prop
  charge :
    (previous : Previous) →
    classification.Response previous →
    classification.classificationExecution.Output previous →
    Coordinate previous → Nat
  capacity :
    (previous : Previous) →
    Supply previous →
    classification.Response previous →
    classification.classificationExecution.Output previous → Nat
  targetDependentDecidable :
    (previous : Previous) →
    (response : classification.Response previous) →
    (classified : classification.classificationExecution.Output previous) →
    (coordinate : Coordinate previous) →
      Decidable
        (TargetDependent previous response classified coordinate)

namespace RankProfile

variable [HasResidual Previous Residual]
variable
  {classification :
    ClassificationProfile.{
      uPrevious, uResidual, uResponse, uDatum, uClass, uPromotion}
      Previous Residual}
variable (profile :
  RankProfile.{uPrevious, uResidual, uResponse, uSupply, uDatum, uClass,
    uPromotion, uCoordinate} classification)

/-- Exact local-supply and response presentations on the common predecessor. -/
def supplyAndResponses :
    Query Previous fun previous =>
      PProd (profile.Supply previous)
        (classification.Response previous) :=
  profile.localSupply.and classification.exactResponsePresentation

/-- CT10's exact newest ledger entry. -/
def classificationResult :
    Query classification.AfterClassification fun stage =>
      classification.classificationExecution.Output stage.previous :=
  Query.latest

/-- Exact coordinate schedule transported through CT10 and paired with CT10's
literal result. -/
def coordinateInputs :
    Query classification.AfterClassification fun stage =>
      PProd
        (Core.Finite.Enumeration (profile.Coordinate stage.previous))
        (classification.classificationExecution.Output stage.previous) :=
  profile.coordinateSchedule.preserve.and classification.classificationResult

/-- Exact coordinate schedule used by CT15. The `dependentMap` projects the
schedule already present in `coordinateInputs`; it performs no enumeration. -/
def rankCoordinates :
    Query classification.AfterClassification fun stage =>
      Core.Finite.Enumeration (profile.Coordinate stage.previous) :=
  profile.coordinateInputs.dependentMap fun _ inputs => inputs.fst

/-- Exact supply/response context transported through CT10. -/
def rankContext :
    Query classification.AfterClassification fun stage =>
      PProd
        (PProd (profile.Supply stage.previous)
          (classification.Response stage.previous))
        (classification.classificationExecution.Output stage.previous) :=
  profile.supplyAndResponses.preserve.and classification.classificationResult

/-- CT15 semantics are indexed by the literal CT10 extension and read only the
preserved response/supply context plus CT10's newest entry. -/
def rankSpec : CT15.Spec classification.AfterClassification where
  Coordinate := fun stage => profile.Coordinate stage.previous
  TargetDependent := fun stage coordinate =>
    let context := profile.rankContext.read stage
    profile.TargetDependent stage.previous context.fst.snd context.snd
      coordinate
  charge := fun stage coordinate =>
    let context := profile.rankContext.read stage
    profile.charge stage.previous context.fst.snd context.snd coordinate
  capacity := fun stage =>
    let context := profile.rankContext.read stage
    profile.capacity stage.previous context.fst.fst context.fst.snd
      context.snd

/-- Canonical CT15 capability derived from the exact coordinate query and
CT15's own local check schedule. -/
def rankCapability : CT15.Capability profile.rankSpec where
  coordinates := profile.rankCoordinates
  targetDependentDecidable := fun stage coordinate =>
    let context := profile.rankContext.read stage
    profile.targetDependentDecidable stage.previous context.fst.snd
      context.snd coordinate
  inputSize := fun stage =>
    CT15.localCheckBound (profile.rankCoordinates.read stage)
  workCoefficient := Fintype.card Unit
  workDegree := Fintype.card Unit
  workBound := by
    intro stage
    simp only [Fintype.card_unit, Nat.pow_one, Nat.one_mul]
    exact Nat.le_succ _

/-- The second atomic execution is the canonical CT15 adapter on CT10's
literal extension. -/
noncomputable def rankExecution :
    Core.Strategy.CTExecution classification.AfterClassification :=
  CTAdapters.ct15 profile.rankCapability

/-- Exact CT10 → CT15 dependent composition. -/
noncomputable def throughRank :
    Core.Strategy.CTExecution Previous :=
  classification.classificationExecution.compose profile.rankExecution

/-- Literal accumulated-ledger stage after the CT10 → CT15 composition. -/
abbrev AfterRank :=
  Ledger.Extension Previous profile.throughRank.Output

/-- Exact composed CT10–CT15 result stored in the newest ledger entry. -/
def throughRankResult :
    Query profile.AfterRank fun stage =>
      profile.throughRank.Output stage.previous :=
  Query.latest

/-- CT10 result projected from the exact composed output. -/
def ct10ResultAfterRank :
    Query profile.AfterRank fun stage =>
      classification.classificationExecution.Output stage.previous :=
  profile.throughRankResult.map fun _ output => output.fst

/-- CT15 result projected dependently from the exact composed output. Its
dependent predecessor index is inferred from that exact output, rather than
being reconstructed by Strategy code. -/
def ct15ResultAfterRank :=
  profile.throughRankResult.dependentMap fun _ output => output.snd

end RankProfile

/-- Primitive whole-support and closed-code semantics over the literal
CT10–CT15 output. The two counted operations are the existing CT16 capability
inputs; neither can supply a terminal or an execution outcome. -/
structure CodeProfile
    {Previous : Type uPrevious} {Residual : Type uResidual}
    [HasResidual Previous Residual]
    {classification :
      ClassificationProfile.{
        uPrevious, uResidual, uResponse, uDatum, uClass, uPromotion}
        Previous Residual}
    (rank :
      RankProfile.{uPrevious, uResidual, uResponse, uSupply, uDatum, uClass,
        uPromotion, uCoordinate} classification) where
  InSupport :
    (stage : rank.AfterRank) → rank.Coordinate stage.previous → Prop
  ClosedCode : rank.AfterRank → Type uCode
  closedCode : (stage : rank.AfterRank) → ClosedCode stage
  targetCode : (stage : rank.AfterRank) → ClosedCode stage
  inSupportDecidable :
    (stage : rank.AfterRank) → (coordinate : rank.Coordinate stage.previous) →
      Decidable (InSupport stage coordinate)
  computeCode :
    (stage : rank.AfterRank) → Core.Counted (ClosedCode stage)
  computeCodeBudget : Core.PolynomialCheckBudget rank.AfterRank
  computeCodeCorrect :
    ∀ stage, (computeCode stage).value = closedCode stage
  computeCodeChecks :
    ∀ stage, (computeCode stage).checks = computeCodeBudget.checks stage
  decideCodeEquality :
    (stage : rank.AfterRank) → (code : ClosedCode stage) →
      Core.Counted (Decidable (code = targetCode stage))
  equalityBudget : Core.PolynomialCheckBudget rank.AfterRank
  equalityChecks :
    ∀ stage code,
      (decideCodeEquality stage code).checks = equalityBudget.checks stage

namespace CodeProfile

variable [HasResidual Previous Residual]
variable
  {classification :
    ClassificationProfile.{
      uPrevious, uResidual, uResponse, uDatum, uClass, uPromotion}
      Previous Residual}
variable
  {rank :
    RankProfile.{uPrevious, uResidual, uResponse, uSupply, uDatum, uClass,
      uPromotion, uCoordinate} classification}
variable (profile :
  CodeProfile.{uPrevious, uResidual, uResponse, uSupply, uDatum, uClass,
    uPromotion, uCoordinate, uCode} rank)

/-- Exact CT10 and CT15 projections from the one composed ledger entry. -/
def codeInputs :=
  rank.ct10ResultAfterRank.and rank.ct15ResultAfterRank

/-- Exact CT10/CT15 output paired with the inherited coordinate schedule. -/
def codeInputsAndCoordinates :=
  (codeInputs (rank := rank)).and rank.coordinateSchedule.preserve

/-- Exact inherited local-supply and response values at the CT16 predecessor. -/
def supplyAndResponsesAfterRank :
    Query rank.AfterRank fun stage =>
      PProd (rank.Supply stage.previous)
        (classification.Response stage.previous) :=
  rank.supplyAndResponses.preserve

/-- Complete CT16 input context assembled only with typed query composition. -/
def codeContext :=
  (codeInputsAndCoordinates (rank := rank)).and
    (supplyAndResponsesAfterRank (rank := rank))

/-- CT16 receives the exact predecessor-owned coordinate schedule. -/
def codeCoordinates :
    Query rank.AfterRank fun stage =>
      Core.Finite.Enumeration (rank.Coordinate stage.previous) :=
  (codeContext (rank := rank)).dependentMap fun _ context => context.fst.snd

/-- Whole-support semantics on the literal CT10–CT15 predecessor. -/
def codeSpec : CT16.Spec rank.AfterRank where
  Coordinate := fun stage => rank.Coordinate stage.previous
  InSupport := profile.InSupport
  ClosedCode := profile.ClosedCode
  closedCode := profile.closedCode
  targetCode := profile.targetCode

/-- Counted implementation of the registered closed-code denotation. -/
def codeComputation :
    CT16.ClosedCodeComputation profile.codeSpec where
  run := profile.computeCode
  correct := profile.computeCodeCorrect
  budget := profile.computeCodeBudget
  checks_eq := profile.computeCodeChecks

/-- Counted equality decision against the registered target code. -/
def codeEqualityDecision :
    CT16.CodeEqualityDecision profile.codeSpec where
  run := profile.decideCodeEquality
  budget := profile.equalityBudget
  checks_eq := profile.equalityChecks

/-- Canonical CT16 capability over the exact composed predecessor queries. -/
def codeCapability : CT16.Capability profile.codeSpec where
  coordinates := codeCoordinates (rank := rank)
  inSupportDecidable := profile.inSupportDecidable
  codeComputation := profile.codeComputation
  equalityDecision := profile.codeEqualityDecision

/-- The third atomic execution is the canonical CT16 adapter on the exact
CT10–CT15 output. -/
noncomputable def codeExecution :
    Core.Strategy.CTExecution rank.AfterRank :=
  CTAdapters.ct16 profile.codeCapability

/-- The complete reusable Strategy. Core owns both dependent ledger
extensions and retains all three exact CT outputs. -/
noncomputable def execution :
    Core.Strategy.CTExecution Previous :=
  rank.throughRank.compose profile.codeExecution

/-- Literal accumulated-ledger stage after CT10 → CT15 → CT16. -/
abbrev AfterDichotomy :=
  Ledger.Extension Previous profile.execution.Output

/-- Exact complete Strategy output stored as the newest ledger entry. -/
def completeResult :
    Query profile.AfterDichotomy fun stage =>
      profile.execution.Output stage.previous :=
  Query.latest

/-- Exact CT10 result retained by the complete composition. -/
def ct10Result :
    Query profile.AfterDichotomy fun stage =>
      classification.classificationExecution.Output stage.previous :=
  profile.completeResult.map fun _ output => output.fst.fst

/-- Exact CT15 result retained by the complete composition. Its dependent
predecessor index is inherited from the complete output. -/
def ct15Result :=
  profile.completeResult.dependentMap fun _ output => output.fst.snd

/-- Exact CT16 result retained by the complete composition. Its dependent
predecessor index is inherited from the complete output. -/
def ct16Result :=
  profile.completeResult.dependentMap fun _ output => output.snd

/-- Literal CT10 → CT15 → CT16 output with every adapter predecessor
identity retained.  This is the provenance-bearing output of the canonical
composition, not a reconstructed response or rank summary. -/
structure ExactOutput (previous : Previous) where
  output : profile.execution.Output previous
  classificationPrevious :
    output.fst.fst.stage.previous = previous
  rankInput :
    classification.classificationResult.read
      output.fst.snd.stage.previous = output.fst.fst
  /-- CT15 ran on the literal CT10 extension of *this* predecessor.  The
  composition builds its middle stage as `Ledger.extend previous _`, so this
  is the definitional identity; recording it keeps the CT15 capacity, which
  reads the inherited local supply at that stage's predecessor, comparable
  with the local supply at `previous`. -/
  rankPrevious :
    output.fst.snd.stage.previous.previous = previous
  codeInput :
    rank.throughRankResult.read output.snd.stage.previous = output.fst

/-- Exact rank-side alternatives retained from CT15 and CT16.  The complete
composed output is stored in every constructor, so no terminal evidence or
predecessor fact is copied into a detached summary. -/
inductive RankDropResidual (previous : Previous) where
  | dependent
      (exact : profile.ExactOutput previous)
      (selected : exact.output.fst.snd.terminal = .rankDrop)
  | capacity
      (exact : profile.ExactOutput previous)
      (selected : exact.output.fst.snd.terminal = .c4)
  | properSupport
      (exact : profile.ExactOutput previous)
      (rankSelected : exact.output.fst.snd.terminal = .fullRankLedger)
      (codeSelected : exact.output.snd.terminal = .properSupport)
  | mismatch
      (exact : profile.ExactOutput previous)
      (rankSelected : exact.output.fst.snd.terminal = .fullRankLedger)
      (codeSelected : exact.output.snd.terminal = .mismatch)

/-- The exact coordinate selected by CT15 on the dependence branch.  This is
a projection of the private CT15 hit stored in `ExactOutput`; downstream
strategies do not repeat the search or walk predecessor stages. -/
def dependentCoordinate
    {previous : Previous}
    (exact : profile.ExactOutput previous)
    (selected : exact.output.fst.snd.terminal = .rankDrop) :
    rank.rankSpec.Coordinate exact.output.fst.snd.stage.previous :=
  (exact.output.fst.snd.stage.added.rankDropOutput selected).certificate.value

/-- The selected coordinate is a member of the exact residual-owned schedule
consumed by CT15. -/
theorem dependentCoordinate_mem
    {previous : Previous}
    (exact : profile.ExactOutput previous)
    (selected : exact.output.fst.snd.terminal = .rankDrop) :
    dependentCoordinate profile exact selected ∈
      (rank.rankCapability.coordinatesAt
        exact.output.fst.snd.stage.previous).values := by
  exact (exact.output.fst.snd.stage.added.rankDropOutput selected).certificate.member

/-- The selected coordinate satisfies the literal target-dependence predicate
that CT15 inspected. -/
theorem dependentCoordinate_sound
    {previous : Previous}
    (exact : profile.ExactOutput previous)
    (selected : exact.output.fst.snd.terminal = .rankDrop) :
    rank.rankSpec.TargetDependent exact.output.fst.snd.stage.previous
      (dependentCoordinate profile exact selected) := by
  exact (exact.output.fst.snd.stage.added.rankDropOutput selected).certificate.sound

/-- Every coordinate in CT15's retained prefix is certified independent of
the target.  This is the exact determination-basis prefix used by later
localization, not a reconstructed list. -/
theorem dependentCoordinate_prefix
    {previous : Previous}
    (exact : profile.ExactOutput previous)
    (selected : exact.output.fst.snd.terminal = .rankDrop) :
    ∀ coordinate,
      coordinate ∈ (rank.rankCapability.coordinatesAt
        exact.output.fst.snd.stage.previous).values.take
        (exact.output.fst.snd.stage.added.rankDropOutput selected).certificate.index.1 →
      ¬ rank.rankSpec.TargetDependent exact.output.fst.snd.stage.previous
        coordinate := by
  exact (exact.output.fst.snd.stage.added.rankDropOutput selected).certificate.first

/-- Close the literal CT15 dependence terminal from a pointwise exclusion of
the inspected predicate.  The selected coordinate and its proof are read
from CT15's retained hit; consumers supply only the semantic exclusion and
never repeat the finite search. -/
theorem dependent_impossible
    {previous : Previous}
    (exact : profile.ExactOutput previous)
    (selected : exact.output.fst.snd.terminal = .rankDrop)
    (excluded : ∀ coordinate,
      ¬ rank.rankSpec.TargetDependent exact.output.fst.snd.stage.previous
        coordinate) : False :=
  excluded (dependentCoordinate profile exact selected)
    (dependentCoordinate_sound profile exact selected)

/-- Close the literal CT16 proper-support terminal whenever the registered
support predicate recognizes the very schedule CT16 scans.  Both the missing
coordinate and its two laws are read from CT16's own retained hit; the
consumer supplies only the schedule/support agreement. -/
theorem properSupport_impossible
    {previous : Previous}
    (exact : profile.ExactOutput previous)
    (codeSelected : exact.output.snd.terminal = .properSupport)
    (whole : ∀ (stage : rank.AfterRank)
      (coordinate : rank.Coordinate stage.previous),
        coordinate ∈ ((codeCoordinates (rank := rank)).read stage).values →
          profile.InSupport stage coordinate) : False :=
  let missing :=
    (exact.output.snd.stage.added.properSupportResidual codeSelected).residual
  missing.absent (whole _ _ missing.member)

/-- Close the literal CT16 closed-code mismatch terminal from the registered
code semantics alone.  CT16's retained hit already carries the computed code,
its equality with `closedCode`, and its disagreement with `targetCode`; the
consumer supplies only the pointwise agreement of the two registered codes. -/
theorem mismatch_impossible
    {previous : Previous}
    (exact : profile.ExactOutput previous)
    (codeSelected : exact.output.snd.terminal = .mismatch)
    (agree : ∀ stage : rank.AfterRank,
      profile.closedCode stage = profile.targetCode stage) : False :=
  let mismatch :=
    (exact.output.snd.stage.added.closedTypeMismatchResidual
      codeSelected).residual
  mismatch.notEqual (mismatch.state.exact.trans (agree _))

/-- Close the literal CT15 capacity-overload terminal from the registered
charge budget alone.

CT15's own `.c4` hit already carries the generated full-rank charge ledger,
its defining equality with the canonical `ledgerTotal` of the exact coordinate
schedule, and the strict overload `capacity < total`.  This is the very ledger
whose *opposite* fit is what the full-rank terminal records and what
`fullRankValue_le_capacity` consumes there, so nothing about the schedule, the
charge, or the capacity is recomputed here: the consumer supplies only the
budget statement that the registered charge of the exact schedule fits the
registered capacity, and the two strict inequalities cancel. -/
theorem capacity_impossible
    {previous : Previous}
    (exact : profile.ExactOutput previous)
    (selected : exact.output.fst.snd.terminal = .c4)
    (fits : ∀ stage : classification.AfterClassification,
      ((rank.rankCapability.coordinatesAt stage).values.map
          (rank.rankSpec.charge stage)).sum ≤
        rank.rankSpec.capacity stage) : False := by
  set stage := exact.output.fst.snd.stage.previous with stageDef
  have output := exact.output.fst.snd.stage.added.c4Output selected
  have overload : rank.rankSpec.capacity stage < output.ledger.total :=
    output.certificate
  have total :
      output.ledger.total = CT15.ledgerTotal rank.rankCapability stage :=
    output.ledger.total_exact
  have chargeSum :
      ((rank.rankCapability.coordinatesAt stage).values.map
          (rank.rankSpec.charge stage)).sum =
        CT15.ledgerTotal rank.rankCapability stage := by
    simp [CT15.ledgerTotal, CT15.ledgerEntries, List.map_map,
      Function.comp_def]
  have bound := fits stage
  omega

/-- Exact full-rank alternative.  Both terminal equalities refer to the
literal CT15 and CT16 results retained in the one composed output. -/
structure FullRankResidual (previous : Previous) where
  exact : profile.ExactOutput previous
  rankSelected : exact.output.fst.snd.terminal = .fullRankLedger
  codeSelected : exact.output.snd.terminal = .exactCode

/-- The exact target-relative rank retained by one full-rank alternative.
This is the value CT15 stored in its own full-rank terminal, projected; no
schedule is re-enumerated and no rank is recomputed. -/
def fullRankValue {previous : Previous}
    (fullRank : profile.FullRankResidual previous) : Nat :=
  (fullRank.exact.output.fst.snd.stage.added.fullRankLedgerOutput
    fullRank.rankSelected).rank.value

/-- The retained rank is dominated by the capacity CT15 fitted its generated
charge ledger under.

Both halves are already in the terminal CT15 produced: the full-rank state
equates the rank with the *cardinality* of the coordinate schedule, and the
full-rank residual fits the *charge total* of that same schedule under the
registered capacity.  A per-coordinate charge floor of one turns the first
quantity into a lower bound for the second, entry by entry, so the two
existing certificates compose without any further observation. -/
theorem fullRankValue_le_capacity {previous : Previous}
    (fullRank : profile.FullRankResidual previous)
    (chargePos : ∀ (stage : classification.AfterClassification)
        (coordinate : rank.rankSpec.Coordinate stage),
      0 < rank.rankSpec.charge stage coordinate) :
    profile.fullRankValue fullRank ≤
      rank.rankSpec.capacity fullRank.exact.output.fst.snd.stage.previous := by
  set stage := fullRank.exact.output.fst.snd.stage.previous with stageDef
  set output := fullRank.exact.output.fst.snd.stage.added.fullRankLedgerOutput
    fullRank.rankSelected with outputDef
  have schedule :
      ((rank.rankCapability.coordinatesAt stage).values.map
          (rank.rankSpec.charge stage)).length ≤
        ((rank.rankCapability.coordinatesAt stage).values.map
          (rank.rankSpec.charge stage)).sum := by
    refine List.length_le_sum_of_one_le _ ?_
    intro value member
    obtain ⟨coordinate, _, rfl⟩ := List.mem_map.1 member
    exact chargePos stage coordinate
  calc profile.fullRankValue fullRank
      = (rank.rankCapability.coordinatesAt stage).values.length := output.full.full
    _ ≤ ((rank.rankCapability.coordinatesAt stage).values.map
          (rank.rankSpec.charge stage)).sum := by
        simpa using schedule
    _ = CT15.ledgerTotal rank.rankCapability stage := by
        simp [CT15.ledgerTotal, CT15.ledgerEntries, List.map_map,
          Function.comp_def]
    _ = output.ledger.total := output.ledger.total_exact.symm
    _ ≤ rank.rankSpec.capacity stage := output.residual

/-- Exhaustive interpretation of the literal composed CT result.  This
function performs no CT execution other than `execution.run`, and it selects
no branch from registration data. -/
noncomputable def route (previous : Previous) :
    Sum (profile.RankDropResidual previous)
      (profile.FullRankResidual previous) :=
  let output := profile.execution.run previous
  let exact : profile.ExactOutput previous :=
    ⟨output, rfl, rfl, rfl, rfl⟩
  match rankTerminal : output.fst.snd.terminal with
  | .rankDrop =>
      .inl (.dependent exact rankTerminal)
  | .c4 =>
      .inl (.capacity exact rankTerminal)
  | .fullRankLedger =>
      match codeTerminal : output.snd.terminal with
      | .properSupport =>
          .inl (.properSupport exact rankTerminal codeTerminal)
      | .exactCode =>
          .inr ⟨exact, rankTerminal, codeTerminal⟩
      | .mismatch =>
          .inl (.mismatch exact rankTerminal codeTerminal)

/-- Standard Core dichotomy over the exact CT10 → CT15 → CT16 execution.
The author-facing DAG, when registered, supplies only the two continuations;
Core owns this classifier and the residual payloads. -/
noncomputable def dichotomy : Core.Strategy.Dichotomy Previous where
  LeftPayload := profile.RankDropResidual
  RightPayload := profile.FullRankResidual
  classify := profile.route

end CodeProfile


/-! ## Complete registration-driven Strategy

The compiler bundles the three phase profiles and builds them from one inert
residual-indexed registration together with the exact local-supply ledger
query published by a completed `LocalSupplyLowerBound`. -/

/-- The three dependent phase profiles of the complete Strategy. -/
structure Profile (Previous : Type uPrevious) (Residual : Type uResidual)
    [HasResidual Previous Residual] where
  SupportAmbient : Previous → Type uAmbient
  normalizedSupport :
    SupportComplementNormalization.ExactLedger.{
      uResidual, uPrevious, uAmbient, uPiece} Previous Residual
      SupportAmbient
  classification :
    ClassificationProfile.{
      uPrevious, uResidual, uResponse, uDatum, uClass, uPromotion}
      Previous Residual
  rank :
    RankProfile.{uPrevious, uResidual, uResponse, uSupply, uDatum, uClass,
      uPromotion, uCoordinate} classification
  code :
    CodeProfile.{uPrevious, uResidual, uResponse, uSupply, uDatum, uClass,
      uPromotion, uCoordinate, uCode} rank

namespace Profile

variable [HasResidual Previous Residual]
variable (profile :
  Profile.{uPrevious, uResidual, uResponse, uSupply, uDatum, uClass,
    uPromotion, uCoordinate, uCode, uAmbient, uPiece} Previous Residual)

/-- Exact CT9 complement inherited by this target-rank execution. -/
def exactComplement := profile.normalizedSupport.complement

/-- Exact CT6 local-piece schedule inherited by this target-rank execution. -/
def exactLocalPieces := profile.normalizedSupport.localPieces

/-- CT6's no-failure theorem on every inherited local piece. -/
def exactLocalPiecesActive := profile.normalizedSupport.active

/-- The complete CT10 → CT15 → CT16 execution owned by Core. -/
noncomputable def execution : Core.Strategy.CTExecution Previous :=
  profile.code.execution

/-- The standard two-sided Core dichotomy exposed to a sealed DAG. -/
noncomputable def dichotomy : Core.Strategy.Dichotomy Previous :=
  profile.code.dichotomy

end Profile

/-- Build the three dependent phase profiles from one inert registration and
the exact local-supply ledger query supplied by the compiler. Every inherited
value is read with `Query.residual` or with the supplied capability query.
CT16 reads the exact CT10 terminal retained in the composed ledger and compares
it with CT10's exhaustive-response terminal. Thus the closed-code test neither
rescans nor reconstructs the response table, and no application-supplied code
or equality result enters this composition. -/
noncomputable def Profile.ofRegistrationAt
    {Previous : Type uPrevious} {Residual : Type uResidual}
    [HasResidual Previous Residual]
    {AmbientItem : Residual → Type uAmbient}
    {Coordinate : Residual → Type uCoordinate}
    (registration :
      Registration.{uResidual, uAmbient, uCoordinate, uPromotion, uClass,
        uDatum, uResponse} Residual AmbientItem Coordinate)
    (current : Query Previous fun _ => Residual)
    (normalizedSupport :
      SupportComplementNormalization.ExactLedger.{
        uResidual, uPrevious, uAmbient, uPiece} Previous Residual
        (fun previous => AmbientItem (current.read previous)))
    (localSupply : Query Previous fun _ =>
      ULift.{uSupply} LocalSupplyLowerBound.Summary) :
    Profile.{uPrevious, uResidual, uResponse, uSupply, uDatum, uClass,
      uPromotion, uCoordinate, uCode, uAmbient, uPiece} Previous Residual :=
  let residual := current
  let classification :
      ClassificationProfile.{
        uPrevious, uResidual, uResponse, uDatum, uClass, uPromotion}
        Previous Residual :=
    { Response := fun previous => registration.Response (current.read previous)
      exactResponsePresentation := residual.dependentMap fun _ residual =>
        registration.response residual
      Datum := fun previous => registration.Datum (current.read previous)
      Class := fun previous => registration.Class (current.read previous)
      Promotion := fun previous => registration.Promotion (current.read previous)
      observationData := residual.dependentMap fun _ residual =>
        registration.observationData residual
      completeClasses := residual.dependentMap fun _ residual =>
        registration.completeClasses residual
      classOf := fun previous => registration.classOf (current.read previous)
      Direct := fun previous => registration.Direct (current.read previous)
      promote := fun previous => registration.promote (current.read previous)
      directDecidable := fun previous =>
        registration.directDecidable (current.read previous) }
  -- The exact CT9-complement coordinate schedule, defined once and read
  -- through the framework query in both places that need it: the profile
  -- publishes it as `coordinateSchedule`, and the rank budget below reads the
  -- same query.  No second copy of the schedule is stored anywhere.
  let coordinateSchedule :
      Query Previous fun previous =>
        Core.Finite.Enumeration (Coordinate (current.read previous)) :=
    normalizedSupport.complement.dependentMap fun previous complement =>
      registration.coordinates (current.read previous) complement
  let rank :
      RankProfile.{uPrevious, uResidual, uResponse, uSupply, uDatum, uClass,
        uPromotion, uCoordinate} classification :=
    { Supply := fun _ => ULift.{uSupply} LocalSupplyLowerBound.Summary
      localSupply := localSupply
      Coordinate := fun previous =>
        Coordinate (current.read previous)
      coordinateSchedule := coordinateSchedule
      TargetDependent := fun previous response _ coordinate =>
        registration.TargetDependent (current.read previous) response coordinate
      charge := fun previous response _ coordinate =>
        registration.charge (current.read previous) response coordinate
      -- Manuscript node [32] compares the target-relative rank against
      -- `W₂(R)`, the count of raw curvature coordinates.  That count is not a
      -- supply observation: it is the exact coordinate schedule the
      -- registration already owns, so the budget is the registered charge of
      -- that same schedule, read back through the query above, plus the
      -- registration's own residual-owned slack.
      --
      -- The preceding local-supply ledger publishes external stubs
      -- (`e(R, W)` plus the ambient defect); that is the *stub* supply of
      -- `lem:stub-positive`, not the curvature-test count, and reading it here
      -- charged the rank budget against an unrelated quantity.  The supply
      -- ledger remains inherited as `localSupply` and stays available to
      -- CT15's context and to every later Strategy; it simply is not this
      -- budget.
      capacity := fun previous _supply response _ =>
        ((coordinateSchedule.read previous).values.map
            (registration.charge (current.read previous) response)).sum +
          registration.capacitySlack (current.read previous) response
      targetDependentDecidable := fun previous response _ coordinate =>
        registration.targetDependentDecidable (current.read previous)
          response coordinate }
  { SupportAmbient := fun previous => AmbientItem (current.read previous)
    normalizedSupport
    classification
    rank
    code :=
      { InSupport := fun stage coordinate =>
          coordinate ∈ (rank.coordinateSchedule.read stage.previous).values
        ClosedCode := fun _ => ULift.{uCode} CT10.Terminal
        closedCode := fun stage =>
          ULift.up ((rank.ct10ResultAfterRank.read stage).terminal)
        targetCode := fun _ => ULift.up CT10.Terminal.exhaustive
        inSupportDecidable := fun stage _coordinate =>
          letI : DecidableEq (Coordinate (current.read stage.previous)) :=
            (rank.coordinateSchedule.read stage.previous).decEq
          inferInstance
        computeCode := fun stage =>
          Core.Counted.pure
            (ULift.up ((rank.ct10ResultAfterRank.read stage).terminal))
        computeCodeBudget := Core.PolynomialCheckBudget.constant (fun _ => 0) 0
        computeCodeCorrect := fun _ => rfl
        computeCodeChecks := fun _ => rfl
        decideCodeEquality := fun _stage code =>
          ⟨inferInstanceAs (Decidable
              (code = ULift.up CT10.Terminal.exhaustive)), 1⟩
        equalityBudget := Core.PolynomialCheckBudget.constant (fun _ => 0) 1
        equalityChecks := fun _ _ => rfl } }

/-- Stable-residual specialization of `ofRegistrationAt`.  This compatibility
entry point contains no additional execution: all CT construction is owned by
the query-native definition above. -/
noncomputable def Profile.ofRegistration
    {Previous : Type uPrevious} {Residual : Type uResidual}
    [HasResidual Previous Residual]
    {AmbientItem : Residual → Type uAmbient}
    {Coordinate : Residual → Type uCoordinate}
    (registration :
      Registration.{uResidual, uAmbient, uCoordinate, uPromotion, uClass,
        uDatum, uResponse} Residual AmbientItem Coordinate)
    (normalizedSupport :
      SupportComplementNormalization.ExactLedger.{
        uResidual, uPrevious, uAmbient, uPiece} Previous Residual
        (fun previous => AmbientItem (residualOf previous)))
    (localSupply : Query Previous fun _ =>
      ULift.{uSupply} LocalSupplyLowerBound.Summary) :
    Profile.{uPrevious, uResidual, uResponse, uSupply, uDatum, uClass,
      uPromotion, uCoordinate, uCode, uAmbient, uPiece} Previous Residual :=
  Profile.ofRegistrationAt registration Query.residual normalizedSupport
    localSupply

/-- The rank a registration-built composition publishes is dominated by the
registered charge of the exact coordinate schedule it consumed.

This is the whole content of the independent-rank ledger entry.  Three facts
compose, and all three are already carried by the objects involved:

* CT15's full-rank terminal equates the rank with the cardinality of its own
  coordinate schedule and fits that schedule's charge total under the
  registered capacity (`CodeProfile.fullRankValue_le_capacity`);
* the registration's `charge_pos` makes the cardinality a lower bound for the
  charge total;
* `ofRegistrationAt` sets that capacity to the charge total of the very same
  schedule, plus the registration's own slack.

Manuscript node [32] is `r_Ω(R) ≤ W₂(R)`, and `W₂(R)` is the count of raw
curvature coordinates -- for a registration charging one unit per coordinate,
exactly the right-hand side below.  The composed output's `rankPrevious`
identity is what lets the last step be read at `previous` rather than at
CT15's own predecessor stage.  No hypothesis beyond the registration's own
laws participates. -/
theorem Profile.ofRegistrationAt_fullRankValue_le_chargeTotal
    {Previous : Type uPrevious} {Residual : Type uResidual}
    [HasResidual Previous Residual]
    {AmbientItem : Residual → Type uAmbient}
    {Coordinate : Residual → Type uCoordinate}
    (registration :
      Registration.{uResidual, uAmbient, uCoordinate, uPromotion, uClass,
        uDatum, uResponse} Residual AmbientItem Coordinate)
    (current : Query Previous fun _ => Residual)
    (normalizedSupport :
      SupportComplementNormalization.ExactLedger.{
        uResidual, uPrevious, uAmbient, uPiece} Previous Residual
        (fun previous => AmbientItem (current.read previous)))
    (localSupply : Query Previous fun _ =>
      ULift.{uSupply} LocalSupplyLowerBound.Summary)
    {previous : Previous}
    (fullRank :
      (Profile.ofRegistrationAt.{uPrevious, uResidual, uResponse, uSupply,
        uDatum, uClass, uPromotion, uCoordinate, uCode, uAmbient, uPiece}
        registration current normalizedSupport localSupply).code.FullRankResidual
        previous) :
    (Profile.ofRegistrationAt.{uPrevious, uResidual, uResponse, uSupply,
      uDatum, uClass, uPromotion, uCoordinate, uCode, uAmbient, uPiece}
      registration current normalizedSupport localSupply).code.fullRankValue
        fullRank ≤
      ((registration.coordinates (current.read previous)
            (normalizedSupport.complement.read previous)).values.map
          (registration.charge (current.read previous)
            (registration.response (current.read previous)))).sum +
        registration.capacitySlack (current.read previous)
          (registration.response (current.read previous)) := by
  refine (CodeProfile.fullRankValue_le_capacity _ fullRank ?_).trans ?_
  · intro stage coordinate
    exact registration.charge_pos _ _ coordinate
  · exact le_of_eq (congrArg
      (fun source =>
        ((registration.coordinates (current.read source)
              (normalizedSupport.complement.read source)).values.map
            (registration.charge (current.read source)
              (registration.response (current.read source)))).sum +
          registration.capacitySlack (current.read source)
            (registration.response (current.read source)))
      fullRank.exact.rankPrevious)

/-- Every registration-built composition hands CT16 exactly the coordinate
schedule that its own `InSupport` predicate recognizes, so the CT16
proper-support terminal of `Profile.ofRegistrationAt` is unreachable.  No
registration field, application fact, or extra hypothesis participates: the
support law is the definitional identity between the two schedules. -/
theorem Profile.ofRegistrationAt_properSupport_impossible
    {Previous : Type uPrevious} {Residual : Type uResidual}
    [HasResidual Previous Residual]
    {AmbientItem : Residual → Type uAmbient}
    {Coordinate : Residual → Type uCoordinate}
    (registration :
      Registration.{uResidual, uAmbient, uCoordinate, uPromotion, uClass,
        uDatum, uResponse} Residual AmbientItem Coordinate)
    (current : Query Previous fun _ => Residual)
    (normalizedSupport :
      SupportComplementNormalization.ExactLedger.{
        uResidual, uPrevious, uAmbient, uPiece} Previous Residual
        (fun previous => AmbientItem (current.read previous)))
    (localSupply : Query Previous fun _ =>
      ULift.{uSupply} LocalSupplyLowerBound.Summary)
    {previous : Previous}
    (exact :
      (Profile.ofRegistrationAt.{uPrevious, uResidual, uResponse, uSupply,
        uDatum, uClass, uPromotion, uCoordinate, uCode, uAmbient, uPiece}
        registration current normalizedSupport localSupply).code.ExactOutput
        previous)
    (codeSelected : exact.output.snd.terminal = .properSupport) : False :=
  CodeProfile.properSupport_impossible _ exact codeSelected
    fun _ _ member => member

/-- The CT15 capacity-overload terminal of a `Profile.ofRegistrationAt`
composition is unreachable.  No registration field, application fact, or extra
hypothesis participates.

CT15's overload gate compares the charge total of the coordinate schedule it
enumerates against the registered capacity.  `ofRegistrationAt` builds that
capacity out of the charge total of the *same* schedule, read back through the
same query, plus the registration's own slack, so the comparison is
`total ≤ total + slack` -- true by `Nat.le_add_right` and nothing else.

That is not an accident of the wiring, it is manuscript node [32]: the rank
budget there is `W₂(R)`, the count of raw curvature coordinates, which is the
coordinate schedule itself and never a supply observation.  The manuscript has
no overload alternative on that comparison at all, and after the wiring is
right neither does the formalization. -/
theorem Profile.ofRegistrationAt_capacity_impossible
    {Previous : Type uPrevious} {Residual : Type uResidual}
    [HasResidual Previous Residual]
    {AmbientItem : Residual → Type uAmbient}
    {Coordinate : Residual → Type uCoordinate}
    (registration :
      Registration.{uResidual, uAmbient, uCoordinate, uPromotion, uClass,
        uDatum, uResponse} Residual AmbientItem Coordinate)
    (current : Query Previous fun _ => Residual)
    (normalizedSupport :
      SupportComplementNormalization.ExactLedger.{
        uResidual, uPrevious, uAmbient, uPiece} Previous Residual
        (fun previous => AmbientItem (current.read previous)))
    (localSupply : Query Previous fun _ =>
      ULift.{uSupply} LocalSupplyLowerBound.Summary)
    {previous : Previous}
    (exact :
      (Profile.ofRegistrationAt.{uPrevious, uResidual, uResponse, uSupply,
        uDatum, uClass, uPromotion, uCoordinate, uCode, uAmbient, uPiece}
        registration current normalizedSupport localSupply).code.ExactOutput
        previous)
    (selected : exact.output.fst.snd.terminal = .c4) : False :=
  CodeProfile.capacity_impossible _ exact selected fun _stage =>
    Nat.le_add_right _ _

/-- CT10's exhaustive terminal is forced on every retained CT10 result of a
`Profile.ofRegistrationAt` composition whose registration is classification
exhaustive.  This is CT10's own `terminal_exhaustive_of_noDirect_of_observed`
read through the registration presentation; the statement is about the result
the ledger already carries, so no search is repeated and no execution is
re-run. -/
theorem Profile.ofRegistrationAt_ct10_terminal
    {Previous : Type uPrevious} {Residual : Type uResidual}
    [HasResidual Previous Residual]
    {AmbientItem : Residual → Type uAmbient}
    {Coordinate : Residual → Type uCoordinate}
    (registration :
      Registration.{uResidual, uAmbient, uCoordinate, uPromotion, uClass,
        uDatum, uResponse} Residual AmbientItem Coordinate)
    (current : Query Previous fun _ => Residual)
    (normalizedSupport :
      SupportComplementNormalization.ExactLedger.{
        uResidual, uPrevious, uAmbient, uPiece} Previous Residual
        (fun previous => AmbientItem (current.read previous)))
    (localSupply : Query Previous fun _ =>
      ULift.{uSupply} LocalSupplyLowerBound.Summary)
    (exhaustive : registration.toBaseRegistration.ClassificationExhaustive)
    (result :
      CT10.ExecutionResult
        (Profile.ofRegistrationAt.{uPrevious, uResidual, uResponse, uSupply,
          uDatum, uClass, uPromotion, uCoordinate, uCode, uAmbient, uPiece}
          registration current normalizedSupport
          localSupply).classification.classificationSpec
        (Profile.ofRegistrationAt.{uPrevious, uResidual, uResponse, uSupply,
          uDatum, uClass, uPromotion, uCoordinate, uCode, uAmbient, uPiece}
          registration current normalizedSupport
          localSupply).classification.classificationCapability) :
    result.terminal = CT10.Terminal.exhaustive :=
  CT10.ExecutionResult.terminal_exhaustive_of_noDirect_of_observed result
    (fun cls => exhaustive.1 _ cls)
    (fun cls => by
      obtain ⟨datum, member, classified⟩ :=
        exhaustive.2 (current.read result.stage.previous) cls
      exact ⟨datum, member, classified⟩)

/-- The CT16 closed-code mismatch terminal of a `Profile.ofRegistrationAt`
composition is unreachable for a classification-exhaustive registration.  The
composed closed code is CT10's retained terminal and the composed target code
is `CT10.Terminal.exhaustive`, so the mismatch alternative is exactly CT10's
non-exhaustive alternative, which the two registration-level facts exclude. -/
theorem Profile.ofRegistrationAt_mismatch_impossible
    {Previous : Type uPrevious} {Residual : Type uResidual}
    [HasResidual Previous Residual]
    {AmbientItem : Residual → Type uAmbient}
    {Coordinate : Residual → Type uCoordinate}
    (registration :
      Registration.{uResidual, uAmbient, uCoordinate, uPromotion, uClass,
        uDatum, uResponse} Residual AmbientItem Coordinate)
    (current : Query Previous fun _ => Residual)
    (normalizedSupport :
      SupportComplementNormalization.ExactLedger.{
        uResidual, uPrevious, uAmbient, uPiece} Previous Residual
        (fun previous => AmbientItem (current.read previous)))
    (localSupply : Query Previous fun _ =>
      ULift.{uSupply} LocalSupplyLowerBound.Summary)
    (exhaustive : registration.toBaseRegistration.ClassificationExhaustive)
    {previous : Previous}
    (exact :
      (Profile.ofRegistrationAt.{uPrevious, uResidual, uResponse, uSupply,
        uDatum, uClass, uPromotion, uCoordinate, uCode, uAmbient, uPiece}
        registration current normalizedSupport localSupply).code.ExactOutput
        previous)
    (codeSelected : exact.output.snd.terminal = .mismatch) : False :=
  CodeProfile.mismatch_impossible _ exact codeSelected fun _stage =>
    congrArg ULift.up
      (Profile.ofRegistrationAt_ct10_terminal.{uPrevious, uResidual, uResponse,
        uSupply, uDatum, uClass, uPromotion, uCoordinate, uCode, uAmbient,
        uPiece} registration current normalizedSupport localSupply exhaustive _)

end Hypostructure.Core.Strategy.TargetRelativeRankDichotomy
