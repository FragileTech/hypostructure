import Hypostructure.PDE.Strategy.RegularityRegistry

/-!
# Fibre pressure, bottleneck classification, and homogeneous exhaustion

`Hypostructure.PDE.Strategy.RegularityRegistry` fills the six accounting
families a local regularity argument needs to *count*.  This module fills the
three that make it *close*: the coupled fibre pressure (CT9 → CT13 → CT14), the
finite bottleneck classification (CT9 → CT14 → CT10 → CT6), and the homogeneous
bottleneck (the nine-CT exhaustion).  The three chain in that order, and the
`StrategyData` fields that carry the last two name the earlier ones by index, so
they are registered together.

Everything below is read off one observable, exactly as in the registry it
extends: `system.stageReached input` is how far the local argument got at the
framework's derived window, and `Stage.rank` turns that into a number between
`0` and `Stage.gradientClosed.rank = 5`.  The dictionary is:

| framework word | PDE reading |
| --- | --- |
| fibre | a window of the nested tower around the singularity |
| fibre capacity | the ceiling rank, i.e. `gradientClosed` |
| pressure label | the stage the window's certificate reached |
| coarse code | the same stage, read as the window's class |
| bottleneck | a stage the local argument cannot pass |
| homogeneity | every window sits at the same stage |
| separator | the first stage strictly above what was reached |

The framework's derived tower is a single window, so every schedule of windows
is a singleton and the tower is homogeneous by construction: one fibre, one
label, one code.  A genuine multi-window cover replaces `windowSchedule` and
`stageReached`, and nothing else here changes.

No field is an analytic provision.  Every numeric quantity is `Stage.rank`,
which is a closed-form function of which alternative the argument reached, and
every law below is discharged from the single arithmetic identity
`stage.rank ≤ Stage.gradientClosed.rank` --- the ceiling is the ceiling.  In
particular the homogeneous bottleneck's exceptional candidate family is `Empty`:
no local failure, response defect, admissibility failure, support deficit, or
support-capacity failure can occur when both sides of every comparison are read
off the same stage.
-/

namespace Hypostructure.PDE.Strategy.Registry.FibrePressure

open Hypostructure
open Hypostructure.PDE.Strategy
open Hypostructure.PDE.Strategy.RegularityStratification
open scoped Distributions ContDiff

universe u v w x

variable {M : LocalModel.{u}} {T : Core.Target M.problem}
  {Place : Type v} [NormedAddCommGroup Place] [NormedSpace ℝ Place]
  [MeasurableSpace Place] [BorelSpace Place] [FiniteDimensional ℝ Place]
  {Value : Type w} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
  [CompleteSpace Value]
  {Index : Type x} [Fintype Index]
  {μ : MeasureTheory.Measure Place} [μ.IsAddHaarMeasure]
  (system : BalancedRegularity M T Place Value Index μ)

/-! ## The one arithmetic fact

`Stage.gradientClosed` is the last alternative of the stratification, so its
rank dominates every other.  This is the only inequality the three
registrations below ever need; each of the homogeneous bottleneck's five
exceptional-schedule obligations is discharged from it. -/

/-- **The ceiling is the ceiling.**  No stage of the regularity stratification
outranks gradient closure. -/
private theorem rank_le_gradientClosed (stage : Stage) :
    stage.rank ≤ Stage.gradientClosed.rank := by
  cases stage <;> decide

/-- The stage the local argument reached at the derived window never outranks
gradient closure. -/
private theorem stageReached_rank_le
    (system : BalancedRegularity M T Place Value Index μ)
    (input : Core.Strategy.ProblemInput M.problem) :
    (system.stageReached input).rank ≤ Stage.gradientClosed.rank :=
  rank_le_gradientClosed _

/-- Reading the top of the stratification back into the analysis: the argument
records `gradientClosed` exactly when alternative 6 --- smoothness of the
velocity field on the window --- actually holds.  `stageReached` selects the
highest alternative that holds, so naming the last one names its predicate. -/
theorem gradientClosed_of_stageReached
    (system : BalancedRegularity M T Place Value Index μ)
    (input : Core.Strategy.ProblemInput M.problem)
    (closed : system.stageReached input = Stage.gradientClosed) :
    system.GradientClosed input := by
  classical
  by_contra notReached
  simp only [BalancedRegularity.stageReached, if_neg notReached] at closed
  split_ifs at closed

/-- The same reading one stage down: the argument records `velocityRecovered`
exactly when alternative 5 --- recovery of the quotient field modulo a zero or
smooth harmonic-kernel mode --- actually holds.  `stageReached` tests
alternative 5 immediately after alternative 6, so naming its stage names its
predicate. -/
theorem recoveredModuloKernel_of_stageReached
    (system : BalancedRegularity M T Place Value Index μ)
    (input : Core.Strategy.ProblemInput M.problem)
    (recovered : system.stageReached input = Stage.velocityRecovered) :
    system.RecoveredModuloKernel input := by
  classical
  simp only [BalancedRegularity.stageReached] at recovered
  split_ifs at recovered with _ reached
  exact reached

/-! ## Shared schedules

The tower has one window and the stratification has six stages; those two
schedules generate every finite family the three registrations need. -/

/-- The obstruction schedule of the reconciliation step: the six stages, read
from the bottom.  `regular` is the canonical fallback because it is the state a
window is in before any alternative has been passed, so it is the obstruction
that is always available to charge against. -/
private def stageObstructions : CT13.ObstructionSchedule Stage where
  fallbackDefault := .regular
  remaining :=
    [.vorticityReduced, .vorticitySmoothed, .pressureDecomposed,
      .velocityRecovered, .gradientClosed]
  nodup := by decide
  decEq := inferInstance

/-- The one-point response schedule.  The local argument's response table has a
single coordinate --- the reading taken at the window --- and a single row, so
its symbolic coverage is the subsingleton one. -/
private abbrev responseUnitSystem : Core.Response.System Stage :=
  Core.Response.System.ofDecodedContexts Unit Unit Stage
    (fun stage _ => stage) id

/-- **The table's reading is on target exactly when the argument closed.**

The representative of the table is the stage the local argument reached, so
the response it records is that stage and `Accepts` is "the closing
alternative".  Making the representative `Unit` --- as a placeholder table
would --- puts the residual out of the table's sight and makes both sides
vacuously true; here the equivalence is `Iff.rfl` on a reading that carries
information. -/
private def responseUnitSemantics :
    Core.Response.TargetSemantics responseUnitSystem where
  TargetResponse := fun stage _ => stage = .gradientClosed
  Accepts := fun stage => stage = .gradientClosed
  target_iff_accepts := fun _ _ => Iff.rfl

/-- The single coordinate, candidate, and row of that table. -/
private def responseSchedule : Core.Finite.Enumeration Unit :=
  Core.Finite.Enumeration.singleton ()

/-! ## Coupled homogeneous fibre pressure

CT9 partitions the tower's windows into fibres by the stage each reached and
asks whether any fibre is over capacity; CT13 reconciles the obstruction each
fibre presents against the windows that can pay for it; CT14 aggregates the
resulting pressure.

The reading that makes all three exact: a fibre is the set of windows carrying
one stage, its capacity is the ceiling rank, and the pressure a window exerts is
the rank it reached.  The derived tower contributes one window, so every fibre
has at most one member and CT9's bounded terminal is forced --- the tower is
never overloaded, which is the statement that a single-window cover cannot
concentrate pressure.
-/

/-- **The registered coupled fibre pressure.**

*CT9.*  Items are windows; the label of a window is the stage its certificate
reached; the capacity of a label is the ceiling `Stage.gradientClosed.rank`.

*CT13.*  A window is an eligible payer exactly when it has not already closed
--- a closed window owes nothing.  The resource it supplies is the stage it
reached, the charge against it is that stage's rank, and the standing demand is
the same rank, so the reconciliation ledger balances by construction.

*CT14.*  The aggregate is taken over the windows again, with the rank reached as
lower mass and the ceiling as capacity, and the aggregate label of a window is
its stage. -/
noncomputable def coupledHomogeneousFibrePressures :
    Core.Strategy.CoupledHomogeneousFibrePressure.Registration
      (Core.Strategy.ProblemInput M.problem) where
  Item := fun _ => PUnit
  Token := fun _ => PUnit
  Role := fun _ => Stage
  Label := fun _ => Stage
  items := fun input => Core.Finite.Enumeration.singleton PUnit.unit
  completeLabels := fun _ => Stage.schedule
  labelOf := fun input _ => system.stageReached input
  fibreCapacity := fun _ _ => Stage.gradientClosed.rank
  Payer := fun _ => PUnit
  Obstruction := fun _ => Stage
  Resource := fun _ => Stage
  payers := fun input => Core.Finite.Enumeration.singleton PUnit.unit
  obstructions := fun _ => stageObstructions
  tierTwo := fun input _ => Core.Finite.Enumeration.singleton PUnit.unit
  Eligible := fun input _ => system.stageReached input ≠ .gradientClosed
  obstructionCost := fun _ stage => stage.rank
  payerResource := fun input _ => system.stageReached input
  charge := fun input _ => (system.stageReached input).rank
  demand := fun input => (system.stageReached input).rank
  eligibleDecidable := fun input _ =>
    inferInstanceAs (Decidable (system.stageReached input ≠ .gradientClosed))
  resourceDecidableEq := fun _ => inferInstance
  Member := fun _ => PUnit
  AggregateLabel := fun _ => Stage
  members := fun input => Core.Finite.Enumeration.singleton PUnit.unit
  memberLowerMass := fun input _ => (system.stageReached input).rank
  memberCapacity := fun _ _ => some Stage.gradientClosed.rank
  memberLabel := fun input _ => some (system.stageReached input)
  aggregateLabelDecidableEq := fun _ => inferInstance

/-! ## Finite bottleneck classification

The same tower read for *where it stops*.  CT9 groups the windows by coarse
code, CT14 checks the pressure each code carries against its capacity, CT10
classifies the codes into those that close directly and those that must be
promoted, and CT6 scans an ordered separator family for the first failure.

A separator index is a stage, scanned in the stratification's own order, and it
*fails* when it is strictly above the stage the argument reached.  CT6's first
failure is therefore literally the first alternative the local argument could
not pass --- the bottleneck.  When the argument closed, the reached rank is the
ceiling and no stage is above it, so the scan finds nothing.
-/

/-- **The registered bottleneck classification.**

Coarse codes and pressure labels are both stages: the code of a window is the
stage it reached, and the pressure a code may carry is the ceiling rank.  A
semantic tag is `Direct` exactly when it is `gradientClosed`, i.e. when the
window's class closes with no promotion; every other stage must be promoted, and
promotion is the identity because a stage is already its own promoted form.

The separator scan is the bottleneck itself: `SeparatorFailure input stage`
holds when `stage` outranks what was reached, and its retained data is the proof
of that strict inequality.  The contribution of a separator is its own rank ---
how far the argument would have to climb to clear it. -/
noncomputable def finiteBottleneckClassifications :
    Core.Strategy.FiniteBottleneckClassification.Registration
      (Core.Strategy.ProblemInput M.problem) where
  PatternItem := fun _ => PUnit
  CoarseCode := fun _ => Stage
  patternItems := fun input => Core.Finite.Enumeration.singleton PUnit.unit
  completeCoarseCodes := fun _ => Stage.schedule
  coarseCodeOf := fun input _ => system.stageReached input
  PressureLabel := fun _ => Stage
  pressureCapacity := fun _ _ => some Stage.gradientClosed.rank
  pressureLabel := fun _ code => some code
  pressureLabelDecidableEq := fun _ => inferInstance
  Datum := fun _ => PUnit
  SemanticTag := fun _ => Stage
  Promotion := fun _ => Stage
  data := fun input => Core.Finite.Enumeration.singleton PUnit.unit
  completeSemanticTags := fun _ => Stage.schedule
  classOf := fun input _ => system.stageReached input
  Direct := fun _ tag => tag = .gradientClosed
  promote := fun _ tag => tag
  directDecidable := fun _ _ => inferInstance
  SeparatorIndex := fun _ => Stage
  SeparatorData := fun input stage =>
    PLift ((system.stageReached input).rank < stage.rank)
  separatorOrder := fun _ => Stage.schedule.toEnumeration
  SeparatorFailure := fun input stage =>
    (system.stageReached input).rank < stage.rank
  separatorFailureData := fun _ _ failure => PLift.up failure
  separatorFailureDecidable := fun _ _ => inferInstance
  separatorContribution := fun _ stage => stage.rank

/-! ## Homogeneous bottleneck

The nine-CT exhaustion `CT9 → CT14 → CT10 → CT6 → CT3 → CT6 → CT1 → CT5 → CT14`
run over the same window and the same six stages.

The four routes read, in PDE terms:

* `target` --- CT1 found the closing candidate, i.e. the argument reached
  `gradientClosed`, and the framework's own bridge `target_of_gradientClosed`
  turns that into the registered target;
* `exceptional` --- impossible here, and registered as such: the exceptional
  candidate family is `Empty`;
* `structured` --- the argument did not close, and the support ledger is what
  survives;
* `bounded` --- the argument did not close, and the final CT14 records the
  capacity certificate `(stageReached).rank ≤ Stage.gradientClosed.rank`, i.e.
  the window's stage is under the ceiling.

Every audit the exhaustion performs compares two readings of the same stage, so
each of the five `…Scheduled` obligations is discharged from
`rank_le_gradientClosed` rather than by exhibiting a candidate.  That is exactly
the hypothesis `exceptionalImpossible` records, and it lets Core delete the
exceptional output instead of carrying it as an open endpoint.
-/

/-- **The registered homogeneous bottleneck.**

*CT9 and the first CT14.*  Homogeneity codes are stages; the tower is
homogeneous because its one window carries one code, and the code's capacity is
the ceiling rank.

*CT10.*  A local class is a stage; it is `Direct` exactly when it is
`gradientClosed`.

*The two CT6 audits.*  A local failure --- and, on the second scan, an
admissibility failure --- is a window whose stage *outranks* the ceiling.  There
is none, and the retained failure data is the proof of the impossible strict
inequality, so both scans reach their active-ledger terminal.

*CT3.*  The response table is the one-coordinate unit table: the argument takes
a single reading at the window, and source and replacement produce the same
value, so no response defect is distinguishable.

*CT1.*  The single target candidate is realized exactly when the argument
reached `gradientClosed`; the exceptional family is `Empty`.

*CT5.*  The one window supports itself exactly when its stage is under the
ceiling, which it always is; the required support is the rank reached and the
capacity is the ceiling.

*The final CT14.*  Lower mass is the rank reached, capacity is the ceiling
rank, and the bounded route's certificate is therefore the ceiling statement
`(stageReached).rank ≤ Stage.gradientClosed.rank`. -/
noncomputable def homogeneousBottlenecks :
    Core.Strategy.HomogeneousBottleneck.Registration
      (Core.Strategy.ProblemInput M.problem)
      (fun input => T.Predicate input.object) where
  Item := fun _ => PUnit
  HomogeneityCode := fun _ => Stage
  items := fun input => Core.Finite.Enumeration.singleton PUnit.unit
  completeHomogeneityCodes := fun _ => Stage.schedule
  homogeneityCodeOf := fun input _ => system.stageReached input
  homogeneityCapacity := fun _ _ => Stage.gradientClosed.rank

  CapacityLabel := fun _ => Stage
  codeCapacity := fun _ _ => some Stage.gradientClosed.rank
  codeLabel := fun _ code => some code
  codeLabelDecidableEq := fun _ => inferInstance

  Datum := fun _ => PUnit
  LocalClass := fun _ => Stage
  Promotion := fun _ => Stage
  data := fun input => Core.Finite.Enumeration.singleton PUnit.unit
  completeLocalClasses := fun _ => Stage.schedule
  classOf := fun input _ => system.stageReached input
  Direct := fun _ localClass => localClass = .gradientClosed
  promote := fun _ localClass => localClass
  directDecidable := fun _ _ => inferInstance

  LocalIndex := fun _ => PUnit
  LocalFailureData := fun input _ =>
    PLift (Stage.gradientClosed.rank < (system.stageReached input).rank)
  localOrder := fun input => Core.Finite.Enumeration.singleton PUnit.unit
  LocalFailure := fun input _ =>
    Stage.gradientClosed.rank < (system.stageReached input).rank
  localFailureData := fun _ _ failure => PLift.up failure
  localFailureDecidable := fun _ _ => inferInstance
  localContribution := fun input _ => (system.stageReached input).rank

  Representative := Stage
  responseSystem := responseUnitSystem
  targetSemantics := responseUnitSemantics
  ResponseCandidate := Unit
  ResponseRow := Unit
  -- The row-level data of the table cannot see the residual; only
  -- `responseSource` can.  So the rows carry the alternative the argument is
  -- aiming at, and the source carries the one it actually reached.
  candidatePiece := fun _ => Stage.gradientClosed
  rowPiece := fun _ => Stage.gradientClosed
  rowResponse := fun _ _ => Stage.gradientClosed
  responseSource := fun input => system.stageReached input
  responseCoordinates := fun _ => responseSchedule
  responseCandidates := fun _ => responseSchedule
  responseRows := fun _ => responseSchedule
  ResponseAdmissible := fun input _ _ => system.stageReached input ≠ .regular
  ResponseStrictlySmaller := fun input _ _ =>
    system.stageReached input ≠ .gradientClosed
  responseValueDecEq := by
    change DecidableEq Stage
    infer_instance
  responseAdmissibleDecidable := fun input _ _ =>
    inferInstanceAs (Decidable (system.stageReached input ≠ .regular))
  responseSmallerDecidable := fun input _ _ =>
    inferInstanceAs (Decidable (system.stageReached input ≠ .gradientClosed))
  responseCandidateCoverage := by
    intro input _candidate _member
    letI : Subsingleton responseUnitSystem.Context := by
      change Subsingleton Unit
      infer_instance
    exact
      Core.Response.FiniteTable.SymbolicCoverage.ofSubsingletonSingleton
        responseUnitSystem
        { source := system.stageReached input
          replacement := Stage.gradientClosed }
        ()
  responseRowCoverage := by
    intro input _row _member
    letI : Subsingleton responseUnitSystem.Context := by
      change Subsingleton Unit
      infer_instance
    exact
      Core.Response.FiniteTable.SymbolicCoverage.ofSubsingletonSingleton
        responseUnitSystem
        { source := system.stageReached input
          replacement := Stage.gradientClosed }
        ()

  AdmissibilityField := fun _ => PUnit
  AdmissibilityFailureData := fun input _ =>
    PLift (Stage.gradientClosed.rank < (system.stageReached input).rank)
  admissibilityOrder := fun input => Core.Finite.Enumeration.singleton PUnit.unit
  AdmissibilityFailure := fun input _ =>
    Stage.gradientClosed.rank < (system.stageReached input).rank
  admissibilityFailureData := fun _ _ failure => PLift.up failure
  admissibilityFailureDecidable := fun _ _ => inferInstance
  admissibilityContribution := fun input _ => (system.stageReached input).rank

  TargetCandidate := fun _ => PUnit
  ExceptionalCandidate := fun _ => Empty
  outcomeCandidates := fun _ =>
    { values := [Sum.inl PUnit.unit]
      nodup := List.nodup_singleton _
      decEq := Classical.decEq _ }
  RealizesTarget := fun input _ => system.stageReached input = .gradientClosed
  RealizesException := fun _ impossible => nomatch impossible
  targetRealizationDecidable := fun input _ =>
    inferInstanceAs (Decidable (system.stageReached input = .gradientClosed))
  exceptionRealizationDecidable := fun _ impossible => nomatch impossible
  targetOfRealization := fun input _ closed =>
    system.target_of_gradientClosed input
      (gradientClosed_of_stageReached system input closed)

  supportBudget := RegularityRegistry.countingBudget
  SupportSite := fun _ => PUnit
  SupportWitness := fun _ _ => PUnit
  supportFamily := fun input =>
    { indices := Core.Finite.Enumeration.singleton PUnit.unit
      fibres := fun _ => Core.Finite.Enumeration.singleton PUnit.unit }
  SupportActive := fun input _ => system.stageReached input ≠ .gradientClosed
  -- The schedule is now the *residual's own* --- empty once the argument has
  -- closed --- so this relation no longer has to be total over a constant
  -- family.  It says what it means: a scheduled window is one the argument is
  -- still working on.  The earlier always-true reading (`rank ≤ ceiling`) was
  -- an artefact of the constant schedule, not a demand of the framework.
  -- CT13's reconciliation needs a non-empty fibre, so this module keeps a
  -- constant one-window schedule and the relation must be total over it.  It
  -- states the honest always-true fact rather than pretending to a condition.
  SupportRelation := fun input _ _ =>
    (system.stageReached input).rank ≤ Stage.gradientClosed.rank
  supportContribution := fun input _ _ => (system.stageReached input).rank
  supportRequired := fun input => (system.stageReached input).rank
  supportCapacity := fun _ => Stage.gradientClosed.rank
  supportActiveDecidable := fun input _ =>
    inferInstanceAs (Decidable (system.stageReached input ≠ .gradientClosed))
  supportRelationDecidable := fun _ _ _ => inferInstance
  supportResourceLEDecidable := Nat.decLe

  BoundedMember := fun _ => PUnit
  BoundedLabel := fun _ => Stage
  boundedMembers := fun input => Core.Finite.Enumeration.singleton PUnit.unit
  boundedLowerMass := fun input _ => (system.stageReached input).rank
  boundedCapacity := fun _ _ => some Stage.gradientClosed.rank
  boundedLabel := fun input _ => some (system.stageReached input)
  boundedLabelDecidableEq := fun _ => inferInstance

  localFailureScheduled := by
    intro input _ _ failure
    exact absurd (stageReached_rank_le system input) (Nat.not_le.mpr failure)
  responseDefectScheduled := by
    intro _ _ _ _ _ defect
    exact (defect rfl).elim
  admissibilityFailureScheduled := by
    intro input _ _ failure
    exact absurd (stageReached_rank_le system input) (Nat.not_le.mpr failure)
  supportDeficitScheduled := by
    intro input _ _ _ unsupported
    exact absurd (stageReached_rank_le system input)
      (unsupported ⟨0, Nat.zero_lt_one⟩)
  supportCapacityFailureScheduled := by
    intro input failure
    exact absurd (stageReached_rank_le system input) failure
  boundedCapacityTotal := by
    intro _ _ _
    exact ⟨Stage.gradientClosed.rank, rfl⟩
  boundedLabelTotal := by
    intro input _ _
    exact ⟨system.stageReached input, rfl⟩

  exceptionalImpossible := some ⟨fun _ impossible => nomatch impossible⟩

end Hypostructure.PDE.Strategy.Registry.FibrePressure
