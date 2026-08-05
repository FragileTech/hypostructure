import Hypostructure.PDE.Strategy.RegularityRegistry
import Hypostructure.PDE.Strategy.Registry.FibrePressure

/-!
# Target-relative rank and the cold branch, for a PDE regularity problem

`RegularityRegistry` fills the accounting families of `Core.StrategyData` from a
`BalancedRegularity` system.  This module fills the two remaining families that
are *not* accounting: the target-relative rank dichotomy and the cold-branch
aggregation.  Both are read off exactly one quantity, the stage the local
regularity argument reached at the selected residual:

| notion | PDE reading |
| --- | --- |
| rank of a residual | `(system.stageReached input).rank`, how many stages of the stratification the local argument cleared |
| target-dependent | the stage reached is not the closing one, `≠ .gradientClosed` |
| cold branch | a window at which the argument made no progress at all, `.regular` |

Nothing here executes, decides, routes or writes a ledger entry.  Every field
is inert data; Core's own strategy for each family runs the CTs, owns both
ledger extensions and selects every terminal.  In particular no field is an
analytic provision: `Stage.rank` is a closed-form function of which alternative
the argument reached, and the two laws that are not definitional
(`charge_pos` and `rankDropImpossible`) are finite case checks on the six
stages.
-/

namespace Hypostructure.PDE.Strategy.Registry.RankAndCold

open Hypostructure
open Hypostructure.PDE.Strategy
open Hypostructure.PDE.Strategy.RegularityStratification

universe u v w x y z

variable {M : LocalModel.{u}} {T : Core.Target M.problem}
  {Place : Type v} [NormedAddCommGroup Place] [NormedSpace ℝ Place]
  [MeasurableSpace Place] [BorelSpace Place] [FiniteDimensional ℝ Place]
  {Value : Type w} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
  [CompleteSpace Value]
  {Index : Type x} [Fintype Index]
  {μ : MeasureTheory.Measure Place} [μ.IsAddHaarMeasure]
  (system : BalancedRegularity M T Place Value Index μ)

/-! ## The stratification as an observation table

CT10 needs a finite observation schedule and a complete class schedule.  For a
regularity argument both are the same thing --- the six alternatives of
`stokes:prop:finite-state-stratification` --- because the only thing observed
at a window *is* which alternative the argument reached there.  The classifier
is therefore the identity, and the resulting table has one row per stage.
-/

/-- **The ceiling of the stratification.**  No alternative clears more stages
than the closing one; this is the only inequality the rank side needs, and it
is a six-case check on the finite state set. -/
theorem rank_le_ceiling (stage : Stage) :
    stage.rank ≤ Stage.gradientClosed.rank := by
  cases stage <;> decide

/-- **The six stages, as CT10's complete class schedule.**

The stages are lifted into the registry's data universe so the carrier does
not force the data universe of the surrounding `StrategyData` down to `Type`.
Completeness is the stratification's own `Stage.schedule.complete`; no schedule
is regenerated here. -/
noncomputable def stageClasses :
    Core.Finite.CompleteEnumeration (ULift Stage) where
  toEnumeration :=
    Stage.schedule.toEnumeration.map ULift.up ULift.up_injective
      (Classical.decEq _)
  complete := fun cls =>
    (Core.Finite.Enumeration.mem_map_values _ _ _ _ _).2
      ⟨cls.down, Stage.schedule.complete cls.down, rfl⟩

/-! ## Target-relative rank

The coordinates of the rank table are the windows of the cover around the
singularity --- one, for the framework's derived nested tower, exactly as in
`RegularityRegistry.windowSchedule`.  A coordinate is *target-dependent* when
the response at it is not the closing stage, i.e. when the local argument has
not finished there.  That is the reading under which `TargetDependent` is a
function of the registered response alone and needs no side condition.

The ambient support carrier stays a parameter: it is fixed by whichever
`SupportComplementNormalization` producer the local-supply entry reads, and
this registration never inspects it --- the window schedule is the derived
tower, not a selection out of the ambient support.
-/

/-- **The registered target-relative rank dichotomy.**

Reading, field by field:

* the *response* at a residual is the stage the local argument reached there;
* the *observations* and the *classes* are the six stages, with the identity
  classifier: what is observed at the derived window is precisely which
  alternative was reached;
* a class is *direct* when it clears more stages than the closing one, which no
  stage does --- so CT10's direct exit is unreachable and the registered
  rank-drop closure is supplied rather than left `none`;
* each retained coordinate carries one unit of charge, and the residual-owned
  slack is how many stages are still to be cleared at the window: that is the
  headroom above the schedule's own charge total that CT15's capacity gate is
  allowed to read;
* a coordinate is *target-dependent* exactly when the response is not
  `.gradientClosed`, i.e. when the gradient has not been named at that window.
-/
noncomputable def targetRelativeRankDichotomy
    {AmbientItem : Core.Strategy.ProblemInput M.problem → Type y} :
    Core.Strategy.TargetRelativeRankDichotomy.Registration
      (Core.Strategy.ProblemInput M.problem) AmbientItem
      (fun _ => PUnit) where
  Response := fun _ => ULift Stage
  response := fun input => ULift.up (system.stageReached input)
  Datum := fun _ => ULift Stage
  Class := fun _ => ULift Stage
  Promotion := fun _ => ULift Stage
  observationData := fun _ => stageClasses.toEnumeration
  completeClasses := fun _ => stageClasses
  classOf := fun _ _ datum => datum
  Direct := fun _ _ cls => Stage.gradientClosed.rank < cls.down.rank
  promote := fun _ _ cls => cls
  directDecidable := fun _ _ _ => inferInstance
  coordinates := fun _ _ => Core.Finite.Enumeration.singleton PUnit.unit
  charge := fun _ _ _ => 1
  charge_pos := fun _ _ _ => Nat.one_pos
  capacitySlack := fun _ response =>
    Stage.gradientClosed.rank - response.down.rank
  rankDropImpossible :=
    some (PLift.up
      ⟨fun _ cls => Nat.not_lt.2 (rank_le_ceiling cls.down),
        fun _ cls => ⟨cls, stageClasses.complete cls, rfl⟩⟩)
  TargetDependent := fun _ response _ => response.down ≠ .gradientClosed
  targetDependentDecidable := fun _ response _ =>
    inferInstanceAs (Decidable (response.down ≠ .gradientClosed))

/-- The registered classification is exhaustive, which is what makes CT10's
retained terminal the exhaustive one and therefore leaves the composed
CT16 closed-code test with no mismatch alternative.  Both halves are read off
the table above with no further input: no stage clears more than the ceiling,
and every stage is its own observation under the identity classifier. -/
theorem targetRelativeRankDichotomy_classificationExhaustive
    {AmbientItem : Core.Strategy.ProblemInput M.problem → Type y} :
    (targetRelativeRankDichotomy (M := M) (T := T) (Place := Place)
      (Value := Value) (Index := Index) (μ := μ) system
      (AmbientItem := AmbientItem)).toBaseRegistration.ClassificationExhaustive :=
  ⟨fun _ cls => Nat.not_lt.2 (rank_le_ceiling cls.down),
    fun _ cls => ⟨cls, stageClasses.complete cls, rfl⟩⟩

/-! ## The cold branch

A cold corridor is a window the local argument entered and left without
progress.  Read through the stratification that is a single, decidable
alternative: the stage reached is `.regular`, the bottom of the tower.  The
finite corridor family below records exactly that, as the F1--F5 partition Core
already owns:

| event | PDE reading |
| --- | --- |
| F1 | the window closed: the balance names the pressure gradient |
| F2 | the quotient velocity was recovered and the kernel normalized away |
| F3 | the pressure split into its Calderon--Zygmund child and the tail |
| F4 | the vorticity reduction ran, with or without the smoothing step |
| F5 | none of the above: no progress at all, the cold alternative |

F5 is not registered: Core derives it as the complement of the first four and
proves the partition exhaustive.  So "cold" is *defined* here as the absence of
every recorded step, which is what makes the classification a fact about the
window rather than a routing decision.
-/

/-- **The cold corridor family at one residual.**

One owner (the derived nested tower), one item (its window), and the four
recorded events above.  The corridor's finite state is the window's window ---
a single state --- so Core's repeated-state and terminal alternatives are both
available and neither carries an obligation. -/
noncomputable def coldWindowFamily
    (input : Core.Strategy.ProblemInput M.problem) :
    Core.Finite.ColdCorridor.Producer.FamilyProducer PUnit where
  owners := Core.Finite.Enumeration.singleton PUnit.unit
  Item := fun _ => PUnit
  State := fun _ => PUnit
  stateFintype := fun _ => inferInstance
  producer := fun _ =>
    Core.Finite.ColdCorridor.Producer.ofFirstFour
      { schedule := Core.Finite.Enumeration.singleton PUnit.unit
        state := fun _ => PUnit.unit }
      (fun _ => PUnit)
      (fun _ => PUnit.unit)
      (fun _ _ => system.stageReached input = .gradientClosed)
      (fun _ _ => system.stageReached input = .velocityRecovered)
      (fun _ _ => system.stageReached input = .pressureDecomposed)
      (fun _ _ =>
        system.stageReached input = .vorticitySmoothed ∨
          system.stageReached input = .vorticityReduced)
      (fun _ => inferInstance) (fun _ => inferInstance)
      (fun _ => inferInstance) (fun _ => inferInstance)

/-- **The registered cold continuation.**

The stage-polymorphic boundary Core consumes: given the live packing, the
inherited handoff schedule and the exact closure queries, the registration
returns the corridor family of the residual those queries are read at.  It
returns a *query*, never a value: the family stays indexed by the literal
active stage, so nothing downstream can rebuild it from the stable residual.

The upstream producers are parameters because they are exactly the neighbours
the `Core.StrategyData` entry indexes --- the counterexample reduction, the
packing closure and the homogeneous handoff.  This registration consults none
of them; the cold alternative of a regularity argument is a statement about the
window, and the packing only says which window. -/
noncomputable def coldBranchLedgerRegistration
    {progress : Core.Progress M.problem}
    {replacement : Core.Strategy.InterfaceReplacement.Profile
      (P := M.problem) (T := T) progress}
    {packingSemantics :
      Core.Strategy.ObstructionPackingClosure.Semantics
        (Core.Strategy.ProblemInput M.problem)
        (fun input => T.Predicate input.object)}
    {HandoffSupport : Core.Strategy.ProblemInput M.problem → Type z} :
    Core.Strategy.ColdBranchAggregation.LedgerRegistration
      M.problem T progress replacement packingSemantics HandoffSupport where
  atStage := fun _exact current _activeObject _packing _handoffSupports
      _handoffAbsent =>
    { Owner := fun _ => PUnit
      family := current.map fun _ input => coldWindowFamily system input
      -- Consumes `BalancedRegularity.target_of_gradientClosed` at
      -- `PDE/Strategy/BalancedRegularity.lean:374` and
      -- `Registry.FibrePressure.gradientClosed_of_stageReached` at
      -- `PDE/Strategy/Registry/FibrePressure.lean:87`.  The stored (F1) owner's
      -- event witness *is* alternative 6 at this residual, so the registered
      -- target is read off it; nothing is decided or reproved here.
      storedF1ForcesTarget := fun previous stage owner =>
        system.target_of_gradientClosed (current previous)
          (Registry.FibrePressure.gradientClosed_of_stageReached system
            (current previous)
            ((coldWindowFamily system
                (current previous)).storedFailureEvent
              stage Core.Finite.ColdCorridor.Failure.f1
              (by decide) owner).sound)
      classifiedStateForcesTarget := fun _previous _stage => none }

/-! ### The node-145--164 argument list

`ColdBranchAggregation.Registration` is the other, self-contained presentation
of the same branch: the dependent argument list of nodes 145--164, read at one
literal predecessor.  Every carrier is the derived window, so the only content
is in the six contracts, and each of them is a statement about the stage the
argument reached:

* node 146 compares the window's progress against the ceiling --- it never
  exceeds it, so the split always takes the at-most branch;
* node 154 compares the same progress against `.regular` --- a hit is *any*
  progress at all, so the no-hit branch is precisely the cold one;
* node 156's event, and node 160's goodness, are both "the argument closed";
* node 158's scale is the progress and its bound is the ceiling;
* node 159 asks for one admissible window, which the ceiling bound supplies.
-/

/-- **The registered node-145--164 cold argument list.**

Stage-polymorphic in the predecessor: every contract reads the stage the
argument reached through `residualOf`, so the registration is valid at any
ledger depth and never reconstructs a predecessor. -/
noncomputable def coldBranchAggregation
    {Previous : Type z}
    [Core.Residual.HasResidual Previous
      (Core.Strategy.ProblemInput M.problem)] :
    Core.Strategy.ColdBranchAggregation.Registration Previous where
  inputs := fun _previous =>
    { Interface := fun _ => PUnit
      interface := PUnit.unit
      contract146 :=
        { profile := fun stage =>
            { value :=
                (system.stageReached (Core.Residual.residualOf stage)).rank
              threshold := Stage.gradientClosed.rank } }
      Route := fun _ => PUnit
      route := PUnit.unit
      Private := fun _ => PUnit
      privateData := PUnit.unit
      Audit := fun _ => PUnit
      audit := PUnit.unit
      Cold := fun _ => PUnit
      cold := PUnit.unit
      Filter := fun _ => PUnit
      filter := PUnit.unit
      Stubs := fun _ => PUnit
      stubs := PUnit.unit
      Scan := fun _ => PUnit
      scan := PUnit.unit
      contract154 :=
        { profile := fun stage =>
            { value :=
                (system.stageReached (Core.Residual.residualOf stage)).rank
              threshold := Stage.regular.rank } }
      Certificate := fun _ => PUnit
      certificate := PUnit.unit
      contract156 :=
        { event := fun stage =>
            system.stageReached (Core.Residual.residualOf stage) =
              .gradientClosed
          event_decidable := fun _ => inferInstance }
      Germ := fun _ => PUnit
      germ := PUnit.unit
      contract158 :=
        { scale := fun stage =>
            (system.stageReached (Core.Residual.residualOf stage)).rank
          bounded := fun stage =>
            (system.stageReached (Core.Residual.residualOf stage)).rank ≤
              Stage.gradientClosed.rank
          bounded_of_scale := fun _ => rank_le_ceiling _ }
      contract159 :=
        { candidate := fun _ => PUnit
          admissible := fun stage _ =>
            (system.stageReached (Core.Residual.residualOf stage)).rank ≤
              Stage.gradientClosed.rank
          witness := fun _ => ⟨PUnit.unit⟩
          witness_admissible := fun _ => ⟨PUnit.unit, rank_le_ceiling _⟩ }
      contract160 :=
        { good := fun stage =>
            system.stageReached (Core.Residual.residualOf stage) =
              .gradientClosed
          good_decidable := fun _ => inferInstance }
      Evidence := fun _ => PUnit
      evidence := PUnit.unit
      Residual := fun _ => PUnit
      residual := PUnit.unit
      contract163 :=
        { package := fun _ => PUnit
          package_of_good := fun _ => ⟨PUnit.unit⟩ }
      Package := fun _ => PUnit
      package := PUnit.unit }

end Hypostructure.PDE.Strategy.Registry.RankAndCold
