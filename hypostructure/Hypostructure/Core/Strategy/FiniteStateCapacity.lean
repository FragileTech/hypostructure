import Hypostructure.CTAdapters
import Hypostructure.Core.ArithmeticTransport
import Hypostructure.Core.FiniteEntropy
import Hypostructure.Core.Residual.Stage
import Hypostructure.Core.Strategy.FiniteStateCapacitySemantics
import Hypostructure.Core.Strategy.FiniteBarrierEnumeration
import Hypostructure.Core.Strategy.LocalSupplyLowerBound
import Hypostructure.Core.Strategy.TargetRelativeRankDichotomySemantics
import Hypostructure.Core.Strategy.FiniteStateNetChargeContinuationSemantics
import Hypostructure.Core.Strategy.FiniteStateCapacityTheorems
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Finite-state capacity

This reusable Strategy is exactly CT17 followed by CT14.  CT17 reads the
residual-owned finite-state presentation.  CT14 runs on CT17's literal ledger
extension. `CTExecution.compose` owns both writes and retains both exact CT
outputs. The subsequent power comparison and logarithmic transport are
proof-only projections of the same literal predecessor: they add neither a
CT execution nor a ledger write.

`FiniteStateCapacity` does not derive the finite-barrier or local-supply
summaries itself.  Earlier sealed Strategies (`FiniteBarrierEnumeration`,
`LocalSupplyLowerBound`) derive them from their own CT outputs and Core
publishes the exact values into the accumulated ledger.  `Profile` receives
only typed `Query` handles to those exact ledger values; the registration
never sees either summary.
-/

namespace Hypostructure.Core.Strategy.FiniteStateCapacity

open Hypostructure
open Hypostructure.Core.Residual

universe uPrevious uResidual uAmbient uData

/-- One residual-indexed registration lifted to an arbitrary literal
predecessor ledger stage.  `BarrierSummary`/`SupplySummary` are fixed by Core
to the exact summary types the two producing Strategies publish; the proof
author never supplies either value.

`current` is the compiler's one active-input query, exactly the query the
normalized-support ledger is indexed by, and `complement` is the exact
normalized-support complement inherited from the local-supply predecessor at
that very query.  Core never reconstructs either: the compiler hands over the
producer's own `SupportComplementNormalization.ExactLedger.complement`.  This
is the same `current`/`normalizedSupport` pairing
`LocalSupplyLowerBound.Profile.ofRegistrationAt` and
`TargetRelativeRankDichotomy.Profile.ofRegistrationAt` already take. -/
structure Profile (Previous : Type uPrevious) (Residual : Type uResidual)
    [HasResidual Previous Residual] where
  AmbientItem : Residual → Type uAmbient
  registration : Registration.{uResidual, uAmbient, uData} Residual AmbientItem
  current : Query Previous fun _ => Residual := Query.residual
  complement : Query Previous fun previous =>
    Core.Finite.Enumeration (AmbientItem (current previous))
  /-- Exact rank/coordinate equality published by the upstream full-rank
  branch.  This is a theorem-backed projection, not a second rank scan. -/
  fullRankCertificate :
    Query Previous fun _ =>
      TargetRelativeRankDichotomy.FullRankCertificate
  independentRank : Query Previous fun _ => Nat
  finiteBarrierSummary :
    Query Previous fun _ => FiniteBarrierEnumeration.Summary
  localSupply : Query Previous fun _ => LocalSupplyLowerBound.Summary

namespace Profile

variable [HasResidual Previous Residual]

def inheritedInputs (profile : Profile Previous Residual) :
    Query Previous fun _ =>
      PProd Nat (PProd FiniteBarrierEnumeration.Summary
        LocalSupplyLowerBound.Summary) :=
  profile.independentRank.and
    (profile.finiteBarrierSummary.and profile.localSupply)

def inheritedIndependentRank (profile : Profile Previous Residual) :
    Query Previous fun _ => Nat :=
  profile.inheritedInputs.map fun _ inputs => inputs.fst

def inheritedFiniteBarrierSummary (profile : Profile Previous Residual) :
    Query Previous fun _ => FiniteBarrierEnumeration.Summary :=
  profile.inheritedInputs.map fun _ inputs => inputs.snd.fst

def inheritedLocalSupply (profile : Profile Previous Residual) :
    Query Previous fun _ => LocalSupplyLowerBound.Summary :=
  profile.inheritedInputs.map fun _ inputs => inputs.snd.snd

def independentRankAt (profile : Profile Previous Residual)
    (previous : Previous) : Nat :=
  profile.inheritedIndependentRank previous

def finiteBarrierSummaryAt (profile : Profile Previous Residual)
    (previous : Previous) : FiniteBarrierEnumeration.Summary :=
  profile.inheritedFiniteBarrierSummary previous

def localSupplyAt (profile : Profile Previous Residual)
    (previous : Previous) : LocalSupplyLowerBound.Summary :=
  profile.inheritedLocalSupply previous

/-- Residual access uses the compiler's one active-input query, the same query
the inherited complement is indexed by.  At the spine it is literally
`Query.residual`. -/
def residualQuery (profile : Profile Previous Residual) :
    Query Previous fun _ => Residual :=
  profile.current

/-- The inherited support complement at one literal predecessor.  It is the
producer's own exact schedule, read through the query; nothing is rebuilt. -/
def complementAt (profile : Profile Previous Residual) (previous : Previous) :
    Core.Finite.Enumeration
      (profile.AmbientItem (profile.residualQuery previous)) :=
  profile.complement previous

def targets (profile : Profile Previous Residual) :
    Query Previous fun previous =>
      Core.Finite.Enumeration
        (profile.registration.Target (profile.residualQuery previous)) :=
  profile.residualQuery.dependentMap fun previous residual =>
    profile.registration.targets residual (profile.independentRankAt previous)
      (profile.finiteBarrierSummaryAt previous) (profile.localSupplyAt previous)

def offsets (profile : Profile Previous Residual) :
    Query Previous fun previous =>
      Core.Finite.Enumeration
        (profile.registration.Offset (profile.residualQuery previous)) :=
  profile.residualQuery.dependentMap fun previous residual =>
    profile.registration.offsets residual (profile.independentRankAt previous)
      (profile.finiteBarrierSummaryAt previous) (profile.localSupplyAt previous)

def scales (profile : Profile Previous Residual) :
    Query Previous fun _ => Core.Finite.Enumeration Nat :=
  profile.residualQuery.map fun previous residual =>
    profile.registration.scales residual (profile.independentRankAt previous)
      (profile.finiteBarrierSummaryAt previous) (profile.localSupplyAt previous)

def selectedScale (profile : Profile Previous Residual) :
    Query Previous fun _ => Nat :=
  profile.residualQuery.map fun previous residual =>
    profile.registration.selectedScale residual
      (profile.independentRankAt previous)
      (profile.finiteBarrierSummaryAt previous) (profile.localSupplyAt previous)

def positions (profile : Profile Previous Residual) (scale : Nat) :
    Query Previous fun previous =>
      Core.Finite.Enumeration
        (profile.registration.Position
          (profile.residualQuery previous) scale) :=
  profile.residualQuery.dependentMap fun previous residual =>
    profile.registration.positions residual
      (profile.independentRankAt previous)
      (profile.finiteBarrierSummaryAt previous) (profile.localSupplyAt previous)
      scale

def finiteScaleLimit (profile : Profile Previous Residual) :
    Query Previous fun _ => Nat :=
  profile.residualQuery.map fun previous residual =>
    profile.registration.finiteScaleLimit residual
      (profile.independentRankAt previous)
      (profile.finiteBarrierSummaryAt previous) (profile.localSupplyAt previous)

/-- CT17 specification from primitive residual observations only. -/
def stateSpec (profile : Profile Previous Residual) :
    CT17.Spec Previous where
  Target := fun previous =>
    profile.registration.Target (profile.residualQuery previous)
  Offset := fun previous =>
    profile.registration.Offset (profile.residualQuery previous)
  Position := fun previous scale =>
    profile.registration.Position
      (profile.residualQuery previous) scale
  Value := fun previous =>
    profile.registration.Value (profile.residualQuery previous)
  targetValue := fun previous target =>
    profile.registration.targetValue
      (profile.residualQuery previous)
      (profile.independentRankAt previous)
      (profile.finiteBarrierSummaryAt previous) (profile.localSupplyAt previous)
      target
  blockValue := fun previous scale position offset =>
    profile.registration.blockValue
      (profile.residualQuery previous)
      (profile.independentRankAt previous)
      (profile.finiteBarrierSummaryAt previous) (profile.localSupplyAt previous)
      scale position offset
  orbitValue := fun previous scale offset =>
    profile.registration.orbitValue
      (profile.residualQuery previous)
      (profile.independentRankAt previous)
      (profile.finiteBarrierSummaryAt previous) (profile.localSupplyAt previous)
      scale offset
  Compatible := fun previous target offset =>
    profile.registration.Compatible
      (profile.residualQuery previous) target offset

/-- CT17 capability built from the official query projections. -/
def stateCapability (profile : Profile Previous Residual) :
    CT17.Capability profile.stateSpec where
  targets := profile.targets
  offsets := profile.offsets
  scales := profile.scales
  selectedScale := profile.selectedScale
  selectedScale_mem := fun previous =>
    profile.registration.selectedScale_mem
      (profile.residualQuery previous)
      (profile.independentRankAt previous)
      (profile.finiteBarrierSummaryAt previous) (profile.localSupplyAt previous)
  positions := profile.positions
  finiteScaleLimit := profile.finiteScaleLimit
  compatibleDecidable := fun previous target offset =>
    profile.registration.compatibleDecidable
      (profile.residualQuery previous) target offset
  valueDecidableEq := fun previous =>
    profile.registration.valueDecidableEq
      (profile.residualQuery previous)
  inputSize := fun previous =>
    CT17.localCheckBound
      (profile.targets previous)
      (profile.offsets previous)
      ((profile.positions (profile.selectedScale previous)) previous)
  workCoefficient := Fintype.card Unit
  workDegree := Fintype.card Unit
  workBound := by
    intro previous
    simp only [Fintype.card_unit, Nat.pow_one, Nat.one_mul]
    exact Nat.le_succ _

noncomputable def stateExecution (profile : Profile Previous Residual) :
    CTExecution Previous :=
  CTAdapters.ct17 profile.stateCapability

/-- Literal ledger stage after CT17. -/
abbrev AfterState (profile : Profile Previous Residual) :=
  Ledger.Extension Previous profile.stateExecution.Output

/-- Exact CT17 output at the newest ledger entry. -/
def stateResult (profile : Profile Previous Residual) :
    Query profile.AfterState fun stage =>
      profile.stateExecution.Output stage.previous :=
  Query.latest

/-- CT14's schedule is projected at CT17's exact result stage. -/
def capacityMembers (profile : Profile Previous Residual) :
    Query profile.AfterState fun stage =>
      let result := profile.stateResult stage
      Core.Finite.Enumeration
        (profile.stateSpec.Position result.stage.previous
          (profile.stateCapability.scaleAt result.stage.previous)) :=
  profile.stateResult.dependentMap fun _stage result =>
    match terminalEq : result.terminal with
    | .incompatibility =>
        match terminalEq ▸ result.outcome with
        | .incompatibility _ =>
            letI :=
              (profile.stateCapability.positionsAt result.stage.previous).decEq
            Core.Finite.Enumeration.empty _
    | .exhausted =>
        match terminalEq ▸ result.outcome with
        | .exhausted _ _ _ =>
            letI :=
              (profile.stateCapability.positionsAt result.stage.previous).decEq
            Core.Finite.Enumeration.empty _
    | .survivors =>
        match terminalEq ▸ result.outcome with
        | .survivors _compatible _finite residual =>
            letI :=
              (profile.stateCapability.positionsAt result.stage.previous).decEq
            Core.Finite.Enumeration.ofNodupList
              residual.enumeration.survivors residual.enumeration.nodup
    | .targetHit =>
        match terminalEq ▸ result.outcome with
        | .targetHit _ _ _ =>
            letI :=
              (profile.stateCapability.positionsAt result.stage.previous).decEq
            Core.Finite.Enumeration.empty _
    | .orbit =>
        match terminalEq ▸ result.outcome with
        | .orbit _ _ _ =>
            letI :=
              (profile.stateCapability.positionsAt result.stage.previous).decEq
            Core.Finite.Enumeration.empty _

/-- CT14 primitive semantics over the preserved residual. -/
def capacitySpec (profile : Profile Previous Residual) :
    CT14.Spec profile.AfterState where
  Member := fun stage =>
    let result := profile.stateResult stage
    profile.stateSpec.Position result.stage.previous
      (profile.stateCapability.scaleAt result.stage.previous)
  Label := fun stage =>
    let result := profile.stateResult stage
    profile.registration.Label
      (profile.residualQuery result.stage.previous)
  memberLowerMass := fun stage member =>
    let result := profile.stateResult stage
    profile.registration.memberLowerMass
      (profile.residualQuery result.stage.previous)
      (profile.independentRankAt result.stage.previous)
      (profile.finiteBarrierSummaryAt result.stage.previous)
      (profile.localSupplyAt result.stage.previous) member
  memberCapacity := fun stage member =>
    let result := profile.stateResult stage
    profile.registration.memberCapacity
      (profile.residualQuery result.stage.previous)
      (profile.independentRankAt result.stage.previous)
      (profile.finiteBarrierSummaryAt result.stage.previous)
      (profile.localSupplyAt result.stage.previous) member
  memberLabel := fun stage member =>
    let result := profile.stateResult stage
    profile.registration.memberLabel
      (profile.residualQuery result.stage.previous)
      (profile.independentRankAt result.stage.previous)
      (profile.finiteBarrierSummaryAt result.stage.previous)
      (profile.localSupplyAt result.stage.previous) member

def capacityCapability (profile : Profile Previous Residual) :
    CT14.Capability profile.capacitySpec where
  members := profile.capacityMembers
  labelDecidableEq := fun stage =>
    let result := profile.stateResult stage
    profile.registration.labelDecidableEq
      (profile.residualQuery result.stage.previous)
  inputSize := fun stage =>
    CT14.localCheckBound (profile.capacityMembers stage)
  workCoefficient := Fintype.card Unit
  workDegree := Fintype.card Unit
  workBound := by
    intro stage
    simp only [Fintype.card_unit, Nat.pow_one, Nat.one_mul]
    exact Nat.le_succ _

/-- The prescribed and only Strategy execution. -/
noncomputable def execution (profile : Profile Previous Residual) :
    CTExecution Previous :=
  (CTAdapters.ct17 profile.stateCapability).compose
    (CTAdapters.ct14 profile.capacityCapability)

/-- The exact realized-state count at the literal predecessor.  The domain
registers a finite carrier, never a numerical surrogate. -/
noncomputable def realizedStateCount (profile : Profile Previous Residual) :
    Query Previous fun _ => Nat :=
  profile.residualQuery.map fun previous _residual => by
    letI := profile.registration.realizedStateFinite
      (profile.residualQuery previous)
      (profile.complementAt previous)
      (profile.independentRankAt previous)
      (profile.finiteBarrierSummaryAt previous)
      (profile.localSupplyAt previous)
    exact Nat.card (profile.registration.RealizedState
      (profile.residualQuery previous)
      (profile.complementAt previous)
      (profile.independentRankAt previous)
      (profile.finiteBarrierSummaryAt previous)
      (profile.localSupplyAt previous))

def ambientOrder (profile : Profile Previous Residual) :
    Query Previous fun _ => Nat :=
  profile.residualQuery.map fun previous _residual =>
    profile.registration.ambientOrder (profile.residualQuery previous)
      (profile.complementAt previous)
      (profile.independentRankAt previous)
      (profile.finiteBarrierSummaryAt previous) (profile.localSupplyAt previous)

def remainderCard (profile : Profile Previous Residual) :
    Query Previous fun _ => Nat :=
  profile.residualQuery.map fun previous _residual =>
    profile.registration.remainderCard (profile.residualQuery previous)
      (profile.complementAt previous)
      (profile.independentRankAt previous)
      (profile.finiteBarrierSummaryAt previous) (profile.localSupplyAt previous)

def statePowerExponent (profile : Profile Previous Residual) :
    Query Previous fun _ => Nat :=
  profile.residualQuery.map fun previous residual =>
    profile.registration.statePowerExponent residual
      (profile.independentRankAt previous)
      (profile.finiteBarrierSummaryAt previous) (profile.localSupplyAt previous)

/-- Exact natural-power state-count split, computed from the literal residual
and Core's cardinality of the registered realized-state carrier. -/
noncomputable def statePowerProfile (profile : Profile Previous Residual) :
    Query Previous fun _ => Core.OrderThresholdSplit.Profile Nat :=
  profile.ambientOrder.and
      (profile.remainderCard.and
        (profile.realizedStateCount.and profile.statePowerExponent))
    |>.map fun _ inputs =>
      { threshold := inputs.fst ^ inputs.snd.fst
        value := inputs.snd.snd.fst ^ inputs.snd.snd.snd }

abbrev StatePowerAtLeast (profile : Profile Previous Residual)
    (previous : Previous) : Prop :=
  (profile.statePowerProfile previous).threshold ≤
    (profile.statePowerProfile previous).value

abbrev StatePowerBelow (profile : Profile Previous Residual)
    (previous : Previous) : Prop :=
  (profile.statePowerProfile previous).value <
    (profile.statePowerProfile previous).threshold

inductive StatePowerResidual (profile : Profile Previous Residual)
    (previous : Previous) where
  | atLeast (selected : profile.StatePowerAtLeast previous)
      (remainderBits :
        ((profile.remainderCard previous : ℝ) /
          profile.statePowerExponent previous) *
            Real.logb 2 (profile.ambientOrder previous) ≤
          Real.logb 2 (profile.realizedStateCount previous))
  | below (selected : profile.StatePowerBelow previous)

noncomputable def statePowerResidual (profile : Profile Previous Residual)
    (previous : Previous) : profile.StatePowerResidual previous := by
  let ambient := profile.ambientOrder previous
  let remainder := profile.remainderCard previous
  let states := profile.realizedStateCount previous
  let power := profile.statePowerExponent previous
  have powerPositive : 0 < power :=
    profile.registration.statePowerExponent_pos
      (profile.residualQuery previous)
      (profile.independentRankAt previous)
      (profile.finiteBarrierSummaryAt previous)
      (profile.localSupplyAt previous)
  have statePositive : 0 < states := by
    dsimp [states, realizedStateCount]
    letI := profile.registration.realizedStateFinite
      (profile.residualQuery previous)
      (profile.complementAt previous)
      (profile.independentRankAt previous)
      (profile.finiteBarrierSummaryAt previous)
      (profile.localSupplyAt previous)
    letI := profile.registration.realizedStateNonempty
      (profile.residualQuery previous)
      (profile.complementAt previous)
      (profile.independentRankAt previous)
      (profile.finiteBarrierSummaryAt previous)
      (profile.localSupplyAt previous)
    exact Nat.card_pos
  let split := (profile.statePowerProfile previous).run
  match split with
  | .high selected =>
      exact StatePowerResidual.atLeast selected (by
        change ((remainder : ℝ) / power) * Real.logb 2 ambient ≤
          Real.logb 2 states
        by_cases ambientZero : ambient = 0
        · -- `Real.logb 2 0 = 0` kills the whole left-hand side, so the goal is
          -- exactly the nonnegativity of the realized-state logarithm.
          have logStatesNonnegative : 0 ≤ Real.logb 2 states := by
            apply Real.logb_nonneg (by norm_num)
            exact_mod_cast statePositive
          simp [ambientZero, logStatesNonnegative]
        · have ambientPositive : 0 < ambient := Nat.pos_of_ne_zero ambientZero
          have powered : ambient ^ remainder ≤ states ^ power := by
            simpa [statePowerProfile, ambientOrder, remainderCard,
              realizedStateCount, statePowerExponent, ambient, remainder,
              states, power] using selected
          have poweredReal : (ambient : ℝ) ^ remainder ≤ (states : ℝ) ^ power := by
            have castPowered :
                ((ambient ^ remainder : ℕ) : ℝ) ≤
                  ((states ^ power : ℕ) : ℝ) := by
              exact_mod_cast powered
            simpa only [Nat.cast_pow] using castPowered
          have logged := (Real.logb_le_logb (show (1 : ℝ) < 2 by norm_num)
            (pow_pos (by exact_mod_cast ambientPositive) remainder)
            (pow_pos (by exact_mod_cast statePositive) power)).2 poweredReal
          rw [Real.logb_pow, Real.logb_pow] at logged
          have powerRealPositive : (0 : ℝ) < power := by exact_mod_cast powerPositive
          rw [div_mul_eq_mul_div]
          apply (div_le_iff₀ powerRealPositive).2
          nlinarith)
  | .low selected => exact StatePowerResidual.below selected

/-- Logarithmic joint budget from the literal state count, remainder
contribution, and finite powered-capacity presentation. -/
def JointBudget (profile : Profile Previous Residual) (previous : Previous) : Prop :=
  let residual := profile.residualQuery previous
  let rank := profile.independentRankAt previous
  let barrier := profile.finiteBarrierSummaryAt previous
  let supply := profile.localSupplyAt previous
  let exponent := profile.registration.jointExponent residual rank barrier supply
  let desired := profile.registration.jointDesiredExponent residual rank barrier supply
  let error := profile.registration.jointErrorExponent residual rank barrier supply
  let capacity := profile.registration.jointCapacity residual rank barrier supply
  (exponent : ℝ) *
      (((profile.remainderCard previous : ℝ) /
        profile.statePowerExponent previous) *
        Real.logb 2 (profile.ambientOrder previous)) + desired ≤
    (exponent : ℝ) * Real.logb 2 capacity + error

/-- Compute the joint budget by logarithmically normalizing the registered
finite-capacity inequality and adding the exact state-count contribution. -/
noncomputable def jointBudget (profile : Profile Previous Residual)
    (previous : Previous)
    (remainderBits :
      ((profile.remainderCard previous : ℝ) /
        profile.statePowerExponent previous) *
          Real.logb 2 (profile.ambientOrder previous) ≤
        Real.logb 2 (profile.realizedStateCount previous)) :
    profile.JointBudget previous := by
  let residual := profile.residualQuery previous
  let complement := profile.complementAt previous
  let rank := profile.independentRankAt previous
  let barrier := profile.finiteBarrierSummaryAt previous
  let supply := profile.localSupplyAt previous
  let states := profile.realizedStateCount previous
  let joint :=
    profile.registration.jointProfile residual complement rank barrier supply
  let exponent := profile.registration.jointExponent residual rank barrier supply
  let paid := profile.registration.jointPaidExponent residual rank barrier supply
  let desired := profile.registration.jointDesiredExponent residual rank barrier supply
  let error := profile.registration.jointErrorExponent residual rank barrier supply
  let capacity := profile.registration.jointCapacity residual rank barrier supply
  have statesPositive : 0 < states := by
    dsimp [states, realizedStateCount]
    letI := profile.registration.realizedStateFinite residual complement rank
      barrier supply
    letI := profile.registration.realizedStateNonempty residual complement rank
      barrier supply
    exact Nat.card_pos
  have capacityPositive : 0 < capacity :=
    profile.registration.jointCapacity_pos residual rank barrier supply
  have paidCapacity :
      states ^ exponent * 2 ^ paid ≤ capacity ^ exponent := by
    have powered :=
      joint.base_pow_mul_base_pow_sumWeight_le_codeCard_pow
        2 exponent
        (profile.registration.jointWeight residual complement rank barrier supply)
        (profile.registration.jointLocalLower residual complement rank barrier
          supply)
    rw [profile.registration.jointBaseCard residual complement rank barrier supply,
      profile.registration.jointPaidExponent_exact
        residual complement rank barrier supply] at powered
    exact powered.trans
      (Nat.pow_le_pow_left
        (profile.registration.jointCodeCapacity
          residual complement rank barrier supply) exponent)
  have finiteCapacity : states ^ exponent * 2 ^ desired ≤
      capacity ^ exponent * 2 ^ error := by
    have desiredExact : desired = paid + error := by
      exact profile.registration.jointDesiredExponent_exact
        residual rank barrier supply
    rw [desiredExact, pow_add, ← Nat.mul_assoc]
    exact Nat.mul_le_mul_right (2 ^ error) paidCapacity
  have finiteCapacityReal : (states : ℝ) ^ exponent * 2 ^ desired ≤
      (capacity : ℝ) ^ exponent * 2 ^ error := by
    exact_mod_cast finiteCapacity
  have logged := (Real.logb_le_logb (show (1 : ℝ) < 2 by norm_num)
    (mul_pos (pow_pos (by exact_mod_cast statesPositive) exponent)
      (pow_pos (by norm_num) desired))
    (mul_pos (pow_pos (by exact_mod_cast capacityPositive) exponent)
      (pow_pos (by norm_num) error))).2 finiteCapacityReal
  rw [Real.logb_mul
    (ne_of_gt (pow_pos (by exact_mod_cast statesPositive) exponent))
    (ne_of_gt (pow_pos (by norm_num) desired)),
    Real.logb_mul
      (ne_of_gt (pow_pos (by exact_mod_cast capacityPositive) exponent))
      (ne_of_gt (pow_pos (by norm_num) error)),
    Real.logb_pow, Real.logb_pow, Real.logb_pow, Real.logb_pow] at logged
  norm_num at logged
  have scaled := mul_le_mul_of_nonneg_left remainderBits
    (show (0 : ℝ) ≤ exponent by positivity)
  dsimp [JointBudget, residual, rank, barrier, supply, exponent, desired,
    error, capacity]
  linarith

/-- Terminal certificate on the state-power-at-least alternative. The
terminal consumes the exact joint budget and excludes its literal negation,
matching the normalized budget-reversal terminalization. -/
structure JointCapacityTerminal (profile : Profile Previous Residual)
    (previous : Previous) where
  private mk ::
  statePower : profile.StatePowerAtLeast previous
  jointBudget : profile.JointBudget previous
  highBudgetImpossible : ¬ (¬ profile.JointBudget previous)

/-- Exact normalized-budget reversal terminal used on the state-power-at-least
branch. This is the framework-native translation of the original high branch:
the stored non-strict joint budget excludes its literal negation. -/
noncomputable def jointCapacityTerminal
    (profile : Profile Previous Residual) (previous : Previous)
    (statePower : profile.StatePowerAtLeast previous)
    (remainderBits :
      ((profile.remainderCard previous : ℝ) /
        profile.statePowerExponent previous) *
          Real.logb 2 (profile.ambientOrder previous) ≤
        Real.logb 2 (profile.realizedStateCount previous)) :
    profile.JointCapacityTerminal previous :=
  let budget := profile.jointBudget previous remainderBits
  JointCapacityTerminal.mk statePower budget (not_not_intro budget)

/-- First residual-owned power, using the independent-rank ledger exponent. -/
def forcedPower (profile : Profile Previous Residual) :
    Query Previous fun _ => Nat :=
  profile.residualQuery.map fun previous residual =>
    profile.registration.forcedBase residual
      (profile.independentRankAt previous)
      (profile.finiteBarrierSummaryAt previous)
      (profile.localSupplyAt previous) ^ profile.independentRankAt previous

/-- Comparison power from the same literal predecessor. -/
def flatPower (profile : Profile Previous Residual) :
    Query Previous fun _ => Nat :=
  profile.residualQuery.map fun previous residual =>
    profile.registration.flatBase residual
      (profile.independentRankAt previous)
      (profile.finiteBarrierSummaryAt previous)
      (profile.localSupplyAt previous) ^ profile.independentRankAt previous

/-- Exhaustive comparison of the two residual-owned powered quantities. -/
def residualPowerProfile (profile : Profile Previous Residual) :
    Query Previous fun _ => Core.OrderThresholdSplit.Profile Nat :=
  profile.forcedPower.and
      (profile.flatPower.and
        (profile.ambientOrder.and
          (profile.remainderCard.and profile.statePowerExponent)))
    |>.map fun _ inputs =>
      { threshold :=
          inputs.snd.fst ^ inputs.snd.snd.snd.snd *
            inputs.snd.snd.fst ^ inputs.snd.snd.snd.fst
        value := inputs.fst ^ inputs.snd.snd.snd.snd }

abbrev ResidualPowerAtLeast (profile : Profile Previous Residual)
    (previous : Previous) : Prop :=
  (profile.residualPowerProfile previous).threshold ≤
    (profile.residualPowerProfile previous).value

abbrev ResidualPowerBelow (profile : Profile Previous Residual)
    (previous : Previous) : Prop :=
  (profile.residualPowerProfile previous).value <
    (profile.residualPowerProfile previous).threshold

/-- Product-fit guard on the at-least power alternative. -/
abbrev ProductFit (profile : Profile Previous Residual) (previous : Previous) : Prop :=
  profile.forcedPower previous ≤
    profile.flatPower previous * profile.realizedStateCount previous

/-- Product fit and a below-threshold state count contradict the at-least
residual-power alternative. -/
theorem productFit_atLeast_impossible (profile : Profile Previous Residual)
    (previous : Previous) (statePower : profile.StatePowerBelow previous)
    (atLeast : profile.ResidualPowerAtLeast previous)
    (fit : profile.ProductFit previous) : False := by
  let forced := profile.forcedPower previous
  let flat := profile.flatPower previous
  let states := profile.realizedStateCount previous
  let upper := profile.ambientOrder previous ^ profile.remainderCard previous
  let exponent := profile.statePowerExponent previous
  have flatPositive : 0 < flat := by
    dsimp [flat, flatPower]
    exact Nat.pow_pos (profile.registration.flatBase_pos
      (profile.residualQuery previous)
      (profile.independentRankAt previous)
      (profile.finiteBarrierSummaryAt previous)
      (profile.localSupplyAt previous))
  have statePowerBelow : states ^ exponent < upper := by
    simpa [StatePowerBelow, statePowerProfile, ambientOrder, remainderCard,
      statePowerExponent, realizedStateCount, states, upper, exponent] using statePower
  have strictLarge : forced ^ exponent < flat ^ exponent * upper := by
    exact _root_.Hypostructure.Core.ArithmeticTransport.PoweredTransfer.forced_pow_lt_flat_pow_mul_upper_of
      fit statePowerBelow flatPositive
  have atLeast' : flat ^ exponent * upper ≤ forced ^ exponent := by
    simpa [ResidualPowerAtLeast, residualPowerProfile, forcedPower, flatPower,
      ambientOrder, remainderCard, statePowerExponent, forced, flat, upper,
      exponent] using atLeast
  exact (Nat.not_le_of_lt strictLarge) atLeast'

/-- Scaled deficiency cap derived from the exact local-supply summary already
read from the predecessor ledger. -/
structure ScaledDeficiencyCap (profile : Profile Previous Residual)
    (previous : Previous) where
  finiteCap :
    (profile.localSupplyAt previous).netDeficiency.scale *
        (profile.localSupplyAt previous).netDeficiency.deficiency ≤
      (profile.localSupplyAt previous).netDeficiency.coefficient *
          (profile.localSupplyAt previous).netDeficiency.remainder +
        (profile.localSupplyAt previous).netDeficiency.scale *
          (profile.localSupplyAt previous).netDeficiency.surplus
  realCap :
    ((profile.localSupplyAt previous).netDeficiency.deficiency : ℝ) ≤
      ((profile.localSupplyAt previous).netDeficiency.coefficient : ℝ) /
          (profile.localSupplyAt previous).netDeficiency.scale *
        (profile.localSupplyAt previous).netDeficiency.remainder +
      (profile.localSupplyAt previous).netDeficiency.surplus

noncomputable def scaledDeficiencyCap (profile : Profile Previous Residual)
    (previous : Previous) : profile.ScaledDeficiencyCap previous := by
  let supply := profile.localSupplyAt previous
  let accounting := supply.netDeficiency
  let scale := accounting.scale
  let coefficient := accounting.coefficient
  let deficiency := accounting.deficiency
  let surplus := accounting.surplus
  let remainder := accounting.remainder
  have scalePositive : 0 < scale := accounting.scale_pos
  have finiteCap : scale * deficiency ≤ coefficient * remainder + scale * surplus :=
    accounting.finiteCap
  have finiteCapReal : (scale : ℝ) * deficiency ≤
      coefficient * remainder + scale * surplus := by
    exact_mod_cast finiteCap
  have divided := div_le_div_of_nonneg_right finiteCapReal
    (by exact_mod_cast scalePositive.le : (0 : ℝ) ≤ scale)
  refine {
    finiteCap := by
      simpa [supply, accounting, scale,
        coefficient, deficiency, surplus, remainder] using finiteCap,
    realCap := ?_ }
  calc
    (deficiency : ℝ) = ((scale : ℝ) * deficiency) / scale := by
      field_simp [ne_of_gt (by exact_mod_cast scalePositive : (0 : ℝ) < scale)]
    _ ≤ (coefficient * remainder + scale * surplus) / scale := divided
    _ = (coefficient : ℝ) / scale * remainder + surplus := by
      field_simp [ne_of_gt (by exact_mod_cast scalePositive : (0 : ℝ) < scale)]

/-- Live below-threshold power continuation with its derived scaled-deficiency
cap. -/
structure ResidualPowerBelowContinuation (profile : Profile Previous Residual)
    (previous : Previous) where
  statePower : profile.StatePowerBelow previous
  residualPower : profile.ResidualPowerBelow previous
  deficiency : profile.ScaledDeficiencyCap previous

noncomputable def residualPowerBelowContinuation
    (profile : Profile Previous Residual)
    (previous : Previous) (statePower : profile.StatePowerBelow previous)
    (residualPower : profile.ResidualPowerBelow previous) :
    profile.ResidualPowerBelowContinuation previous :=
  ⟨statePower, residualPower, profile.scaledDeficiencyCap previous⟩

/-- Exhaustive capacity outcome after the state and residual-power
comparisons. Every constructor carries the exact derived facts for that
alternative; none is reclassified as target closure. -/
inductive CapacityOutcome (profile : Profile Previous Residual)
    (previous : Previous) where
  | jointTerminal (terminal : profile.JointCapacityTerminal previous)
  | fitFailure (statePower : profile.StatePowerBelow previous)
      (residualPower : profile.ResidualPowerAtLeast previous)
      (fitFailed : ¬ profile.ProductFit previous)
  | below (residual : profile.ResidualPowerBelowContinuation previous)

noncomputable def capacityOutcome (profile : Profile Previous Residual)
    (previous : Previous) : profile.CapacityOutcome previous :=
  match profile.statePowerResidual previous with
  | .atLeast atLeast remainderBits =>
      .jointTerminal
        (profile.jointCapacityTerminal previous atLeast remainderBits)
  | .below below =>
      match (profile.residualPowerProfile previous).run with
      | .high atLeast =>
          if fit : profile.ProductFit previous then
            False.elim
              (profile.productFit_atLeast_impossible previous below atLeast fit)
          else .fitFailure below atLeast fit
      | .low residualPower =>
          .below
            (profile.residualPowerBelowContinuation
              previous below residualPower)

/-- Every non-capacity alternative retains the complete composed CT output. -/
inductive NonCapacityResidual
    (profile : Profile Previous Residual) (previous : Previous) where
  | incompatibility
      (output : profile.execution.Output previous)
      (selected : output.fst.terminal = .incompatibility)
  | exhausted
      (output : profile.execution.Output previous)
      (selected : output.fst.terminal = .exhausted)
  | targetHit
      (output : profile.execution.Output previous)
      (selected : output.fst.terminal = .targetHit)
  | orbit
      (output : profile.execution.Output previous)
      (selected : output.fst.terminal = .orbit)
  | unboundedMember
      (output : profile.execution.Output previous)
      (stateSelected : output.fst.terminal = .survivors)
      (selected : output.snd.terminal = .unboundedMember)
  | missingLabel
      (output : profile.execution.Output previous)
      (stateSelected : output.fst.terminal = .survivors)
      (selected : output.snd.terminal = .missingLabel)
  | aggregate
      (output : profile.execution.Output previous)
      (stateSelected : output.fst.terminal = .survivors)
      (selected : output.snd.terminal = .aggregate)

/-- The registered non-capacity closure, read off the registration.  Core owns
the whole derivation below; the registration only states facts about data it
already carries. -/
abbrev NonCapacityClosure (profile : Profile Previous Residual) : Prop :=
  (∀ (residual : Residual)
      (target : profile.registration.Target residual)
      (offset : profile.registration.Offset residual),
    profile.registration.Compatible residual target offset) ∧
  (∀ residual rank barrier supply,
    profile.registration.selectedScale residual rank barrier supply ≤
      profile.registration.finiteScaleLimit residual rank barrier supply) ∧
  (∀ residual rank barrier supply,
    0 < (profile.registration.positions residual rank barrier supply
      (profile.registration.selectedScale residual rank barrier supply)).card) ∧
  (∀ residual rank barrier supply (scale : Nat)
      (position : profile.registration.Position residual scale)
      (offset : profile.registration.Offset residual)
      (target : profile.registration.Target residual),
    profile.registration.blockValue residual rank barrier supply scale
        position offset ≠
      profile.registration.targetValue residual rank barrier supply target) ∧
  (∀ residual rank barrier supply position,
    profile.registration.memberCapacity residual rank barrier supply
      position ≠ none) ∧
  (∀ residual rank barrier supply position,
    profile.registration.memberLabel residual rank barrier supply
      position ≠ none) ∧
  (∀ residual rank barrier supply position,
    profile.registration.memberLowerMass residual rank barrier supply
        position ≤
      (profile.registration.memberCapacity residual rank barrier supply
        position).getD 0)

/-- The registered closure, as stored on the registration, is exactly the
Core-side statement above. -/
def nonCapacityClosureOfRegistration (profile : Profile Previous Residual) :
    Option (PLift profile.NonCapacityClosure) :=
  profile.registration.nonCapacityImpossible

/-- CT17 never reaches its incompatibility terminal under the registered
closure: the incompatibility evidence exhibits a scheduled pair that the
registration proves compatible. -/
theorem state_not_incompatibility (profile : Profile Previous Residual)
    (closure : profile.NonCapacityClosure)
    (result : CT17.ExecutionResult profile.stateSpec profile.stateCapability) :
    result.terminal ≠ .incompatibility := by
  intro selected
  have outcome : CT17.Outcome profile.stateCapability
      result.stage.previous .incompatibility := selected ▸ result.outcome
  cases outcome with
  | incompatibility residual =>
      exact residual.sound (closure.1 _ _ _)

/-- CT17 never leaves the finite-scale regime under the registered closure. -/
theorem state_scale_finite (profile : Profile Previous Residual)
    (closure : profile.NonCapacityClosure) (previous : Previous) :
    ¬ CT17.OrbitScaleState profile.stateCapability previous := by
  intro orbitScale
  exact absurd orbitScale.large (Nat.not_lt.mpr (closure.2.1 _ _ _ _))

theorem state_not_targetHit (profile : Profile Previous Residual)
    (closure : profile.NonCapacityClosure)
    (result : CT17.ExecutionResult profile.stateSpec profile.stateCapability) :
    result.terminal ≠ .targetHit := by
  intro selected
  have outcome : CT17.Outcome profile.stateCapability
      result.stage.previous .targetHit := selected ▸ result.outcome
  cases outcome with
  | targetHit _ orbitScale _ =>
      exact profile.state_scale_finite closure _ orbitScale

theorem state_not_orbit (profile : Profile Previous Residual)
    (closure : profile.NonCapacityClosure)
    (result : CT17.ExecutionResult profile.stateSpec profile.stateCapability) :
    result.terminal ≠ .orbit := by
  intro selected
  have outcome : CT17.Outcome profile.stateCapability
      result.stage.previous .orbit := selected ▸ result.outcome
  cases outcome with
  | orbit _ orbitScale _ =>
      exact profile.state_scale_finite closure _ orbitScale

/-- Under the registered closure every scheduled position survives: no
registered block value ever equals a registered target value. -/
theorem state_survives (profile : Profile Previous Residual)
    (closure : profile.NonCapacityClosure) (previous : Previous)
    (position : profile.stateSpec.Position previous
      (profile.stateCapability.scaleAt previous)) :
    CT17.Survives profile.stateCapability previous position := by
  intro index
  exact closure.2.2.2.1 _ _ _ _ _ _ _ _

theorem state_not_exhausted (profile : Profile Previous Residual)
    (closure : profile.NonCapacityClosure)
    (result : CT17.ExecutionResult profile.stateSpec profile.stateCapability) :
    result.terminal ≠ .exhausted := by
  intro selected
  have outcome : CT17.Outcome profile.stateCapability
      result.stage.previous .exhausted := selected ▸ result.outcome
  cases outcome with
  | exhausted _ _ certificate =>
      have positive :
          0 < (profile.stateCapability.positionsAt result.stage.previous).card :=
        closure.2.2.1 _ _ _ _
      exact certificate.exhausted
        ((profile.stateCapability.positionsAt result.stage.previous).get
          ⟨0, positive⟩)
        (Core.Finite.Enumeration.get_mem _ _)
        (profile.state_survives closure _ _)

/-- CT17's only remaining terminal under the registered closure. -/
theorem state_terminal_survivors (profile : Profile Previous Residual)
    (closure : profile.NonCapacityClosure)
    (result : CT17.ExecutionResult profile.stateSpec profile.stateCapability) :
    result.terminal = .survivors := by
  rcases CT17.outcome_exhaustive result with
    h | h | h | h | h
  · exact absurd h (profile.state_not_incompatibility closure result)
  · exact absurd h (profile.state_not_exhausted closure result)
  · exact h
  · exact absurd h (profile.state_not_targetHit closure result)
  · exact absurd h (profile.state_not_orbit closure result)

theorem capacity_not_unboundedMember (profile : Profile Previous Residual)
    (closure : profile.NonCapacityClosure)
    (result :
      CT14.ExecutionResult profile.capacitySpec profile.capacityCapability) :
    result.terminal ≠ .unboundedMember := by
  intro selected
  have outcome : CT14.Outcome profile.capacityCapability
      result.stage.previous .unboundedMember := selected ▸ result.outcome
  cases outcome with
  | unboundedMember _ residual =>
      exact closure.2.2.2.2.1 _ _ _ _ _ residual.sound

theorem capacity_not_missingLabel (profile : Profile Previous Residual)
    (closure : profile.NonCapacityClosure)
    (result :
      CT14.ExecutionResult profile.capacitySpec profile.capacityCapability) :
    result.terminal ≠ .missingLabel := by
  intro selected
  have outcome : CT14.Outcome profile.capacityCapability
      result.stage.previous .missingLabel := selected ▸ result.outcome
  cases outcome with
  | missingLabel _ _ residual =>
      exact closure.2.2.2.2.2.1 _ _ _ _ _ residual.sound

theorem capacity_not_aggregate (profile : Profile Previous Residual)
    (closure : profile.NonCapacityClosure)
    (result :
      CT14.ExecutionResult profile.capacitySpec profile.capacityCapability) :
    result.terminal ≠ .aggregate := by
  intro selected
  have outcome : CT14.Outcome profile.capacityCapability
      result.stage.previous .aggregate := selected ▸ result.outcome
  cases outcome with
  | aggregate ledger certificate =>
      have fits :
          CT14.lowerMass profile.capacityCapability result.stage.previous ≤
            CT14.upperCapacity profile.capacityCapability
              result.stage.previous := by
        simp only [CT14.lowerMass, CT14.upperCapacity, CT14.lowerMassEntries,
          CT14.capacityEntries, List.map_map, Function.comp_def]
        refine List.sum_le_sum ?_
        intro member _
        exact closure.2.2.2.2.2.2 _ _ _ _ member
      have exceeds : ledger.capacity.total < ledger.lower.total := certificate
      rw [ledger.capacity.total_exact, ledger.lower.total_exact] at exceeds
      exact absurd fits (Nat.not_le.mpr exceeds)

/-- Every non-capacity alternative is impossible under the registered
closure. -/
theorem nonCapacityResidual_false (profile : Profile Previous Residual)
    (closure : profile.NonCapacityClosure) (previous : Previous)
    (nonCapacity : profile.NonCapacityResidual previous) : False := by
  cases nonCapacity with
  | incompatibility output selected =>
      exact profile.state_not_incompatibility closure output.fst selected
  | exhausted output selected =>
      exact profile.state_not_exhausted closure output.fst selected
  | targetHit output selected =>
      exact profile.state_not_targetHit closure output.fst selected
  | orbit output selected =>
      exact profile.state_not_orbit closure output.fst selected
  | unboundedMember output _ selected =>
      exact profile.capacity_not_unboundedMember closure output.snd selected
  | missingLabel output _ selected =>
      exact profile.capacity_not_missingLabel closure output.snd selected
  | aggregate output _ selected =>
      exact profile.capacity_not_aggregate closure output.snd selected

/-! ### Why the closure carries no entropy conjunct

`prop:two-budget` does not close this branch: it *routes* it.  Its own
statement ends "in every case the surviving residual is subsequently passed
to the large-budget net-charge analysis of `prop:negative-net-charge`, with
any additional curvature cost used only when it has been established by the
preceding rank-forcing lemmas", and its proof discharges branch (c) with
"branch (c) asserts no such dominance and is simply routed forward".
`rem:closure-robust` says the same thing from the other side: "the
curvature-rank and forced-cost machinery is not required for the net-charge
closure outside the explicit residuals", which "already follows from the
window-only density bound together with the local analysis".

So the forced/flat realization `forcedBase ^ rank ≤ flatBase ^ rank * |𝒢(R)|`
is not a fact any registration owes.  Read at the ambient class it is
vacuous, and read at `def:remainder-entropy`'s complement-indexed `𝒢(R)` it
is false in general -- and demanding it uniformly over a quantified exponent
registers `forcedBase ≤ flatBase`, i.e. `c_Ω = 0`, contradicting
`cor:forced-curvature-cost`.  `Core.FiniteEntropy.le_of_forall_pow_le_pow_mul`
is the arithmetic core of that collapse, and it runs on *any* free exponent
binder, so no reshaping of the conjunct escapes it.

`NonCapacityClosure` therefore stops at the seven schedule facts, and all
three of `prop:two-budget`'s branches leave this Strategy on the capacity
side.  `ProductFit` survives only where it is genuinely decided:
`productFit_atLeast_impossible` rules out the one arithmetically impossible
combination inside `capacityOutcome`, and the failed product fit is a
surviving residual routed forward, not an alternative anyone must exclude. -/

/-- The forced power base at one literal predecessor, read off the same four
inherited values every other projection uses. -/
def forcedBaseAt (profile : Profile Previous Residual) (previous : Previous) :
    Nat :=
  profile.registration.forcedBase (profile.residualQuery previous)
    (profile.independentRankAt previous)
    (profile.finiteBarrierSummaryAt previous) (profile.localSupplyAt previous)

/-- The flat power base at one literal predecessor. -/
def flatBaseAt (profile : Profile Previous Residual) (previous : Previous) :
    Nat :=
  profile.registration.flatBase (profile.residualQuery previous)
    (profile.independentRankAt previous)
    (profile.finiteBarrierSummaryAt previous) (profile.localSupplyAt previous)

@[simp] theorem forcedPower_read (profile : Profile Previous Residual)
    (previous : Previous) :
    profile.forcedPower previous =
      profile.forcedBaseAt previous ^ profile.independentRankAt previous := rfl

@[simp] theorem flatPower_read (profile : Profile Previous Residual)
    (previous : Previous) :
    profile.flatPower previous =
      profile.flatBaseAt previous ^ profile.independentRankAt previous := rfl

/-- Exact CT17-survivor and CT14-capacity continuation.

`prop:two-budget` ends by passing the surviving residual of *every* one of its
branches to the large-budget net-charge analysis, so all three arrive here:
the high-entropy alternative (`CapacityOutcome.jointTerminal`), the
low-entropy large-budget alternative (`CapacityOutcome.below`), and the
low-entropy alternative whose product fit fails (`CapacityOutcome.fitFailure`)
-- `prop:two-budget` makes no curvature-rank claim on the last of these and
"is simply routed forward".  `NonCapacityResidual` keeps only the CT
alternatives that are not a branch of `prop:two-budget` at all.

The payload is therefore exactly the branch-independent scaled-deficiency cap:
`scaledDeficiencyCap` reads the inherited local-supply summary and nothing
else, so it is available on either alternative. -/
structure CapacityResidual
    (profile : Profile Previous Residual) (previous : Previous) where
  output : profile.execution.Output previous
  stateSelected : output.fst.terminal = .survivors
  selected : output.snd.terminal = .capacity
  continuation : profile.ScaledDeficiencyCap previous

/-- Standard Core dichotomy over one execution of the complete composition. -/
noncomputable def dichotomy (profile : Profile Previous Residual) :
    Core.Strategy.Dichotomy Previous where
  LeftPayload := profile.NonCapacityResidual
  RightPayload := profile.CapacityResidual
  classify := fun previous =>
    let output := profile.execution.run previous
    match stateSelected : output.fst.terminal with
    | .incompatibility =>
        .inl (.incompatibility output stateSelected)
    | .exhausted =>
        .inl (.exhausted output stateSelected)
    | .targetHit =>
        .inl (.targetHit output stateSelected)
    | .orbit =>
        .inl (.orbit output stateSelected)
    | .survivors =>
        match capacitySelected : output.snd.terminal with
        | .unboundedMember =>
            .inl (.unboundedMember output stateSelected capacitySelected)
        | .missingLabel =>
            .inl (.missingLabel output stateSelected capacitySelected)
        | .aggregate =>
            .inl (.aggregate output stateSelected capacitySelected)
        | .capacity =>
            match profile.capacityOutcome previous with
            | .jointTerminal _ =>
                -- `prop:two-budget`'s high-entropy branch: the joint budget is
                -- derived on this arm and the surviving residual is passed on
                -- to the large-budget net-charge analysis, exactly as the
                -- low-entropy arm below.
                .inr ⟨output, stateSelected, capacitySelected,
                  profile.scaledDeficiencyCap previous⟩
            | .fitFailure _ _ _ =>
                -- `prop:two-budget`'s nonrepetitive low-entropy branch (c):
                -- the proposition "makes no curvature-rank claim in this
                -- case; the branch is passed to the large-budget net-charge
                -- analysis".  The surviving residual carries the same
                -- branch-independent cap the other two arms carry.
                .inr ⟨output, stateSelected, capacitySelected,
                  profile.scaledDeficiencyCap previous⟩
            | .below continuation =>
                .inr ⟨output, stateSelected, capacitySelected,
                  continuation.deficiency⟩

/-- Literal ledger stage entering the non-capacity continuation. -/
abbrev NonCapacityStage (profile : Profile Previous Residual) :=
  profile.dichotomy.LeftStage

/-- Literal ledger stage entering the capacity continuation. -/
abbrev CapacityStage (profile : Profile Previous Residual) :=
  profile.dichotomy.RightStage

/-- Read the exact FSC non-capacity payload appended by Core. -/
def nonCapacityResidualQuery (profile : Profile Previous Residual) :
    Query profile.NonCapacityStage fun stage =>
      profile.NonCapacityResidual stage.previous :=
  Query.latest

/-- Read the exact FSC capacity payload appended by Core. -/
def capacityResidualQuery (profile : Profile Previous Residual) :
    Query profile.CapacityStage fun stage =>
      profile.CapacityResidual stage.previous :=
  Query.latest

/-- Exact continuation cap read from the newest FSC ledger payload. -/
def capacityContinuationQuery (profile : Profile Previous Residual) :
    Query profile.CapacityStage fun stage =>
      profile.ScaledDeficiencyCap stage.previous :=
  profile.capacityResidualQuery.map fun _ residual =>
    residual.continuation

/-! The large-budget continuation is also the paper's destination for the
low-entropy/non-capacity arm.  Its seven inherited quantities are therefore
available before the FSC classification; only the selected finite-capacity
branch receives the stronger cap carried by `capacityContinuationQuery`. -/

noncomputable def inheritedContinuationLedger
    (profile : Profile Previous Residual) :
    FiniteStateNetChargeContinuation.CapacityLedger Previous :=
  { localSupply :=  fun previous =>
      profile.localSupplyAt previous
    fullRankCertificate := profile.fullRankCertificate
    forcedPower := profile.forcedPower
    flatPower := profile.flatPower
    realizedStateCount := profile.realizedStateCount
    ambientOrder := profile.ambientOrder
    remainderCard := profile.remainderCard
    statePowerExponent := profile.statePowerExponent
    scaledDeficiency :=  fun previous =>
      (profile.scaledDeficiencyCap previous).finiteCap }

/-- Query-only interface to the exact selected capacity ledger entry. -/
noncomputable def continuationLedger
    (profile : Profile Previous Residual) :
    FiniteStateNetChargeContinuation.CapacityLedger profile.CapacityStage :=
  let continuation := profile.capacityContinuationQuery
  { localSupply := continuation.map fun stage _ =>
      profile.localSupplyAt stage.previous
    fullRankCertificate := continuation.map fun stage _ =>
      profile.fullRankCertificate stage.previous
    forcedPower := continuation.map fun stage _ =>
      profile.forcedPower stage.previous
    flatPower := continuation.map fun stage _ =>
      profile.flatPower stage.previous
    realizedStateCount := continuation.map fun stage _ =>
      profile.realizedStateCount stage.previous
    ambientOrder := continuation.map fun stage _ =>
      profile.ambientOrder stage.previous
    remainderCard := continuation.map fun stage _ =>
      profile.remainderCard stage.previous
    statePowerExponent := continuation.map fun stage _ =>
      profile.statePowerExponent stage.previous
    scaledDeficiency := continuation.map fun _ selected =>
      selected.finiteCap }


theorem capacityResidualQuery_read_extend
    (profile : Profile Previous Residual) (previous : Previous)
    (residual : profile.CapacityResidual previous) :
    profile.capacityResidualQuery (Ledger.extend previous residual) =
      residual :=
  rfl

theorem capacityContinuationQuery_read_extend
    (profile : Profile Previous Residual) (previous : Previous)
    (residual : profile.CapacityResidual previous) :
    profile.capacityContinuationQuery (Ledger.extend previous residual) =
      residual.continuation :=
  rfl

end Profile

end Hypostructure.Core.Strategy.FiniteStateCapacity
