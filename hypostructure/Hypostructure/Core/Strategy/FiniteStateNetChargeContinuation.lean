import Hypostructure.Core.OrderThresholdSplit
import Hypostructure.Core.Residual.Ledger
import Hypostructure.Core.Strategy.Execution
import Hypostructure.Core.Strategy.FiniteDensityBudgetSemantics
import Hypostructure.Core.Strategy.FiniteStateNetChargeContinuationSemantics

/-!
# Finite-state net-charge continuation

Framework-owned continuation of a selected finite-state capacity terminal.
The two inputs are exact typed capabilities published upstream on this very
branch -- the capacity ledger of `FiniteStateCapacity` and the cap ledger of
the surviving `FiniteDensityBudget` alternative; the registration contains no
mathematical result.
-/

namespace Hypostructure.Core.Strategy.FiniteStateNetChargeContinuation

open Hypostructure
open Hypostructure.Core.Residual

universe uPrevious uResidual

/-! The continuation ends at the node-[62] split.  These are live residual
terminals, not completed proof terminals: each branch keeps the literal
node-[62] ledger and every inherited query for later DAG continuations. -/

inductive Terminal where
  | typeA
  | typeB
  deriving DecidableEq, Repr

/-- Lift the compiler-owned capacity and density queries to the literal active
stage. -/
structure Profile (Previous : Type uPrevious) (Residual : Type uResidual)
    [HasResidual Previous Residual] where
  Target : Residual → Prop
  registration : Registration Residual Target
  capacity : CapacityLedger Previous
  /-- The retained cap of the surviving multiplicative density alternative.
  It is the same branch fact `prop:p13-density` is read off; the compiler
  transports it here from the `FiniteDensityBudget` node that produced it. -/
  density : FiniteDensityBudget.CapLedger Previous

namespace Profile

variable [HasResidual Previous Residual]
variable (profile : Profile Previous Residual)

abbrev DensityCap56 (previous : Previous) : Prop :=
  ∀ rate : Nat,
    2 ^ rate * (profile.density.barrierSummary previous).flatProduct ≤
        (profile.density.barrierSummary previous).safeProduct →
      0 < (profile.density.barrierSummary previous).flatProduct →
        2 ^ (rate * profile.density.packingCount previous) ≤
          profile.density.ambientCapacity previous

abbrev Stage56 :=
  Ledger.Extension Previous profile.DensityCap56

noncomputable def stage56 (previous : Previous) : profile.Stage56 :=
  Ledger.extend previous
    (fun _rate rateFloor flatPositive =>
      profile.density.two_pow_rate_mul_packingCount_le_ambientCapacity
        previous rateFloor flatPositive)

def capacity56 : CapacityLedger profile.Stage56 :=
  profile.capacity.preserveProp (Added := profile.DensityCap56)

def density56 : FiniteDensityBudget.CapLedger profile.Stage56 :=
  profile.density.preserveProp (Added := profile.DensityCap56)

abbrev RateCap56 (stage : profile.Stage56) : Prop :=
  ∀ num den windowOrder stubRate windowCount : Nat,
    0 < num → 0 < den →
    (profile.capacity56.localSupply stage).selectedCount =
        windowOrder * windowCount →
      (profile.capacity56.localSupply stage).netDeficiency.remainder +
          (profile.capacity56.localSupply stage).selectedCount =
            (profile.capacity56.localSupply stage).ambientCount →
        (den * stubRate + num * windowOrder) * windowCount <
            num * (profile.capacity56.localSupply stage).ambientCount →
          (profile.capacity56.localSupply
              stage).netDeficiency.coefficient ≤ stubRate * windowCount →
            (profile.capacity56.localSupply
                stage).netDeficiency.remainder ≤
              (profile.capacity56.localSupply
                stage).netDeficiency.scale →
              ((profile.capacity56.localSupply
                    stage).netDeficiency.coefficient : ℝ) /
                  (profile.capacity56.localSupply
                    stage).netDeficiency.scale <
                (num : ℝ) / (den : ℝ)

abbrev Stage56Rate :=
  Ledger.Extension profile.Stage56 profile.RateCap56

noncomputable def stage56Rate (previous : Previous) : profile.Stage56Rate :=
  let stage := profile.stage56 previous
  Ledger.extend stage
    (by
      intro num den windowOrder stubRate windowCount numPos denPos
        windowCover partition densityCap stubBound scaleBound
      set summary := profile.capacity56.localSupply stage with summaryEq
      -- Compare the coefficient with the residual scale at the supplied rate.
      -- The products are nonlinear, so each comparison is explicit.
      have strict : den * summary.netDeficiency.coefficient <
          num * summary.netDeficiency.scale := by
        -- The density cap, expanded and with the ambient count partitioned.
        have capExpand : den * stubRate * windowCount +
            num * windowOrder * windowCount <
              num * summary.ambientCount := by
          have expanded := densityCap
          rw [add_mul] at expanded
          exact expanded
        have ambientEq : summary.ambientCount =
            summary.netDeficiency.remainder + windowOrder * windowCount := by
          rw [← windowCover]
          omega
        have capRemainder : den * stubRate * windowCount <
            num * summary.netDeficiency.remainder := by
          rw [ambientEq, Nat.mul_add] at capExpand
          have assoc : num * windowOrder * windowCount =
              num * (windowOrder * windowCount) := mul_assoc _ _ _
          rw [assoc] at capExpand
          exact Nat.lt_of_add_lt_add_right capExpand
        -- `coefficient` is capped by the stub bound, `remainder` by the scale.
        have scaled : den * summary.netDeficiency.coefficient ≤
            den * stubRate * windowCount := by
          have step : den * summary.netDeficiency.coefficient ≤
              den * (stubRate * windowCount) :=
            Nat.mul_le_mul_left _ stubBound
          rwa [← mul_assoc] at step
        have widened : num * summary.netDeficiency.remainder ≤
            num * summary.netDeficiency.scale :=
          Nat.mul_le_mul_left _ scaleBound
        exact lt_of_le_of_lt scaled (lt_of_lt_of_le capRemainder widened)
      have scalePosNat : 0 < summary.netDeficiency.scale :=
        summary.netDeficiency.scale_pos
      rw [div_lt_div_iff₀ (by exact_mod_cast scalePosNat)
        (by exact_mod_cast denPos)]
      have castStrict :
          ((den * summary.netDeficiency.coefficient : Nat) : ℝ) <
            ((num * summary.netDeficiency.scale : Nat) : ℝ) := by
        exact_mod_cast strict
      push_cast at castStrict
      linarith)

def capacity56Rate : CapacityLedger profile.Stage56Rate :=
  profile.capacity56.preserveProp (Added := profile.RateCap56)

def density56Rate : FiniteDensityBudget.CapLedger profile.Stage56Rate :=
  profile.density56.preserveProp (Added := profile.RateCap56)

abbrev Stage57 :=
  Ledger.Extension profile.Stage56Rate
    (fun stage =>
      let _summary := profile.capacity56Rate.localSupply stage
      LocalSupplyLowerBound.NetDeficiencyAccounting)

noncomputable def stage57 (previous : Previous) : profile.Stage57 :=
  let stage := profile.stage56Rate previous
  Ledger.extend stage
    (profile.capacity56Rate.localSupply stage).netDeficiency

def capacity57 : CapacityLedger profile.Stage57 :=
  profile.capacity56Rate.preserve (Added := fun stage =>
    let _summary := profile.capacity56Rate.localSupply stage
    LocalSupplyLowerBound.NetDeficiencyAccounting)

def density57 : FiniteDensityBudget.CapLedger profile.Stage57 :=
  profile.density56Rate.preserve (Added := fun stage =>
    let _summary := profile.capacity56Rate.localSupply stage
    LocalSupplyLowerBound.NetDeficiencyAccounting)

abbrev Charge58 (stage : profile.Stage57) : Prop :=
  let supply := profile.capacity57.localSupply stage
  supply.netDeficiency.scale * supply.netDeficiency.deficiency ≤
    supply.netDeficiency.coefficient * supply.netDeficiency.remainder +
      supply.netDeficiency.scale * supply.netDeficiency.surplus

abbrev Stage58 :=
  Ledger.Extension profile.Stage57 profile.Charge58

noncomputable def stage58 (previous : Previous) : profile.Stage58 :=
  let stage := profile.stage57 previous
  Ledger.extend stage (profile.capacity57.scaledDeficiency stage)

def capacity58 : CapacityLedger profile.Stage58 :=
  profile.capacity57.preserveProp (Added := profile.Charge58)

def density58 : FiniteDensityBudget.CapLedger profile.Stage58 :=
  profile.density57.preserveProp (Added := profile.Charge58)

private def comparison59 (stage : profile.Stage58) :
    Core.OrderThresholdSplit.Profile Nat :=
  { value := profile.capacity58.forcedPower stage ^
      profile.capacity58.statePowerExponent stage
    threshold :=
      profile.capacity58.flatPower stage ^
          profile.capacity58.statePowerExponent stage *
        profile.capacity58.ambientOrder stage ^
          profile.capacity58.remainderCard stage }

abbrev High59 (stage : profile.Stage58) : Prop :=
  (profile.comparison59 stage).threshold <
    (profile.comparison59 stage).value

abbrev NoHigh59 (stage : profile.Stage58) : Prop :=
  (profile.comparison59 stage).value ≤
    (profile.comparison59 stage).threshold

abbrev Decision59 (stage : profile.Stage58) :=
  Core.Residual.Decision.Binary profile.High59 profile.NoHigh59 stage

abbrev Stage59 :=
  Ledger.Extension profile.Stage58 profile.Decision59

noncomputable def stage59 (previous : Previous) : profile.Stage59 :=
  let stage := profile.stage58 previous
  let decision : Core.Residual.Decision.Node _
      profile.High59 profile.NoHigh59 :=
    Core.Residual.Decision.Node.create
      (fun _ => by classical exact inferInstance)
      (fun _ absent => le_of_not_gt absent)
  decision.run stage

def capacity59 : CapacityLedger profile.Stage59 :=
  profile.capacity58.preserve (Added := profile.Decision59)

def density59 : FiniteDensityBudget.CapLedger profile.Stage59 :=
  profile.density58.preserve (Added := profile.Decision59)

abbrev NetCapContradiction60 (stage : profile.Stage59) : Prop :=
  ∀ rate : ℝ,
    (((profile.capacity59.localSupply stage).netDeficiency.coefficient : ℝ) /
        (profile.capacity59.localSupply stage).netDeficiency.scale < rate) →
      0 < (profile.capacity59.localSupply stage).netDeficiency.remainder →
        ¬ (rate *
              (profile.capacity59.localSupply stage).netDeficiency.remainder +
            (profile.capacity59.localSupply stage).netDeficiency.surplus ≤
          (profile.capacity59.localSupply stage).netDeficiency.deficiency)

abbrev Stage60 :=
  Ledger.Extension profile.Stage59 profile.NetCapContradiction60

noncomputable def stage60 (previous : Previous) : profile.Stage60 :=
  let stage := profile.stage59 previous
  Ledger.extend stage
    (fun _rate above remainderPos =>
      (profile.capacity59.localSupply stage).netDeficiency.not_rate_reached
        above remainderPos)

def capacity60 : CapacityLedger profile.Stage60 :=
  profile.capacity59.preserveProp (Added := profile.NetCapContradiction60)

def density60 : FiniteDensityBudget.CapLedger profile.Stage60 :=
  profile.density59.preserveProp (Added := profile.NetCapContradiction60)

abbrev Stage61 :=
  Ledger.Extension profile.Stage60
    (fun _ => LocalSupplyLowerBound.Summary)

noncomputable def stage61 (previous : Previous) : profile.Stage61 :=
  let stage := profile.stage60 previous
  Ledger.extend stage (profile.capacity60.localSupply stage)

def capacity61 : CapacityLedger profile.Stage61 :=
  profile.capacity60.preserve
    (Added := fun _ => LocalSupplyLowerBound.Summary)

def density61 : FiniteDensityBudget.CapLedger profile.Stage61 :=
  profile.density60.preserve
    (Added := fun _ => LocalSupplyLowerBound.Summary)

/-- Node [62] compares the *assigned surplus* of the normalized support with
zero: `∑_{h ∈ X} (d_G(h) - baseline) > 0` selects Type B, and its vanishing
selects Type A.  The quantity is the local-supply ledger's own aggregate of
the registered per-member surplus observation, not a derived capacity total. -/
private def comparison62 (stage : profile.Stage61) :
    Core.OrderThresholdSplit.Profile Nat :=
  { value := (profile.capacity61.localSupply stage).assignedSurplus
    threshold := 0 }

/-- The exact integer quantity in `def:net-charge`, read from the retained
local-supply ledger.  The multiplier is the paper's reciprocal discharge rate
(four in the Erdős--Gyárfás specialization); all three summands are ledger
coordinates, so this definition performs no graph-side recount. -/
def netChargeValue (stage : profile.Stage61) : Int :=
  4 * ((profile.capacity61.localSupply stage).requiredMass : Int) -
      4 * ((profile.capacity61.localSupply stage).assignedSurplus : Int) -
    (profile.capacity61.localSupply stage).netDeficiency.remainder

theorem netChargeValue_eq_definition (stage : profile.Stage61) :
    profile.netChargeValue stage =
      4 * (((profile.capacity61.localSupply stage).requiredMass : Int) -
        ((profile.capacity61.localSupply stage).assignedSurplus : Int)) -
      ((profile.capacity61.localSupply stage).netDeficiency.remainder : Int) := by
  simp only [netChargeValue]
  ring

theorem netChargeValue_eq_scaledNetCharge (stage : profile.Stage61) :
    profile.netChargeValue stage =
      4 * ((profile.capacity61.localSupply stage).requiredMass : Int) -
        4 * ((profile.capacity61.localSupply stage).assignedSurplus : Int) -
        ((profile.capacity61.localSupply stage).netDeficiency.remainder : Int) := by
  rfl

theorem netChargeValue_nonnegative_iff (stage : profile.Stage61) :
    0 ≤ profile.netChargeValue stage ↔
      ((profile.capacity61.localSupply stage).netDeficiency.remainder : Int) ≤
        4 * ((profile.capacity61.localSupply stage).requiredMass : Int) -
          4 * ((profile.capacity61.localSupply stage).assignedSurplus : Int) := by
  rw [netChargeValue_eq_scaledNetCharge]
  omega

private noncomputable def comparison62Family :
    Core.OrderThresholdSplit.DependentProfileFamily Unit
      (fun _ => profile.Stage61) Nat :=
  { profile := fun _ stage => profile.comparison62 stage }

abbrev High62 (stage : profile.Stage61) : Prop :=
  (profile.comparison62 stage).threshold <
    (profile.comparison62 stage).value

abbrev NoHigh62 (stage : profile.Stage61) : Prop :=
  (profile.comparison62 stage).value ≤
    (profile.comparison62 stage).threshold

abbrev Decision62 (stage : profile.Stage61) :=
  Core.Residual.Decision.Binary profile.High62 profile.NoHigh62 stage

abbrev Stage62 :=
  Ledger.Extension profile.Stage61 profile.Decision62

noncomputable def stage62 (previous : Previous) : profile.Stage62 :=
  let stage := profile.stage61 previous
  (profile.comparison62Family.strictDecisionNode (residual := ())).run stage

def capacity62 : CapacityLedger profile.Stage62 :=
  profile.capacity61.preserve (Added := profile.Decision62)

def density62 : FiniteDensityBudget.CapLedger profile.Stage62 :=
  profile.density61.preserve (Added := profile.Decision62)

inductive Phase
  | n56 | n57 | n58 | n59 | n60 | n61 | n62
  deriving DecidableEq, Fintype

def decision62Query :
    Query profile.Stage62 (fun stage => profile.Decision62 stage.previous) :=
  Query.latest

/-! The two live outputs retain the complete node-[62] ledger.  The sum is
owned by this continuation: its left and right payloads are the node-[63]
and node-[64] residuals respectively, while the branch decision is read from
the exact ledger-backed node-[62] decision. -/

structure TypeAResidual (_previous : Previous) where
  stage : profile.Stage62
  noSurplus :
    (profile.capacity62.localSupply stage).assignedSurplus = 0

structure TypeBResidual (_previous : Previous) where
  stage : profile.Stage62
  positiveSurplus :
    0 < (profile.capacity62.localSupply stage).assignedSurplus

theorem TypeAResidual.remainder_le_subcubicAtomCard {previous : Previous}
    (residual : profile.TypeAResidual previous) :
    (profile.capacity62.localSupply
        residual.stage).netDeficiency.remainder ≤
      (profile.capacity62.localSupply residual.stage).subcubicAtomCard := by
  have part :=
    (profile.capacity62.localSupply residual.stage).subcubicAtomPart
  have vanishes := residual.noSurplus
  omega

theorem TypeBResidual.subcubicAtomCard_lt_remainder {previous : Previous}
    (residual : profile.TypeBResidual previous) :
    (profile.capacity62.localSupply residual.stage).subcubicAtomCard <
      (profile.capacity62.localSupply
        residual.stage).netDeficiency.remainder :=
  (profile.capacity62.localSupply residual.stage).assignedSurplusNonAtom
    residual.positiveSurplus

/-- The Type B remainder is nonempty.

Immediate from the same published field, since the atom part is a count over
the members the remainder counts.  Node `[60]`'s net-cap contradiction takes
`0 < netDeficiency.remainder` as an explicit hypothesis; on the Type B branch a
consumer now discharges it from the residual rather than assuming it. -/
theorem TypeBResidual.remainder_pos {previous : Previous}
    (residual : profile.TypeBResidual previous) :
    0 < (profile.capacity62.localSupply
      residual.stage).netDeficiency.remainder :=
  (profile.capacity62.localSupply
    residual.stage).remainder_pos_of_assignedSurplus_pos residual.positiveSurplus

/-- **`prop:p13-density` on the node-[63] residual.**

The surviving density branch's cap, read back on the Type A output through the
node-[56] ledger entry this continuation writes.  The consumer supplies only
the two conditions on the barrier `Summary` it already registered; no rate,
threshold or numeral is named here, and nothing is recomputed from the
residual. -/
theorem TypeAResidual.two_pow_rate_mul_packingCount_le_ambientCapacity
    {previous : Previous} (residual : profile.TypeAResidual previous)
    {rate : Nat}
    (rateFloor :
      2 ^ rate *
          (profile.density62.barrierSummary residual.stage).flatProduct ≤
        (profile.density62.barrierSummary residual.stage).safeProduct)
    (flatPositive :
      0 < (profile.density62.barrierSummary residual.stage).flatProduct) :
    2 ^ (rate * profile.density62.packingCount residual.stage) ≤
      profile.density62.ambientCapacity residual.stage :=
  profile.density62.two_pow_rate_mul_packingCount_le_ambientCapacity
    residual.stage rateFloor flatPositive

/-- **`prop:p13-density` on the node-[64] residual.**  The Type B mirror of
`TypeAResidual.two_pow_rate_mul_packingCount_le_ambientCapacity`; both open
frontier residuals carry the same node-[56] entry. -/
theorem TypeBResidual.two_pow_rate_mul_packingCount_le_ambientCapacity
    {previous : Previous} (residual : profile.TypeBResidual previous)
    {rate : Nat}
    (rateFloor :
      2 ^ rate *
          (profile.density62.barrierSummary residual.stage).flatProduct ≤
        (profile.density62.barrierSummary residual.stage).safeProduct)
    (flatPositive :
      0 < (profile.density62.barrierSummary residual.stage).flatProduct) :
    2 ^ (rate * profile.density62.packingCount residual.stage) ≤
      profile.density62.ambientCapacity residual.stage :=
  profile.density62.two_pow_rate_mul_packingCount_le_ambientCapacity
    residual.stage rateFloor flatPositive


/-- **`prop:negative-net-charge`'s hypothesis or the window-stub excess, on the
node-`[63]` residual.** -/
theorem TypeAResidual.negativeNetCharge_or_windowStubExcess
    {previous : Previous} (residual : profile.TypeAResidual previous)
    {windowOrder stubRate : Nat}
    (windowCover :
      (profile.capacity62.localSupply residual.stage).selectedCount =
        windowOrder * profile.density62.packingCount residual.stage)
    (partition :
      (profile.capacity62.localSupply
          residual.stage).netDeficiency.remainder +
          (profile.capacity62.localSupply residual.stage).selectedCount =
        (profile.capacity62.localSupply residual.stage).ambientCount)
    (densityCap :
      (4 * stubRate + windowOrder) *
          profile.density62.packingCount residual.stage <
        (profile.capacity62.localSupply residual.stage).ambientCount) :
    4 * (((profile.capacity62.localSupply
              residual.stage).requiredMass : Int) -
          ((profile.capacity62.localSupply
            residual.stage).assignedSurplus : Int)) <
        ((profile.capacity62.localSupply
          residual.stage).netDeficiency.remainder : Int) ∨
      ((stubRate * profile.density62.packingCount residual.stage :
          Nat) : Int) <
        ((profile.capacity62.localSupply
            residual.stage).requiredMass : Int) -
          ((profile.capacity62.localSupply
            residual.stage).assignedSurplus : Int) :=
  (profile.capacity62.localSupply
    residual.stage).negativeNetCharge_or_windowStubExcess
    windowCover partition densityCap

/-- **`prop:negative-net-charge`'s hypothesis or the window-stub excess, on the
node-`[64]` residual.**  The Type B mirror of
`TypeAResidual.negativeNetCharge_or_windowStubExcess`. -/
theorem TypeBResidual.negativeNetCharge_or_windowStubExcess
    {previous : Previous} (residual : profile.TypeBResidual previous)
    {windowOrder stubRate : Nat}
    (windowCover :
      (profile.capacity62.localSupply residual.stage).selectedCount =
        windowOrder * profile.density62.packingCount residual.stage)
    (partition :
      (profile.capacity62.localSupply
          residual.stage).netDeficiency.remainder +
          (profile.capacity62.localSupply residual.stage).selectedCount =
        (profile.capacity62.localSupply residual.stage).ambientCount)
    (densityCap :
      (4 * stubRate + windowOrder) *
          profile.density62.packingCount residual.stage <
        (profile.capacity62.localSupply residual.stage).ambientCount) :
    4 * (((profile.capacity62.localSupply
              residual.stage).requiredMass : Int) -
          ((profile.capacity62.localSupply
            residual.stage).assignedSurplus : Int)) <
        ((profile.capacity62.localSupply
          residual.stage).netDeficiency.remainder : Int) ∨
      ((stubRate * profile.density62.packingCount residual.stage :
          Nat) : Int) <
        ((profile.capacity62.localSupply
            residual.stage).requiredMass : Int) -
          ((profile.capacity62.localSupply
            residual.stage).assignedSurplus : Int) :=
  (profile.capacity62.localSupply
    residual.stage).negativeNetCharge_or_windowStubExcess
    windowCover partition densityCap

theorem TypeBResidual.negativeNetCharge_or_windowJoinPressure
    {previous : Previous} (residual : profile.TypeBResidual previous)
    {windowOrder stubRate windowSurplus : Nat}
    (windowStub :
      (profile.capacity62.localSupply residual.stage).requiredMass ≤
        stubRate * profile.density62.packingCount residual.stage +
          windowSurplus)
    (windowCover :
      (profile.capacity62.localSupply residual.stage).selectedCount =
        windowOrder * profile.density62.packingCount residual.stage)
    (partition :
      (profile.capacity62.localSupply
          residual.stage).netDeficiency.remainder +
          (profile.capacity62.localSupply residual.stage).selectedCount =
        (profile.capacity62.localSupply residual.stage).ambientCount) :
    4 * (((profile.capacity62.localSupply
              residual.stage).requiredMass : Int) -
          ((profile.capacity62.localSupply
            residual.stage).assignedSurplus : Int)) <
        ((profile.capacity62.localSupply
          residual.stage).netDeficiency.remainder : Int) ∨
      ((profile.capacity62.localSupply
          residual.stage).ambientCount : Int) ≤
        (((4 * stubRate + windowOrder) *
            profile.density62.packingCount residual.stage : Nat) : Int) +
          4 * ((windowSurplus : Int) -
            ((profile.capacity62.localSupply
              residual.stage).assignedSurplus : Int)) := by
  by_cases negative :
      4 * (((profile.capacity62.localSupply
                residual.stage).requiredMass : Int) -
            ((profile.capacity62.localSupply
              residual.stage).assignedSurplus : Int)) <
        ((profile.capacity62.localSupply
          residual.stage).netDeficiency.remainder : Int)
  · exact Or.inl negative
  · exact Or.inr
      ((profile.capacity62.localSupply
        residual.stage).windowJoinPressure_of_not_negativeNetCharge
        windowStub windowCover partition negative)

abbrev ClassifiedOutput (previous : Previous) :=
  Sum (profile.TypeAResidual previous) (profile.TypeBResidual previous)

def typeAResidualQuery :
    Query (profile.ClassifiedOutput previous)
      (fun _ => Option (profile.TypeAResidual previous)) :=
   fun output =>
    match output with
    | .inl residual => some residual
    | .inr _ => none

def typeBResidualQuery :
    Query (profile.ClassifiedOutput previous)
      (fun _ => Option (profile.TypeBResidual previous)) :=
   fun output =>
    match output with
    | .inl _ => none
    | .inr residual => some residual

abbrev node63ResidualQuery (previous : Previous) :=
  profile.typeAResidualQuery (previous := previous)
abbrev node64ResidualQuery (previous : Previous) :=
  profile.typeBResidualQuery (previous := previous)

/-- The exact node-[62] stage selected by either open frontier residual. -/
def classifiedStageQuery :
    Query (profile.ClassifiedOutput previous) (fun _ => profile.Stage62) :=
   fun output =>
    match output with
    | .inl residual => residual.stage
    | .inr residual => residual.stage

/-- Every inherited capacity query remains available on both node-[63] and
node-[64] outputs through the standard residual projection. -/
def classifiedCapacityLedger : CapacityLedger (profile.ClassifiedOutput previous) :=
  profile.capacity62.comap profile.classifiedStageQuery

/-- The retained density-cap ledger, likewise available on both open frontier
outputs.  Its three scalar queries are the packing cardinality, the barrier
`Summary` and the represented ambient capacity the surviving alternative was
compared at. -/
def classifiedDensityLedger :
    FiniteDensityBudget.CapLedger (profile.ClassifiedOutput previous) :=
  profile.density62.comap profile.classifiedStageQuery

def classifiedDecision62Query :
    Query (profile.ClassifiedOutput previous)
      (fun output => profile.Decision62
        (profile.classifiedStageQuery output).previous) :=
  profile.decision62Query.comap profile.classifiedStageQuery

noncomputable def execution : Core.Strategy.CTExecution Previous where
  Terminal := Terminal
  Output := profile.ClassifiedOutput
  run := fun previous =>
    let final := profile.stage62 previous
    match profile.decision62Query final with
    | Core.Residual.Decision.Binary.yesBranch high =>
        have positiveSurplus :
            0 < (profile.capacity62.localSupply final).assignedSurplus := by
          change 0 <
            (profile.capacity61.localSupply final.previous).assignedSurplus
          simpa [High62, comparison62] using high
        .inr ⟨final, positiveSurplus⟩
    | Core.Residual.Decision.Binary.noBranch noHigh =>
        have noSurplus :
            (profile.capacity62.localSupply final).assignedSurplus = 0 := by
          change
            (profile.capacity61.localSupply final.previous).assignedSurplus = 0
          apply Nat.eq_zero_of_le_zero
          simpa [NoHigh62, comparison62] using noHigh
        .inl ⟨final, noSurplus⟩
  terminal := fun _ output =>
    match output with
    | .inl _ => .typeA
    | .inr _ => .typeB
  checks := fun _ => Fintype.card Phase
  work := fun _ => Fintype.card Phase

def netDeficiencyQuery :=
  let query := (Query.latest (Previous := profile.Stage56Rate)
    (Added := fun stage =>
      let _summary := profile.capacity56Rate.localSupply stage
      LocalSupplyLowerBound.NetDeficiencyAccounting))
  let query := query.preserve (Added := profile.Charge58)
  let query := query.preserve (Added := profile.Decision59)
  let query := query.preserve (Added := profile.NetCapContradiction60)
  let query := query.preserve
    (Added := fun _ => LocalSupplyLowerBound.Summary)
  query.preserve (Added := profile.Decision62)

def decision59Query :=
  let query := (Query.latest (Previous := profile.Stage58)
    (Added := profile.Decision59))
  let query := query.preserve (Added := profile.NetCapContradiction60)
  let query := query.preserve
    (Added := fun _ => LocalSupplyLowerBound.Summary)
  query.preserve (Added := profile.Decision62)

/-- Node `[60]`'s net-cap contradiction, retrieved on the node-`[62]` stage.

The same shape as `densityCap56Query`: the fact is read back through the
framework's own `preserve` chain, never recomputed. -/
def netCapContradiction60Query :=
  let query := (Query.latest (Previous := profile.Stage59)
    (Added := profile.NetCapContradiction60))
  let query := query.preserve
    (Added := fun _ => LocalSupplyLowerBound.Summary)
  query.preserve (Added := profile.Decision62)

def densityCap56Query :=
  let query := (Query.latest (Previous := Previous)
    (Added := profile.DensityCap56))
  let query := query.preserve (Added := profile.RateCap56)
  let query := query.preserve (Added := fun stage =>
    let _summary := profile.capacity56Rate.localSupply stage
    LocalSupplyLowerBound.NetDeficiencyAccounting)
  let query := query.preserve (Added := profile.Charge58)
  let query := query.preserve (Added := profile.Decision59)
  let query := query.preserve (Added := profile.NetCapContradiction60)
  let query := query.preserve
    (Added := fun _ => LocalSupplyLowerBound.Summary)
  query.preserve (Added := profile.Decision62)

end Profile

end Hypostructure.Core.Strategy.FiniteStateNetChargeContinuation
