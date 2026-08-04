import Hypostructure.PDE.Strategy.BalancedRegularity
import Hypostructure.PDE.Strategy.ScaleThresholdDichotomy
import Hypostructure.Core.Strategy.Data

/-!
# The PDE strategy registry

Core's `StrategyData` carries one list per registered family, and the graph
specialization fills every one of them.  This module is the PDE counterpart:
for a `BalancedRegularity` system it produces the registration of each family,
so a global-regularity problem populates the same registry a combinatorial one
does.

Every family is read the same way, and the reading is forced by what a local
regularity argument actually accounts for:

| family | PDE reading |
| --- | --- |
| density budget | how many windows the cover around the singularity may use |
| baseline demand | the Sobolev grade each window demands against what it has |
| local supply | the grade a window actually supplies |
| barrier enumeration | the finitely many stages a barrier can sit at |
| capacity tokens | one token per window certificate |
| pair response | the velocity/potential pair at a window |

Nothing here executes, decides, routes or writes a ledger entry: each value is
inert data, and Core's own strategy for the family runs the CTs.  In particular
no field below is an analytic provision --- the grades are `Stage.rank`, which
is a closed-form function of which alternative the argument reached.
-/

namespace Hypostructure.PDE.Strategy.RegularityRegistry

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

/-- The counting budget: grades are natural numbers and they add. -/
def countingBudget : Core.ResourceBudget where
  Resource := Nat
  le := (· ≤ ·)
  leRefl := Nat.le_refl
  leTrans := Nat.le_trans
  zero := Nat.zero
  add := Nat.add
  ceiling := id
  zeroLe := Nat.zero_le
  addMono := Nat.add_le_add
  addAssoc := Nat.add_assoc
  zeroAdd := Nat.zero_add
  addZero := Nat.add_zero

/--
**The window schedule of one residual.**

The framework's derived nested tower around the singularity is one site, so a
residual the argument is still working on schedules exactly one window.  A
residual that has *closed* --- reached the final alternative --- schedules
**none**: there is nothing left to localize at.

Making the schedule residual-dependent rather than a constant singleton is what
keeps every "for each scheduled site …" obligation a statement about the
selected residual's own data.  With a constant schedule those obligations have
to hold at residuals where they are meaningless, which is what forces a
totality no local argument should have to supply.
-/
noncomputable def windowSchedule (input : Core.Strategy.ProblemInput M.problem) :
    Core.Finite.Enumeration PUnit :=
  open Classical in
  if system.stageReached input = .gradientClosed then
    Core.Finite.Enumeration.empty PUnit
  else
    Core.Finite.Enumeration.singleton PUnit.unit

/-- A window is scheduled exactly while the argument is unfinished there. -/
theorem mem_windowSchedule_iff (input : Core.Strategy.ProblemInput M.problem)
    (site : PUnit) :
    site ∈ (windowSchedule system input).values ↔
      system.stageReached input ≠ .gradientClosed := by
  classical
  unfold windowSchedule
  by_cases closed : system.stageReached input = .gradientClosed <;>
    simp [closed, Core.Finite.Enumeration.empty,
      Core.Finite.Enumeration.singleton, Core.Finite.Enumeration.ofNodupList]

/-! ## Density budget

How many windows the local argument may use.  One, for the derived tower.
-/

/-- **The registered window-density budget.**

The argument may open one window per alternative it has already cleared, plus
the one it is working on.  A residual that has cleared nothing gets a single
window, which is the derived tower; a residual near the end may spend more.
This reads the selected residual rather than fixing a constant. -/
noncomputable def densityBudget :
    Core.Strategy.FiniteDensityBudget.Registration
      (Core.Strategy.ProblemInput M.problem) where
  ambientCapacity := fun input => (system.stageReached input).rank + 1
  ambientCapacity_pos := fun _ => Nat.succ_pos _

/-! ## Baseline demand accounting

The grade a window demands against the grade the stratification has reached
there.  `Site` is the window, `Witness` is the stage certificate at it, and the
resource is the rank.
-/

/-- **The registered baseline grade demand.** -/
noncomputable def baselineDemand :
    Core.Strategy.BaselineDemandAccounting.Registration
      (Core.Strategy.ProblemInput M.problem) where
  budget := countingBudget
  Site := fun _ => PUnit
  Witness := fun _ _ => PUnit
  family := fun _input =>
    { indices := windowSchedule system _input
      fibres := fun _ => Core.Finite.Enumeration.singleton PUnit.unit }
  Active := fun input _ => system.stageReached input ≠ .gradientClosed
  Supports := fun input _ _ => system.stageReached input ≠ .regular
  contribution := fun input _ _ => (system.stageReached input).rank
  required := fun input => (system.stageReached input).rank
  capacity := fun _ => Stage.gradientClosed.rank
  activeDecidable := fun input _ =>
    inferInstanceAs (Decidable (system.stageReached input ≠ .gradientClosed))
  supportsDecidable := fun input _ _ =>
    inferInstanceAs (Decidable (system.stageReached input ≠ .regular))
  resourceLEDecidable := fun left right => Nat.decLe left right

/-! ## Local supply lower bound

What a window supplies, against what it requires.  Both are read off the stage
the argument reached, so the accounting is exact and carries no estimate.
-/

/-- **The registered per-window grade supply.** -/
noncomputable def localSupply :
    Core.Strategy.LocalSupplyLowerBound.Registration
      (Core.Strategy.ProblemInput M.problem) (fun _ => PUnit) where
  Member := fun _ => PUnit
  Label := fun _ => PUnit
  members := fun input _ => windowSchedule system input
  requiredMass := fun input _ _ => (system.stageReached input).rank + 1
  observedSupply := fun input _ _ => (system.stageReached input).rank
  defectCorrection := fun _ _ _ => 1
  surplus := fun input _ _ =>
    Stage.gradientClosed.rank - (system.stageReached input).rank
  label := fun _ _ _ => PUnit.unit
  labelDecidableEq := fun _ => inferInstance
  pointwise := fun _ _ _ => Nat.le_refl _

/-! ## Capacity tokens

One token per window certificate.  A demand is the grade a stage asks for and
a token is the certificate that pays it; eligibility is total, because the
framework's window certificate covers whatever the stage demands at the window
it was produced on.
-/

/-- **The registered capacity-token accounting.** -/
noncomputable def capacityTokens :
    Core.Strategy.CanonicalCapacityTokenAccounting.Registration
      (Core.Strategy.ProblemInput M.problem) where
  Demand := fun _ => PUnit
  Token := fun _ => PUnit
  Role := fun _ => PUnit
  Label := fun _ => PUnit
  demands := fun input => windowSchedule system input
  tokens := fun input => windowSchedule system input
  completeLabels := fun _ =>
    Core.Finite.CompleteEnumeration.ofFinEnum (inferInstance : FinEnum PUnit)
  Eligible := fun input _ _ => system.stageReached input ≠ .gradientClosed
  eligibleDecidable := fun input _ _ =>
    inferInstanceAs (Decidable (system.stageReached input ≠ .gradientClosed))
  demandWeight := fun input _ => (system.stageReached input).rank
  tokenCapacity := fun _ _ => Stage.gradientClosed.rank
  required := fun input => (system.stageReached input).rank
  roleOf := fun _ _ => PUnit.unit
  labelOf := fun _ _ _ => PUnit.unit
  labelCapacity := fun _ _ => Stage.gradientClosed.rank
  aggregateLabel := fun _ => PUnit
  aggregateLabelDecidableEq := fun _ => inferInstance
  memberAggregateLabel := fun _ _ => PUnit.unit

/-! ## Pair response accounting

The pair a window carries is the field together with its potential --- the
velocity and the pressure of the balance.  A pair is *dependent* exactly when
the stage reached at it is not the closing one, i.e. when the local argument
has not finished there; that is the only reading under which the exactness laws
below are the identity rather than an assumption.
-/

/-- **The registered pair-response accounting.** -/
noncomputable def pairResponse :
    Core.Strategy.CanonicalPairResponseAccounting.Registration
      (Core.Strategy.ProblemInput M.problem) where
  Pair := fun _ => PUnit
  -- The pair is scheduled exactly while the argument is unfinished, so
  -- `IntendedPair` says something rather than being forced to `True` by a
  -- constant schedule that always contains it.
  pairSchedule := fun input => windowSchedule system input
  IntendedPair := fun input _ => system.stageReached input ≠ .gradientClosed
  pairSchedule_exact := fun input pair =>
    mem_windowSchedule_iff system input pair
  Dependent := fun input _ => system.stageReached input ≠ .gradientClosed
  AdmittedDependent := fun input _ => system.stageReached input ≠ .gradientClosed
  dependent_exact := fun _ _ => Iff.rfl
  dependentDecidable := fun input _ =>
    inferInstanceAs (Decidable (system.stageReached input ≠ .gradientClosed))
  pairCharge := fun input _ => (system.stageReached input).rank
  pairCapacity := fun _ => Stage.gradientClosed.rank
  BlockerKind := fun _ => PUnit
  completeBlockerKinds := fun _ =>
    Core.Finite.CompleteEnumeration.ofFinEnum (inferInstance : FinEnum PUnit)
  CanonicalBlocker := fun input _ _ =>
    system.stageReached input ≠ .gradientClosed
  blocker_exact := fun _ _ =>
    ⟨fun dependent => ⟨PUnit.unit, dependent⟩, fun ⟨_, blocked⟩ => blocked⟩
  roleOf := fun input _ =>
    if system.stageReached input = .gradientClosed then
      Core.Strategy.CanonicalPairResponseAccounting.Role.freeAnchor
    else
      Core.Strategy.CanonicalPairResponseAccounting.Role.blocked PUnit.unit
  role_freeAnchor_exact := fun input _ => by
    by_cases closed : system.stageReached input = .gradientClosed <;>
      simp [closed, Core.Strategy.CanonicalPairResponseAccounting.Role.freeAnchor,
        Core.Strategy.CanonicalPairResponseAccounting.Role.blocked]
  role_blocked_exact := fun input _ kind => by
    cases kind
    by_cases closed : system.stageReached input = .gradientClosed <;>
      simp [closed, Core.Strategy.CanonicalPairResponseAccounting.Role.freeAnchor,
        Core.Strategy.CanonicalPairResponseAccounting.Role.blocked]
  roleCapacity := fun _ _ => Stage.gradientClosed.rank

/-! ## Boundary demand accounting

The demand a window places on its boundary, paid by the enclosing window of the
nested tower.  Both are read off the stage, so the accounting is exact.
-/

/-- **The registered boundary demand accounting.** -/
noncomputable def boundaryDemand :
    Core.Strategy.BoundaryDemandAccounting.Registration
      (Core.Strategy.ProblemInput M.problem) where
  Demand := fun _ => PUnit
  Payer := fun _ => PUnit
  demands := fun input => windowSchedule system input
  payers := fun input => windowSchedule system input
  Eligible := fun input _ _ => system.stageReached input ≠ .gradientClosed
  eligibleDecidable := fun input _ _ =>
    inferInstanceAs (Decidable (system.stageReached input ≠ .gradientClosed))
  demandWeight := fun input _ => (system.stageReached input).rank
  payerCapacity := fun _ _ => Stage.gradientClosed.rank
  Member := fun _ => PUnit
  Label := fun _ => PUnit
  members := fun input => windowSchedule system input
  memberLowerMass := fun input _ => (system.stageReached input).rank
  memberCapacityRate := fun _ _ => Stage.gradientClosed.rank
  memberLabel := fun _ _ => PUnit.unit
  labelDecidableEq := fun _ => inferInstance

end Hypostructure.PDE.Strategy.RegularityRegistry
