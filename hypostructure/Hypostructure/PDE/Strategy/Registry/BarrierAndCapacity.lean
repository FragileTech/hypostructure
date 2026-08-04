import Hypostructure.PDE.Strategy.RegularityRegistry
import Hypostructure.PDE.Strategy.FiniteStateCapacity

/-!
# Barrier and capacity registrations for a global-regularity problem

`RegularityRegistry` fills the accounting families of `Core.StrategyData` from
a `BalancedRegularity` system.  This module fills the four remaining ones a
local regularity argument needs:

| family | PDE reading |
| --- | --- |
| barrier enumeration | the stages the argument can stall at, and the refinement table relating them |
| finite-state capacity | the window certificate, as an exact represented state |
| scan | walking the six alternatives in order, looking for the one that closed |
| response | observing which alternative a window reached, and whether that closed it |

Every numeric quantity is read off `RegularityStratification.Stage.rank`, the
position of an alternative in `stokes:prop:finite-state-stratification`:

* a **barrier candidate** is a stage the argument can stall at, and it is
  *accepted* when the argument got at least that far;
* a **capacity** is `Stage.gradientClosed.rank`, the top of the stratification,
  because the closing alternative is what the local argument is allowed to
  spend;
* a **demand**, **weight**, or **mass** is `(system.stageReached input).rank`,
  the position the argument actually reached.

Nothing here executes, decides, routes, or writes a ledger entry: each value is
inert data and Core's own strategy for the family runs the CTs.  In particular
no field below is an analytic provision --- every one of them is a closed-form
function of which alternative the argument reached.
-/

namespace Hypostructure.PDE.Strategy.Registry.BarrierAndCapacity

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

/-! ## The barrier alphabet

The labels of the barrier are the alternatives themselves, so the alphabet has
one letter per stage: one more than the rank of the closing stage.
-/

/-- **How many alternatives the stratification offers.**

One more than `Stage.gradientClosed.rank`, because the ranks run from the
already-smooth case up to the closing one inclusive.  This is the label
alphabet the relation barrier is stated over. -/
def stageCount : Nat := Stage.gradientClosed.rank + 1

/--
**The refinement order of the stratification, as a bit relation.**

Bit `earlier` of the row at `middle` is set exactly when an argument that has
reached `middle` has already passed `earlier` --- which is the stratification's
own `refines`, `earlier.rank ≤ middle.rank`.  Because the ranks are an initial
segment, that predicate is the downward closed mask
`allOnes >>> (stageCount - 1 - middle)`, so the table is generated rather than
tabulated and cannot drift from `Stage.refines`.

The leg length is not read: having reached an alternative asserts the same
thing however long the chain of local arguments that got there.  Consequently
the safe and flat counts Core derives from this profile depend only on the
alternative, which is what makes the barrier a statement about the
stratification and not about a particular window.
-/
def refinementProfile : Core.FiniteBitRelationBarrier.Profile stageCount where
  row := fun _ middle =>
    BitVec.allOnes stageCount >>> (stageCount - 1 - middle.1)

/-! ## Barrier enumeration

The finitely many stages the argument can stall at.  A candidate is accepted
when the argument reached it, so the accepted subfamily is exactly the initial
segment of alternatives the local certificate has passed, and its two legs are
the part of the stratification already traversed and the part traversed beyond
the stalling stage.
-/

/--
**The registered stall-stage barrier enumeration.**

`stokes:prop:finite-state-stratification` supplies six alternatives; this is
that list read as a barrier schedule.  `accepted` says the argument got at
least as far as the candidate, `leftLength` is how far it had to come to reach
the candidate, and `rightLength` is how much further it went --- so a candidate
accepted at the top has an empty right leg and nothing is left to obstruct.
-/
noncomputable def barrierEnumeration :
    Core.Strategy.FiniteBarrierEnumeration.Registration
      (Core.Strategy.ProblemInput M.problem) where
  Candidate := fun _ => Stage
  candidates := fun _ => Stage.schedule
  accepted := fun input stage => stage.rank ≤ (system.stageReached input).rank
  acceptedDecidable := fun input stage =>
    Nat.decLe stage.rank (system.stageReached input).rank
  labelCount := fun _ => stageCount
  relationPosition := fun _ relation => relation
  leftLength := fun _ candidate => candidate.rank
  rightLength := fun input candidate =>
    (system.stageReached input).rank - candidate.rank

/-! ## Finite-state capacity

The represented state of the finite-state capacity is the object itself, and
the window certificate is the single state the framework's derived tower
carries.  `Hypostructure.PDE.Strategy.FiniteStateCapacity.Registration` already
owns the substitution of that state into Core's registration, so this module
supplies only the PDE presentation and hands it to `toCore`.
-/

/--
**The glue capacity of one window certificate.**

The derived tower around the singularity is a single window carrying a single
certificate, so the symbolic base, the owner index, the local fibre and the
code are all one-point and the glue is the identity pairing of the two.  That
is the honest reading: a lone certificate glues to itself, and the joint
accounting below therefore charges no entropy against it.
-/
def windowJointProfile : Core.Strategy.FiniteStateCapacity.JointProfile.{u} where
  Base := PUnit.{u + 1}
  finiteBase := inferInstance
  Owner := PUnit.{u + 1}
  finiteOwner := inferInstance
  Local := fun _ => PUnit.{u + 1}
  finiteLocal := fun _ => inferInstance
  Global := PUnit.{u + 1} × (PUnit.{u + 1} → PUnit.{u + 1})
  Code := PUnit.{u + 1} × (PUnit.{u + 1} → PUnit.{u + 1})
  finiteCode := inferInstance
  glue := fun base choice => (base, choice)
  recoverBase := Prod.fst
  recoverLocal := Prod.snd
  recoverBase_glue := fun _ _ => rfl
  recoverLocal_glue := fun _ _ _ => rfl
  code := id
  codeInjectiveOnGlue := fun _ _ _ _ equal => equal

/--
**The represented finite-state capacity of the window certificate.**

The state is the object itself, and the certificate the derived tower carries
is a single target, offset, position and value --- the stratification says the
local argument closes at *one* alternative, so there is nothing to enumerate
beyond it.  The numbers are the stratification's:

* the selected scale is `(system.stageReached input).rank`, the alternative
  reached, so the scale the capacity is measured at is the one the argument
  stopped at;
* `memberLowerMass` is that same rank --- what the window demands;
* `memberCapacity` is `Stage.gradientClosed.rank` --- what a closing
  certificate can pay;
* `ambientOrder` and `remainderCard` are read off the inherited support
  complement, so the vertex set the entropy comparison runs on is the one the
  local-supply predecessor already produced;
* the joint exponents are `0` paid and `(system.stageReached input).rank`
  desired: a lone certificate glues trivially and pays nothing, so the whole
  grade the argument reached is carried as error.  That is what makes
  `jointDesiredExponent_exact` the identity `d = 0 + d` rather than an
  estimate.
-/
noncomputable def representedStateCapacity :
    FiniteStateCapacity.Registration.{u, u, u, u} M
      (Core.Strategy.ProblemInput M.problem) (fun _ => PUnit) where
  state := fun input => input.object
  Target := fun _ _ => PUnit
  Offset := fun _ _ => PUnit
  Position := fun _ _ _ => PUnit
  Value := fun _ _ => PUnit
  targets := fun _ _ _ _ _ => Core.Finite.Enumeration.singleton PUnit.unit
  offsets := fun _ _ _ _ _ => Core.Finite.Enumeration.singleton PUnit.unit
  scales := fun input _ _ _ _ =>
    Core.Finite.Enumeration.singleton (system.stageReached input).rank
  selectedScale := fun input _ _ _ _ => (system.stageReached input).rank
  selectedScale_mem := fun _ _ _ _ _ => by
    simp [Core.Finite.Enumeration.singleton,
      Core.Finite.Enumeration.ofNodupList]
  positions := fun _ _ _ _ _ _ => Core.Finite.Enumeration.singleton PUnit.unit
  finiteScaleLimit := fun _ _ _ _ _ => Stage.gradientClosed.rank
  targetValue := fun _ _ _ _ _ _ => PUnit.unit
  blockValue := fun _ _ _ _ _ _ _ _ => PUnit.unit
  orbitValue := fun _ _ _ _ _ _ _ => PUnit.unit
  Compatible := fun input _ _ _ => system.stageReached input ≠ .regular
  compatibleDecidable := fun input _ _ _ =>
    inferInstanceAs (Decidable (system.stageReached input ≠ .regular))
  valueDecidableEq := fun _ _ => inferInstance
  Label := fun _ _ => PUnit
  memberLowerMass := fun input _ _ _ _ _ => (system.stageReached input).rank
  memberCapacity := fun _ _ _ _ _ _ => some Stage.gradientClosed.rank
  memberLabel := fun _ _ _ _ _ _ => some PUnit.unit
  labelDecidableEq := fun _ _ => inferInstance
  RealizedState := fun _ _ _ _ _ _ => PUnit
  realizedStateFinite := fun _ _ _ _ _ _ => inferInstance
  realizedStateNonempty := fun _ _ _ _ _ _ => inferInstance
  ambientOrder := fun _ _ complement _ _ _ => complement.card
  remainderCard := fun _ _ complement _ _ _ => complement.card
  statePowerExponent := fun _ _ _ _ _ => Stage.gradientClosed.rank
  statePowerExponent_pos := fun _ _ _ _ _ => by decide
  forcedBase := fun input _ _ _ _ => (system.stageReached input).rank
  flatBase := fun _ _ _ _ _ => Stage.gradientClosed.rank
  flatBase_pos := fun _ _ _ _ _ => by decide
  jointProfile := fun _ _ _ _ _ _ => windowJointProfile
  jointBaseCard := by
    intro _ _ _ _ _ _
    simp [windowJointProfile]
  jointExponent := fun _ _ _ _ _ => Stage.gradientClosed.rank
  jointWeight := fun _ _ _ _ _ _ _ => 0
  jointLocalLower := by
    intro _ _ _ _ _ _ _
    simp [windowJointProfile]
  jointPaidExponent := fun _ _ _ _ _ => 0
  jointPaidExponent_exact := by
    intro _ _ _ _ _ _
    simp [windowJointProfile,
      Core.DependentOwnerGlueCapacity.BaseProfile.weightSum]
  jointDesiredExponent := fun input _ _ _ _ => (system.stageReached input).rank
  jointErrorExponent := fun input _ _ _ _ => (system.stageReached input).rank
  jointCapacity := fun _ _ _ _ _ => Stage.gradientClosed.rank
  jointCapacity_pos := fun _ _ _ _ _ => by decide
  jointCodeCapacity := by
    intro _ _ _ _ _ _
    simp [windowJointProfile, Stage.rank]
  jointDesiredExponent_exact := fun _ _ _ _ _ => (Nat.zero_add _).symm

/-- **The registered finite-state capacity.**

The PDE presentation above with the exact represented state substituted in.
No finite scan, comparison, or branch is recomputed here: `toCore` is a
rearrangement, and Core's `FiniteStateCapacity` strategy runs CT17 and CT14. -/
noncomputable def stateCapacity :
    Core.Strategy.FiniteStateCapacity.Registration.{u, u, u}
      (Core.Strategy.ProblemInput M.problem) (fun _ => PUnit) :=
  (representedStateCapacity system).toCore

/-! ## Scan

Walking the six alternatives in the appendix's order and asking, at each,
whether the local argument got that far.
-/

/--
**The registered stage scan.**

The schedule is the stratification's own complete schedule, so the scan visits
the alternatives in the order `stokes:prop:finite-state-stratification` lists
them.  The witness at an alternative is that the argument reached it, i.e. that
its rank is at or below the rank reached; the scan therefore stops at the
frontier of what the local certificate established, and the alternatives past
that frontier carry no witness.
-/
noncomputable def stageScan : Core.ScanData.{u, u, 0} M.problem where
  Item := fun _ => Stage
  schedule := fun _ => Stage.schedule.toEnumeration
  witness := fun input stage => stage.rank ≤ (system.stageReached input).rank
  witnessDecidable := fun input stage =>
    Nat.decLe stage.rank (system.stageReached input).rank
  metadata :=
    { name := "Regularity stage scan"
      note := "Walks the six alternatives of the stratification in order; the \
        witness at an alternative is that the local argument reached it." }

/-! ## Response

What a window answers when it is asked how far the argument got there, and how
that answer is classified.
-/

/--
**The registered window response.**

The item is the framework's derived window around the singularity, the response
is the alternative reached there, and the class is whether that alternative is
the closing one.  Reading the class as `Bool` rather than as the stage again is
the point of the family: the response retains the whole stratification, while
the classification retains only the distinction the argument turns on ---
closed, or stalled below the gradient.
-/
noncomputable def stageResponse : Core.ResponseData.{u, u, 0} M.problem where
  Item := fun _ => PUnit
  Response := fun _ => Stage
  Class := fun _ => Bool
  schedule := fun _ => Core.Finite.Enumeration.singleton PUnit.unit
  observe := fun input _ => system.stageReached input
  classify := fun _ stage => decide (stage = .gradientClosed)
  metadata :=
    { name := "Window stage response"
      note := "Observes the alternative the local argument reached at the \
        derived window and classifies it as closed or stalled." }

end Hypostructure.PDE.Strategy.Registry.BarrierAndCapacity
