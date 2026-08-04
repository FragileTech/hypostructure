import Hypostructure.PDE.Strategy.RegularityRegistry
import Hypostructure.PDE.Strategy.InterfaceReplacement

/-!
# The counterexample reduction of a balanced global-regularity problem

Core's `CounterexampleReductionData` is the single record that powers four
consecutive DAG vertices --- `targetAlgebraReduction`,
`minimalSubobjectExclusion`, `criticalModificationStructure` and
`interfaceReplacementClosure`.  Graph fills it from a minimum-degree problem
and a cycle target; this module fills it from a `BalancedRegularity` system,
so a global-regularity problem walks the same four vertices a combinatorial
one does.

Every reading below is forced by what a local regularity argument actually
produces, and every one of them is a function of `Stage` --- the six ordered
alternatives of `stokes:prop:finite-state-stratification`:

| field | PDE reading |
| --- | --- |
| progress | the *stage deficit*: how many alternatives are still open |
| code | which alternative the local argument reached on the object |
| acceptance | the alternative reached is the closing one |
| subobject | a window of the tower on which the argument gets strictly further |
| atomic | such a window together with the single stage it carries |
| critical | the window still carries the singularity, so deleting it deletes the counterexample |
| carrier | the windows on which the argument has already closed |
| related | one nesting step of the tower between two closed windows |
| interface | the trace datum a replacement piece has to match: its stage |

Nothing here executes, decides, routes or writes a ledger entry: the record is
inert data and Core's three sealed strategies run the CTs on it.  In
particular no field is an analytic provision --- the only analytic fact used
is `BalancedRegularity.target_of_gradientClosed`, which is the framework's
own, and it is used exactly once, to prove `target_iff_code`.

Nothing here is Stokes either: `stateOf` is the only external datum, and it is
the branch state every `Core.Problem` already has to publish.
-/

namespace Hypostructure.PDE.Strategy.Registry.CounterexampleReduction

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
  (stateOf : ∀ object : M.problem.Ambient, M.problem.BranchState object)

/-! ## The stage of a bare object

`BalancedRegularity.stageReached` reads a *residual*: an object together with
its baseline and its branch state.  The reduction record reads bare ambient
objects, so this section transports the stage across that gap.  The transport
is total and it is the only place `stateOf` is consumed: the branch state is
the problem's own publication, never an analytic choice.
-/

/--
**The alternative the local argument reaches on an object.**

An object that carries the baseline presents the residual
`⟨object, baseline, stateOf object⟩`, and its stage is that residual's.  An
object off the baseline is not a problem object at all, so the local argument
never starts on it and its stage is the first alternative --- which, by
`stageDeficit` below, makes it maximally far from closing and hence never a
legitimate window.
-/
noncomputable def stageOf (object : M.problem.Ambient) : Stage :=
  letI := Classical.propDecidable
  if baseline : M.problem.Baseline object then
    system.stageReached
      { object := object
        baseline := baseline
        branchState := stateOf object }
  else .regular

/--
**The stage deficit of an object**: how many of the six alternatives the local
argument still has to clear on it.  It is `0` exactly on the objects where the
argument has reached `gradientClosed`, and `Stage.gradientClosed.rank` on the
objects where it has not started.
-/
noncomputable def stageDeficit (object : M.problem.Ambient) : Nat :=
  Stage.gradientClosed.rank - (stageOf system stateOf object).rank

/--
**The registered progress of a global-regularity problem.**

An object is *smaller* when the local argument gets strictly further on it.
That is the only well-founded order a stratified regularity argument produces
on its own: there is no universal analytic size (`PDE.Progress` says as much),
but there are six ordered states and the argument only ever moves up them, so
the deficit only ever moves down.  Well-foundedness is `Nat`'s.
-/
noncomputable def stageProgress : Core.Progress.{u, u, 0} M.problem where
  Measure := Nat
  lt := (· < ·)
  wellFounded := Nat.lt_wfRel.wf
  measure := stageDeficit system stateOf

/-! ## The target algebra

CT1 asks for a code type, an acceptance predicate on codes, and the
equivalence between the target and the existence of an accepted code.  The
code is the stage; acceptance says the stage is the closing one.
-/

/--
**An object is closed** when the local argument reaches the sixth alternative
on one of its baselines, or when the object already answers the target.

The second disjunct is not slack: `BalancedRegularity` registers the balance
in one direction only --- a smooth velocity *gives* the target
(`target_of_gradientClosed`), while the target is an arbitrary predicate that
smoothness implies and that implies nothing back.  So "closed" is the largest
reading of the sixth alternative that is still a property of the object, and
`target_iff_closed` shows it is exactly the target.
-/
def Closed (object : M.problem.Ambient) : Prop :=
  (∃ baseline : M.problem.Baseline object,
      system.GradientClosed
        { object := object
          baseline := baseline
          branchState := stateOf object }) ∨
    T.Predicate object

/--
**Closure is the target.**

The forward direction is the second disjunct.  The backward direction is the
one piece of PDE content this module consumes: a residual that reached
`gradientClosed` has a smooth velocity, and the balance then names the
pressure gradient and hands over the registered target.
-/
theorem target_iff_closed (object : M.problem.Ambient) :
    T.Predicate object ↔ Closed system stateOf object := by
  constructor
  · intro target
    exact Or.inr target
  · rintro (⟨baseline, reached⟩ | target)
    · exact system.target_of_gradientClosed
        { object := object
          baseline := baseline
          branchState := stateOf object } reached
    · exact target

/--
**The code of an object**: which of the six ordered alternatives the local
argument reached on it.  The stratification is finite and problem-independent,
so the code type is the same for every object and is `Stage` itself, lifted to
the ambient universe.
-/
def StageCode (_object : M.problem.Ambient) : Type u :=
  ULift.{u, 0} Stage

/--
**A code is accepted when it is the closing stage of a closed object.**

Both conjuncts are needed and neither is decorative: the first says the code
names alternative 6 rather than one of the five that leave a residual, the
second says the object really sits there.
-/
def Accepts (object : M.problem.Ambient) (code : StageCode object) : Prop :=
  code.down = Stage.gradientClosed ∧ Closed system stateOf object

/-! ## Windows of the tower

The localization built from `BalancedRegularity.singularityProfile` produces a
nested tower of windows around the singularity.  A *subobject* is one of its
windows, presented the way `SubobjectMinimalityProfile` reads it: the ambient
object the window restricts to, the fact that the local argument gets strictly
further there, and the interior-regularity transport that carries a regular
window back up to the object it was cut from.
-/

/--
**A window of the tower around the singularity.**

`progressed` is the strict decrease `minimalSubobjectExclusion` needs, and
under `stageProgress` it says exactly what a localization step is for: the
restricted object clears at least one more alternative than the object it came
from.  `regularity` is interior regularity read as transport --- regularity on
the window is regularity of the whole, which is the direction a covering
argument runs.
-/
structure Window (object : M.problem.Ambient) : Type u where
  /-- The ambient object the window restricts to. -/
  restricted : M.problem.Ambient
  /-- The local argument clears strictly more alternatives on the window. -/
  progressed :
    stageDeficit system stateOf restricted < stageDeficit system stateOf object
  /-- Interior regularity: a regular window makes the whole object regular. -/
  regularity : T.Predicate restricted → T.Predicate object

/--
**An atomic window**: a window of the tower that carries a single stage.

"Atomic" is the finite-algebra reading of a window: instead of a mixture of
alternatives over a subcover, the window sits at one alternative, named by
`stage`.  `balance` is the only law attached to it, and it is attached where
it belongs --- a window on which the argument has closed still carries the
balance, so what is left after deleting it is still a problem object.
-/
structure AtomicWindow (object : M.problem.Ambient) : Type u where
  /-- The underlying window of the tower. -/
  window : Window system stateOf object
  /-- The single alternative the window carries. -/
  stage : Stage
  /-- The balance survives on a window the argument has already closed. -/
  balance : stage = Stage.gradientClosed →
    M.problem.Baseline object → M.problem.Baseline window.restricted

/--
**A window is critical when it still carries the singularity**, that is, when
the alternative it sits at is not the closing one.  Deleting a critical window
deletes the obstruction with it, so what is left is no longer a counterexample
and the minimal-counterexample argument gains nothing; deleting a non-critical
one leaves a genuine smaller problem object, which is exactly the content of
`baseline_of_not_critical`.
-/
def Critical (object : M.problem.Ambient)
    (atomic : AtomicWindow system stateOf object) : Prop :=
  atomic.stage ≠ Stage.gradientClosed

/--
**A closed window**: an atomic window on which the local argument has already
reached the sixth alternative.  These are the members
`criticalModificationStructure` scans, and they are precisely the non-critical
ones.
-/
def ClosedWindow (object : M.problem.Ambient) : Type u :=
  { atomic : AtomicWindow system stateOf object //
      atomic.stage = Stage.gradientClosed }

/--
**Two closed windows are nested** when one is a window of the other: the tower
takes one step from the outer to the inner.  This is the relation whose
witnesses `criticalModificationStructure` turns into atomic modifications, and
the modification it produces is the inner window of the step.
-/
def Nested (object : M.problem.Ambient)
    (inner outer : ClosedWindow system stateOf object) : Prop :=
  ∃ step : Window system stateOf outer.val.window.restricted,
    step.restricted = inner.val.window.restricted

/-! ## Interface replacement

`interfaceReplacementClosure` needs an atom/context assembly and a signature.
PDE already owns both constructions
(`PDE.Strategy.InterfaceReplacement.profile`); this section only supplies the
decomposition and the trace datum, and reuses that profile verbatim.
-/

/--
**The single-piece decomposition of a localized problem.**

The framework's localization has already cut the object down to one nested
tower around one singularity, so there is one interface --- the boundary of
the outer window --- one piece, which is the localized object itself, and a
point context.  A model with a genuine multi-window cut replaces this
decomposition and nothing else.
-/
def decomposition : PDE.Boundary.Decomposition.{u, u, u, u} M.problem where
  interface := { Label := PUnit }
  Piece := fun _ => M.problem.Ambient
  Outside := fun _ => PUnit
  assemble := fun _ piece _ => piece
  compatible := fun _ _ => True
  decompose := fun object => ⟨PUnit.unit, object, PUnit.unit⟩
  reconstruct := fun _ _ => rfl

/--
**The registered interface-replacement profile.**

The semantics is equality --- a represented balance is determined by its own
fields, so no two distinct ambient objects are silently identified --- and the
target is invariant under it for free.  The signature, the datum a replacement
piece has to match across the interface, is the stage: a candidate replacement
is admissible when the local argument reaches the *same* alternative on it, so
the replacement cannot buy regularity it has not paid for.
-/
noncomputable def interfaceProfile :
    Core.Strategy.InterfaceReplacement.Profile
      (P := M.problem) (T := T) (stageProgress system stateOf) :=
  PDE.Strategy.InterfaceReplacement.profile
    (Level := Unit) (uMeasure := ())
    (stageProgress system stateOf)
    (Core.SemanticEquivalence.equality M.problem)
    (Core.TargetInvariant.equality M.problem T.Predicate)
    (decomposition (M := M))
    (fun _ => trivial)
    (fun _ => ULift.{u, 0} Stage)
    (fun piece => ULift.up (stageOf system stateOf piece))

/-! ## The registration -/

/--
**The registered counterexample reduction of a balanced global-regularity
problem.**

This is the value that goes into `Core.StrategyData.counterexampleReductions`,
and it is the whole of what the four vertices `targetAlgebraReduction`,
`minimalSubobjectExclusion`, `criticalModificationStructure` and
`interfaceReplacementClosure` consume.  Every field is a reading of the six-state
stratification; the single analytic step, `target_of_gradientClosed`, is the
framework's own and enters through `target_iff_closed`.
-/
noncomputable def counterexampleReduction :
    Core.CounterexampleReductionData.{u, u, 0} M.problem T where
  selection :=
    Core.MinimalCounterexampleSelectionData.ofProgress
      (stageProgress system stateOf)
      { name := "Stage-deficit minimal counterexample"
        note := "The measure is how many of the six alternatives of the \
          regularity stratification are still open." }
  Code := fun object => StageCode object
  Accepts := Accepts system stateOf
  target_iff_code := by
    intro object
    constructor
    · intro target
      exact ⟨ULift.up Stage.gradientClosed,
        rfl, (target_iff_closed system stateOf object).mp target⟩
    · rintro ⟨_code, accepted⟩
      exact (target_iff_closed system stateOf object).mpr accepted.2
  acceptsDecidable := fun _object _code => Classical.propDecidable _
  Subobject := Window system stateOf
  subobjectProfile := {
    toAmbient := fun window => window.restricted
    smaller := fun window => window.progressed
    targetMonotone := fun window regular => window.regularity regular
    stateOf := stateOf }
  Atomic := AtomicWindow system stateOf
  Carrier := ClosedWindow system stateOf
  Related := Nested system stateOf
  Critical := Critical system stateOf
  atomicSubobject := fun atomic => atomic.window
  baseline_of_not_critical := fun baseline atomic notCritical =>
    atomic.balance (not_not.mp notCritical) baseline
  atomic_of_related := fun inner _outer _nested => inner.val
  noncritical_of_related := fun inner _outer _nested =>
    not_not_intro inner.property
  metadata :=
    { name := "Balanced global-regularity counterexample reduction"
      note := "Every reading is a function of the six ordered alternatives of \
        the regularity stratification." }
  targetAlgebraMetadata :=
    { name := "Stage code"
      note := "The code of an object is the alternative the local argument \
        reached on it; it is accepted when that alternative is the closing \
        one." }
  minimalSubobjectMetadata :=
    { name := "Window of the tower"
      note := "A subobject is a window on which the argument clears strictly \
        more alternatives, and regularity of the window is regularity of the \
        object." }
  criticalModificationMetadata :=
    { name := "Critical window"
      note := "A window is critical when it still carries the singularity; a \
        non-critical one leaves the balance intact on what remains." }
  interfaceReplacement := interfaceProfile system stateOf
  interfaceReplacementClosureMetadata :=
    { name := "Stage-matching replacement"
      note := "A replacement piece must reach the same alternative across the \
        interface, so it cannot buy regularity it has not paid for." }

end Hypostructure.PDE.Strategy.Registry.CounterexampleReduction
