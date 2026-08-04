import Hypostructure.Core.Strategy.ExactFiniteLocalAlgebraSemantics
import Hypostructure.Core.Strategy.Data
import Hypostructure.PDE.Singularity

/-!
# The regularity stratification as a finite local algebra

`stokes:prop:finite-state-stratification` records six ordered alternatives,
"exhaustive and mutually exclusive, and each closes by a local argument".  Read
as a *registration* rather than as prose, that is a finite labelled algebra:

* the **labels** are the six stages;
* the **items** are the admissible windows around the singularity;
* the **relation** is the refinement order --- reaching a stage means every
  earlier stage was reached;
* the **capacity** of a stage is how far the local argument has got.

`Core.Strategy.ExactFiniteLocalAlgebra` already owns the execution of exactly
this shape (CT9 enumerates the items, CT16 hashes the relation table and
compares it to the registered code), so nothing here executes, decides, routes,
or writes a ledger entry.  This module contributes the six-state semantics and
the window-to-stage labelling, which is the entire PDE content.

Nothing in this file is Stokes-specific: the stages are the stages of *any*
incompressible parabolic balance, and the module is parameterized by a local
model and its singularity profile.
-/

namespace Hypostructure.PDE.Strategy.RegularityStratification

open Hypostructure
open Core.Strategy.ExactFiniteLocalAlgebra

universe u

/-! ## The six states -/

/--
**The ordered alternatives of the regularity stratification.**

Each constructor is the state the local argument has reached at one window.
The order is the appendix's own: a later state presupposes every earlier one,
which is what `refines` below records and what makes the family a stratification
rather than six unrelated predicates.
-/
inductive Stage where
  /-- Case 1: the representative is already smooth near the singularity. -/
  | regular
  /-- Case 2, `stokes:prop:activity-gate`: the curl removes the pressure and
  leaves the local heat equation for the vorticity. -/
  | vorticityReduced
  /-- Case 3, `stokes:cor:vorticity-smoothing`: the vorticity is smooth on the
  compactly contained subcylinder. -/
  | vorticitySmoothed
  /-- Case 4, `stokes:lem:local-CZ-pressure`: the pressure splits into its
  Calderon-Zygmund child and the complementary tail. -/
  | pressureDecomposed
  /-- Case 5, `stokes:lem:velocity-recovery` and
  `stokes:lem:harmonic-kernel-normalization`: the quotient velocity is
  recovered and the harmonic kernel is normalized away. -/
  | velocityRecovered
  /-- Case 6, `stokes:lem:pressure-normalization`: the balance names the
  pressure gradient. -/
  | gradientClosed
  deriving DecidableEq, Repr

namespace Stage

/-- How far the local argument has got, as a number.  This is the `capacity`
the finite algebra carries; it orders the states and nothing more. -/
def rank : Stage → Nat
  | .regular => 0
  | .vorticityReduced => 1
  | .vorticitySmoothed => 2
  | .pressureDecomposed => 3
  | .velocityRecovered => 4
  | .gradientClosed => 5

/-- The complete list of states, in the appendix's order. -/
def all : List Stage :=
  [.regular, .vorticityReduced, .vorticitySmoothed, .pressureDecomposed,
    .velocityRecovered, .gradientClosed]

theorem mem_all (stage : Stage) : stage ∈ all := by
  cases stage <;> simp [all]

theorem nodup_all : all.Nodup := by decide

/-- The refinement order: `refines later earlier` when the later state
presupposes the earlier one.  This is the single relation of the algebra. -/
def refines (later earlier : Stage) : Bool := earlier.rank ≤ later.rank

/-- The complete schedule of states. -/
def schedule : Core.Finite.CompleteEnumeration Stage where
  toEnumeration := Core.Finite.Enumeration.ofNodupList all nodup_all
  complete := mem_all

end Stage

/-! ## The registered semantics

One relation --- refinement --- over the six states.  `targetCode` is forced to
be the table the schedules generate, so it cannot drift from the semantics it
claims to tabulate.
-/

/-- The single relation index: the stratification has exactly one relation. -/
abbrev RelationIndex : Type := Unit

/-- The complete schedule of relation indices. -/
def relationSchedule : Core.Finite.CompleteEnumeration RelationIndex :=
  Core.Finite.CompleteEnumeration.ofFinEnum (inferInstance : FinEnum Unit)

/--
**The six-state refinement semantics of the regularity stratification.**

Residual-indexed only because `Semantics` is; nothing here reads the input.
-/
def semantics (Input : Type u) : Semantics.{u, 0, 0} Input where
  Label := fun _ => Stage
  labels := fun _ => Stage.schedule
  capacity := fun _ stage => stage.rank
  RelationIndex := fun _ => RelationIndex
  relationIndices := fun _ => relationSchedule
  relation := fun _ _ later earlier => Stage.refines later earlier
  targetCode := fun _ =>
    ((relationSchedule.toEnumeration.product
      (Stage.schedule.toEnumeration.product
        Stage.schedule.toEnumeration)).values.map fun coordinate =>
          Stage.refines coordinate.2.1 coordinate.2.2)
  targetCode_exact := fun _ => rfl

/-! ## The registration

The items are the windows the framework's cover supplies around the
singularity, and the label of a window is the stage its local certificate
reaches.  Both are supplied by the caller as *data*: this module states no
analytic fact and proves no regularity.
-/

/--
**The window-to-stage labelling of one problem.**

`windows` is the finite family of admissible windows around the singularity;
`stageAt` says which alternative of the stratification closes at each.  A
caller that has a per-window certificate labels by the stage that certificate
reaches, which is exactly what `stokes:prop:finite-state-stratification`
asserts is always possible.
-/
structure Labelling (Input : Type u) where
  /-- The admissible windows around the singularity, as a finite schedule. -/
  Window : Input → Type u
  windows : (input : Input) → Core.Finite.Enumeration (Window input)
  /-- The alternative reached at each window. -/
  stageAt : (input : Input) → Window input → Stage

/--
**The registered exact finite local algebra of the stratification.**

This is the value that goes into `Core.StrategyData.exactFiniteLocalAlgebras`.
Core's `ExactFiniteLocalAlgebra` strategy runs CT9 over `windows` and CT16 over
the relation table; neither is invoked here.
-/
def Labelling.registration {Input : Type u} (labelling : Labelling Input) :
    Registration.{u, u, 0, 0} Input where
  Item := labelling.Window
  items := labelling.windows
  semantics := semantics Input
  label := labelling.stageAt

/-! ## The stage alternatives, as registered dichotomies

The same six states read as Core dichotomies, one per stage, so a DAG can walk
them in order.  Each is `Core.DichotomyData.ofAlternative`: Core decides the
alternative classically and retains its exact negation on the surviving arm.
-/

variable {M : LocalModel.{u}} {T : Core.Target M.problem}

/--
**One alternative of the stratification, registered.**

`Reached` is the proposition "the construction of this stage is available for
the selected residual".  A closing arm is supplied only where the mathematics
already derives the target.
-/
structure Alternative (M : LocalModel.{u}) (T : Core.Target M.problem) where
  /-- Which of the six states this vertex decides. -/
  stage : Stage
  /-- The proposition that state asserts of the selected residual. -/
  Reached : Core.Strategy.ProblemInput M.problem → Prop
  metadata : Core.Documentation := {}
  reachedMetadata : Core.Documentation := {}
  failedMetadata : Core.Documentation := {}
  /-- Closure from the alternative holding. -/
  closeReached : Option (PLift (∀ input : Core.Strategy.ProblemInput M.problem,
    PLift (Reached input) → T.Predicate input.object)) := none
  /-- Closure from the alternative failing --- available where the stage's
  construction is unconditional, so that its absence is absurd. -/
  closeFailed : Option (PLift (∀ input : Core.Strategy.ProblemInput M.problem,
    PLift (¬ Reached input) → T.Predicate input.object)) := none

/-- The registered dichotomy of one alternative. -/
noncomputable def Alternative.dichotomy (alternative : Alternative M T) :
    Core.DichotomyData.{u, u, 0} M.problem T :=
  Core.DichotomyData.ofAlternative alternative.Reached
    alternative.metadata alternative.reachedMetadata alternative.failedMetadata
    alternative.closeReached alternative.closeFailed

/-- The registered dichotomy list of an ordered stratification, in the
appendix's order.  A DAG indexes them by position. -/
noncomputable def dichotomies (alternatives : List (Alternative M T)) :
    List (Core.DichotomyData.{u, u, 0} M.problem T) :=
  alternatives.map Alternative.dichotomy

@[simp] theorem dichotomies_length (alternatives : List (Alternative M T)) :
    (dichotomies alternatives).length = alternatives.length := by
  simp [dichotomies]

end Hypostructure.PDE.Strategy.RegularityStratification
