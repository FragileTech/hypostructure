import Hypostructure.PDE.Strategy.RegularityRegistry
import Hypostructure.PDE.Strategy.ObstructionPackingClosure

/-!
# The window packing and its normalized complement

`RegularityRegistry` registers the six *accounting* families of a balanced
system --- how much a window demands, supplies, and is charged.  This module
registers the two *geometric* ones, and they are chained: a support-complement
normalization is indexed by the packing whose complement it normalizes, so the
second registration below names the first.

| family | PDE reading |
| --- | --- |
| obstruction packing | the admissible windows around the singularity, two of them conflicting exactly when they overlap |
| support normalization | the cells left over once the selected windows are removed |

The reading is the appendix's own.  A global-regularity argument covers the
singularity by admissible windows, keeps a maximal pairwise-disjoint
subfamily, and then has to say what happens on what is left.  Core owns all of
that: it selects the canonical maximal packing (CT1), cuts the ambient cells
into the covered and the uncovered part (CT9), compares the leftover mass with
the density cap (CT14), rescans the leftover for obstructions (CT1), and scans
the leftover cells in order (CT6).  The two registrations below contribute
carriers, the overlap relation, and the one implication that closes the
problem; they execute, decide, route and write nothing.

Both `freeForcesTarget` and `failureForcesTarget` --- the only two implications
either family owns --- are the *same* PDE fact,
`BalancedRegularity.target_of_gradientClosed`: once the velocity is smooth on
the region the balance names its own pressure gradient, and that is the
registered target.  Neither is a vacuous arm: the window schedule is cold
exactly while the argument has not closed, so "no window survives" and "a
leftover cell carries the closing certificate" are two readings of
`Stage.gradientClosed`, the ceiling of `Stage.rank`.

Nothing here is Stokes-specific: the windows are the windows of any
incompressible parabolic balance.
-/

namespace Hypostructure.PDE.Strategy.Registry.PackingNormalization

open Hypostructure
open Hypostructure.PDE.Strategy
open Hypostructure.PDE.Strategy.RegularityStratification
open scoped Distributions ContDiff

universe u v w x y

variable {M : LocalModel.{u}} {T : Core.Target M.problem}
  {Place : Type v} [NormedAddCommGroup Place] [NormedSpace ℝ Place]
  [MeasurableSpace Place] [BorelSpace Place] [FiniteDimensional ℝ Place]
  {Value : Type w} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
  [CompleteSpace Value]
  {Index : Type x} [Fintype Index]
  {μ : MeasureTheory.Measure Place} [μ.IsAddHaarMeasure]
  (system : BalancedRegularity M T Place Value Index μ)

/-! ## The window schedule

The framework's derived nested tower around the singularity is one admissible
window, exactly as in `RegularityRegistry.windowSchedule`; a cover with more
windows replaces this profile and nothing else.

A window is *cold* --- it still obstructs --- precisely while the local
argument has not closed on it, i.e. while the velocity is not yet smooth on
the region.  That is what makes the empty-schedule arm of Core's CT1 carry
content instead of being an impossible branch: no cold window left is
`Stage.gradientClosed`.
-/

/--
**The admissible windows around the singularity, as a cold-window profile.**

`Window` is the derived nested tower, `schedule` is the singleton it forms,
and `cold` is failure of alternative 6: the window is an obstruction exactly
while `GradientClosed` does not hold.  Coldness is decided classically because
smoothness of a distributional representative is a genuine analytic
alternative, not a finite check --- Core never runs this decision, it only
filters the schedule with it.
-/
noncomputable def windowProfile :
    PDE.InducedPathCold.Profile (Core.Strategy.ProblemInput M.problem) where
  Window := fun _ => PUnit
  schedule := Core.Residual.Query.ofFunction fun _ =>
    Core.Finite.Enumeration.singleton PUnit.unit
  cold := fun input _ => ¬ system.GradientClosed input
  coldDecidable := fun input _ =>
    Classical.propDecidable (¬ system.GradientClosed input)

/-- The single cell of the derived tower is scheduled, whatever stage the
argument has reached.  This is the only fact about `windowProfile`'s schedule
the packing needs, and it is what makes "the cold schedule is empty" equivalent
to "alternative 6 is reached". -/
theorem unit_mem_schedule (input : Core.Strategy.ProblemInput M.problem) :
    PUnit.unit ∈
      (((windowProfile system).schedule).read input).values := by
  show PUnit.unit ∈ [PUnit.unit]
  exact List.Mem.head _

/-- **A cold window survives while the argument has not closed.**  Contrapositive
of the implication the packing registers: if the tower's window is not cold then
alternative 6 was reached. -/
theorem gradientClosed_of_coldValues_nil
    (input : Core.Strategy.ProblemInput M.problem)
    (empty : PDE.InducedPathCold.coldValues (windowProfile system) input = []) :
    system.GradientClosed input := by
  by_contra stillCold -- the window is cold, so it survives the filter
  have member :
      PUnit.unit ∈ PDE.InducedPathCold.coldValues (windowProfile system) input := by
    letI : ∀ window : (windowProfile system).Window input,
        Decidable ((windowProfile system).cold input window) :=
      (windowProfile system).coldDecidable input
    refine List.mem_filter.mpr ⟨unit_mem_schedule system input, ?_⟩
    exact decide_eq_true stillCold
  rw [empty] at member
  exact List.not_mem_nil member

/-! ## The registered packing

An occurrence is a window and two occurrences conflict exactly when the cells
they cover overlap.  That is the reading Core's canonical maximal selection is
built for, and it is the reading the normalization below needs: "conflict" has
to be "shares an ambient cell" for the maximality law to be derivable.
-/

/--
**The registered window packing.**

The cold-window adapter is Core's own PDE hook: it takes the exact schedule and
turns overlap of the covered cells into the conflict relation Core packs
against.  The obstruction-free arm is not empty talk --- by
`gradientClosed_of_coldValues_nil` an empty cold schedule *is* alternative 6,
and `target_of_gradientClosed` reads the registered target off it.
-/
noncomputable def windowPacking :
    Core.Strategy.ObstructionPackingClosure.Semantics.{u, y}
      (Core.Strategy.ProblemInput M.problem)
      (fun input => T.Predicate input.object) :=
  PDE.Strategy.ObstructionPackingClosure.coldWindowSemantics
    (fun input => T.Predicate input.object)
    (windowProfile system)
    (fun _ => PUnit.{y + 1})
    (fun _ _ => {PUnit.unit})
    (fun input empty =>
      system.target_of_gradientClosed input
        (gradientClosed_of_coldValues_nil system input empty))

/-! ## The registered normalization

The ambient items are the cells a window covers, `cover` returns them, and the
complement CT9 cuts out is the part of the tower no selected window reaches.
Its local pieces are its own cells --- there is nothing to reconstruct, so
`localPieces` is the complement enumeration itself.

CT6 scans those leftover cells and stops at the first *failure*.  As everywhere
in this family, a "failure" is the event that closes the problem rather than one
that breaks it: a leftover cell fails when the local argument terminates there
with the smooth representative, and `failureForcesTarget` is then
`target_of_gradientClosed` again.  When the argument has not closed, no window
is free, the packing covers the single cell, the complement is empty, there is
no piece to fail, and Core routes to its normalized successor.
-/

/--
**The registered support-complement normalization.**

Every field is inert data read off the same derived tower as the packing.
`conflict_iff_shared_item` is the overlap reading spelled out: two windows
conflict when their covered cells meet, which for the derived tower is
`Finset.not_disjoint_iff` on its single cell.  `cover_ne` holds because a
window is nonempty --- it covers the cell it is a window on --- and that single
provision is all Core needs to derive packing maximality and the leftover-mass
bound, so neither becomes an application obligation.

`contribution` is `Stage.rank`, as in every accounting family of
`RegularityRegistry`: how far the local argument got at the cell, on the 0..5
scale whose ceiling is `Stage.gradientClosed.rank`.
-/
noncomputable def windowNormalization :
    Core.Strategy.SupportComplementNormalization.Registration
      (Core.Strategy.ProblemInput M.problem)
      (fun input => T.Predicate input.object)
      (windowPacking system) where
  AmbientItem := fun _ => PUnit
  ambientSupport := fun _ => Core.Finite.Enumeration.singleton PUnit.unit
  cover := fun _ _ => [PUnit.unit]
  coverNodup := by simp
  coverSupported := by simp
  coverCard := fun _ => 1
  cover_card := by simp
  conflict_iff_shared_item := by
    intro _input _left _right
    have shared : ∃ item : PUnit, item ∈ [PUnit.unit] ∧ item ∈ [PUnit.unit] :=
      ⟨PUnit.unit, List.mem_singleton_self _, List.mem_singleton_self _⟩
    have overlap :
        ¬ Disjoint ({PUnit.unit} : Finset PUnit) ({PUnit.unit} : Finset PUnit) :=
      Finset.not_disjoint_iff.mpr
        ⟨PUnit.unit, Finset.mem_singleton_self _, Finset.mem_singleton_self _⟩
    exact ⟨fun _ => shared, fun _ => overlap⟩
  cover_ne := fun _ _ => List.cons_ne_nil _ _
  LocalPiece := fun _ _ => PUnit
  localPieces := fun _ complement => complement
  FailureData := fun input _ _ => ULift (PLift (system.GradientClosed input))
  Failure := fun input _ _ => system.GradientClosed input
  failureData := fun _ _ _ closed => ULift.up (PLift.up closed)
  failureDecidable := fun input _ _ =>
    Classical.propDecidable (system.GradientClosed input)
  contribution := fun input _ _ => (system.stageReached input).rank
  failureForcesTarget := fun input _ _ closed _ =>
    system.target_of_gradientClosed input closed

end Hypostructure.PDE.Strategy.Registry.PackingNormalization
