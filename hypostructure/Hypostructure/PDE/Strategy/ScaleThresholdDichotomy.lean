import Hypostructure.Core.Strategy.ScaleThresholdDichotomySemantics
import Hypostructure.PDE.Strategy.RegularityStratification

/-!
# The parabolic scale threshold of a regularity stratification

A local regularity argument runs on a tower of nested cylinders, and at each
generation of that tower it demands a Sobolev grade.  The argument closes when
the grade the certificate *supplies* still covers the grade the next generation
*demands*, and it stalls when it does not.  That comparison is a scale-dependent
threshold in exactly the sense
`Core/Strategy/Official/Features/ScaleDependentThreshold.lean` already
formalizes: a finite table of fixed and scale-indexed rows, evaluated at the
current size and compared against the current load.

So the parabolic scaling of the appendix is not new machinery --- it is the
registered scale-threshold family, read with

* **size** = the generation of the nested window tower around the singularity,
* **load** = the rank of the stratification stage the local argument has
  reached there.

Core owns the threshold evaluation, the comparison, the route, the ledger entry
and the work accounting; this module supplies the two observations and the
table, which is all a registration may contain.
-/

namespace Hypostructure.PDE.Strategy.ScaleThresholdDichotomy

open Hypostructure
open Hypostructure.Core.Strategy.Official.Features

universe u

/--
**The parabolic scale threshold of a stratified local argument.**

`generation` reads how deep the nested window tower has gone --- for the
framework's own `NestedFocus` that is `outer`, `middle`, `inner`, so `0`, `1`,
`2` --- and the load is the rank of the stage reached, which is the capacity
the finite local algebra of `RegularityStratification` already assigns.

Nothing analytic is asserted.  The table is inert coefficient data and the two
observations are functions of the selected residual.
-/
noncomputable def stageScaleRegistration (M : LocalModel.{u})
    (table : ScaleDependentThreshold.Table)
    (generation : Core.Strategy.ProblemInput M.problem → Nat)
    (stage : Core.Strategy.ProblemInput M.problem →
      RegularityStratification.Stage) :
    Core.Strategy.ScaleThresholdDichotomy.Registration
      (Core.Strategy.ProblemInput M.problem) where
  table := fun _ => table
  size := generation
  load := fun input => (stage input).rank

@[simp] theorem stageScaleRegistration_table (M : LocalModel.{u})
    (table : ScaleDependentThreshold.Table) (generation stage)
    (input : Core.Strategy.ProblemInput M.problem) :
    (stageScaleRegistration M table generation stage).table input = table :=
  rfl

@[simp] theorem stageScaleRegistration_load (M : LocalModel.{u})
    (table : ScaleDependentThreshold.Table) (generation stage)
    (input : Core.Strategy.ProblemInput M.problem) :
    (stageScaleRegistration M table generation stage).load input =
      (stage input).rank :=
  rfl

/--
**The table of a stratification that gains one grade per generation.**

The parabolic bootstrap of `stokes:lem:local-heat-smoothing` gains a fixed
number of derivatives per nested cylinder, so the threshold is affine in the
generation.  `fixedRows` carries the starting grade and `scaleRows` the gain;
supplying it as data keeps the arithmetic auditable, which is the whole reason
`ScaleDependentThreshold.Table` retains its rows separately.
-/
def affineTable (startingGrade : Nat)
    (rows : List ScaleDependentThreshold.ScaleRow) :
    ScaleDependentThreshold.Table where
  fixedRows := [startingGrade]
  scaleRows := rows

@[simp] theorem affineTable_threshold_zero (startingGrade : Nat)
    (rows : List ScaleDependentThreshold.ScaleRow) :
    (affineTable startingGrade rows).threshold 0 = startingGrade := by
  simp [affineTable, ScaleDependentThreshold.Table.threshold_zero]

end Hypostructure.PDE.Strategy.ScaleThresholdDichotomy
