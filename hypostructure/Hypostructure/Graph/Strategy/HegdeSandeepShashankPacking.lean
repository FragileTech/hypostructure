import Hypostructure.Graph.External.HegdeSandeepShashank
import Hypostructure.Graph.Strategy.InducedPathPresentation
import Hypostructure.Graph.MinimumDegreeCycleTarget

/-!
# Induced-path presentation derived from the external cycle theorem

The Hegde--Sandeep--Shashank theorem is the framework's registered external
input.  Every consequence a minimum-degree cycle problem draws from it --- the
ambient closure law, its restriction to an induced sub-support, and the
transport of the resulting cycle back through the induced embedding --- is
owned here.

An application registers only its problem presentation, its executable cycle
length predicate together with the framework-owned bridge into that
predicate, and the target it already registered.  It supplies no proof and
repeats neither the external order nor the external threshold.
-/

namespace Hypostructure.Graph.Strategy

open Hypostructure
open Hypostructure.Graph

universe u v

variable {u v}

/-- The induced-path presentation of the external theorem for a canonical
minimum-degree cycle problem.

`order` is the external induced-path order and `baselineDegree` is the
problem's own registered threshold query; the numeric side condition is the
single hypothesis `thresholdOK`, comparing the registered baseline with the
external theorem's own threshold. -/
noncomputable def hegdeSandeepShashankInducedPathPresentation
    (k : Nat)
    (BranchState : FiniteObject.{u} → Type v)
    (Presentation : Type) (presentation : Presentation)
    (LengthOK : Nat → Prop)
    (lengthBridge : ∀ length,
      (∃ exponent : Nat, 2 ≤ exponent ∧ length = 2 ^ exponent) →
        LengthOK length)
    (thresholdOK : External.HegdeSandeepShashank.minimumDegree ≤ k)
    (T : Core.Target
      (problemWithPresentation (MinimumDegreeAtLeast.{u} k) BranchState
        Presentation presentation))
    (targetBridge : ∀ object, T.Predicate object ↔
      HasCycleWithLength LengthOK object) :
    InducedPathPresentation
      (Core.Strategy.ProblemInput
        (problemWithPresentation (MinimumDegreeAtLeast.{u} k) BranchState
          Presentation presentation))
      (fun input => T.Predicate input.object) where
  object := fun input => input.object
  order := fun _ =>
    External.HegdeSandeepShashank.inducedPathOrder
  order_pos := fun _ => by
    norm_num [External.HegdeSandeepShashank.inducedPathOrder]
  baselineDegree :=
    minimumDegreeThresholdQuery (k := k) (BranchState := BranchState)
      (Presentation := Presentation) (presentation := presentation)
  freeForcesTarget := by
    intro input free
    exact (targetBridge input.object).mpr
      (External.HegdeSandeepShashank.hasCycleWithLength lengthBridge
        thresholdOK input.object
        (minimumDegreeAtLeast_of_problemInput input) free)
  componentFreeForcesTarget := by
    intro input support minimumDegree free
    rcases External.HegdeSandeepShashank.hasCycleWithLength lengthBridge
      thresholdOK (input.object.induce support) minimumDegree free with
      ⟨certificate⟩
    exact (targetBridge input.object).mpr
      ⟨certificate.mapHom (input.object.induceEmbedding support).toHom
        (input.object.induceEmbedding support).injective⟩

end Hypostructure.Graph.Strategy
