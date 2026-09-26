import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.NamedSurplusExits
import Hypostructure.Graph.SparsePressureLedger
import Hypostructure.Graph.GluedCrossingCycle
import Hypostructure.Graph.Strategy.HomogeneousBottleneckRows.Basic

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-- Node `[180]`, direct arithmetic arm.  The row applies the canonical serial
spectrum API, recovers the actual simple cycle stored by `[179]`, proves its
exponent is at least two from simple-cycle length, and publishes the accepted
cycle. -/
@[reducible] noncomputable def pairPowerOfTwoCycleRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.pairPowerOfTwoCycle
    { Requires := [K .pairSerialArithmetic]
      Produces := [K .pairPowerOfTwoCycle]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs => by
      classical
      let package := Classical.choice
        (inputs.get (K .pairSerialArithmetic)).down
      let serial := package.1
      let arithmetic := Classical.choice package.2
      let spectrum := arithmetic.spectrum
      letI : NeZero arithmetic.modulus := arithmetic.modulus_neZero
      letI : NeZero spectrum.modulus :=
        { out := by
            change arithmetic.modulus ≠ 0
            exact NeZero.ne arithmetic.modulus }
      have spanning : spectrum.ScaleSpanning := by
        simpa [spectrum, PairSerialArithmetic.spectrum] using
          arithmetic.spanning
      let hit := spectrum.exists_pow_realized
        arithmetic.wide arithmetic.criterion spanning
      let exponent := Classical.choose hit
      have realized := Classical.choose_spec hit
      let cycle := Classical.choice realized
      have threeLe : 3 ≤ 2 ^ exponent := by
        rw [← cycle.length_eq]
        exact cycle.isCycle.three_le_length
      have exponentLower : 2 ≤ exponent := by
        by_contra lower
        have cases : exponent = 0 ∨ exponent = 1 := by omega
        rcases cases with zero | one
        · have powerEq : 2 ^ exponent = 1 := by simp [zero]
          omega
        · have powerEq : 2 ^ exponent = 2 := by simp [one]
          omega
      have accepted : data.LengthOK (2 ^ exponent) :=
        (data.lengthOK_iff_powerOfTwo (2 ^ exponent)).2
          (Core.DyadicLength.powerOfTwoLength_of_exists
            ⟨exponent, exponentLower, rfl⟩)
      let certificate : Graph.CycleCertificate inputs.current.object
          data.LengthOK :=
        { vertex := cycle.vertex
          walk := cycle.walk
          isCycle := cycle.isCycle
          length_ok := by simpa [cycle.length_eq] using accepted }
      exact .cons (key := K .pairPowerOfTwoCycle)
        (show Value BranchState Presentation presentation data
            .pairPowerOfTwoCycle inputs.current from
          ⟨⟨certificate⟩⟩)
        .nil)

end Hypostructure.Graph.Strategy.Spine
