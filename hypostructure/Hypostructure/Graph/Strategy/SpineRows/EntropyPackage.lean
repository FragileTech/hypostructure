import Hypostructure.Graph.Strategy.SpineVocabulary

/-! Independently compiled spine row declarations. -/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

variable [FactSystem (Input BranchState Presentation presentation data)]

/-! ## Node `[52]`: window plus remainder accounting

`prop:two-budget` (a) and the high-entropy half of `prop:p13-density`.  The
window package of node `[21]` and the remainder states of node `[51]` are one
target-testable family, and `eq:feasibility` compares the states it realizes
against the near-cubic skeleton budget.  The forced curvature cost of node
`[48]` is `def:Theta`'s sharpening, which `rem:closure-robust` says the closure
does not need and which is realized by remainder graphs already counted in the
remainder class; it is not a further factor of the demand.

This row commits the *demand* side of that comparison, exactly: raising the
joint demand to the `d`-th power clears the `1/d` the entropy split carries, and
substituting the high-entropy arm's own `n^{|R|} ≤ |𝒢(R)|^d` for the remainder
factor gives the manuscript's `2^{rate·p}·n^{|R|/d}`.  No independence
hypothesis is used to state a lower bound on what the branch has to distinguish;
the budget side is node `[53]`'s comparison. -/
@[reducible] noncomputable def entropyPackageRow
    (data : Data.{u}) :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.entropyPackageDemand
    { Requires := [K .remainderEntropyHigh]
      Produces := [K .entropyPackageDemand]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .entropyPackageDemand)
        (show Value BranchState Presentation presentation data
            .entropyPackageDemand inputs.current from
          ⟨by
            simp only [Holds]
            have packingSpec := Classical.choose_spec
              (inputs.current.object.exists_windowPacking_card_eq data.windowOrder)
            have high :=
              (inputs.get (K .remainderEntropyHigh)).down
                (canonicalWindowPacking data inputs.current.object) packingSpec.1
            rw [jointPackageDemand, mul_pow]
            exact Nat.mul_le_mul (le_refl _) high⟩)
        .nil)

end Hypostructure.Graph.Strategy.Spine
