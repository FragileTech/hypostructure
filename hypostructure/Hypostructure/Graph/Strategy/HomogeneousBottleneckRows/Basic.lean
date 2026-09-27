import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.NamedSurplusExits
import Hypostructure.Graph.SparsePressureLedger
import Hypostructure.Graph.GluedCrossingCycle

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-- Node `[180]`'s accepted cycle is incompatible with the selected
counterexample fact already present on the same ExactLedger. -/
noncomputable instance instIncompatibleSelectionPairPowerOfTwoCycle :
    Incompatible (Input BranchState Presentation presentation data)
      (K .selection) (K .pairPowerOfTwoCycle) where
  contradiction := fun _current selection cycle =>
    selection.down.1 cycle.down

/-- Node `[133]`: a named sparse surplus exit is incompatible with node
`[125]`'s survivor fact, which is exactly the absence of every such exit. -/
noncomputable instance instIncompatibleSparseSurplusSurvivorSparsePairExit :
    Incompatible (Input BranchState Presentation presentation data)
      (K .sparseSurplusSurvivor) (K .sparsePairExit) where
  contradiction := fun _current survivor exit => survivor.down exit.down

/-- Node `[19]`'s strict lower bound `σ(G) > C_sp ⌈√n⌉` is incompatible with a
spine surplus estimate `σ(G) ≤ C_sp ⌈√n⌉` on the same object. -/
noncomputable instance instIncompatibleSurplusAboveSpineSurplusEstimate :
    Incompatible (Input BranchState Presentation presentation data)
      (K .surplusAbove) (K .spineSurplusEstimate) where
  contradiction := fun current above estimate => by
    have lower : data.surplusThreshold current.object.vertexCount <
        current.object.degreeSurplus data.threshold := above.down
    have upper : current.object.degreeSurplus data.threshold ≤
        data.spineScale * Core.ceilSqrt current.object.vertexCount :=
      estimate.down
    exact Nat.not_lt_of_ge (by
      simpa [Parameters.surplusThreshold] using upper) lower

/-- The registered `C_sp` absorbs the safety coefficient of the generic
quadratic estimate: the homogeneous cap already does (`L_geom ≥ 2`), and
`C_sp` adds only nonnegative deficit and token-supply terms to it. -/
theorem Data.quadraticSafetyScale_le_spineScale (data : Data.{u}) :
    Graph.TokenLoad.quadraticSafetyScale ≤ data.spineScale := by
  have registered := data.quadraticSafetyScale_le_twiceAdditive
  change Graph.TokenLoad.quadraticSafetyScale ≤
    2 * (1 + 2 * Graph.SameTokenBlockerRoles.homogeneousTokenCap
      data.routingLabelBound) at registered
  change Graph.TokenLoad.quadraticSafetyScale ≤
    2 * (1 + 2 * Graph.SameTokenBlockerRoles.homogeneousTokenCap
      data.routingLabelBound) +
      (2 * data.surplusScale +
        2 * Graph.SameTokenBlockerRoles.homogeneousTokenCap
          data.routingLabelBound * (3 * (data.threshold - 1) + 2))
  omega

/-- Node `[125]`: publish, once, the presentation identities the
sparse-surplus rows spend (`SurplusPresentationStatement`), exactly as
`cubicBaselineRow` publishes the cubic baseline.  Every later surplus, pair and
`[144]` row reads them from the ledger with `inputs.get`. -/
@[reducible] noncomputable def surplusPresentationRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.surplusPresentation
    { Requires := []
      Produces := [K .surplusPresentation]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun _inputs =>
      .cons (key := K .surplusPresentation)
        ⟨data.baselineDeficitSafety, data.joinSlack, data.lengthOK_iff_powerOfTwo,
          data.routingLabelBound_eq, data.quadraticSafetyScale_le_spineScale⟩
        .nil)

end Hypostructure.Graph.Strategy.Spine
