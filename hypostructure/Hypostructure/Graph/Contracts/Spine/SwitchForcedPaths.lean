import Hypostructure.Graph.Statements.SwitchForcedPaths
import Hypostructure.Graph.Statements.Spine
import Hypostructure.Graph.Contracts.TypeB.Local

/-!
# Contracts: the forced paths and cycles of G's switches and vertex splits

Proof-agnostic contract lemmas for `Statements/SwitchForcedPaths.lean`, one
`<statement>_holds` per statement.  Each is stated over a `Graph.FiniteObject`
with the registered `Parameters`; the hypotheses are exactly facts the entry
ledger carries: the selection (`K .selection`), the baseline
(`K .minDegreeBaseline`), the presentation laws (`K .cubicBaseline`), the
tight-endpoint law (`K .tightEndpoint`) and the return avoidance
(`K .returnAvoidance`).  The mathematics is the vocabulary-free library
`Graph/SwitchForcedPaths.lean`.

This module imports no strategy, row, or vocabulary module.
-/

namespace Hypostructure.Graph.Contracts.Spine.SwitchForcedPaths

open Hypostructure
open Hypostructure.Graph
open Hypostructure.Graph.Strategy.Spine

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Parameters} {object : Graph.FiniteObject.{u}}

/-- The two-edge switch of G, from the selection and the baseline. -/
theorem twoSwitchForcedPath_holds
    (selection : SelectionStatement BranchState Presentation presentation data object)
    (baseline : MinDegreeBaselineStatement data object) :
    TwoSwitchForcedPathStatement data object := by
  intro u₁ v₁ u₂ v₂ a₁ a₂ h12 h1v2 hv1u2 hvv nonadj slack₁ slack₂
  exact Graph.SwitchForcedPaths.twoSwitch_forced_path selection.1
    (fun H smaller base => selection.2.sizeMinimal H smaller base) baseline
    a₁ a₂ h12 h1v2 hv1u2 hvv nonadj slack₁ slack₂

/-- The same-vertex switch of G, from the selection, the baseline and the
return avoidance. -/
theorem sameVertexSwitchForcedPath_holds
    (selection : SelectionStatement BranchState Presentation presentation data object)
    (baseline : MinDegreeBaselineStatement data object)
    (returnAvoidance : ReturnAvoidanceStatement data object) :
    SameVertexSwitchForcedPathStatement data object := by
  intro h u₁ u₂ a₁ a₂ h12 nonadj heavy
  obtain ⟨p, pp, ok⟩ := Graph.SwitchForcedPaths.sameVertexSwitch_forced_path selection.1
    (fun H smaller base => selection.2.sizeMinimal H smaller base) baseline
    a₁ a₂ h12 nonadj heavy
  exact ⟨p, pp, ok, Graph.SwitchForcedPaths.sameVertex_path_dichotomy selection.1
    returnAvoidance a₁ a₂ h12 p pp⟩

/-- The vertex split of G at every high centre, from the selection, the
baseline, the presentation laws (`δ = 3`, the quadrilateral accepted) and the
tight-endpoint law (which makes `G[N(h)]` a matching,
`lem:heavy-neighbourhood-normal-form`). -/
theorem highCentreSplitForced_holds
    (selection : SelectionStatement BranchState Presentation presentation data object)
    (baseline : MinDegreeBaselineStatement data object)
    (three : data.threshold = 3) (quadrilateral : data.LengthOK 4)
    (tight : TightEndpointStatement data object) :
    HighCentreSplitForcedStatement data object := by
  intro h high
  have normal := Graph.Contracts.TypeB.highCentreNormalForm selection.1 quadrilateral tight
    h high
  exact Graph.SwitchForcedPaths.highCentre_split_forced selection.1
    (fun H smaller base => selection.2.sizeMinimal H smaller base) baseline h
    (by omega) normal.inducedMatching

/-- The cross-vertex switch family of G, from the selection, the baseline and
the dyadic target law of the presentation. -/
theorem crossSwitchFamily_holds
    (selection : SelectionStatement BranchState Presentation presentation data object)
    (baseline : MinDegreeBaselineStatement data object)
    (dyadic : ∀ length, data.LengthOK length ↔ Core.DyadicLength.PowerOfTwoLength length) :
    CrossSwitchFamilyStatement data object := by
  have lengths : data.LengthOK = Core.DyadicLength.PowerOfTwoLength :=
    funext fun length => propext (dyadic length)
  have avoidsDyadic : ¬ Graph.HasCycleWithLength Core.DyadicLength.PowerOfTwoLength object :=
    lengths ▸ selection.1
  intro u₁ v h' a₁ vh dv dh
  refine ⟨?_, ?_⟩
  · intro u au hu1 huv hu1h na
    exact Graph.SwitchForcedPaths.twoSwitch_forced_path selection.1
      (fun H smaller base => selection.2.sizeMinimal H smaller base) baseline a₁ au
      (Ne.symm hu1) hu1h (Ne.symm huv) vh na dv dh
  · intro u u' j P Q au au' uu hj pp qp lp lq
    exact Graph.SwitchForcedPaths.star_forbidden avoidsDyadic hj au au' uu P Q pp qp lp lq

end Hypostructure.Graph.Contracts.Spine.SwitchForcedPaths
