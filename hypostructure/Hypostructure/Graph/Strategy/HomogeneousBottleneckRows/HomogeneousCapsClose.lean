import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Strategy.HomogeneousBottleneckRows.Basic
import Hypostructure.Graph.Contracts.SurplusPair.Estimate

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-- Node `[144]`, capped arm, `cor:homogeneous-same-token-caps-close` with
`thm:homogeneous-overload-geometric-closure`: on the literal fixed-caps
residual, spend the sparse slack identity and publish the manuscript's
homogeneous-cap closure statement; at the object's certified capacity ledger
it is the sparse-pressure cap at `M₀ = Cap_hom(L_geom)`, which gives node
`[138]`'s `σ(G) ≤ C_sp ⌈√n⌉`. -/
@[reducible] noncomputable def homogeneousCapsCloseRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.homogeneousCapsClose
    { Requires := [K .homogeneousCapsHold, K .sparseSlackSurplus,
        K .surplusAbove, K .surplusPresentation]
      Produces := [K .homogeneousBottleneck, K .spineSurplusEstimate]
      requiresUnique := by key_fresh
      producesUnique := by key_fresh
      producesNonempty := by simp }
    (fun inputs =>
      let close : Holds BranchState Presentation presentation data
          .homogeneousBottleneck inputs.current.object :=
        Graph.Contracts.SurplusPair.homogeneousBottleneck_of_capsHold
          (inputs.get (K .homogeneousCapsHold)).down
          (inputs.get (K .sparseSlackSurplus)).down
      .cons (key := K .homogeneousBottleneck) ⟨close⟩
        (.cons (key := K .spineSurplusEstimate)
          ⟨Graph.Contracts.SurplusPair.spineSurplusEstimate_of_capsClose close
            (inputs.get (K .surplusAbove)).down
            (inputs.get (K .surplusPresentation)).down.2.2.2.1
            (inputs.get (K .surplusPresentation)).down.2.2.2.2⟩
          .nil))

end Hypostructure.Graph.Strategy.Spine
