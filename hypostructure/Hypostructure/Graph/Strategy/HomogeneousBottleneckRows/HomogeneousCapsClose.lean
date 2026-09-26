import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.NamedSurplusExits
import Hypostructure.Graph.SparsePressureLedger
import Hypostructure.Graph.GluedCrossingCycle
import Hypostructure.Graph.Strategy.HomogeneousBottleneckRows.Basic
import Hypostructure.Graph.SparseUpperEnvelope

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
residual, spend the already registered sparse slack identity and publish the
manuscript's homogeneous-cap closure statement.  At the certified capacity
ledger already on the branch, that closure is the sparse-pressure bound `R_L(n)`
at `M₀ = Cap_hom(L_geom)`, so the same generic quadratic absorption as node
`[137]`'s capped arm gives node `[138]`'s `σ(G) ≤ C_sp ⌈√n⌉`. -/
@[reducible] noncomputable def homogeneousCapsCloseRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.homogeneousCapsClose
    { Requires := [K .homogeneousCapsHold, K .sparseSlackSurplus,
        K .fibrePressure, K .surplusAbove]
      Produces := [K .homogeneousBottleneck, K .spineSurplusEstimate]
      requiresUnique := by key_fresh
      producesUnique := by key_fresh
      producesNonempty := by simp }
    (fun inputs =>
      let close : Holds BranchState Presentation presentation data
          .homogeneousBottleneck inputs.current.object :=
        Graph.homogeneousCapsCloseStatement inputs.current.object
          (inputs.get (K .homogeneousCapsHold)).down
          (inputs.get (K .sparseSlackSurplus)).down
      .cons (key := K .homogeneousBottleneck)
        (show Value BranchState Presentation presentation data
            .homogeneousBottleneck inputs.current from ⟨close⟩)
        (.cons (key := K .spineSurplusEstimate)
          (show Value BranchState Presentation presentation data
              .spineSurplusEstimate inputs.current from
            ⟨by
              obtain ⟨_active, capacity, _activationEq, certified, _token,
                  _role, _tokenMem, _display, _roleBound, _forced,
                  _pattern⟩ :=
                (inputs.get (K .fibrePressure)).down
              have above : data.surplusThreshold
                    inputs.current.object.vertexCount <
                  inputs.current.object.degreeSurplus data.threshold :=
                (inputs.get (K .surplusAbove)).down
              obtain ⟨_loads, _blocked, surplus, _edges⟩ :=
                close capacity certified.ledger
              have capped : Graph.SparsePressureCappedAt certified
                  data.routingLabelBound := by
                have patternEq :
                    Graph.SameTokenRoutingGerms.patternBound
                        (Graph.SameTokenRoutingGerms.RoutingLabel
                          data.BoundaryProfile
                          (Graph.WindowCurvature.Label data.windowOrder)) =
                      Graph.SameTokenBlockerRoles.geometricPatternBound
                        data.routingLabelBound := by
                  unfold Graph.SameTokenRoutingGerms.patternBound
                    Graph.SameTokenRoutingGerms.labelBound
                    Graph.SameTokenBlockerRoles.geometricPatternBound
                  rw [data.routingLabelBound_eq]
                rw [patternEq] at surplus
                exact surplus
              have sizePos : 0 < inputs.current.object.vertexCount :=
                inputs.current.object.vertexCount_pos_of_degreeSurplus_pos
                  (lt_of_le_of_lt (Nat.zero_le _) above)
              have safety := data.quadraticSafetyScale_le_spineScale
              have estimate := Graph.surplus_le_scale_of_capped capacity
                certified data.routingLabelBound capped sizePos safety
              change inputs.current.object.degreeSurplus data.threshold ≤
                data.spineScale * Core.ceilSqrt inputs.current.object.vertexCount
              exact estimate⟩)
          .nil))

end Hypostructure.Graph.Strategy.Spine
