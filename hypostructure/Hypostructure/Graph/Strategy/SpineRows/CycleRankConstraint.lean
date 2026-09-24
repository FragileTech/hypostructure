import Hypostructure.Graph.Strategy.SpineRows.Basic

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

/-! ## `lem:cycle-rank`: the selected graph's rank lower bound

The manuscript defines `β(G) = m - n + 1` and proves
`β(G) ≥ n/2 + 1` from the handshake inequality `3n ≤ 2m`.  The ExactLedger
stores the division-free Nat statement `n + 2 ≤ 2β(G)`.  Its only input is
the active residual's registered minimum-degree baseline; no earlier proof is
reopened and no numerical graph data are supplied separately. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def cycleRankConstraintRow :
    @AtomicStrategy (Input BranchState Presentation presentation data) _
      (instFactSystem (BranchState := BranchState)
        (Presentation := Presentation) (presentation := presentation)
        (data := data)) :=
  letI : FactSystem (Input BranchState Presentation presentation data) :=
    instFactSystem (BranchState := BranchState) (Presentation := Presentation)
      (presentation := presentation) (data := data)
  @factOnly (Input BranchState Presentation presentation data) _
    (instFactSystem (BranchState := BranchState)
      (Presentation := Presentation) (presentation := presentation)
      (data := data))
    `Hypostructure.Graph.Strategy.Spine.cycleRankConstraint
    (sourceFreeManifest (K .cycleRankConstraint))
    (fun inputs =>
      let object := inputs.current.object
      let lower : ∀ vertex : object.Vertex,
          data.threshold ≤ object.degree vertex :=
        fun vertex => inputs.current.baseline.trans
          (object.minDegree_le_degree vertex)
      let thresholdHandshake :
          data.threshold * object.vertexCount ≤ 2 * object.edgeCount :=
        Graph.baselineDegree_mul_vertexCount_le_two_mul_edgeCount
          object data.threshold lower
      let handshake : 3 * object.vertexCount ≤ 2 * object.edgeCount :=
        (Nat.mul_le_mul_right object.vertexCount data.three_le_threshold).trans
          thresholdHandshake
      .cons (key := K .cycleRankConstraint)
        (show Value BranchState Presentation presentation data
            .cycleRankConstraint inputs.current from
          ⟨by
            change object.vertexCount + 2 ≤
              2 * (object.edgeCount + 1 - object.vertexCount)
            have rankNontruncated :
                object.vertexCount ≤ object.edgeCount + 1 := by
              omega
            rw [Nat.mul_sub_left_distrib]
            exact Nat.le_sub_of_add_le (by omega)⟩)
        .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
