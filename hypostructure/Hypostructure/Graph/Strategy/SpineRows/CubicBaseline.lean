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

/-! ## The presentation laws of G, published once at the entry

`cubicBaselineRow` is the one row that reads the registered presentation's
law fields.  It publishes them as the single ledger fact `K .cubicBaseline`
(`PresentationLawsStatement`), stated at the incoming residual's `G` and at
`G`'s induced subgraphs: the cubic baseline identities, the Type B presentation
facts (with the one copy of the dyadic target law), the sparse-surplus
presentation identities, and the spine laws (`thm:p13free` at `G` and `G[S]`,
the scale family, the net-cap slack, the barrier-table label semantics).
Every consumer reads the law it needs from this fact with `inputs.get`. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def cubicBaselineRow
    : @AtomicStrategy (Input BranchState Presentation presentation data) _
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
    `Hypostructure.Graph.Strategy.Spine.cubicBaseline
    { Requires := []
      Produces := [K .cubicBaseline]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .cubicBaseline)
        ⟨⟨data.threshold_eq_three, data.dischargeScale_eq_four,
            data.degenerateClosureRejected, data.windowRate_eq_barrier,
            data.labelCount, data.labelSizeDistribution⟩,
          ⟨data.quadrilateralAccepted, data.lengthOK_iff_powerOfTwo,
            data.fanCapSlack, data.highCentreDeficitSlack,
            data.bridgeMassSlack⟩,
          ⟨data.baselineDeficitSafety, data.joinSlack,
            data.routingLabelBound_eq, data.quadraticSafetyScale_le_spineScale⟩,
          ⟨data.freeForcesTarget inputs.current.object,
            fun support =>
              data.freeForcesTarget (inputs.current.object.induce support),
            data.separatedScaleCount_eq_log2,
            data.netCapRateSlack, data.windowBarrierLabel_mem,
            data.windowBarrierLabel_injective, data.windowBarrierLabel_surjective,
            data.windowBarrier_left_semantic, data.windowBarrier_right_semantic,
            data.windowBarrier_sum_semantic⟩⟩ .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
