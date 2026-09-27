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

/-! ## The presentation laws, published once at the entry

The registered presentation certifies the laws the spine, Branch D and the
near-cubic rows read: `thm:p13free` (the cited HSS closure law, node `[16]`),
the dyadic target, the full dyadic scale family, the finite `τ_win < 1/4`
slack, and the certified barrier table's label semantics.  This row is the one
place those presentation fields are read; it states each law at `G` and at
`G`'s induced subgraphs and appends it to the literal ledger, where every
consumer reads it with `inputs.get` (the `K .cubicBaseline` pattern). -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def spinePresentationLawsRow :
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
    `Hypostructure.Graph.Strategy.Spine.spinePresentationLaws
    (sourceFreeManifest (K .spinePresentationLaws))
    (fun inputs =>
      .cons (key := K .spinePresentationLaws)
        ⟨⟨data.freeForcesTarget inputs.current.object,
          fun support => data.freeForcesTarget (inputs.current.object.induce support),
          data.lengthOK_iff_powerOfTwo, data.separatedScaleCount_eq_log2,
          data.netCapRateSlack, data.windowBarrierLabel_mem,
          data.windowBarrierLabel_injective, data.windowBarrierLabel_surjective,
          data.windowBarrier_left_semantic, data.windowBarrier_right_semantic,
          data.windowBarrier_sum_semantic⟩⟩
        .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
