import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.Spine.SpineWindows

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

/-! ## Node `[23]`: the live-hot window overflow -/

/-! **Node `[23]`, the live-hot entropy comparison.**  On the literal overflow
residual, `def:cold-window-ledger` says that the canonical hot family either
has its full package realized by labelled skeletons or is empty.  In the first
case `lem:p13-window-package` converts the registered rate into a lower bound
on the realized state count and `lem:skeleton-dominates` bounds that count by
the skeleton budget.  In the empty case the required package has one state,
while the selected object's skeleton class is nonempty.  Thus the exact cap
opposite to the overflow arm holds.

All three manuscript premises are read through `FactInputs.get`, and the
statement is indexed by `inputs.current`; no detached graph or proof payload is
accepted by the row. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def liveHotBarrierCapRow :
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
    `Hypostructure.Graph.Strategy.Spine.liveHotBarrierCap
    { Requires :=
        [K .hotColdPartition, K .skeletonDominates, K .windowPackageSeparated]
      Produces := [K .barrierCap]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .barrierCap)
        ⟨Contracts.Spine.barrierCap_of_hotColdPartition data.toParameters
          inputs.current.object (inputs.get (K .hotColdPartition)).down
          (inputs.get (K .skeletonDominates)).down
          (inputs.get (K .windowPackageSeparated)).down⟩
        .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
