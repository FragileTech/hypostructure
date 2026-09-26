import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.NamedSurplusExits
import Hypostructure.Graph.SparsePressureLedger
import Hypostructure.Graph.GluedCrossingCycle
import Hypostructure.Graph.Strategy.HomogeneousBottleneckRows.Basic
import Hypostructure.Graph.Contracts.SurplusPair.SparseExit

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-- Node `[20]`: expose the proved structure of the same bound target-defect
witness. The exact attempted quotient and identified pair are copied from the
incoming residual; its context is obtained from that pair's defect proof. -/
@[reducible] noncomputable def sparseTargetDefectStructureRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.sparseTargetDefectStructure
    { Requires := [K .sparseTargetDefectResidual, K .selection]
      Produces := [K .sparseTargetDefectStructure]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .sparseTargetDefectStructure)
        ⟨Graph.Contracts.SurplusPair.sparseTargetDefectStructure_of_residual
          (inputs.get (K .sparseTargetDefectResidual)).down
          (inputs.get (K .selection)).down.1⟩
        .nil)

end Hypostructure.Graph.Strategy.Spine
