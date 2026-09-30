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

/-- Node `[125]`, `def:named-surplus-exits`: G survives the named sparse exits
of its declared sparse family (Lean improvement: a theorem about G).  The named
exits are the two cycle conclusions in G, (a) an accepted cycle and (e) a
suppression-chord certificate whose lifted length is accepted, and `[4]`'s
selection refutes both
(`Graph.Contracts.SurplusPair.not_declaredSparseSurplusExit`).  No decision. -/
@[reducible] noncomputable def sparseSurplusSurvivorRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.sparseSurplusSurvivor
    { Requires := [K .selection]
      Produces := [K .sparseSurplusSurvivor]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .sparseSurplusSurvivor)
        ⟨Graph.Contracts.SurplusPair.not_declaredSparseSurplusExit
          (inputs.get (K .selection)).down⟩
        .nil)

end Hypostructure.Graph.Strategy.Spine
