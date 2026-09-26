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

/-- Node `[125]`, `def:named-surplus-exits`: test the paper's five named
sparse-surplus exits on the literal incoming ledger.  The left arm publishes
the concrete exit; the right arm publishes exactly its negation, namely that
the current object survives all five exits.  This is the manuscript's
"after sparse exits" branch point: selection and replacement facts are not
re-proved here.  Every target-defect inhabitant retains the concrete
rank-reducing attempted quotient supplied by its originating residual; no
arbitrary boundary defect or `DeclaredQuotient` is fabricated here. -/
noncomputable def sparseSurplusSurvivorDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous : ExactLedger (Input BranchState Presentation presentation data)
      current known)
    (exitFresh : K .sparsePairExit ∉ known)
    (survivorFresh : K .sparseSurplusSurvivor ∉ known) :
    Decision (K .sparsePairExit) (K .sparseSurplusSurvivor) previous :=
  Decision.run previous (K .sparsePairExit) (K .sparseSurplusSurvivor)
    `Hypostructure.Graph.Strategy.Spine.sparseSurplusSurvivorDichotomy
    (Classical.choice (show Nonempty
        ((K .sparsePairExit).At current ⊕
          (K .sparseSurplusSurvivor).At current) from by
      by_cases exit : Graph.SparseSurplusExit
          (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) data.LengthOK current.object
      · exact ⟨.inl ⟨exit⟩⟩
      · exact ⟨.inr ⟨exit⟩⟩))
    exitFresh survivorFresh

/-- Node `[125]`, named sparse-exit routing.  Four constructors are literal
terminals against facts already present in the incoming residual.  The
target-defect constructor alone survives, retaining its concrete attempted
quotient as the paper's target-defect handoff. -/
@[reducible] noncomputable def sparseSurplusExitRoutingRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.sparseSurplusExitRouting
    { Requires := [K .sparsePairExit, K .selection, K .replacementExclusion]
      Produces := [K .sparseTargetDefectResidual]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .sparseTargetDefectResidual)
        ⟨Graph.Contracts.SurplusPair.sparseTargetDefectResidual_of_exit
          (inputs.get (K .sparsePairExit)).down
          (inputs.get (K .selection)).down
          (inputs.get (K .replacementExclusion)).down⟩
        .nil)

end Hypostructure.Graph.Strategy.Spine
