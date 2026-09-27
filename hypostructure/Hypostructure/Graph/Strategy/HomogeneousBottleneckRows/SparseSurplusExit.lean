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
re-proved here.  The exits are tested at G's declared sparse family
(`DeclaredSparseSurplusExit`): clause (b) is a target-defective identification
of two of G's own declared coordinates read on G's own piece.

The node's box reads "after `P₁₃` label algebra and sparse exits": the decision
reads that predecessor fact (`K .localAlgebra`) from the ledger.  The exit test
itself is a property of G's declared sparse family, with no further witness to
pin, so its two arms are the exit and its literal negation. -/
noncomputable def sparseSurplusSurvivorDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous : ExactLedger (Input BranchState Presentation presentation data)
      current known)
    [FactKeys.Has (K .localAlgebra) known]
    (exitFresh : K .sparsePairExit ∉ known)
    (survivorFresh : K .sparseSurplusSurvivor ∉ known) :
    Decision (K .sparsePairExit) (K .sparseSurplusSurvivor) previous :=
  Decision.run previous (K .sparsePairExit) (K .sparseSurplusSurvivor)
    `Hypostructure.Graph.Strategy.Spine.sparseSurplusSurvivorDichotomy
    (Classical.choice (show Nonempty
        ((K .sparsePairExit).At current ⊕
          (K .sparseSurplusSurvivor).At current) from by
      have _labelAlgebra := (previous.get (K .localAlgebra)).down
      by_cases exit : DeclaredSparseSurplusExit data.toParameters current.object
      · exact ⟨.inl ⟨exit⟩⟩
      · exact ⟨.inr ⟨exit⟩⟩))
    exitFresh survivorFresh

/-- Node `[125]`, named sparse-exit routing.  Four constructors are literal
terminals against facts already present in the incoming residual.  The
target-defect constructor alone survives, as the target-defective
identification of two of G's declared coordinates. -/
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
