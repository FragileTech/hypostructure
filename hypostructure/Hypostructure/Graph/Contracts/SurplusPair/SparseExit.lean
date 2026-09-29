import Hypostructure.Graph.Statements.SurplusPair
import Hypostructure.Graph.NamedSurplusExits
import Hypostructure.Graph.SparsePressureLedger
import Hypostructure.Graph.GluedCrossingCycle

/-!
# Contract lemmas: the named sparse exits of node `[20]`

`def:named-surplus-exits` on the selected minimal counterexample: the only
exit compatible with the selection and replacement facts is the target-defect
exit (b), and exit (b), stated about G, is empty at G: two readings of G always
agree in G's own surroundings `G − Z`.
-/

namespace Hypostructure.Graph.Contracts.SurplusPair

open Hypostructure
open Hypostructure.Graph.Strategy.Spine

universe u v

variable {data : Parameters} {object : Graph.FiniteObject.{u}}

/-- Node `[20]`, the named sparse-exit routing: at a selected minimal
counterexample (no accepted cycle; every strictly smaller baseline object has
one) whose proper supports admit no replacement, a sparse surplus exit of G's
declared family is the target-defect exit (b), i.e. a target-defective
identification of two of G's declared coordinates. -/
theorem sparseTargetDefectResidual_of_exit
    {BranchState : Graph.FiniteObject.{u} → Type v}
    {Presentation : Type} {presentation : Presentation}
    (exit : SparsePairExitStatement data object)
    (selected : SelectionStatement BranchState Presentation presentation data
      object)
    (replacementExcluded : ReplacementExclusionStatement data object) :
    SparseTargetDefectResidualStatement data object := by
  cases exit with
  | dyadic cycle =>
      exact (selected.1 cycle).elim
  | targetDefect defect =>
      obtain ⟨witness, canonical⟩ := exists_sparseTargetDefectWitness defect
      exact ⟨witness, canonical,
        sparseTargetDefectWitness_spec_of_eq_some canonical⟩
  | compression support replacement =>
      exact (replacementExcluded support replacement).elim
  | delocalization representative smaller baseline noTarget =>
      exact (noTarget (selected.2 representative smaller baseline)).elim
  | suppressionChord family certificate violates =>
      let expanded := family.expandCycle certificate
      have accepted : data.LengthOK expanded.walk.length := by
        rw [expanded.length_eq]
        exact violates
      have cycle : Graph.HasCycleWithLength data.LengthOK
          object :=
        ⟨⟨family.sourceVertex certificate.vertex, expanded.walk,
          expanded.isCycle, accepted⟩⟩
      exact (selected.1 cycle).elim

/-- **Exit (b) is empty at G** (Lean improvement: clause (b) of
`def:named-surplus-exits`, stated about G, is decided at G): on an object with
no accepted cycle every reading of G's piece glued into G's own surroundings
`G − Z` is a target-free subgraph of G, so two readings always agree there and
G's declared sparse family has no target-defective identification. -/
theorem sparseTargetDefectEmpty_of_avoids
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object) :
    SparseTargetDefectEmptyStatement data object :=
  ⟨fun Z X => Graph.ActualContext.not_target_actualGlue avoids Z X,
    Graph.not_residualTargetDefect_of_avoids avoids _ _⟩

/-- The canonical witness of exit (b) contradicts exit (b)'s emptiness at G. -/
theorem not_sparseTargetDefectResidual_of_empty
    (empty : SparseTargetDefectEmptyStatement data object)
    (residual : SparseTargetDefectResidualStatement data object) : False := by
  obtain ⟨witness, -, spec⟩ := residual
  obtain ⟨-, -, -, -, -, separated⟩ := spec
  exact separated (iff_of_false (empty.1 _ _) (empty.1 _ _))

end Hypostructure.Graph.Contracts.SurplusPair
