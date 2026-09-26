import Hypostructure.Graph.Statements.SurplusPair
import Hypostructure.Graph.NamedSurplusExits
import Hypostructure.Graph.SparsePressureLedger
import Hypostructure.Graph.GluedCrossingCycle
import Hypostructure.Graph.TargetDefectStructure

/-!
# Contract lemmas: the named sparse exits of node `[20]`

`def:named-surplus-exits` on the selected minimal counterexample: the only
exit compatible with the selection and replacement facts is the target-defect
exit, and its identified pair has the bound target-defect geometry.
-/

namespace Hypostructure.Graph.Contracts.SurplusPair

open Hypostructure
open Hypostructure.Graph.Strategy.Spine

universe u v

variable {data : Parameters} {object : Graph.FiniteObject.{u}}

/-- Node `[20]`, the named sparse-exit routing: at a selected minimal
counterexample (no accepted cycle; every strictly smaller baseline object has
one) whose proper supports admit no replacement, a sparse surplus exit is the
target-defect exit, with its concrete rank-reducing attempted quotient. -/
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
  | targetDefect family coordinateSupport attempt reducing reduced full
      identified defect =>
      exact ⟨_, family, coordinateSupport, attempt, reducing,
        reduced, full, identified, defect⟩
  | compression support replacement =>
      exact (replacementExcluded support replacement).elim
  | delocalization representative smaller baseline transfer =>
      exact (selected.1
        (transfer (selected.2 representative smaller baseline))).elim
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

/-- Node `[20]`: on an object with no accepted cycle, the identified
target-defect pair of a sparse target-defect residual has its bound outside
context and target-free negative constituents. -/
theorem sparseTargetDefectStructure_of_residual
    (residual : SparseTargetDefectResidualStatement data object)
    (noCycle : ¬ Graph.HasCycleWithLength data.LengthOK object) :
    SparseTargetDefectStructureStatement data object := by
  obtain ⟨Coordinate, family, coordinateSupport, attempt,
    reducing, reduced, full, identified, defect⟩ := residual
  classical
  refine ⟨Coordinate, family, coordinateSupport, attempt, reducing,
    reduced, full, identified, ?_⟩
  obtain ⟨outside, different⟩ := defect
  refine ⟨outside, different, ?_⟩
  by_cases positiveLeft : Graph.HasCycleWithLength data.LengthOK
      (Graph.glue reduced outside)
  · have negativeRight : ¬ Graph.HasCycleWithLength data.LengthOK
        (Graph.glue full outside) := by
      intro yes
      exact different ⟨fun _ => yes, fun _ => positiveLeft⟩
    have contextFree : ¬ Graph.HasCycleWithLength data.LengthOK
        (Graph.OutsideContext.pack outside) := by
      intro yes
      exact negativeRight (Graph.hasCycleWithLength_of_hom
        (Graph.contextHom full outside)
        (Graph.contextEmbedding full outside).injective yes)
    have negativeFree : ¬ Graph.HasCycleWithLength data.LengthOK
        (Graph.BoundaryPiece.pack full) := by
      intro yes
      exact negativeRight (Graph.hasCycleWithLength_of_hom
        (Graph.pieceHom full outside)
        (Graph.pieceEmbedding full outside).injective yes)
    apply Or.inl
    refine ⟨positiveLeft, negativeRight, contextFree, negativeFree, ?_, ?_, ?_, ?_⟩
    · intro c
      exact Graph.DefectGeometry.pieceExclusive c contextFree
    · intro c emptyBoundary
      exact Graph.DefectGeometry.empty_local c
        (Graph.DefectGeometry.pieceExclusive c contextFree) emptyBoundary
    · intro c realization
      have pieceFree : ¬ Graph.HasCycleWithLength data.LengthOK
          (Graph.BoundaryPiece.pack reduced) := by
        intro yes
        exact noCycle (Graph.hasCycleWithLength_of_hom
          realization.hom realization.injective yes)
      exact ⟨fun h => pieceFree (Graph.DefectGeometry.local_target c h),
        Graph.DefectGeometry.realized_mixed c
          (Graph.DefectGeometry.pieceExclusive c contextFree) pieceFree⟩
    · intro c
      rcases Graph.DefectGeometry.local_or_mixed c with localized | mixed
      · exact Or.inl localized
      · exact Or.inr ⟨mixed, Graph.DefectGeometry.twoLabels_of_exclusive c
          (Graph.DefectGeometry.pieceExclusive c contextFree) mixed⟩
  · have positiveRight : Graph.HasCycleWithLength data.LengthOK
        (Graph.glue full outside) := by
      by_contra no
      exact different ⟨fun yes => (positiveLeft yes).elim,
        fun yes => (no yes).elim⟩
    have contextFree : ¬ Graph.HasCycleWithLength data.LengthOK
        (Graph.OutsideContext.pack outside) := by
      intro yes
      exact positiveLeft (Graph.hasCycleWithLength_of_hom
        (Graph.contextHom reduced outside)
        (Graph.contextEmbedding reduced outside).injective yes)
    have negativeFree : ¬ Graph.HasCycleWithLength data.LengthOK
        (Graph.BoundaryPiece.pack reduced) := by
      intro yes
      exact positiveLeft (Graph.hasCycleWithLength_of_hom
        (Graph.pieceHom reduced outside)
        (Graph.pieceEmbedding reduced outside).injective yes)
    apply Or.inr
    refine ⟨positiveRight, positiveLeft, contextFree, negativeFree, ?_, ?_, ?_, ?_⟩
    · intro c
      exact Graph.DefectGeometry.pieceExclusive c contextFree
    · intro c emptyBoundary
      exact Graph.DefectGeometry.empty_local c
        (Graph.DefectGeometry.pieceExclusive c contextFree) emptyBoundary
    · intro c realization
      have pieceFree : ¬ Graph.HasCycleWithLength data.LengthOK
          (Graph.BoundaryPiece.pack full) := by
        intro yes
        exact noCycle (Graph.hasCycleWithLength_of_hom
          realization.hom realization.injective yes)
      exact ⟨fun h => pieceFree (Graph.DefectGeometry.local_target c h),
        Graph.DefectGeometry.realized_mixed c
          (Graph.DefectGeometry.pieceExclusive c contextFree) pieceFree⟩
    · intro c
      rcases Graph.DefectGeometry.local_or_mixed c with localized | mixed
      · exact Or.inl localized
      · exact Or.inr ⟨mixed, Graph.DefectGeometry.twoLabels_of_exclusive c
          (Graph.DefectGeometry.pieceExclusive c contextFree) mixed⟩

end Hypostructure.Graph.Contracts.SurplusPair
