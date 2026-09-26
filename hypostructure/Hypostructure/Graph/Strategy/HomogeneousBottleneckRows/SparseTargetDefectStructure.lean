import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.NamedSurplusExits
import Hypostructure.Graph.SparsePressureLedger
import Hypostructure.Graph.GluedCrossingCycle
import Hypostructure.Graph.Strategy.HomogeneousBottleneckRows.Basic

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
      producesUnique := by key_fresh
      producesNonempty := by simp }
    (fun inputs =>
      let residual := (inputs.get (K .sparseTargetDefectResidual)).down
      let selection := (inputs.get (K .selection)).down
      .cons (key := K .sparseTargetDefectStructure)
        (show Value BranchState Presentation presentation data
            .sparseTargetDefectStructure inputs.current from ⟨by
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
                exact selection.1 (Graph.hasCycleWithLength_of_hom
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
                exact selection.1 (Graph.hasCycleWithLength_of_hom
                  realization.hom realization.injective yes)
              exact ⟨fun h => pieceFree (Graph.DefectGeometry.local_target c h),
                Graph.DefectGeometry.realized_mixed c
                  (Graph.DefectGeometry.pieceExclusive c contextFree) pieceFree⟩
            · intro c
              rcases Graph.DefectGeometry.local_or_mixed c with localized | mixed
              · exact Or.inl localized
              · exact Or.inr ⟨mixed, Graph.DefectGeometry.twoLabels_of_exclusive c
                  (Graph.DefectGeometry.pieceExclusive c contextFree) mixed⟩⟩)
        .nil)

end Hypostructure.Graph.Strategy.Spine
