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

/-- The bound target-defect geometry of two readings of one support of a
target-avoiding object, at the boundaried context that separates them. -/
theorem boundTargetDefectGeometryAt_of_separated
    {support : Finset object.Vertex}
    {reduced full : Graph.BoundaryPiece
      (Graph.Strategy.InterfaceReplacement.SupportAtom.boundary object support)}
    {outside : Graph.OutsideContext
      (Graph.Strategy.InterfaceReplacement.SupportAtom.boundary object support)}
    (different : ¬ (Graph.HasCycleWithLength data.LengthOK (Graph.glue reduced outside) ↔
      Graph.HasCycleWithLength data.LengthOK (Graph.glue full outside)))
    (noCycle : ¬ Graph.HasCycleWithLength data.LengthOK object) :
    Graph.BoundTargetDefectGeometryAt object support data.LengthOK reduced full
      outside := by
  classical
  refine ⟨different, ?_⟩
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

/-- The bound target-defect geometry of any two readings of one support of a
target-avoiding object that some boundaried context separates. -/
theorem boundTargetDefectGeometry_of_targetDefect
    {support : Finset object.Vertex}
    {reduced full : Graph.BoundaryPiece
      (Graph.Strategy.InterfaceReplacement.SupportAtom.boundary object support)}
    (defect : Graph.Response.TargetDefect
      (Graph.HasCycleWithLength data.LengthOK) reduced full)
    (noCycle : ¬ Graph.HasCycleWithLength data.LengthOK object) :
    Graph.BoundTargetDefectGeometry object support data.LengthOK reduced full := by
  obtain ⟨outside, different⟩ := defect
  exact ⟨outside, boundTargetDefectGeometryAt_of_separated different noCycle⟩

/-- Node `[20]`: on an object with no accepted cycle, the target-defective
identification of the sparse residual has the bound target-defect geometry of
its two readings on G's piece, at the residual's own canonical witness: the
same pair, the same support `Z` and the same separating context `O`. -/
theorem sparseTargetDefectStructure_of_residual
    (residual : SparseTargetDefectResidualStatement data object)
    (noCycle : ¬ Graph.HasCycleWithLength data.LengthOK object) :
    SparseTargetDefectStructureStatement data object := by
  obtain ⟨witness, canonical, spec⟩ := residual
  exact ⟨witness, canonical,
    boundTargetDefectGeometryAt_of_separated spec.2.2.2.2.2.2 noCycle⟩

end Hypostructure.Graph.Contracts.SurplusPair
