import Hypostructure.Graph.DeclaredRankQuotient
import Hypostructure.Graph.GluedCrossingCycle

/-!
# The boundary-profile attempted quotient on a target-avoiding object

On an object with no accepted cycle, and a target whose length predicate
accepts quadrilaterals, the attempted quotient on any connected support that
records only the boundary-degree profile is never target-complete: adjoining a
disjoint `K₄` to the support's own piece keeps the profile but creates an
accepted quadrilateral, while the unmodified piece reconstructs the avoiding
object.  Hence both representative clauses of `def:admissible-rank-quotient`
are vacuous, and the quotient is a well-defined `AttemptedQuotient` that
identifies any two chosen coordinates and whose identifications preserve the
boundary-degree profile.
-/

namespace Hypostructure.Graph.AttemptedQuotient

open Hypostructure.Graph.Strategy.InterfaceReplacement

universe u

/-- The profile-recording attempted quotient on a connected support of a
target-avoiding object.  It identifies the two given coordinates, and every
identification it makes preserves the boundary-degree profile. -/
theorem exists_profileQuotient_of_avoids
    {Baseline : FiniteObject.{u} → Prop} {LengthOK : Nat → Prop}
    (quadrilateral : LengthOK 4) {object : FiniteObject.{u}}
    (avoids : ¬ HasCycleWithLength LengthOK object)
    {Coordinate : Type u} {family : Finset Coordinate}
    {coordinateSupport : Coordinate → Finset object.Vertex}
    (support : Finset object.Vertex)
    (connected : SupportComponents.Connected.ConnectedOn object support)
    (carries : ∀ coordinate ∈ family, coordinateSupport coordinate ⊆ support)
    (anchor firstCoordinate secondCoordinate : Coordinate)
    (anchorMem : anchor ∈ family) :
    ∃ attempt : AttemptedQuotient Baseline (HasCycleWithLength LengthOK)
        object family coordinateSupport,
      attempt.support = support ∧
        attempt.label firstCoordinate = attempt.label secondCoordinate ∧
        ∀ leftPiece rightPiece,
          attempt.Identifies leftPiece rightPiece →
            leftPiece.boundaryDegreeProfile =
              rightPiece.boundaryDegreeProfile := by
  let boundary := SupportAtom.boundary object support
  let source := SupportAtom.piece object support
  let Four : Type u := ULift.{u} (Fin 4)
  let oldEmbedding :
      (boundary.Vertex ⊕ source.Internal) ↪
        (boundary.Vertex ⊕ (source.Internal ⊕ Four)) :=
    { toFun := fun vertex =>
        match vertex with
        | .inl label => .inl label
        | .inr internal => .inr (.inl internal)
      inj' := by
        intro firstVertex secondVertex equal
        cases firstVertex <;> cases secondVertex <;> simp_all }
  let fourEmbedding : Four ↪ (boundary.Vertex ⊕ (source.Internal ⊕ Four)) :=
    { toFun := fun vertex => .inr (.inr vertex)
      inj' := by
        intro firstVertex secondVertex equal
        simpa using equal }
  let augmented : BoundaryPiece boundary :=
    { Internal := source.Internal ⊕ Four
      internalVertices := by
        letI : FinEnum source.Internal := source.internalVertices
        letI : FinEnum Four := inferInstance
        infer_instance
      graph := source.graph.map oldEmbedding ⊔
        (⊤ : SimpleGraph Four).map fourEmbedding
      decideAdj := Classical.decRel _ }
  have profileEq : source.boundaryDegreeProfile =
      augmented.boundaryDegreeProfile := by
    funext label
    unfold BoundaryPiece.boundaryDegreeProfile BoundaryPiece.boundaryDegree
    rw [FiniteObject.degree_eq_ncard_neighborSet,
      FiniteObject.degree_eq_ncard_neighborSet]
    have neighbours :
        augmented.graph.neighborSet (.inl label) =
          oldEmbedding '' source.graph.neighborSet (.inl label) := by
      ext vertex
      simp only [SimpleGraph.mem_neighborSet]
      constructor
      · intro adjacent
        change
          (source.graph.map oldEmbedding ⊔
            (⊤ : SimpleGraph Four).map fourEmbedding).Adj
              (.inl label) vertex at adjacent
        rcases adjacent with old | square
        · rw [SimpleGraph.map_adj] at old
          obtain ⟨left, right, edge, leftEq, rightEq⟩ := old
          cases left with
          | inl leftLabel =>
              have leftLabelEq : leftLabel = label := by
                simpa [oldEmbedding] using leftEq
              refine ⟨right, ?_, rightEq⟩
              simpa [leftLabelEq] using edge
          | inr leftInternal =>
              simp [oldEmbedding] at leftEq
        · rw [SimpleGraph.map_adj] at square
          obtain ⟨left, right, _edge, leftEq, _rightEq⟩ := square
          simp [fourEmbedding] at leftEq
      · rintro ⟨vertex, adjacent, rfl⟩
        apply show
          (source.graph.map oldEmbedding ⊔
            (⊤ : SimpleGraph Four).map fourEmbedding).Adj
              (oldEmbedding (.inl label)) (oldEmbedding vertex) from ?_
        exact Or.inl ((SimpleGraph.map_adj_apply).2 adjacent)
    change
      (source.graph.neighborSet (.inl label)).ncard =
        (augmented.graph.neighborSet (.inl label)).ncard
    rw [neighbours, Set.ncard_image_of_injective _ oldEmbedding.injective]
  have sourceAvoids :
      ¬ HasCycleWithLength LengthOK
        (glue source (SupportAtom.outside object support)) := by
    intro target
    apply avoids
    exact
      ((cycleTargetInterface LengthOK).isomorphismInvariant.iff_of_iso
        ⟨(SupportAtom.decomposition object support).reconstructionIso⟩).mp
        target
  have augmentedTarget :
      HasCycleWithLength LengthOK
        (glue augmented (SupportAtom.outside object support)) := by
    let zero : Four := ULift.up 0
    let one : Four := ULift.up 1
    let two : Four := ULift.up 2
    let three : Four := ULift.up 3
    have fourAdj (left right : Four) (different : left ≠ right) :
        augmented.graph.Adj (fourEmbedding left) (fourEmbedding right) := by
      apply Or.inr
      rw [SimpleGraph.map_adj_apply]
      simpa using different
    let walk : augmented.graph.Walk (fourEmbedding zero) (fourEmbedding zero) :=
      .cons (fourAdj zero one (by decide))
        (.cons (fourAdj one two (by decide))
          (.cons (fourAdj two three (by decide))
            (.cons (fourAdj three zero (by decide)) .nil)))
    have isCycle : walk.IsCycle := by
      dsimp only [walk]
      rw [SimpleGraph.Walk.cons_isCycle_iff]
      constructor
      · rw [SimpleGraph.Walk.isPath_def]
        simp [zero, one, two, three, fourEmbedding]
        all_goals decide
      · simp [zero, one, two, three, fourEmbedding]
        all_goals decide
    let certificate : CycleCertificate augmented.pack LengthOK :=
      { vertex := fourEmbedding zero
        walk := walk
        isCycle := isCycle
        length_ok := by
          change LengthOK 4
          exact quadrilateral }
    exact
      ⟨certificate.mapHom (pieceHom augmented _)
        (pieceEmbedding augmented _).injective⟩
  let attempt : AttemptedQuotient Baseline (HasCycleWithLength LengthOK)
      object family coordinateSupport :=
    { support := support
      connected := connected
      carries := carries
      Label := PUnit
      Value := ULift.{u + 1, u} (BoundaryDegreeProfile boundary)
      label := fun _ => PUnit.unit
      value := fun piece _ => ULift.up piece.boundaryDegreeProfile
      properRepresentative := by
        intro _proper _reducing complete
        have sameValues : ∀ coordinate ∈ family,
            ULift.up source.boundaryDegreeProfile =
              ULift.up augmented.boundaryDegreeProfile := by
          intro _coordinate _member
          exact congrArg ULift.up profileEq
        have universal := (complete source augmented sameValues).2
        exact
          (sourceAvoids
            ((universal (SupportAtom.outside object support)).mpr
              augmentedTarget)).elim
      closedRepresentative := by
        intro _covers _reducing complete
        have sameValues : ∀ coordinate ∈ family,
            ULift.up source.boundaryDegreeProfile =
              ULift.up augmented.boundaryDegreeProfile := by
          intro _coordinate _member
          exact congrArg ULift.up profileEq
        have universal := (complete source augmented sameValues).2
        exact
          (sourceAvoids
            ((universal (SupportAtom.outside object support)).mpr
              augmentedTarget)).elim }
  refine ⟨attempt, rfl, rfl, ?_⟩
  intro leftPiece rightPiece identified
  have same := identified anchor anchorMem
  exact ULift.up_injective same

end Hypostructure.Graph.AttemptedQuotient
