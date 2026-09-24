import Hypostructure.Graph.Strategy.SpineVocabulary

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

/-! ## `def:open-port-suppression`

This source-free definition row publishes the exact identification of the
paper's suppressible open-port families with the generic compatible-family
construction.  The next label, not this one, proves minimum-degree safety. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def openPortSuppressionRow :
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
    `Hypostructure.Graph.Strategy.Spine.openPortSuppression
    { Requires := []
      Produces := [K .openPortSuppression]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .openPortSuppression) ⟨by
        change OpenPortSuppressionStatement data inputs.current.object
        classical
        intro family _highCentres
        letI : DecidableEq inputs.current.object.Vertex :=
          inputs.current.object.vertices.decEq
        letI : DecidableEq family.Index := family.indices.decEq
        refine ⟨?_, family.support_disjoint, family.center_outside_support,
          family.chord_injective, ?_, ?_, ?_, ?_⟩
        · intro index other
          constructor
          · exact (family.configuration index).neighbors other
          · rintro (rfl | rfl | rfl)
            · exact (family.configuration index).vertex_center
            · exact (family.configuration index).vertex_left
            · exact (family.configuration index).vertex_right
        · intro index
          exact (family.configuration index).shoulder_missing
        · have centreOfPositive : ∀ vertex,
              0 < family.centerLoad vertex →
                ∃ index, (family.configuration index).center = vertex := by
            intro vertex positive
            rw [Graph.TightVertexSuppression.CompatibleFamily.centerLoad] at positive
            obtain ⟨index, indexMem⟩ := Finset.card_pos.mp positive
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at indexMem
            exact ⟨index, indexMem⟩
          constructor
          · intro capacity centre centreHigh
            by_cases loadZero : family.centerLoad centre = 0
            · omega
            · obtain ⟨index, indexCentre⟩ :=
                centreOfPositive centre (Nat.pos_of_ne_zero loadZero)
              have centreRemaining : centre ∈ family.remainingVertices := by
                rw [Graph.TightVertexSuppression.CompatibleFamily.remainingVertices]
                refine Finset.mem_sdiff.mpr
                  ⟨inputs.current.object.mem_vertexFinset centre, ?_⟩
                intro deleted
                rw [Graph.TightVertexSuppression.CompatibleFamily.deletedVertices] at deleted
                obtain ⟨other, _otherMem, otherVertex⟩ := Finset.mem_image.mp deleted
                exact (family.center_outside_support index other).1
                  (indexCentre.trans otherVertex.symm)
              exact capacity centre centreRemaining
          · intro highCapacity vertex vertexRemaining
            by_cases vertexHigh : data.threshold <
                inputs.current.object.degree vertex
            · exact highCapacity vertex vertexHigh
            · by_cases loadZero : family.centerLoad vertex = 0
              · omega
              · obtain ⟨index, indexCentre⟩ :=
                  centreOfPositive vertex (Nat.pos_of_ne_zero loadZero)
                have := _highCentres index
                rw [indexCentre] at this
                exact (vertexHigh this).elim
        · ext vertex
          simp [Graph.TightVertexSuppression.CompatibleFamily.deletedVertices]
        · intro left right
          exact family.suppressed_adj left right⟩
        .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
