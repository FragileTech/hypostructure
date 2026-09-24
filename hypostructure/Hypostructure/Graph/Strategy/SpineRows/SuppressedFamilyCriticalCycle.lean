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

/-! ## `lem:suppressed-family-critical-cycle`

This row supplies the selected-object baseline and minimality to the generic
simultaneous suppression development.  That development already proves the
paper's chord-use and simultaneous simple-cycle expansion argument. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def suppressedFamilyCriticalCycleRow :
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
    `Hypostructure.Graph.Strategy.Spine.suppressedFamilyCriticalCycle
    { Requires := [K .selection, K .openPortSuppressionSafe]
      Produces := [K .suppressedFamilyCriticalCycle]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let selection := (inputs.get (K .selection)).down
      let suppressionSafe := (inputs.get (K .openPortSuppressionSafe)).down
      .cons (key := K .suppressedFamilyCriticalCycle) ⟨by
        change SuppressedFamilyCriticalCycleStatement data inputs.current.object
        classical
        letI : DecidableEq inputs.current.object.Vertex :=
          inputs.current.object.vertices.decEq
        intro family familyNonempty highCentres paperCapacity
        letI : DecidableEq family.Index := family.indices.decEq
        letI : Nonempty family.Index := familyNonempty
        let chosen : family.Index := Classical.choice familyNonempty
        have centreRemaining :
            (family.configuration chosen).center ∈ family.remainingVertices := by
          rw [Graph.TightVertexSuppression.CompatibleFamily.remainingVertices]
          refine Finset.mem_sdiff.mpr
            ⟨inputs.current.object.mem_vertexFinset _, ?_⟩
          intro deleted
          rw [Graph.TightVertexSuppression.CompatibleFamily.deletedVertices] at deleted
          obtain ⟨other, _otherMem, otherVertex⟩ := Finset.mem_image.mp deleted
          exact (family.center_outside_support chosen other).1 otherVertex.symm
        letI : Nonempty family.suppressed.Vertex :=
          ⟨⟨(family.configuration chosen).center, centreRemaining⟩⟩
        have preserved : data.threshold ≤ family.suppressed.minDegree := by
          apply family.suppressed.le_minDegree_of_forall_le_degree
          intro vertex
          rw [data.threshold_eq_three]
          exact suppressionSafe family highCentres paperCapacity vertex
        have target : Graph.HasCycleWithLength data.LengthOK family.suppressed :=
          selection.2.sizeMinimal family.suppressed
            family.lexicographicallySmaller preserved
        obtain ⟨certificate⟩ := target
        have firstExpansion :=
          family.suppressedFamilyExpansion selection.1 certificate
        refine ⟨⟨certificate, firstExpansion.1⟩, ?_⟩
        intro arbitraryCertificate
        obtain ⟨usedNonempty, ⟨expanded, lengthEq⟩⟩ :=
          family.suppressedFamilyExpansion selection.1 arbitraryCertificate
        refine ⟨usedNonempty, ⟨expanded, lengthEq, ?_⟩⟩
        intro accepted
        apply selection.1
        exact ⟨{
          vertex := _
          walk := expanded.walk
          isCycle := expanded.isCycle
          length_ok := accepted }⟩⟩
        .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
