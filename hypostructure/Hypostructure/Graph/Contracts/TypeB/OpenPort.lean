import Hypostructure.Graph.Contracts.TypeB.Support

/-!
# Contracts: open-port suppression

`def:open-port-suppression`, `lem:open-port-suppression-safe`,
`lem:single-open-port-suppression-witness` and
`lem:suppressed-family-critical-cycle`.
-/

namespace Hypostructure.Graph.Contracts.TypeB

open Hypostructure
open Hypostructure.Graph.Strategy.Spine

universe u v

variable {data : Parameters} {object : Graph.FiniteObject.{u}}
variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}

/-- `def:open-port-suppression`, identified with the simultaneous tight-vertex
suppression construction. -/
theorem openPortSuppression :
    OpenPortSuppressionStatement data object := by
  classical
  intro family _highCentres
  letI : DecidableEq object.Vertex :=
    object.vertices.decEq
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
            ⟨object.mem_vertexFinset centre, ?_⟩
          intro deleted
          rw [Graph.TightVertexSuppression.CompatibleFamily.deletedVertices] at deleted
          obtain ⟨other, _otherMem, otherVertex⟩ := Finset.mem_image.mp deleted
          exact (family.center_outside_support index other).1
            (indexCentre.trans otherVertex.symm)
        exact capacity centre centreRemaining
    · intro highCapacity vertex vertexRemaining
      by_cases vertexHigh : data.threshold <
          object.degree vertex
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
    exact family.suppressed_adj left right


/-- `lem:open-port-suppression-safe`. -/
theorem openPortSuppressionSafe
    (definition : OpenPortSuppressionStatement data object)
    (three : 3 ≤ data.threshold)
    (baseline : data.threshold ≤ object.minDegree) :
    OpenPortSuppressionSafeStatement data object := by
  classical
  intro family highCentres paperCapacity vertex
  have suppressionDefinition :=
    definition family highCentres
  rcases suppressionDefinition with
    ⟨_neighbors, _supports, _centres, _chords, _missing,
      capacityIff, _deleted, _adjacency⟩
  have capacity : family.CenterCapacity data.threshold :=
    capacityIff.mpr paperCapacity
  have oldLower :
      data.threshold ≤ object.degree vertex.1 :=
    baseline.trans
      (object.minDegree_le_degree vertex.1)
  have loadBound := capacity vertex.1 vertex.2
  have balance := family.degree_add_centerLoad vertex
  have thresholdLower :
      data.threshold ≤ family.suppressed.degree vertex := by
    omega
  exact three.trans thresholdLower


/-- `lem:single-open-port-suppression-witness` from the size minimality of the
selected object. -/
theorem singleOpenPortSuppressionWitness
    (baseline : data.threshold ≤ object.minDegree)
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (minimal : ∀ smaller : Graph.FiniteObject.{u},
      (progress BranchState Presentation presentation data).Smaller smaller object →
      Graph.MinimumDegreeAtLeast data.threshold smaller →
      Graph.HasCycleWithLength data.LengthOK smaller) :
    SingleOpenPortSuppressionWitnessStatement data object := by
  classical
  intro configuration centreHigh
  obtain ⟨_certificate, ⟨reconstructed⟩⟩ :=
    configuration.singleSuppressionWitness_of_minimal
      (LengthOK := data.LengthOK) (threshold := data.threshold)
      baseline avoids
      (fun smaller smallerDecrease baseline =>
        minimal smaller smallerDecrease baseline)
      centreHigh
  exact Graph.FiniteObject.SurplusPort.openPortWitness_of_deleted
    (endpoint := configuration.vertex) reconstructed.path
      reconstructed.isPath reconstructed.restored_length_ok


/-- `lem:suppressed-family-critical-cycle`. -/
theorem suppressedFamilyCriticalCycle
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (minimal : ∀ smaller : Graph.FiniteObject.{u},
      (progress BranchState Presentation presentation data).Smaller smaller object →
      Graph.MinimumDegreeAtLeast data.threshold smaller →
      Graph.HasCycleWithLength data.LengthOK smaller)
    (suppressionSafe : OpenPortSuppressionSafeStatement data object)
    (thresholdEq : data.threshold = 3) :
    SuppressedFamilyCriticalCycleStatement data object := by
  classical
  letI : DecidableEq object.Vertex :=
    object.vertices.decEq
  intro family familyNonempty highCentres paperCapacity
  letI : DecidableEq family.Index := family.indices.decEq
  letI : Nonempty family.Index := familyNonempty
  let chosen : family.Index := Classical.choice familyNonempty
  have centreRemaining :
      (family.configuration chosen).center ∈ family.remainingVertices := by
    rw [Graph.TightVertexSuppression.CompatibleFamily.remainingVertices]
    refine Finset.mem_sdiff.mpr
      ⟨object.mem_vertexFinset _, ?_⟩
    intro deleted
    rw [Graph.TightVertexSuppression.CompatibleFamily.deletedVertices] at deleted
    obtain ⟨other, _otherMem, otherVertex⟩ := Finset.mem_image.mp deleted
    exact (family.center_outside_support chosen other).1 otherVertex.symm
  letI : Nonempty family.suppressed.Vertex :=
    ⟨⟨(family.configuration chosen).center, centreRemaining⟩⟩
  have preserved : data.threshold ≤ family.suppressed.minDegree := by
    apply family.suppressed.le_minDegree_of_forall_le_degree
    intro vertex
    rw [thresholdEq]
    exact suppressionSafe family highCentres paperCapacity vertex
  have target : Graph.HasCycleWithLength data.LengthOK family.suppressed :=
    minimal family.suppressed
      family.lexicographicallySmaller preserved
  obtain ⟨certificate⟩ := target
  have firstExpansion :=
    family.suppressedFamilyExpansion avoids certificate
  refine ⟨⟨certificate, firstExpansion.1⟩, ?_⟩
  intro arbitraryCertificate
  obtain ⟨usedNonempty, ⟨expanded, lengthEq⟩⟩ :=
    family.suppressedFamilyExpansion avoids arbitraryCertificate
  refine ⟨usedNonempty, ⟨expanded, lengthEq, ?_⟩⟩
  intro accepted
  apply avoids
  exact ⟨{
    vertex := _
    walk := expanded.walk
    isCycle := expanded.isCycle
    length_ok := accepted }⟩


end Hypostructure.Graph.Contracts.TypeB
