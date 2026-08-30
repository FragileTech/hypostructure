import Hypostructure.Graph.Strategy.SpineVocabulary

/-!
# The finite proof of `lem:dominant-type`

This module contains the mathematical calculation consumed by the sealed
strategy row.  Its hypotheses are exactly the facts that row reads from the
`ExactLedger`: the repetitive maximum-packing coordinate (including the same
full-rank equality) and the near-cubic surplus ceiling.
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure

universe u

set_option maxHeartbeats 1000000

/-- The manuscript's relabelling argument, followed by the one exceptional-set
calculation needed to pass from the subcubic remainder to the full remainder. -/
theorem dominantRootedType_of_repetitive
    (data : Data.{u}) (object : Graph.FiniteObject.{u})
    (baseline : data.threshold ≤ object.minDegree)
    (repetitiveInput :
      ∃ packing : Finset (Finset object.Vertex),
        object.IsWindowPacking data.windowOrder packing ∧
          packing.card = object.windowPackingNumber data.windowOrder ∧
          remainderCurvatureTargetRank data object packing =
            remainderWedgeSupply object packing ∧
          RemainderTypeCoordinateRepetitive data object packing)
    (nearCubic : object.degreeSurplus data.threshold ≤
      data.surplusThreshold object.vertexCount) :
    DominantRootedTypeStatement data object fun _subcubic _root => True := by
  classical
  obtain ⟨packing, valid, maximal, rankEq, repetitive⟩ := repetitiveInput
  letI : FinEnum object.Vertex := object.vertices
  letI : Fintype object.Vertex := inferInstance
  letI : DecidableEq object.Vertex := Classical.decEq object.Vertex
  let support := object.remainderSupport packing
  let subcubic := remainderSubcubicSupport data object packing
  have repetitive' :=
    (remainderTypeCoordinateRepetitive_iff data object packing).mp repetitive
  obtain ⟨root, fibreCount⟩ :=
    Graph.RootedLocalType.exists_dominant_of_structurallyRepetitive
      (object.rootedLocalTypeCode
        (remainderSubcubicSupport data object packing) 2)
      (data.surplusThreshold object.vertexCount) repetitive'
  let code := object.rootedLocalTypeCode subcubic 2
  let fibre := Graph.RootedLocalType.typeFibre code root
  let dominant : Finset object.Vertex := fibre.image Subtype.val
  have dominantSubset : dominant ⊆ subcubic := by
    intro vertex member
    obtain ⟨localVertex, _localMember, rfl⟩ := Finset.mem_image.mp member
    exact localVertex.2
  have rootFibre : root ∈ fibre := by
    simp [fibre, Graph.RootedLocalType.typeFibre]
  have rootMem : root.1 ∈ dominant := by
    exact Finset.mem_image.mpr ⟨root, rootFibre, rfl⟩
  have dominantCard : dominant.card = fibre.card := by
    rw [show dominant = fibre.image Subtype.val from rfl,
      Finset.card_image_of_injective _ Subtype.val_injective]
  have subcubicLe : subcubic.card ≤ dominant.card +
      data.surplusThreshold object.vertexCount := by
    rw [Fintype.card_coe, ← dominantCard] at fibreCount
    exact fibreCount
  let high := support.filter fun vertex =>
    ¬ object.degree vertex ≤ data.threshold
  have baselineDegree : ∀ vertex : object.Vertex,
      data.threshold ≤ object.degree vertex := fun vertex =>
    le_trans baseline (object.minDegree_le_degree vertex)
  have highCard : high.card ≤ object.degreeSurplus data.threshold := by
    calc
      high.card = ∑ _vertex ∈ high, 1 := by simp
      _ ≤ ∑ vertex ∈ high,
            (object.degree vertex - data.threshold) := by
        exact Finset.sum_le_sum fun vertex member => by
          have above := (Finset.mem_filter.mp member).2
          omega
      _ ≤ ∑ vertex ∈ (Finset.univ : Finset object.Vertex),
            (object.degree vertex - data.threshold) := by
        exact Finset.sum_le_sum_of_subset (Finset.subset_univ high)
      _ = object.degreeSurplus data.threshold := by
        simpa [Graph.FiniteObject.ambientSurplus] using
          object.ambientSurplus_univ_eq_degreeSurplus
            data.threshold baselineDegree
  have highLe : high.card ≤
      data.surplusThreshold object.vertexCount := highCard.trans nearCubic
  have supportSplit : subcubic.card + high.card = support.card := by
    simpa [subcubic, remainderSubcubicSupport, high] using
      support.card_filter_add_card_filter_not
        (fun vertex => object.degree vertex ≤ data.threshold)
  have supportCount : support.card ≤ dominant.card +
      2 * data.surplusThreshold object.vertexCount := by
    omega
  refine ⟨packing, valid, maximal, rankEq, ?_⟩
  dsimp only
  refine ⟨dominant, root.1, dominantSubset, rootMem, supportCount, ?_,
    True.intro⟩
  intro vertex vertexMem
  obtain ⟨localVertex, localMember, localValue⟩ :=
    Finset.mem_image.mp vertexMem
  have equalToRoot : code localVertex = code root :=
    (Finset.mem_filter.mp localMember).2
  subst vertex
  exact equalToRoot.symm

end Hypostructure.Graph.Strategy.Spine
