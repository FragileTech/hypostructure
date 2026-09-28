import Hypostructure.Graph.CapacityFreeSide.Pair

/-!
# Free side, step 1 (end): every "separated open pair" carries a clause-(f) chord set
-/

namespace Hypostructure.Graph.CapacityFreeSide

open Hypostructure Hypostructure.Graph

universe u

variable {object : FiniteObject.{u}} {threshold : Nat}
  {Baseline Target : FiniteObject.{u} → Prop} {LengthOK : Nat → Prop}

/-- **Lean improvement (not routed by the paper).**  Two selected open ports with
disjoint supports `T`, distinct centres, and each centre outside the other's
support carry a concrete clause-(f) chord-set obstruction: minimality applied to
their simultaneous suppression. -/
theorem chordObstruction_of_separated
    (active : ActiveSurplusDemands Baseline Target LengthOK object threshold)
    (baseline : threshold ≤ object.minDegree)
    (minimal : ∀ smaller : FiniteObject.{u}, smaller.LexicographicallySmaller object →
      threshold ≤ smaller.minDegree → HasCycleWithLength LengthOK smaller)
    {p q : object.Vertex × object.Vertex}
    (hp : p ∈ object.excessPorts threshold) (hq : q ∈ object.excessPorts threshold)
    (openP : ¬ object.graph.Adj (pairResponseChordEnds active p).1
      (pairResponseChordEnds active p).2)
    (openQ : ¬ object.graph.Adj (pairResponseChordEnds active q).1
      (pairResponseChordEnds active q).2)
    (disjT : Disjoint (portT hp) (portT hq))
    (centres : p.1 ≠ q.1)
    (hpT : p.1 ∉ portT hq) (hqT : q.1 ∉ portT hp)
    (pair : Finset (object.Vertex × object.Vertex)) (hpair : ∀ x, x ∈ pair ↔ x = p ∨ x = q) :
    ∃ chords, chords ∈ (pairResponseActivation active).chordObstructions pair := by
  classical
  let F := pairFamily active hp hq openP openQ disjT hpT hqT
  have cfgT : F.configuration ⟨true⟩ = portConfig active hp openP := rfl
  have cfgF : F.configuration ⟨false⟩ = portConfig active hq openQ := rfl
  -- centre capacity: each centre is loaded once and is high
  have cap : F.CenterCapacity threshold := by
    intro v _
    unfold TightVertexSuppression.CompatibleFamily.centerLoad
    by_cases hv : threshold < object.degree v
    · refine le_trans ?_ (show 1 ≤ object.degree v - threshold by omega)
      rw [Finset.card_le_one]
      rintro ⟨i⟩ hi ⟨j⟩ hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
      cases i <;> cases j
      · rfl
      · exact (centres ((portConfig_center active hp openP).symm.trans
          ((cfgT ▸ hj).trans (cfgF ▸ hi).symm) |>.trans (portConfig_center active hq openQ))).elim
      · exact (centres ((portConfig_center active hp openP).symm.trans
          ((cfgT ▸ hi).trans (cfgF ▸ hj).symm) |>.trans (portConfig_center active hq openQ))).elim
      · rfl
    · rw [Finset.card_eq_zero.2 ?_]
      · exact Nat.zero_le _
      refine Finset.eq_empty_of_forall_notMem ?_
      rintro ⟨i⟩ hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      apply hv
      cases i
      · rw [← hi, cfgF, portConfig_center]
        exact FiniteObject.centre_high_of_mem_excessPorts hq
      · rw [← hi, cfgT, portConfig_center]
        exact FiniteObject.centre_high_of_mem_excessPorts hp
  have pRemain : p.1 ∈ F.remainingVertices := by
    simp only [TightVertexSuppression.CompatibleFamily.remainingVertices,
      TightVertexSuppression.CompatibleFamily.deletedVertices, Finset.mem_sdiff,
      object.mem_vertexFinset, true_and, Finset.mem_image, Finset.mem_univ, not_exists]
    rintro ⟨i⟩ h
    cases i
    · rw [cfgF, portConfig_vertex] at h
      exact hpT (h ▸ FiniteObject.SurplusPort.endpoint_mem_support _)
    · rw [cfgT, portConfig_vertex] at h
      exact (object.graph.ne_of_adj (FiniteObject.adj_of_mem_excessPorts hp)) h.symm
  haveI : Nonempty F.suppressed.Vertex := ⟨⟨p.1, pRemain⟩⟩
  haveI : Nonempty F.Index := ⟨⟨true⟩⟩
  have pres := F.minimumDegree_preserved threshold baseline cap
  obtain ⟨cert⟩ := minimal F.suppressed F.lexicographicallySmaller pres
  have sub : pair ⊆ object.excessPorts threshold := by
    intro x hx
    rcases (hpair x).1 hx with rfl | rfl
    · exact hp
    · exact hq
  have portOf : ∀ i : F.Index,
      ((F.configuration i).center, (F.configuration i).vertex) = if i.down then p else q := by
    rintro ⟨i⟩
    cases i
    · simp only [cfgF, portConfig_center, portConfig_vertex, Bool.false_eq_true, if_false]
    · simp only [cfgT, portConfig_center, portConfig_vertex, if_true]
  have img : Finset.univ.image (fun i : F.Index =>
      ((F.configuration i).center, (F.configuration i).vertex)) = pair := by
    ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and, hpair, portOf]
    constructor
    · rintro ⟨⟨i⟩, rfl⟩
      cases i <;> simp
    · rintro (rfl | rfl)
      · exact ⟨⟨true⟩, rfl⟩
      · exact ⟨⟨false⟩, rfl⟩
  refine ⟨(F.usedChords cert.walk).image (fun i : F.Index =>
      ((F.configuration i).center, (F.configuration i).vertex)), ?_⟩
  have chordsSub : (F.usedChords cert.walk).image (fun i : F.Index =>
      ((F.configuration i).center, (F.configuration i).vertex)) ⊆
      object.excessPorts threshold := by
    refine Finset.Subset.trans ?_ sub
    rw [← img]
    exact Finset.image_subset_image (Finset.subset_univ _)
  unfold pairResponseActivation
  dsimp only
  rw [List.mem_filter]
  refine ⟨mem_orderedChordSets _ _ chordsSub, decide_eq_true ?_⟩
  refine ⟨sub, F, cert, img, ?_, rfl⟩
  rintro ⟨i⟩
  left
  cases i
  · rw [cfgF, portConfig_center, portConfig_vertex]
    exact portConfig_ends active hq openQ
  · rw [cfgT, portConfig_center, portConfig_vertex]
    exact portConfig_ends active hp openP

end Hypostructure.Graph.CapacityFreeSide
