import Hypostructure.Graph.ColdGermFamily

/-!
# The cold overlap count

`lem:cold-germ-extraction`'s overlap bound `B_cold` at one centre: the
oriented incidences leaving the part of a cubic window family reached from a
vertex by short subcubic paths number at most
`B_cold = b(P)·(1 + δ(2^{M_cold+2} − 1))`.  The count is the degree bound on
the window vertices, the subcubic ball `card_reach_le`, and `δ ≤ b(P)` at
`δ = 3` and window order at least three.

Also the finite count of a subtype carved out of a finset by one extra
predicate, used to count selected half-edges by their two classes.
-/

namespace Hypostructure.Graph

universe u

/-- The elements of a finset satisfying a predicate, as a subtype, are counted
by the corresponding filter. -/
theorem card_univ_subtype_mem_and {α : Type*} (s : Finset α) (p : α → Prop)
    [DecidablePred p] {_ : Fintype {x // x ∈ s ∧ p x}} :
    (Finset.univ : Finset {x // x ∈ s ∧ p x}).card = (s.filter p).card := by
  let equivalence : {x // x ∈ s ∧ p x} ≃ {x // x ∈ s.filter p} :=
    { toFun := fun x => ⟨x.1, Finset.mem_filter.2 x.2⟩
      invFun := fun x => ⟨x.1, Finset.mem_filter.1 x.2⟩
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl }
  calc
    (Finset.univ : Finset {x // x ∈ s ∧ p x}).card =
        Fintype.card {x // x ∈ s ∧ p x} := Finset.card_univ
    _ = Fintype.card {x // x ∈ s.filter p} := Fintype.card_congr equivalence
    _ = (s.filter p).card := Fintype.card_coe _

namespace ColdCorridor

/-- **The overlap count at one centre.**  In a family of windows all of whose
vertices have degree exactly `threshold = 3`, the oriented incidences leaving
the window vertices reached from `vertex` by subcubic paths of length at most
`M_cold + 2` number at most `B_cold`. -/
theorem card_incidences_reach_windows_le_overlapBound
    (object : FiniteObject.{u}) [DecidableEq object.Vertex]
    (family : Finset (Finset object.Vertex)) (S : DeclaredSignature)
    (threshold : Nat) (threshold_eq_three : threshold = 3)
    (three_le_windowOrder : 3 ≤ S.windowOrder)
    (windowDegree : ∀ window ∈ family, ∀ vertex ∈ window,
      object.degree vertex = threshold)
    (vertex : object.Vertex) :
    (object.incidences.filter fun pair : object.Vertex × object.Vertex =>
        pair.1 ∈ @SubcubicReach.reach object.Vertex
            (@FinEnum.instFintype _ object.vertices) object.graph
            (object.vertexFinset.filter fun current =>
              object.degree current ≤ threshold)
            vertex (exchangeBound S + 2) vertex ∩
          windowsOf object family).card ≤
      overlapBound threshold S := by
  let subcubic := object.vertexFinset.filter fun current =>
    object.degree current ≤ threshold
  let reach := @SubcubicReach.reach object.Vertex
    (@FinEnum.instFintype _ object.vertices) object.graph subcubic vertex
    (exchangeBound S + 2) vertex
  let sourceRegion := reach ∩ windowsOf object family
  have sourceRegionBounded : ∀ current ∈ sourceRegion,
      object.degree current ≤ threshold := by
    intro current currentMem
    obtain ⟨window, windowMem, currentMem⟩ :=
      (mem_windowsOf object family current).1 (Finset.mem_inter.1 currentMem).2
    exact le_of_eq (windowDegree window windowMem current currentMem)
  have incidenceBound :=
    card_incidences_filter_fst_le object sourceRegion threshold
      sourceRegionBounded
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  have cubicBound : ∀ current ∈ subcubic,
      object.graph.degree current ≤ 3 := by
    intro current currentMem
    have bounded := (Finset.mem_filter.1 currentMem).2
    have graphDegree : object.graph.degree current =
        (object.graph.neighborSet current).ncard := by
      rw [Set.ncard_eq_toFinset_card']
      rfl
    calc
      object.graph.degree current =
          (object.graph.neighborSet current).ncard := graphDegree
      _ = object.degree current :=
        (object.degree_eq_ncard_neighborSet current).symm
      _ ≤ 3 := by simpa [threshold_eq_three] using bounded
  have reachBound := SubcubicReach.card_reach_le object.graph
    subcubic cubicBound vertex (exchangeBound S + 2)
  have stubExcessBound : threshold ≤ stubExcess threshold S := by
    rw [stubExcess, threshold_eq_three]
    omega
  calc
    (object.incidences.filter fun pair : object.Vertex × object.Vertex =>
        pair.1 ∈ sourceRegion).card ≤ threshold * sourceRegion.card :=
      incidenceBound
    _ ≤ threshold * reach.card :=
      Nat.mul_le_mul_left _ (Finset.card_le_card Finset.inter_subset_left)
    _ ≤ threshold * (1 + threshold * (2 ^ (exchangeBound S + 2) - 1)) := by
      apply Nat.mul_le_mul_left
      simpa [reach, threshold_eq_three] using reachBound
    _ ≤ stubExcess threshold S *
        (1 + threshold * (2 ^ (exchangeBound S + 2) - 1)) :=
      Nat.mul_le_mul_right _ stubExcessBound
    _ = overlapBound threshold S := rfl

end ColdCorridor

end Hypostructure.Graph
