import Hypostructure.Graph.LadderBridge
import Hypostructure.Graph.TwoGeodesicsCount
import Hypostructure.Graph.CycleCounting.Object
import Hypostructure.Graph.JointObject

/-!
# The ladder count at a finite object (`[144a]`, G audit S144a)

Vocabulary-free.  Instantiates `LadderCount.ladder_count` at a `FiniteObject` with
`Cubic := (degree = 3)`: the matching step from `NeighbourhoodPairs`, the triangular
port walks' geodesic facts, the hub-degree bound, the count.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Hypostructure.Graph.LadderG

open Hypostructure
open Hypostructure.Graph
open Hypostructure.Graph.PathChords
open Hypostructure.Graph.PortPathCover
open Hypostructure.Graph.LadderCount
open Hypostructure.Graph.LadderRun
open Hypostructure.Graph.TwoGeodesics

universe u

variable {object : FiniteObject.{u}}

/-- **`G[N(h)]` is a matching**, in the pairwise form the ladder count uses. -/
theorem match_of_pairs (P : Graph.CycleCounting.NeighbourhoodPairs object) :
    ∀ h x y z : object.Vertex, object.graph.Adj h x → object.graph.Adj h y →
      object.graph.Adj h z → object.graph.Adj x y → object.graph.Adj x z → y = z := by
  intro h x y z hx hy hz hxy hxz
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  unfold Graph.CycleCounting.NeighbourhoodPairs at P
  have key := (P h).1 x (by rw [SimpleGraph.mem_neighborFinset]; exact hx)
  refine Finset.card_le_one.1 key y ?_ z ?_
  · rw [Finset.mem_filter, SimpleGraph.mem_neighborFinset]; exact ⟨hy, hxy⟩
  · rw [Finset.mem_filter, SimpleGraph.mem_neighborFinset]; exact ⟨hz, hxz⟩

/-- **A triangular port walk is geodesic** (its two ends are adjacent). -/
theorem portWalk_tri {LengthOK : Nat → Prop} {a b : object.Vertex}
    {w : object.graph.Walk a b} (hw : PortWalk object LengthOK w) (hab : object.graph.Adj b a) :
    GeodesicDetours s(a, b) w ∧ GeodesicHubAdj LengthOK w := by
  obtain ⟨-, -, -, -, -, h | ⟨x, -, -, -, hna, -⟩⟩ := hw
  · exact ⟨h.2.2.1, h.2.2.2⟩
  · exact absurd hab.symm hna

section Walk

variable {V : Type u} {G : SimpleGraph V}

/-- **A vertex has at most four neighbours on a geodesic walk** (two on the walk's path
edges, two on the port edge). -/
theorem nbrPos_le_four {LengthOK : Nat → Prop} {a b : V} {w : G.Walk a b} (hp : w.IsPath)
    (det : GeodesicDetours s(a, b) w) (hub : GeodesicHubAdj LengthOK w) (ok4 : LengthOK 4)
    (match_ : ∀ h x y z : V, G.Adj h x → G.Adj h y → G.Adj h z → G.Adj x y → G.Adj x z → y = z)
    (v : V) : (nbrPos w v).card ≤ 4 := by
  classical
  by_cases hv : v ∈ w.support
  · obtain ⟨t, ht, htl⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.1 hv
    subst ht
    have hsub : nbrPos w (w.getVert t) ⊆ ({t - 1, t + 1, 0, w.length} : Finset ℕ) := by
      intro j hj
      simp only [nbrPos, Finset.mem_filter, Finset.mem_range] at hj
      obtain ⟨hjl, hadj⟩ := hj
      simp only [Finset.mem_insert, Finset.mem_singleton]
      have hne : j ≠ t := by
        intro h
        subst h
        exact G.loopless.irrefl _ hadj
      by_cases hport : s(w.getVert t, w.getVert j) = s(a, b)
      · rw [Sym2.eq_iff] at hport
        rcases hport with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · right; right; right
          have := getVert_inj hp (s := j) (t := w.length) (by omega) (Nat.le_refl _)
            (by rw [h2, SimpleGraph.Walk.getVert_length])
          omega
        · right; right; left
          have := getVert_inj hp (s := j) (t := 0) (by omega) (Nat.zero_le _)
            (by rw [h2, SimpleGraph.Walk.getVert_zero])
          omega
      · let r : G.Walk (w.getVert t) (w.getVert j) := SimpleGraph.Walk.cons hadj .nil
        have hr : ∀ ε ∈ r.edges, ε ≠ s(a, b) := by
          intro ε hε
          simp only [r, SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil, List.mem_cons,
            List.not_mem_nil, or_false] at hε
          rw [hε]; exact hport
        have := idx_dist_le det htl (by omega) r hr
        simp only [r, SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_nil] at this
        omega
    exact le_trans (Finset.card_le_card hsub) Finset.card_le_four
  · have := nbrPos_le_two_of_match hp hub ok4 match_ hv
    omega

end Walk

section Object

attribute [local instance] Graph.FiniteObject.vertices Graph.FiniteObject.decideAdj

variable {object : FiniteObject.{u}}

theorem deg_eq (v : object.Vertex) : object.degree v = object.graph.degree v := rfl

/-- The seed `T ∪ supp w₁ ∪ supp w₂` as a finset. -/
noncomputable def seedOf (T : Finset object.Vertex) {a1 b1 a2 b2 : object.Vertex}
    (w1 : object.graph.Walk a1 b1) (w2 : object.graph.Walk a2 b2) : Finset object.Vertex :=
  T ∪ w1.support.toFinset ∪ w2.support.toFinset

/-- **The ladder count and the vertex count at a pair of triangular port walks.**  Here
`H = {deg ≠ 3}` and `T` is the finset carrying the cubic vertices off both walks. -/
def LadderCounts (object : FiniteObject.{u}) (T : Finset object.Vertex)
    {a1 b1 a2 b2 : object.Vertex} (w1 : object.graph.Walk a1 b1)
    (w2 : object.graph.Walk a2 b2) : Prop :=
  (w1.length - 1) / 24 ≤ 16 * (JointObject.hubs object).card + 12 * T.card + 30 ∧
  (w2.length - 1) / 24 ≤ 16 * (JointObject.hubs object).card + 12 * T.card + 30 ∧
  object.vertexCount ≤ (JointObject.hubs object).card + T.card + w1.length + w2.length + 2

/-- **Neither walk uses the other's end edge.** -/
def EndEdgesFree (object : FiniteObject.{u}) {a1 b1 a2 b2 : object.Vertex}
    (w1 : object.graph.Walk a1 b1) (w2 : object.graph.Walk a2 b2) : Prop :=
  (∀ ε ∈ w2.edges, ε ≠ s(a1, b1)) ∧ (∀ ε ∈ w1.edges, ε ≠ s(a2, b2))

/-- the linear form of the counts -/
theorem LadderCounts.linear {T : Finset object.Vertex} {a1 b1 a2 b2 : object.Vertex}
    {w1 : object.graph.Walk a1 b1} {w2 : object.graph.Walk a2 b2}
    (h : LadderCounts object T w1 w2) :
    object.vertexCount ≤ 769 * (JointObject.hubs object).card + 577 * T.card + 1490 := by
  obtain ⟨c1, c2, c3⟩ := h
  omega

/-- **Hub degrees at a pair of triangular port walks.** -/
def HubDegrees (object : FiniteObject.{u}) (T : Finset object.Vertex)
    {a1 b1 a2 b2 : object.Vertex} (_w1 : object.graph.Walk a1 b1)
    (_w2 : object.graph.Walk a2 b2) : Prop :=
  ∀ v, object.degree v ≠ 3 → object.degree v ≤ T.card + 8

theorem countHyp_of {LengthOK : Nat → Prop} (ok4 : LengthOK 4) (ok8 : LengthOK 8)
    (ok16 : LengthOK 16)
    (cyc : ¬ ∃ (c : object.Vertex) (cy : object.graph.Walk c c), cy.IsCycle ∧ LengthOK cy.length)
    (pairs : Graph.CycleCounting.NeighbourhoodPairs object)
    {a1 b1 a2 b2 : object.Vertex} {w1 : object.graph.Walk a1 b1} {w2 : object.graph.Walk a2 b2}
    (h1 : PortWalk object LengthOK w1) (h2 : PortWalk object LengthOK w2)
    (t1 : object.graph.Adj b1 a1) (t2 : object.graph.Adj b2 a2) :
    CountHyp object.graph LengthOK (fun v => object.degree v = 3) w1 w2 :=
  { stub := fun m hm a b ha hb hab => LadderBridge.stub_of_degree_three m hm a b ha hb hab
    avoids := cyc, ok4 := ok4, ok8 := ok8, ok16 := ok16
    hp1 := h1.1, hp2 := h2.1
    det1 := (portWalk_tri h1 t1).1, det2 := (portWalk_tri h2 t2).1
    hub1 := (portWalk_tri h1 t1).2, hub2 := (portWalk_tri h2 t2).2
    match_ := match_of_pairs pairs }

theorem ladderCounts_of {LengthOK : Nat → Prop} (ok4 : LengthOK 4) (ok8 : LengthOK 8)
    (ok16 : LengthOK 16)
    (cyc : ¬ ∃ (c : object.Vertex) (cy : object.graph.Walk c c), cy.IsCycle ∧ LengthOK cy.length)
    (pairs : Graph.CycleCounting.NeighbourhoodPairs object)
    {a1 b1 a2 b2 : object.Vertex} {w1 : object.graph.Walk a1 b1} {w2 : object.graph.Walk a2 b2}
    (h1 : PortWalk object LengthOK w1) (h2 : PortWalk object LengthOK w2)
    (t1 : object.graph.Adj b1 a1) (t2 : object.graph.Adj b2 a2)
    (E : EndEdgesFree object w1 w2) (T : Finset object.Vertex)
    (cover : ∀ v, object.degree v = 3 → v ∈ seedOf T w1 w2) :
    LadderCounts object T w1 w2 := by
  classical
  have H := countHyp_of ok4 ok8 ok16 cyc pairs h1 h2 t1 t2
  have H' : CountHyp object.graph LengthOK (fun v => object.degree v = 3) w2 w1 :=
    { stub := H.stub, avoids := H.avoids, ok4 := ok4, ok8 := ok8, ok16 := ok16,
      hp1 := H.hp2, hp2 := H.hp1, det1 := H.det2, det2 := H.det1, hub1 := H.hub2,
      hub2 := H.hub1, match_ := H.match_ }
  have hX : ∀ z, ¬ (fun v => object.degree v = 3) z → z ∈ JointObject.hubs object := by
    intro z hz
    rw [JointObject.mem_hubs]
    exact hz
  have hU : ∀ z, (fun v => object.degree v = 3) z → z ∉ w1.support → z ∉ w2.support →
      z ∈ T := by
    intro z hz n1 n2
    have := cover z hz
    simp only [seedOf, Finset.mem_union, List.mem_toFinset] at this
    tauto
  have hU' : ∀ z, (fun v => object.degree v = 3) z → z ∉ w2.support → z ∉ w1.support →
      z ∈ T := fun z hz n2 n1 => hU z hz n1 n2
  refine ⟨ladder_count_geo H E.1 E.2 _ T hX hU, ladder_count_geo H' E.2 E.1 _ T hX hU', ?_⟩
  -- the vertex count
  have hn := JointObject.vertexCount_eq object
  have split := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset object.Vertex)) (fun v => object.graph.degree v = 3)
  have sub : Finset.univ.filter (fun v => object.graph.degree v = 3) ⊆ seedOf T w1 w2 := by
    intro v hv
    exact cover v (Finset.mem_filter.1 hv).2
  have hle := Finset.card_le_card sub
  have c1 : (seedOf T w1 w2).card ≤ T.card + (w1.length + 1) + (w2.length + 1) := by
    have a1' := Finset.card_union_le (T ∪ w1.support.toFinset) w2.support.toFinset
    have a2' := Finset.card_union_le T w1.support.toFinset
    have b1' := List.toFinset_card_le w1.support
    have b2' := List.toFinset_card_le w2.support
    simp only [SimpleGraph.Walk.length_support] at b1' b2'
    simp only [seedOf]
    omega
  have hubs : (JointObject.hubs object).card =
      (Finset.univ.filter fun v => ¬ object.graph.degree v = 3).card := by
    unfold JointObject.hubs
    congr 1
  rw [hn]
  rw [Finset.card_univ] at split
  omega

theorem hubDegrees_of {LengthOK : Nat → Prop} (ok4 : LengthOK 4) (ok8 : LengthOK 8)
    (ok16 : LengthOK 16)
    (cyc : ¬ ∃ (c : object.Vertex) (cy : object.graph.Walk c c), cy.IsCycle ∧ LengthOK cy.length)
    (pairs : Graph.CycleCounting.NeighbourhoodPairs object)
    {a1 b1 a2 b2 : object.Vertex} {w1 : object.graph.Walk a1 b1} {w2 : object.graph.Walk a2 b2}
    (h1 : PortWalk object LengthOK w1) (h2 : PortWalk object LengthOK w2)
    (t1 : object.graph.Adj b1 a1) (t2 : object.graph.Adj b2 a2)
    (T : Finset object.Vertex)
    (hubCover : ∀ v, object.degree v ≠ 3 → ∀ y, object.graph.Adj v y → y ∈ seedOf T w1 w2) :
    HubDegrees object T w1 w2 := by
  classical
  have H := countHyp_of ok4 ok8 ok16 cyc pairs h1 h2 t1 t2
  intro v hv
  have hsub : object.graph.neighborFinset v ⊆
      T ∪ (nbrPos w1 v).image w1.getVert ∪ (nbrPos w2 v).image w2.getVert := by
    intro y hy
    rw [SimpleGraph.mem_neighborFinset] at hy
    have := hubCover v hv y hy
    simp only [seedOf, Finset.mem_union, List.mem_toFinset] at this
    simp only [Finset.mem_union, Finset.mem_image]
    rcases this with (hT | h) | h
    · left; left; exact hT
    · left; right
      obtain ⟨j, hj, hjl⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.1 h
      refine ⟨j, ?_, hj⟩
      simp only [nbrPos, Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, by rw [hj]; exact hy⟩
    · right
      obtain ⟨j, hj, hjl⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.1 h
      refine ⟨j, ?_, hj⟩
      simp only [nbrPos, Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, by rw [hj]; exact hy⟩
  have n1 := nbrPos_le_four H.hp1 H.det1 H.hub1 ok4 H.match_ v
  have n2 := nbrPos_le_four H.hp2 H.det2 H.hub2 ok4 H.match_ v
  have i1 := Finset.card_image_le (s := nbrPos w1 v) (f := w1.getVert)
  have i2 := Finset.card_image_le (s := nbrPos w2 v) (f := w2.getVert)
  have u1 := Finset.card_union_le (T ∪ (nbrPos w1 v).image w1.getVert) ((nbrPos w2 v).image w2.getVert)
  have u2 := Finset.card_union_le T ((nbrPos w1 v).image w1.getVert)
  have := Finset.card_le_card hsub
  rw [deg_eq, ← SimpleGraph.card_neighborFinset_eq_degree]
  omega

/-- **The surplus is at most `(|T| + 5)|H|`** when every hub has degree at most `|T| + 8`. -/
theorem sigma_le_of_hubDegrees (base : MinimumDegreeAtLeast 3 object) {T : Finset object.Vertex}
    (hd : ∀ v, object.degree v ≠ 3 → object.degree v ≤ T.card + 8) :
    object.degreeSurplus 3 ≤ (T.card + 5) * (JointObject.hubs object).card := by
  rw [JointObject.degreeSurplus_eq base]
  calc ∑ v ∈ JointObject.hubs object, (object.graph.degree v - 3)
      ≤ ∑ v ∈ JointObject.hubs object, (T.card + 5) := by
        apply Finset.sum_le_sum
        intro v hv
        have h1 := hd v (by rw [deg_eq]; exact (JointObject.mem_hubs).1 hv)
        rw [deg_eq] at h1
        omega
    _ = (T.card + 5) * (JointObject.hubs object).card := by simp [mul_comm]

/-- **`|H| ≤ σ`.** -/
theorem hubs_le_sigma (base : MinimumDegreeAtLeast 3 object) :
    (JointObject.hubs object).card ≤ object.degreeSurplus 3 := by
  rw [JointObject.degreeSurplus_eq base]
  calc (JointObject.hubs object).card = ∑ v ∈ JointObject.hubs object, 1 := by simp
    _ ≤ ∑ v ∈ JointObject.hubs object, (object.graph.degree v - 3) := by
        apply Finset.sum_le_sum
        intro v hv
        have h1 := JointObject.deg_ge base v
        have h2 := (JointObject.mem_hubs).1 hv
        omega

end Object

end Hypostructure.Graph.LadderG
