import Hypostructure.Graph.Contracts.Spine.SameTokenSeedCover
import Hypostructure.Graph.Contracts.Spine.SameTokenSwap
import Hypostructure.Graph.WalkAttachment
import Hypostructure.Graph.Statements.SparseExitResidual
import Hypostructure.Graph.TokenLoadClosure

/-!
# Contracts: attachments and chains at the canonical port walks; the separated configuration
(`[144a]`, G audit S144a)

Proof-agnostic contract lemmas for `SameTokenWalkAttachmentStatement` and
`SameTokenSeparatorExcludedStatement` (`Statements/SameTokenSwap.lean`).  The mathematics is
the vocabulary-free `Graph/WalkAttachment.lean` (attachment and chain cycles, separation at a
cut vertex, interior counts) and `Graph/LadderG.lean` (the hub-degree bound).

* `sameTokenWalkAttachment_holds`: both pair seeds are `T ∪ supp w₁ ∪ supp w₂` with canonical
  port walks, and every attachment/chain at them closes a cycle of G, hence an unaccepted length.
* `sameTokenSeparatorExcluded_holds`: in the boundary-free configuration (the antecedent of
  `K .sameTokenU2FreeWhole`) with both ports of a pair triangular, a vertex `v` off the pair seed
  with no neighbour in `T` is impossible.  Such a `v` is a cut vertex of G (`[144a]`, 8104) whose
  neighbours are cubic (`K .slackIndependent`), hence on the two walks; it separates the walks
  (`cut_separates`), so they are disjoint and non-adjacent, every other off-seed vertex has a
  cubic `T`-neighbour, every interior vertex of a walk has a neighbour off both walks, and every
  degree is at most `|T| + 8` (`LadderG.hubDegrees_of`): `n ≤ 729`.  The ledger has
  `n ≥ C_sp(C_sp + 1) + 9` (`K .orderAboveScaleSquare`) with `C_sp ≥ 102`.

This module imports no strategy, row, or vocabulary module.
-/

set_option linter.unusedSectionVars false

namespace Hypostructure.Graph.Contracts.Spine.SameTokenWalkCycles

open Hypostructure
open Hypostructure.Graph
open Hypostructure.Graph.Strategy.Spine
open Hypostructure.Graph.PortPathCover
open Hypostructure.Graph.WalkAttachment
open Hypostructure.Graph.Contracts.Spine.SameTokenSeedCover

universe u

section Walks

variable {data : Parameters} {object : Graph.FiniteObject.{u}}

/-- **The attachment and chain cycles at one pair seed.** -/
theorem pairWalkCycles_of
    (routing : SameTokenRouting data object)
    (routingEq : canonicalSameTokenRouting data object = some routing)
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (family : ActiveSurplusFamilyStatement data object)
    (threshold : data.threshold = 3)
    {pair : Finset (object.Vertex × object.Vertex)}
    (pairMem : pair = routing.demands.first ∨ pair = routing.demands.second) :
    PairWalkCycles data object (routing.capacity.activation.pairSeed pair) := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  obtain ⟨T, a1, b1, a2, b2, w1, w2, hT, hw1, hw2, eP⟩ :=
    pairSeedWalks routing routingEq avoids family threshold pairMem
  have cyc := noCycle_form avoids
  exact ⟨T, a1, b1, a2, b2, w1, w2, hT, hw1, hw2, eP, attachCycles_of hw1.1 cyc,
    attachCycles_of hw2.1 cyc, chainCycles_of hw1.1 hw2.1 cyc⟩

/-- **The attachment and chain cycles of the canonical port walks.** -/
theorem sameTokenWalkAttachment_holds
    (partition : SameTokenPairPartitionStatement data object)
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (family : ActiveSurplusFamilyStatement data object)
    (threshold : data.threshold = 3) :
    SameTokenWalkAttachmentStatement data object := by
  obtain ⟨routing, routingEq, -⟩ := partition
  exact ⟨routing, routingEq,
    pairWalkCycles_of routing routingEq avoids family threshold (Or.inl rfl),
    pairWalkCycles_of routing routingEq avoids family threshold (Or.inr rfl)⟩

end Walks

section Core

attribute [local instance] Graph.FiniteObject.vertices Graph.FiniteObject.decideAdj

variable {object : Graph.FiniteObject.{u}}

/-- Two vertices of a path are joined along the path, avoiding every vertex off it. -/
theorem joined_along {a b v : object.Vertex} {w : object.graph.Walk a b} (hw : w.IsPath)
    (hv : v ∉ w.support) {x y : object.Vertex} (hx : x ∈ w.support) (hy : y ∈ w.support) :
    JoinedAvoiding object.graph v x y := by
  obtain ⟨i, rfl, hi⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.1 hx
  obtain ⟨j, rfl, hj⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.1 hy
  obtain ⟨s, -, -, ms⟩ := seg_path w hw i j hi hj
  refine ⟨s, fun m => ?_⟩
  obtain ⟨k, -, -, rfl⟩ := ms v m
  exact hv (SimpleGraph.Walk.getVert_mem_support _ _)

/-- **The separated configuration is empty.**  At a pair of triangular port walks whose seed
`T ∪ supp w₁ ∪ supp w₂` (`|T| ≤ 6`) contains every degree-`3` vertex, in a connected graph
where every vertex off the seed is a cut vertex of degree at least `4`, hubs are independent
and `n ≥ 730`: every vertex off the seed has a cubic neighbour in `T`, at most `3|T|` vertices
lie off the seed, and `n ≤ 4|T| + |w₁| + |w₂| + 2`. -/
theorem seedAttached_core {LengthOK : ℕ → Prop} (ok4 : LengthOK 4) (ok8 : LengthOK 8)
    (ok16 : LengthOK 16)
    (cyc : ¬ ∃ (c : object.Vertex) (cy : object.graph.Walk c c), cy.IsCycle ∧ LengthOK cy.length)
    (pairs : Graph.CycleCounting.NeighbourhoodPairs object)
    {a1 b1 a2 b2 : object.Vertex} {w1 : object.graph.Walk a1 b1} {w2 : object.graph.Walk a2 b2}
    (h1 : PortWalk object LengthOK w1) (h2 : PortWalk object LengthOK w2)
    (t1 : object.graph.Adj b1 a1) (t2 : object.graph.Adj b2 a2)
    (T seed : Finset object.Vertex) (hT : T.card ≤ 6)
    (eP : seed = T ∪ w1.support.toFinset ∪ w2.support.toFinset)
    (conn : ∀ a b : object.Vertex, object.graph.Reachable a b)
    (cut : ∀ v, v ∉ seed → ∃ l r, l ≠ v ∧ r ≠ v ∧ ¬ JoinedAvoiding object.graph v l r)
    (big : ∀ v, v ∉ seed → 4 ≤ object.degree v)
    (cubicIn : ∀ v, object.degree v = 3 → v ∈ seed)
    (base3 : ∀ v, 3 ≤ object.degree v)
    (slack : ∀ l r, 3 < object.degree l → 3 < object.degree r → ¬ object.graph.Adj l r)
    (large : 730 ≤ object.vertexCount) :
    (∀ v, v ∉ seed → ∃ t ∈ T, object.graph.Adj v t ∧ object.degree t = 3) ∧
      (object.vertexFinset \ seed).card ≤ 3 * T.card ∧
      object.vertexCount ≤ 4 * T.card + w1.length + w2.length + 2 := by
  have H := LadderG.countHyp_of ok4 ok8 ok16 cyc pairs h1 h2 t1 t2
  have memSeed : ∀ x, x ∈ seed ↔ x ∈ T ∨ x ∈ w1.support ∨ x ∈ w2.support := by
    intro x
    rw [eP]
    simp only [Finset.mem_union, List.mem_toFinset, or_assoc]
  have nbrCubic : ∀ v, 3 < object.degree v → ∀ y, object.graph.Adj v y →
      object.degree y = 3 := by
    intro v hv y hy
    by_contra h
    have := base3 y
    exact slack v y hv (by omega) hy
  have hubCover : ∀ v, object.degree v ≠ 3 → ∀ y, object.graph.Adj v y →
      y ∈ LadderG.seedOf T w1 w2 := by
    intro v hv y hy
    have := base3 v
    have c := cubicIn y (nbrCubic v (by omega) y hy)
    rw [eP] at c
    exact c
  have hubDeg := LadderG.hubDegrees_of ok4 ok8 ok16 cyc pairs h1 h2 t1 t2 T hubCover
  have degAll : ∀ v, object.graph.degree v ≤ T.card + 8 := by
    intro v
    by_cases h : object.degree v = 3
    · have : object.graph.degree v = 3 := h
      omega
    · exact hubDeg v h
  have seedNe : ∀ v, v ∉ seed → ∀ x, x ∈ seed → x ≠ v := fun v hv x hx e => hv (e ▸ hx)
  -- the separation at an off-seed vertex with no `T`-neighbour
  have sepAt : ∀ v, v ∉ seed → (∀ t ∈ T, ¬ object.graph.Adj v t) →
      (∀ a ∈ w1.support, ∀ b ∈ w2.support, ¬ JoinedAvoiding object.graph v a b) ∧
        (∃ a ∈ w1.support, object.graph.Adj v a) ∧ (∃ b ∈ w2.support, object.graph.Adj v b) := by
    intro v hv noT
    obtain ⟨l, r, hl, hr, hcut⟩ := cut v hv
    have v1 : v ∉ w1.support := fun m => hv ((memSeed v).2 (Or.inr (Or.inl m)))
    have v2 : v ∉ w2.support := fun m => hv ((memSeed v).2 (Or.inr (Or.inr m)))
    have S := cut_separates conn hl hr hcut {x | x ∈ w1.support} {x | x ∈ w2.support}
      (fun y hy => by
        have := (memSeed y).1 (cubicIn y (nbrCubic v (by have := big v hv; omega) y hy))
        rcases this with h | h | h
        · exact absurd hy (noT y h)
        · exact Or.inl h
        · exact Or.inr h)
      (fun a ha a' ha' _ _ => joined_along H.hp1 v1 ha ha')
      (fun b hb b' hb' _ _ => joined_along H.hp2 v2 hb hb')
    refine ⟨fun a ha b hb => S.1 a ha b hb (seedNe v hv a ((memSeed a).2 (Or.inr (Or.inl ha))))
      (seedNe v hv b ((memSeed b).2 (Or.inr (Or.inr hb)))), S.2.1, S.2.2⟩
  have key : ∀ v, v ∉ seed → ∃ t ∈ T, object.graph.Adj v t := by
    by_contra hno
    push Not at hno
    obtain ⟨v0, hv0, noT⟩ := hno
    obtain ⟨noJoin, -, -⟩ := sepAt v0 hv0 noT
    have ne1 : ∀ x ∈ w1.support, x ≠ v0 := fun x hx =>
      seedNe v0 hv0 x ((memSeed x).2 (Or.inr (Or.inl hx)))
    have ne2 : ∀ x ∈ w2.support, x ≠ v0 := fun x hx =>
      seedNe v0 hv0 x ((memSeed x).2 (Or.inr (Or.inr hx)))
    have noEdge : ∀ a ∈ w1.support, ∀ b ∈ w2.support, ¬ object.graph.Adj a b := by
      intro a ha b hb e
      refine noJoin a ha b hb ⟨SimpleGraph.Walk.cons e SimpleGraph.Walk.nil, ?_⟩
      simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.mem_cons,
        List.not_mem_nil, or_false, not_or]
      exact ⟨fun h => ne1 a ha h.symm, fun h => ne2 b hb h.symm⟩
    have others : ∀ v, v ∉ seed → v ≠ v0 → ∃ t ∈ T, object.graph.Adj v t := by
      intro v hv hne
      by_contra hno'
      push Not at hno'
      obtain ⟨-, ⟨a, ha, va⟩, ⟨b, hb, vb⟩⟩ := sepAt v hv hno'
      refine noJoin a ha b hb
        ⟨SimpleGraph.Walk.cons va.symm (SimpleGraph.Walk.cons vb SimpleGraph.Walk.nil), ?_⟩
      simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.mem_cons,
        List.not_mem_nil, or_false, not_or]
      exact ⟨fun h => ne1 a ha h.symm, fun h => hne h.symm, fun h => ne2 b hb h.symm⟩
    -- the off-seed vertices
    have offErase : ((object.vertexFinset \ seed).erase v0).card ≤ 3 * T.card := by
      refine card_le_of_cubic_cover (G := object.graph) _ T (fun x hx => ?_)
      obtain ⟨hxv, hx'⟩ := Finset.mem_erase.1 hx
      have hxs := (Finset.mem_sdiff.1 hx').2
      obtain ⟨t, ht, adj⟩ := others x hxs hxv
      exact ⟨t, ht, adj, nbrCubic x (by have := big x hxs; omega) t adj⟩
    have offCard : (object.vertexFinset \ seed).card ≤ 3 * T.card + 1 := by
      have := Finset.pred_card_le_card_erase (s := object.vertexFinset \ seed) (a := v0)
      omega
    -- the vertices off both walks
    let Y : Finset object.Vertex :=
      Finset.univ.filter (fun x => x ∉ w1.support ∧ x ∉ w2.support)
    have Ysub : Y ⊆ T ∪ (object.vertexFinset \ seed) := by
      intro x hx
      obtain ⟨-, n1, n2⟩ := Finset.mem_filter.1 hx
      by_cases hs : x ∈ seed
      · rcases (memSeed x).1 hs with h | h | h
        · exact Finset.mem_union_left _ h
        · exact absurd h n1
        · exact absurd h n2
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.2 ⟨object.mem_vertexFinset x, hs⟩)
    have Ycard : Y.card ≤ 25 := by
      have a := Finset.card_le_card Ysub
      have b := Finset.card_union_le T (object.vertexFinset \ seed)
      omega
    have intY1 : ∀ k, 0 < k → k < w1.length → ∃ y ∈ Y, object.graph.Adj (w1.getVert k) y := by
      intro k h0 hk
      obtain ⟨y, adj, off1⟩ := interior_nbr_off H.hp1 H.det1 h0 hk (base3 _)
      have off2 : y ∉ w2.support := fun m =>
        noEdge _ (SimpleGraph.Walk.getVert_mem_support _ _) y m adj
      exact ⟨y, Finset.mem_filter.2 ⟨Finset.mem_univ _, off1, off2⟩, adj⟩
    have intY2 : ∀ k, 0 < k → k < w2.length → ∃ y ∈ Y, object.graph.Adj (w2.getVert k) y := by
      intro k h0 hk
      obtain ⟨y, adj, off2⟩ := interior_nbr_off H.hp2 H.det2 h0 hk (base3 _)
      have off1 : y ∉ w1.support := fun m =>
        noEdge y m _ (SimpleGraph.Walk.getVert_mem_support _ _) adj.symm
      exact ⟨y, Finset.mem_filter.2 ⟨Finset.mem_univ _, off1, off2⟩, adj⟩
    have c1 := interior_le H.hp1 Y (T.card + 8) intY1 (fun y _ => degAll y)
    have c2 := interior_le H.hp2 Y (T.card + 8) intY2 (fun y _ => degAll y)
    have prod : Y.card * (T.card + 8) ≤ 25 * 14 := Nat.mul_le_mul Ycard (by omega)
    -- the vertex count
    have cover : (Finset.univ : Finset object.Vertex) ⊆
        w1.support.toFinset ∪ w2.support.toFinset ∪ Y := by
      intro x _
      by_cases m1 : x ∈ w1.support
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ (List.mem_toFinset.2 m1))
      · by_cases m2 : x ∈ w2.support
        · exact Finset.mem_union_left _ (Finset.mem_union_right _ (List.mem_toFinset.2 m2))
        · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, m1, m2⟩)
    have cc := Finset.card_le_card cover
    have u1 := Finset.card_union_le (w1.support.toFinset ∪ w2.support.toFinset) Y
    have u2 := Finset.card_union_le w1.support.toFinset w2.support.toFinset
    have l1 := List.toFinset_card_le w1.support
    have l2 := List.toFinset_card_le w2.support
    simp only [SimpleGraph.Walk.length_support] at l1 l2
    have hn := JointObject.vertexCount_eq object
    rw [Finset.card_univ] at cc
    omega
  have attach : ∀ v, v ∉ seed → ∃ t ∈ T, object.graph.Adj v t ∧ object.degree t = 3 := by
    intro v hv
    obtain ⟨t, ht, adj⟩ := key v hv
    exact ⟨t, ht, adj, nbrCubic v (by have := big v hv; omega) t adj⟩
  have offCard : (object.vertexFinset \ seed).card ≤ 3 * T.card :=
    card_le_of_cubic_cover (G := object.graph) _ T (fun x hx => attach x (Finset.mem_sdiff.1 hx).2)
  refine ⟨attach, offCard, ?_⟩
  have seedCard : seed.card ≤ T.card + (w1.length + 1) + (w2.length + 1) := by
    have a1' := Finset.card_union_le (T ∪ w1.support.toFinset) w2.support.toFinset
    have a2' := Finset.card_union_le T w1.support.toFinset
    have b1' := List.toFinset_card_le w1.support
    have b2' := List.toFinset_card_le w2.support
    simp only [SimpleGraph.Walk.length_support] at b1' b2'
    rw [eP]
    omega
  have cover : (Finset.univ : Finset object.Vertex) ⊆ seed ∪ (object.vertexFinset \ seed) := by
    intro x _
    by_cases hs : x ∈ seed
    · exact Finset.mem_union_left _ hs
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.2 ⟨object.mem_vertexFinset x, hs⟩)
  have cc := Finset.card_le_card cover
  have u := Finset.card_union_le seed (object.vertexFinset \ seed)
  have hn := JointObject.vertexCount_eq object
  rw [Finset.card_univ] at cc
  omega

end Core

section Separator

variable {data : Parameters} {object : Graph.FiniteObject.{u}}

/-- **`n ≥ 730`**: `n ≥ C_sp(C_sp + 1) + 9` and `C_sp = 2 + 20·M₀ + 2S ≥ 102` (`M₀ ≥ 5` from the
registered quadratic safety `20 ≤ 2(1 + 2M₀)`). -/
theorem order_ge_730 (threshold : data.threshold = 3)
    (order : OrderAboveScaleSquareStatement data object)
    (safety : Graph.TokenLoad.quadraticSafetyScale ≤ 2 * (1 + 2 * data.homogeneousCap)) :
    730 ≤ object.vertexCount := by
  have hC : 102 ≤ data.spineScale := by
    have e : data.spineScale = 2 * (1 + 2 * data.homogeneousCap) +
        (2 * data.surplusScale + 2 * data.homogeneousCap * (3 * (data.threshold - 1) + 2)) :=
      rfl
    have q : Graph.TokenLoad.quadraticSafetyScale = 20 := rfl
    rw [q] at safety
    rw [e, threshold]
    have : 2 * data.homogeneousCap * (3 * (3 - 1) + 2) = 16 * data.homogeneousCap := by ring
    omega
  have h2 : 102 * 103 ≤ data.spineScale * (data.spineScale + 1) := Nat.mul_le_mul hC (by omega)
  unfold OrderAboveScaleSquareStatement at order
  omega

/-- **The separated configuration is empty at one pair seed.** -/
theorem pairSeedAttached_of
    (routing : SameTokenRouting data object)
    (routingEq : canonicalSameTokenRouting data object = some routing)
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (family : ActiveSurplusFamilyStatement data object)
    (threshold : data.threshold = 3)
    (base : MinDegreeBaselineStatement data object)
    (lengthLaw : ∀ length, data.LengthOK length ↔ Core.DyadicLength.PowerOfTwoLength length)
    (slack : SlackIndependentStatement data object)
    (large : 730 ≤ object.vertexCount)
    {pair : Finset (object.Vertex × object.Vertex)}
    (pairMem : pair = routing.demands.first ∨ pair = routing.demands.second)
    [DecidableEq object.Vertex] (Xp Xq Z : Finset object.Vertex)
    (connZ : Graph.SupportComponents.Connected.ConnectedOn object Z)
    (whole :
      (∀ w ∈ Xp, w ∉ Graph.Strategy.InterfaceReplacement.SupportAtom.cutBoundary object Z) →
      (∀ w ∈ Xq, w ∉ Graph.Strategy.InterfaceReplacement.SupportAtom.cutBoundary object Z) →
      Graph.MinimumDegreeAtLeast data.threshold
        (Graph.glue (Graph.Transplant.transplant object Z Xq)
          (Graph.Strategy.InterfaceReplacement.SupportAtom.outside object Z)) →
      Graph.MinimumDegreeAtLeast data.threshold
        (Graph.glue (Graph.Transplant.transplant object Z Xp)
          (Graph.Strategy.InterfaceReplacement.SupportAtom.outside object Z)) →
      (∀ v, v ∈ Z) ∧
        (∀ v, v ∈ Z → v ∉ routing.capacity.activation.pairSeed pair →
          ¬ Graph.SupportComponents.Connected.ConnectedOn object (Z.erase v)) ∧
        (∀ v, v ∉ routing.capacity.activation.pairSeed pair →
          Even (object.degree v) ∧ 4 ≤ object.degree v) ∧
        (∀ v, object.degree v = 3 → v ∈ routing.capacity.activation.pairSeed pair)) :
    PairSeedAttached data object Xp Xq Z (routing.capacity.activation.pairSeed pair) := by
  obtain ⟨T, a1, b1, a2, b2, w1, w2, hT, hw1, hw2, eP⟩ :=
    pairSeedWalks routing routingEq avoids family threshold pairMem
  refine ⟨T, a1, b1, a2, b2, w1, w2, hT, hw1, hw2, eP, fun fP fQ bQ bP t1 t2 => ?_⟩
  obtain ⟨univ, cut, ev, cub⟩ := whole fP fQ bQ bP
  have cyc := noCycle_form avoids
  have ok4 : data.LengthOK 4 := (lengthLaw 4).2 ⟨⟨2, by omega⟩, by norm_num⟩
  have ok8 : data.LengthOK 8 := (lengthLaw 8).2 ⟨⟨3, by omega⟩, by norm_num⟩
  have ok16 : data.LengthOK 16 := (lengthLaw 16).2 ⟨⟨4, by omega⟩, by norm_num⟩
  have pairs : Graph.CycleCounting.NeighbourhoodPairs object :=
    Graph.CycleCounting.neighbourhoodPairs avoids ok4
  have base3 : ∀ v, 3 ≤ object.degree v := fun v => by
    have := le_trans base (object.minDegree_le_degree v)
    omega
  have conn : ∀ a b : object.Vertex, object.graph.Reachable a b := fun a b => by
    obtain ⟨p, -, -⟩ := connZ.2 (univ a) (univ b)
    exact ⟨p⟩
  have nbrOf : ∀ v, 1 ≤ object.degree v → ∃ y, object.graph.Adj v y := by
    intro v h
    letI : FinEnum object.Vertex := object.vertices
    letI : DecidableRel object.graph.Adj := object.decideAdj
    exact (SimpleGraph.degree_pos_iff_exists_adj (G := object.graph) (v := v)).1 h
  have cut' : ∀ v, v ∉ routing.capacity.activation.pairSeed pair →
      ∃ l r, l ≠ v ∧ r ≠ v ∧ ¬ JoinedAvoiding object.graph v l r := by
    intro v hv
    have nc := cut v (univ v) hv
    by_contra hall
    push Not at hall
    apply nc
    refine ⟨?_, ?_⟩
    · obtain ⟨y, hy⟩ := nbrOf v (by have := (ev v hv).2; omega)
      exact ⟨y, Finset.mem_erase.2 ⟨hy.ne.symm, univ y⟩⟩
    · intro l r hl hr
      obtain ⟨hlv, -⟩ := Finset.mem_erase.1 hl
      obtain ⟨hrv, -⟩ := Finset.mem_erase.1 hr
      obtain ⟨p, hp⟩ := hall l r hlv hrv
      refine ⟨p.toPath.1, p.toPath.2, fun x hx => ?_⟩
      have hx' := SimpleGraph.Walk.support_toPath_subset_support p hx
      exact Finset.mem_erase.2 ⟨fun e => hp (e ▸ hx'), univ x⟩
  exact seedAttached_core ok4 ok8 ok16 cyc pairs hw1 hw2 t1 t2 T _
    (by rw [threshold] at hT; exact hT) eP conn cut' (fun v hv => (ev v hv).2) cub base3
    (fun l r hl hr => slack l r (by rw [threshold]; exact hl) (by rw [threshold]; exact hr))
    large

/-- **The separated configuration is empty at G** (Lean improvement). -/
theorem sameTokenSeparatorExcluded_holds
    (partition : SameTokenPairPartitionStatement data object)
    (noProper : NoProperBaselineStatement data object)
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (minimal : ∀ H : Graph.FiniteObject.{u}, H.LexicographicallySmaller object →
      Graph.MinimumDegreeAtLeast data.threshold H → Graph.HasCycleWithLength data.LengthOK H)
    (shape : VertexDeletionComponentsStatement object)
    (base : MinDegreeBaselineStatement data object)
    (threshold : data.threshold = 3)
    (family : ActiveSurplusFamilyStatement data object)
    (lengthLaw : ∀ length, data.LengthOK length ↔ Core.DyadicLength.PowerOfTwoLength length)
    (slack : SlackIndependentStatement data object)
    (order : OrderAboveScaleSquareStatement data object)
    (safety : Graph.TokenLoad.quadraticSafetyScale ≤ 2 * (1 + 2 * data.homogeneousCap)) :
    SameTokenSeparatorExcludedStatement data object := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  have large := order_ge_730 threshold order safety
  obtain ⟨routing, routingEq, Xp, Xq, Z, pinned, whole⟩ :=
    SameTokenSwap.sameTokenU2FreeWhole_holds partition noProper avoids minimal shape base
      threshold
  have connZ : Graph.SupportComponents.Connected.ConnectedOn object Z :=
    (CanonicalSupport.mem_candidates_iff.1 (CanonicalSupport.select?_mem_candidates pinned.2.2)).2
  refine ⟨routing, routingEq, Xp, Xq, Z, pinned, ?_, ?_⟩
  · exact pairSeedAttached_of routing routingEq avoids family threshold base lengthLaw slack
      large (Or.inl rfl) Xp Xq Z connZ (fun fP fQ bQ bP => by
        obtain ⟨-, -, -, univ, cutP, -, evP, -, cub, -⟩ := whole fP fQ bQ bP
        exact ⟨univ, cutP, evP, fun v h => (cub v h).1⟩)
  · exact pairSeedAttached_of routing routingEq avoids family threshold base lengthLaw slack
      large (Or.inr rfl) Xp Xq Z connZ (fun fP fQ bQ bP => by
        obtain ⟨-, -, -, univ, -, cutQ, -, evQ, cub, -⟩ := whole fP fQ bQ bP
        exact ⟨univ, cutQ, evQ, fun v h => (cub v h).2⟩)

end Separator

end Hypostructure.Graph.Contracts.Spine.SameTokenWalkCycles
