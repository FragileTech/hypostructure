import Hypostructure.Graph.Contracts.Spine.SameTokenWalkCycles
import Hypostructure.Graph.Statements.SameTokenHubEscape

/-!
# Contracts: hubs escape to `Y` along the canonical port walks; the triangular sub-arm is
empty (`[144a]` exchange attack, Lean improvement)

Proof-agnostic contract lemmas for the four statements of
`Statements/SameTokenHubEscape.lean`.  The mathematics is the vocabulary-free
`Graph/WalkHubEscape.lean`; the triangular sub-arm is closed by combining its count with the
separated-configuration count of `SameTokenWalkCycles.seedAttached_core` (key 9991's argument,
re-run at the same walk witness): `|Y| ≤ |T| + |V ∖ seed| ≤ 4|T| ≤ 24`, so
`σ ≤ 37·24 + 21 + 72·24 = 2637`, while the ledger has `σ > C_sp⌈√n⌉ ≥ 102·103`.

This module imports no strategy, row, or vocabulary module.
-/

set_option linter.unusedSectionVars false

namespace Hypostructure.Graph.Contracts.Spine.SameTokenHubEscape

open Hypostructure
open Hypostructure.Graph
open Hypostructure.Graph.Strategy.Spine
open Hypostructure.Graph.PortPathCover
open Hypostructure.Graph.WalkHubEscape
open Hypostructure.Graph.Contracts.Spine.SameTokenSeedCover
open Hypostructure.Graph.Contracts.Spine.SameTokenWalkCycles

universe u

section Walks

attribute [local instance] Graph.FiniteObject.vertices Graph.FiniteObject.decideAdj

variable {data : Parameters} {object : Graph.FiniteObject.{u}}

/-- A triangular port walk avoids its port edge. -/
theorem portWalk_av {LengthOK : ℕ → Prop} {a b : object.Vertex} {w : object.graph.Walk a b}
    (h : PortWalk object LengthOK w) (t : object.graph.Adj b a) : ∀ ε ∈ w.edges, ε ≠ s(a, b) := by
  rcases h.2.2.2.2.2 with ⟨-, g, -, -⟩ | ⟨x, -, -, -, nab, -⟩
  · exact g.1
  · exact absurd t.symm nab

/-- **The hypotheses `Tri2` at two triangular port walks of G**, from the ledger facts. -/
theorem tri2_of (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (lengthLaw : ∀ length, data.LengthOK length ↔ Core.DyadicLength.PowerOfTwoLength length)
    (base : MinDegreeBaselineStatement data object) (threshold : data.threshold = 3)
    (slack : SlackIndependentStatement data object)
    {a1 b1 a2 b2 : object.Vertex} {w1 : object.graph.Walk a1 b1} {w2 : object.graph.Walk a2 b2}
    (h1 : PortWalk object data.LengthOK w1) (h2 : PortWalk object data.LengthOK w2)
    (t1 : object.graph.Adj b1 a1) (t2 : object.graph.Adj b2 a2) :
    Tri2 object data.LengthOK w1 w2 := by
  have cyc := noCycle_form avoids
  have ok4 : data.LengthOK 4 := (lengthLaw 4).2 ⟨⟨2, by omega⟩, by norm_num⟩
  have ok8 : data.LengthOK 8 := (lengthLaw 8).2 ⟨⟨3, by omega⟩, by norm_num⟩
  have ok16 : data.LengthOK 16 := (lengthLaw 16).2 ⟨⟨4, by omega⟩, by norm_num⟩
  have pairs : Graph.CycleCounting.NeighbourhoodPairs object :=
    Graph.CycleCounting.neighbourhoodPairs avoids ok4
  refine ⟨LadderG.countHyp_of ok4 ok8 ok16 cyc pairs h1 h2 t1 t2, t1, t2, portWalk_av h1 t1,
    portWalk_av h2 t2, fun v => ?_, fun l r hl hr => slack l r (by rw [threshold]; exact hl)
      (by rw [threshold]; exact hr)⟩
  have := le_trans base (object.minDegree_le_degree v)
  omega

/-- **9852: the W0 escape at the canonical port walks.** -/
theorem sameTokenW0Escape_holds
    (supports : SameTokenPatternSupportsStatement data object)
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (family : ActiveSurplusFamilyStatement data object)
    (threshold : data.threshold = 3)
    (lengthLaw : ∀ length, data.LengthOK length ↔ Core.DyadicLength.PowerOfTwoLength length)
    (base : MinDegreeBaselineStatement data object)
    (slack : SlackIndependentStatement data object) :
    SameTokenW0EscapeStatement data object := by
  obtain ⟨routing, routingEq, -⟩ := supports
  refine ⟨routing, routingEq, fun pair hpair => ⟨?_, ?_⟩⟩
  · obtain ⟨T, a1, b1, a2, b2, w1, w2, hT, hw1, hw2, eP⟩ :=
      pairSeedWalks routing routingEq avoids family threshold hpair
    exact ⟨T, a1, b1, a2, b2, w1, w2, hT, hw1, hw2, eP⟩
  · rintro T a1 b1 a2 b2 w1 w2 ⟨-, hw1, hw2, -⟩ t1 t2
    have Tr := tri2_of avoids lengthLaw base threshold slack hw1 hw2 t1 t2
    exact ⟨w0Escape_of Tr, w0Escape_of Tr.swap⟩

/-- The crossing facts at two walks. -/
theorem crossingFacts_of {LengthOK : ℕ → Prop} {a1 b1 a2 b2 : object.Vertex}
    {w1 : object.graph.Walk a1 b1} {w2 : object.graph.Walk a2 b2}
    (Tr : Tri2 object LengthOK w1 w2) (E : LadderG.EndEdgesFree object w1 w2) :
    CrossingFacts object w1 w2 :=
  ⟨fun _ _ ht0 htl hp0 hpl hc hhub noY => crossing_exit Tr E ht0 htl hp0 hpl hc hhub noY,
    fun _ _ _ _ htt ht' hp hp' h1 h2 hoff => bubble_escape Tr E htt ht' hp hp' h1 h2 hoff,
    crossings_le Tr E⟩

/-- **9853: the crossings of the canonical port walks.** -/
theorem sameTokenCrossingCount_holds
    (supports : SameTokenPatternSupportsStatement data object)
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (threshold : data.threshold = 3)
    (lengthLaw : ∀ length, data.LengthOK length ↔ Core.DyadicLength.PowerOfTwoLength length)
    (base : MinDegreeBaselineStatement data object)
    (slack : SlackIndependentStatement data object) :
    SameTokenCrossingCountStatement data object := by
  obtain ⟨routing, routingEq, -⟩ := supports
  refine ⟨routing, routingEq, fun pair _ => ?_⟩
  rintro T a1 b1 a2 b2 w1 w2 ⟨-, hw1, hw2, -⟩ t1 t2 E
  have Tr := tri2_of avoids lengthLaw base threshold slack hw1 hw2 t1 t2
  exact ⟨crossingFacts_of Tr E, crossingFacts_of Tr.swap ⟨E.2, E.1⟩⟩

/-- The hub count at two walks. -/
theorem hubCountFacts_of {LengthOK : ℕ → Prop} {a1 b1 a2 b2 : object.Vertex}
    {w1 : object.graph.Walk a1 b1} {w2 : object.graph.Walk a2 b2}
    (Tr : Tri2 object LengthOK w1 w2) (E : LadderG.EndEdgesFree object w1 w2)
    (base : Graph.MinimumDegreeAtLeast 3 object) : HubCountFacts object w1 w2 :=
  ⟨hub_count Tr E, hubsY_card Tr, sigma_count Tr base⟩

/-- **9854: the hub count in `|Y|`.** -/
theorem sameTokenHubCount_holds
    (supports : SameTokenPatternSupportsStatement data object)
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (threshold : data.threshold = 3)
    (lengthLaw : ∀ length, data.LengthOK length ↔ Core.DyadicLength.PowerOfTwoLength length)
    (base : MinDegreeBaselineStatement data object)
    (slack : SlackIndependentStatement data object) :
    SameTokenHubCountStatement data object := by
  obtain ⟨routing, routingEq, -⟩ := supports
  refine ⟨routing, routingEq, fun pair _ => ?_⟩
  rintro T a1 b1 a2 b2 w1 w2 ⟨-, hw1, hw2, -⟩ t1 t2 E
  have Tr := tri2_of avoids lengthLaw base threshold slack hw1 hw2 t1 t2
  exact hubCountFacts_of Tr E (threshold ▸ base)

/-- **`C_sp ≥ 102`** (`M₀ ≥ 5` from the registered quadratic safety `20 ≤ 2(1 + 2M₀)`). -/
theorem spineScale_ge_102 (threshold : data.threshold = 3)
    (safety : Graph.TokenLoad.quadraticSafetyScale ≤ 2 * (1 + 2 * data.homogeneousCap)) :
    102 ≤ data.spineScale := by
  have e : data.spineScale = 2 * (1 + 2 * data.homogeneousCap) +
      (2 * data.surplusScale + 2 * data.homogeneousCap * (3 * (data.threshold - 1) + 2)) :=
    rfl
  have q : Graph.TokenLoad.quadraticSafetyScale = 20 := rfl
  rw [q] at safety
  rw [e, threshold]
  have : 2 * data.homogeneousCap * (3 * (3 - 1) + 2) = 16 * data.homogeneousCap := by ring
  omega

/-- **The triangular sub-arm at one pair seed and one walk witness is empty.** -/
theorem triArm_at
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (threshold : data.threshold = 3)
    (base : MinDegreeBaselineStatement data object)
    (lengthLaw : ∀ length, data.LengthOK length ↔ Core.DyadicLength.PowerOfTwoLength length)
    (slack : SlackIndependentStatement data object)
    (large : 730 ≤ object.vertexCount)
    (hC : 102 ≤ data.spineScale)
    (surplus : SurplusAboveStatement data object)
    (ceil : CeilSqrtAboveScaleStatement data object)
    {seed Z : Finset object.Vertex}
    (connZ : Graph.SupportComponents.Connected.ConnectedOn object Z)
    (univ : ∀ v, v ∈ Z)
    (cut : ∀ v, v ∈ Z → v ∉ seed →
      ¬ Graph.SupportComponents.Connected.ConnectedOn object (Z.erase v))
    (ev : ∀ v, v ∉ seed → Even (object.degree v) ∧ 4 ≤ object.degree v)
    (cub : ∀ v, object.degree v = 3 → v ∈ seed)
    {T : Finset object.Vertex} {a1 b1 a2 b2 : object.Vertex}
    {w1 : object.graph.Walk a1 b1} {w2 : object.graph.Walk a2 b2}
    (hT : T.card ≤ 2 * data.threshold)
    (hw1 : PortWalk object data.LengthOK w1) (hw2 : PortWalk object data.LengthOK w2)
    (eP : seed = T ∪ w1.support.toFinset ∪ w2.support.toFinset)
    (t1 : object.graph.Adj b1 a1) (t2 : object.graph.Adj b2 a2)
    (E : LadderG.EndEdgesFree object w1 w2) : False := by
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
    exact (SimpleGraph.degree_pos_iff_exists_adj (G := object.graph) (v := v)).1 h
  have cut' : ∀ v, v ∉ seed →
      ∃ l r, l ≠ v ∧ r ≠ v ∧ ¬ WalkAttachment.JoinedAvoiding object.graph v l r := by
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
  have slack' : ∀ l r, 3 < object.degree l → 3 < object.degree r → ¬ object.graph.Adj l r :=
    fun l r hl hr => slack l r (by rw [threshold]; exact hl) (by rw [threshold]; exact hr)
  have hT6 : T.card ≤ 6 := by rw [threshold] at hT; exact hT
  have att := seedAttached_core ok4 ok8 ok16 cyc pairs hw1 hw2 t1 t2 T seed hT6 eP conn cut'
    (fun v hv => (ev v hv).2) cub base3 slack' large
  have offCard := att.2.1
  -- `|Y| ≤ 4|T| ≤ 24`
  have Ysub : Yset w1 w2 ⊆ T ∪ (object.vertexFinset \ seed) := by
    intro x hx
    obtain ⟨n1, n2⟩ := mem_Yset.1 hx
    by_cases hs : x ∈ seed
    · rw [eP] at hs
      simp only [Finset.mem_union, List.mem_toFinset] at hs
      rcases hs with (h | h) | h
      · exact Finset.mem_union_left _ h
      · exact absurd h n1
      · exact absurd h n2
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.2 ⟨object.mem_vertexFinset x, hs⟩)
  have Ycard : (Yset w1 w2).card ≤ 24 := by
    have a := Finset.card_le_card Ysub
    have b := Finset.card_union_le T (object.vertexFinset \ seed)
    omega
  -- the count
  have Tr := tri2_of avoids lengthLaw base threshold slack hw1 hw2 t1 t2
  have hc := hub_count Tr E
  have hy := hubsY_card Tr
  have sg := sigma_count Tr (threshold ▸ base)
  have prod : (hubsY object w1 w2).card * (Yset w1 w2).card ≤ 72 * 24 :=
    Nat.mul_le_mul (by omega) Ycard
  -- the ledger: `σ > C_sp⌈√n⌉ ≥ 102·103`
  have hs : data.spineScale * Core.ceilSqrt object.vertexCount <
      object.degreeSurplus data.threshold := surplus
  rw [threshold] at hs
  have hce : data.spineScale + 1 ≤ Core.ceilSqrt object.vertexCount := ceil
  have big : 102 * 103 ≤ data.spineScale * Core.ceilSqrt object.vertexCount :=
    Nat.mul_le_mul hC (by omega)
  omega

end Walks

section Arm

variable {data : Parameters} {object : Graph.FiniteObject.{u}}

/-- **9855: the triangular sub-arm is empty at G** (Lean improvement). -/
theorem sameTokenTriArmEmpty_holds
    (partition : SameTokenPairPartitionStatement data object)
    (noProper : NoProperBaselineStatement data object)
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (minimal : ∀ H : Graph.FiniteObject.{u}, H.LexicographicallySmaller object →
      Graph.MinimumDegreeAtLeast data.threshold H → Graph.HasCycleWithLength data.LengthOK H)
    (shape : VertexDeletionComponentsStatement object)
    (base : MinDegreeBaselineStatement data object)
    (threshold : data.threshold = 3)
    (lengthLaw : ∀ length, data.LengthOK length ↔ Core.DyadicLength.PowerOfTwoLength length)
    (slack : SlackIndependentStatement data object)
    (order : OrderAboveScaleSquareStatement data object)
    (safety : Graph.TokenLoad.quadraticSafetyScale ≤ 2 * (1 + 2 * data.homogeneousCap))
    (surplus : SurplusAboveStatement data object)
    (ceil : CeilSqrtAboveScaleStatement data object) :
    SameTokenTriArmEmptyStatement data object := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  have large := order_ge_730 threshold order safety
  have hC := spineScale_ge_102 threshold safety
  obtain ⟨routing, routingEq, Xp, Xq, Z, pinned, whole⟩ :=
    SameTokenSwap.sameTokenU2FreeWhole_holds partition noProper avoids minimal shape base
      threshold
  have connZ : Graph.SupportComponents.Connected.ConnectedOn object Z :=
    (CanonicalSupport.mem_candidates_iff.1 (CanonicalSupport.select?_mem_candidates pinned.2.2)).2
  refine ⟨routing, routingEq, Xp, Xq, Z, pinned, ?_, ?_⟩
  · rintro T a1 b1 a2 b2 w1 w2 ⟨hT, hw1, hw2, eP⟩ fP fQ bQ bP t1 t2 E
    obtain ⟨-, -, -, univ, cutP, -, evP, -, cub, -⟩ := whole fP fQ bQ bP
    exact triArm_at avoids threshold base lengthLaw slack large hC surplus ceil connZ univ cutP
      evP (fun v h => (cub v h).1) hT hw1 hw2 eP t1 t2 E
  · rintro T a1 b1 a2 b2 w1 w2 ⟨hT, hw1, hw2, eP⟩ fP fQ bQ bP t1 t2 E
    obtain ⟨-, -, -, univ, -, cutQ, -, evQ, cub, -⟩ := whole fP fQ bQ bP
    exact triArm_at avoids threshold base lengthLaw slack large hC surplus ceil connZ univ cutQ
      evQ (fun v h => (cub v h).2) hT hw1 hw2 eP t1 t2 E

end Arm

end Hypostructure.Graph.Contracts.Spine.SameTokenHubEscape
