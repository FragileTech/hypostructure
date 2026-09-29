import Hypostructure.Graph.LadderRun

/-!
# Counting the exceptional positions and the bad rung indices (`[144a]`, G audit S144a)

Vocabulary-free.  Continues `LadderRun.lean`: the neighbours of a vertex on a geodesic walk
(`nbrPos`), then the count of clean blocks of twelve rungs against hubs.
-/

namespace Hypostructure.Graph.LadderCount

open Hypostructure.Graph.PathChords
open Hypostructure.Graph.WalkIndex
open Hypostructure.Graph.LadderRun

universe u

section Nbr

variable {V : Type u} {G : SimpleGraph V}

open Classical in
/-- the positions of a walk whose vertex is adjacent to `z` -/
noncomputable def nbrPos {a b : V} (w : G.Walk a b) (z : V) : Finset ℕ :=
  (Finset.range (w.length + 1)).filter fun y => G.Adj z (w.getVert y)

/-- **A vertex off a geodesic walk has at most two neighbours on it** (matching step). -/
theorem nbrPos_le_two_of_match {LengthOK : Nat → Prop} {a b : V} {w : G.Walk a b}
    (hp : w.IsPath) (hub : GeodesicHubAdj LengthOK w) (ok4 : LengthOK 4)
    (match_ : ∀ h x y z : V, G.Adj h x → G.Adj h y → G.Adj h z → G.Adj x y → G.Adj x z → y = z)
    {z : V} (hz : z ∉ w.support) : (nbrPos w z).card ≤ 2 := by
  classical
  by_contra big
  push Not at big
  obtain ⟨y1, h1, y2, h2, y3, h3, n12, n13, n23⟩ := Finset.two_lt_card.1 big
  simp only [nbrPos, Finset.mem_filter, Finset.mem_range] at h1 h2 h3
  have i12 : w.getVert y1 ≠ w.getVert y2 := fun h => n12 (getVert_inj hp (by omega) (by omega) h)
  have i13 : w.getVert y1 ≠ w.getVert y3 := fun h => n13 (getVert_inj hp (by omega) (by omega) h)
  have m1 : w.getVert y1 ∈ w.support := SimpleGraph.Walk.getVert_mem_support _ _
  have m2 : w.getVert y2 ∈ w.support := SimpleGraph.Walk.getVert_mem_support _ _
  have m3 : w.getVert y3 ∈ w.support := SimpleGraph.Walk.getVert_mem_support _ _
  have a12 := hub ok4 z _ _ hz m1 m2 i12 h1.2.symm h2.2
  have a13 := hub ok4 z _ _ hz m1 m3 i13 h1.2.symm h3.2
  exact n23 (getVert_inj hp (by omega) (by omega) (match_ z _ _ _ h1.2 h2.2 h3.2 a12 a13))


/-- **A cubic vertex has at most three neighbours on a walk.** -/
theorem nbrPos_le_three_of_cubic {Cubic : V → Prop}
    (stub : ∀ m, Cubic m → ∀ a b, G.Adj m a → G.Adj m b → a ≠ b →
      ∃ s, G.Adj m s ∧ s ≠ a ∧ s ≠ b ∧ ∀ t, G.Adj m t → t = a ∨ t = b ∨ t = s)
    {a b : V} {w : G.Walk a b} (hp : w.IsPath) {z : V} (hz : Cubic z) :
    (nbrPos w z).card ≤ 3 := by
  classical
  by_cases small : (nbrPos w z).card ≤ 1
  · omega
  push Not at small
  obtain ⟨y1, h1, y2, h2, n12⟩ := Finset.one_lt_card.1 small
  simp only [nbrPos, Finset.mem_filter, Finset.mem_range] at h1 h2
  have i12 : w.getVert y1 ≠ w.getVert y2 := fun h => n12 (getVert_inj hp (by omega) (by omega) h)
  obtain ⟨s, -, -, -, hall⟩ := stub z hz _ _ h1.2 h2.2 i12
  have : (nbrPos w z).card ≤ ({w.getVert y1, w.getVert y2, s} : Finset V).card := by
    apply Finset.card_le_card_of_injOn (fun y => w.getVert y)
    · intro y hy
      simp only [nbrPos, Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hy
      have := hall _ hy.2
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff]
      exact this
    · intro y hy y' hy' h
      simp only [nbrPos, Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hy hy'
      exact getVert_inj hp (by omega) (by omega) h
  exact le_trans this (Finset.card_le_three)

/-- **A vertex off a geodesic walk has at most three neighbours on it.** -/
theorem nbrPos_le_three {LengthOK : Nat → Prop} {Cubic : V → Prop}
    (stub : ∀ m, Cubic m → ∀ a b, G.Adj m a → G.Adj m b → a ≠ b →
      ∃ s, G.Adj m s ∧ s ≠ a ∧ s ≠ b ∧ ∀ t, G.Adj m t → t = a ∨ t = b ∨ t = s)
    {a b : V} {w : G.Walk a b} (hp : w.IsPath) (hub : GeodesicHubAdj LengthOK w)
    (ok4 : LengthOK 4)
    (match_ : ∀ h x y z : V, G.Adj h x → G.Adj h y → G.Adj h z → G.Adj x y → G.Adj x z → y = z)
    {z : V} (hz : z ∉ w.support) : (nbrPos w z).card ≤ 3 := by
  by_cases hc : Cubic z
  · exact nbrPos_le_three_of_cubic stub hp hc
  · have := nbrPos_le_two_of_match hp hub ok4 match_ hz
    omega

end Nbr


section Count

variable {V : Type u} {G : SimpleGraph V} [DecidableEq V]

/-- The global hypotheses of the count. -/
structure CountHyp (G : SimpleGraph V) (LengthOK : Nat → Prop) (Cubic : V → Prop)
    {a1 b1 a2 b2 : V} (w1 : G.Walk a1 b1) (w2 : G.Walk a2 b2) : Prop where
  stub : ∀ x, Cubic x → ∀ a b, G.Adj x a → G.Adj x b → a ≠ b →
    ∃ s, G.Adj x s ∧ s ≠ a ∧ s ≠ b ∧ ∀ t, G.Adj x t → t = a ∨ t = b ∨ t = s
  avoids : ¬ ∃ (c : V) (cy : G.Walk c c), cy.IsCycle ∧ LengthOK cy.length
  ok4 : LengthOK 4
  ok8 : LengthOK 8
  ok16 : LengthOK 16
  hp1 : w1.IsPath
  hp2 : w2.IsPath
  det1 : GeodesicDetours s(a1, b1) w1
  det2 : GeodesicDetours s(a2, b2) w2
  hub1 : GeodesicHubAdj LengthOK w1
  hub2 : GeodesicHubAdj LengthOK w2
  match_ : ∀ h x y z : V, G.Adj h x → G.Adj h y → G.Adj h z → G.Adj x y → G.Adj x z → y = z

variable {LengthOK : Nat → Prop} {Cubic : V → Prop} {a1 b1 a2 b2 : V} {w1 : G.Walk a1 b1}
  {w2 : G.Walk a2 b2}

open Classical in
/-- the exceptional positions of the second walk -/
noncomputable def excPos (Cubic : V → Prop) (w1 : G.Walk a1 b1) (w2 : G.Walk a2 b2) : Finset ℕ :=
  (Finset.range (w2.length + 1)).filter fun y => Exceptional Cubic w1 w2 y

/-- **There are few exceptional positions**: at most `4|X| + 3|U| + 8`, `X` the non-cubic
vertices and `U` the cubic vertices off both walks. -/
theorem excPos_card_le (H : CountHyp G LengthOK Cubic w1 w2) (X U : Finset V)
    (hX : ∀ z, ¬ Cubic z → z ∈ X)
    (hU : ∀ z, Cubic z → z ∉ w1.support → z ∉ w2.support → z ∈ U) :
    (excPos Cubic w1 w2).card ≤ 4 * X.card + 3 * U.card + 8 := by
  classical
  let S : Finset V := X ∪ U ∪ {a1, b1}
  let S' : Finset V := S.filter (· ∉ w2.support)
  let Apos : Finset ℕ := (Finset.range (w2.length + 1)).filter fun y => ¬ Cubic (w2.getVert y)
  have hsub : excPos Cubic w1 w2 ⊆ ({0, w2.length} : Finset ℕ) ∪ Apos ∪
      S'.biUnion (fun s => nbrPos w2 s) := by
    intro y hy
    simp only [excPos, Finset.mem_filter, Finset.mem_range] at hy
    obtain ⟨hyl, hexc⟩ := hy
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Apos,
      Finset.mem_filter, Finset.mem_range, Finset.mem_biUnion]
    unfold Exceptional at hexc
    rcases hexc with h | h | h | ⟨s, hs, hsn, hsc⟩
    · left; left; left; exact h
    · left; left; right; omega
    · left; right; exact ⟨hyl, h⟩
    · right
      refine ⟨s, ?_, ?_⟩
      · simp only [S', S, Finset.mem_filter, Finset.mem_union, Finset.mem_insert,
          Finset.mem_singleton]
        refine ⟨?_, hsn⟩
        rcases hsc with h | h | h | h
        · left; left; exact hX s h
        · right; left; exact h
        · right; right; exact h
        · by_cases hcs : Cubic s
          · left; right; exact hU s hcs h hsn
          · left; left; exact hX s hcs
      · simp only [nbrPos, Finset.mem_filter, Finset.mem_range]
        exact ⟨hyl, hs.symm⟩
  have hApos : Apos.card ≤ X.card := by
    apply Finset.card_le_card_of_injOn (fun y => w2.getVert y)
    · intro y hy
      simp only [Apos, Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hy
      exact hX _ hy.2
    · intro y hy y' hy' h
      simp only [Apos, Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hy hy'
      exact getVert_inj H.hp2 (by omega) (by omega) h
  have hS' : ∀ s ∈ S', (nbrPos w2 s).card ≤ 3 := by
    intro s hs
    simp only [S', Finset.mem_filter] at hs
    exact nbrPos_le_three H.stub H.hp2 H.hub2 H.ok4 H.match_ hs.2
  have hbi : (S'.biUnion (fun s => nbrPos w2 s)).card ≤ 3 * S'.card := by
    calc (S'.biUnion (fun s => nbrPos w2 s)).card ≤ ∑ s ∈ S', (nbrPos w2 s).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ s ∈ S', 3 := Finset.sum_le_sum hS'
      _ = 3 * S'.card := by simp [mul_comm]
  have hSc : S'.card ≤ X.card + U.card + 2 := by
    calc S'.card ≤ S.card := Finset.card_filter_le _ _
      _ ≤ (X ∪ U).card + ({a1, b1} : Finset V).card := Finset.card_union_le _ _
      _ ≤ X.card + U.card + 2 := by
        have h1 := Finset.card_union_le X U
        have h2 : ({a1, b1} : Finset V).card ≤ 2 := Finset.card_le_two
        omega
  have h0 : ({0, w2.length} : Finset ℕ).card ≤ 2 := Finset.card_le_two
  calc (excPos Cubic w1 w2).card
      ≤ (({0, w2.length} : Finset ℕ) ∪ Apos ∪ S'.biUnion (fun s => nbrPos w2 s)).card :=
        Finset.card_le_card hsub
    _ ≤ ({0, w2.length} : Finset ℕ).card + Apos.card + (S'.biUnion (fun s => nbrPos w2 s)).card := by
        have := Finset.card_union_le (({0, w2.length} : Finset ℕ) ∪ Apos)
          (S'.biUnion (fun s => nbrPos w2 s))
        have := Finset.card_union_le ({0, w2.length} : Finset ℕ) Apos
        omega
    _ ≤ 4 * X.card + 3 * U.card + 8 := by omega


/-- a clean rung index of the first walk -/
def Clean (Cubic : V → Prop) (w1 : G.Walk a1 b1) (w2 : G.Walk a2 b2) (t : ℕ) : Prop :=
  Cubic (w1.getVert t) ∧ w1.getVert t ∉ w2.support ∧
    ∃ y, 0 < y ∧ y < w2.length ∧ G.Adj (w1.getVert t) (w2.getVert y) ∧
      Cubic (w2.getVert y) ∧ w2.getVert y ∉ w1.support

open Classical in
/-- the interior indices of the first walk that are not clean -/
noncomputable def badSet (Cubic : V → Prop) (w1 : G.Walk a1 b1) (w2 : G.Walk a2 b2) :
    Finset ℕ :=
  (Finset.range w1.length).filter fun t => 0 < t ∧ ¬ Clean Cubic w1 w2 t

open Classical in
/-- the interior indices of the first walk lying on the second -/
noncomputable def ovSet (w1 : G.Walk a1 b1) (w2 : G.Walk a2 b2) : Finset ℕ :=
  (Finset.range w1.length).filter fun t => 0 < t ∧ w1.getVert t ∈ w2.support

open Classical in
/-- the interior indices of the first walk lying on the second and having a neighbour on the
second walk outside the first (the *meeting points*: where the second walk leaves or enters
the first) -/
noncomputable def ovDiv (w1 : G.Walk a1 b1) (w2 : G.Walk a2 b2) : Finset ℕ :=
  (Finset.range w1.length).filter fun t => 0 < t ∧ w1.getVert t ∈ w2.support ∧
    ∃ y, y ≤ w2.length ∧ G.Adj (w1.getVert t) (w2.getVert y) ∧ w2.getVert y ∉ w1.support

theorem badSet_card_le (H : CountHyp G LengthOK Cubic w1 w2) (X U : Finset V)
    (hX : ∀ z, ¬ Cubic z → z ∈ X)
    (hU : ∀ z, Cubic z → z ∉ w1.support → z ∉ w2.support → z ∈ U) :
    (badSet Cubic w1 w2).card ≤ 4 * X.card + (ovDiv w1 w2).card + 3 * U.card + 6 := by
  classical
  let S2 : Finset V := X ∪ U ∪ {a2, b2}
  let S2' : Finset V := S2.filter (· ∉ w1.support)
  let B1 : Finset ℕ := (Finset.range (w1.length + 1)).filter fun t => ¬ Cubic (w1.getVert t)
  have hsub : badSet Cubic w1 w2 ⊆ B1 ∪ ovDiv w1 w2 ∪ S2'.biUnion (fun s => nbrPos w1 s) := by
    intro t ht
    simp only [badSet, Finset.mem_filter, Finset.mem_range] at ht
    obtain ⟨htl, ht0, hclean⟩ := ht
    simp only [Finset.mem_union, B1, ovDiv, Finset.mem_filter, Finset.mem_range,
      Finset.mem_biUnion]
    by_cases hc : Cubic (w1.getVert t)
    · have hpred : G.Adj (w1.getVert t) (w1.getVert (t - 1)) := by
        have := w1.adj_getVert_succ (i := t - 1) (by omega)
        have e : t - 1 + 1 = t := by omega
        rw [e] at this
        exact this.symm
      have hsucc : G.Adj (w1.getVert t) (w1.getVert (t + 1)) := w1.adj_getVert_succ htl
      have hpne : w1.getVert (t - 1) ≠ w1.getVert (t + 1) := by
        intro h
        have := getVert_inj H.hp1 (by omega) (by omega) h
        omega
      obtain ⟨s, hs_adj, hsp, hss, hall⟩ := H.stub _ hc _ _ hpred hsucc hpne
      have hs_off : s ∉ w1.support := by
        intro hs
        rcases induced_nbrs H.hp1 H.det1 ht0 htl hs hs_adj with h | h
        · exact hsp h
        · exact hss h
      by_cases hsS : s ∈ S2
      · right
        refine ⟨s, ?_, ?_⟩
        · simp only [S2', Finset.mem_filter]
          exact ⟨hsS, hs_off⟩
        · simp only [nbrPos, Finset.mem_filter, Finset.mem_range]
          exact ⟨by omega, hs_adj.symm⟩
      · have hcs : Cubic s := by
          by_contra h
          apply hsS
          simp only [S2, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
          exact Or.inl (Or.inl (hX s h))
        have hs2 : s ∈ w2.support := by
          by_contra h
          apply hsS
          simp only [S2, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
          exact Or.inl (Or.inr (hU s hcs hs_off h))
        obtain ⟨y, hy, hyl⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.1 hs2
        have hy0 : y ≠ 0 := by
          intro h0
          apply hsS
          simp only [S2, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
          right; left
          rw [← hy, h0, SimpleGraph.Walk.getVert_zero]
        have hyl' : y ≠ w2.length := by
          intro h0
          apply hsS
          simp only [S2, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
          right; right
          rw [← hy, h0, SimpleGraph.Walk.getVert_length]
        by_cases hin : w1.getVert t ∈ w2.support
        · left; right
          refine ⟨htl, ht0, hin, y, hyl, ?_, ?_⟩
          · rw [hy]; exact hs_adj
          · rw [hy]; exact hs_off
        · exfalso
          apply hclean
          refine ⟨hc, hin, y, by omega, by omega, ?_, ?_, ?_⟩
          · rw [hy]; exact hs_adj
          · rw [hy]; exact hcs
          · rw [hy]; exact hs_off
    · left; left; exact ⟨by omega, hc⟩
  have hB1 : B1.card ≤ X.card := by
    apply Finset.card_le_card_of_injOn (fun y => w1.getVert y)
    · intro y hy
      simp only [B1, Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hy
      exact hX _ hy.2
    · intro y hy y' hy' h
      simp only [B1, Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hy hy'
      exact getVert_inj H.hp1 (by omega) (by omega) h
  have hS' : ∀ s ∈ S2', (nbrPos w1 s).card ≤ 3 := by
    intro s hs
    simp only [S2', Finset.mem_filter] at hs
    exact nbrPos_le_three H.stub H.hp1 H.hub1 H.ok4 H.match_ hs.2
  have hbi : (S2'.biUnion (fun s => nbrPos w1 s)).card ≤ 3 * S2'.card := by
    calc (S2'.biUnion (fun s => nbrPos w1 s)).card ≤ ∑ s ∈ S2', (nbrPos w1 s).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ s ∈ S2', 3 := Finset.sum_le_sum hS'
      _ = 3 * S2'.card := by simp [mul_comm]
  have hSc : S2'.card ≤ X.card + U.card + 2 := by
    calc S2'.card ≤ S2.card := Finset.card_filter_le _ _
      _ ≤ (X ∪ U).card + ({a2, b2} : Finset V).card := Finset.card_union_le _ _
      _ ≤ X.card + U.card + 2 := by
        have h1 := Finset.card_union_le X U
        have h2 : ({a2, b2} : Finset V).card ≤ 2 := Finset.card_le_two
        omega
  calc (badSet Cubic w1 w2).card
      ≤ (B1 ∪ ovDiv w1 w2 ∪ S2'.biUnion (fun s => nbrPos w1 s)).card := Finset.card_le_card hsub
    _ ≤ B1.card + (ovDiv w1 w2).card + (S2'.biUnion (fun s => nbrPos w1 s)).card := by
        have := Finset.card_union_le (B1 ∪ ovDiv w1 w2) (S2'.biUnion (fun s => nbrPos w1 s))
        have := Finset.card_union_le B1 (ovDiv w1 w2)
        omega
    _ ≤ 4 * X.card + (ovDiv w1 w2).card + 3 * U.card + 6 := by omega


/-- the properties of the exceptional position produced by a clean block -/
def BlockProp (Cubic : V → Prop) (w1 : G.Walk a1 b1) (w2 : G.Walk a2 b2) (b : ℕ)
    (p y a : ℕ) : Prop :=
  1 + 24 * b + 5 ≤ p ∧ p ≤ 1 + 24 * b + 6 ∧ y ≤ w2.length ∧ Exceptional Cubic w1 w2 y ∧
    0 < a ∧ a < w2.length ∧ (y = a + 1 ∨ y + 1 = a) ∧
    G.Adj (w1.getVert p) (w2.getVert a) ∧ w2.getVert a ∉ w1.support ∧
    w1.getVert p ∉ w2.support ∧ Cubic (w2.getVert a) ∧ Cubic (w1.getVert p) ∧ p < w1.length

/-- **A clean block of twenty-four rung indices has an exceptional position.** -/
theorem block_exc (H : CountHyp G LengthOK Cubic w1 w2) {b : ℕ}
    (hb : 1 + 24 * b + 24 ≤ w1.length)
    (hclean : ∀ j < 24, Clean Cubic w1 w2 (1 + 24 * b + j)) :
    ∃ p y a, BlockProp Cubic w1 w2 b p y a := by
  classical
  have hex : ∀ j : ℕ, ∃ y : ℕ, j < 24 → (0 < y ∧ y < w2.length ∧
      G.Adj (w1.getVert (1 + 24 * b + j)) (w2.getVert y) ∧ Cubic (w2.getVert y) ∧
      w2.getVert y ∉ w1.support) := by
    intro j
    by_cases hj : j < 24
    · obtain ⟨-, -, y, hy⟩ := hclean j hj
      exact ⟨y, fun _ => hy⟩
    · exact ⟨0, fun h => absurd h hj⟩
  choose σ hσ using hex
  have R : RunHyp G LengthOK Cubic w1 w2 (1 + 24 * b) σ :=
    { stub := H.stub, avoids := H.avoids, ok4 := H.ok4, ok8 := H.ok8, ok16 := H.ok16,
      hp1 := H.hp1, hp2 := H.hp2, det1 := H.det1, det2 := H.det2
      m_pos := by omega, m_len := by omega
      v_cubic := fun j hj => (hclean j (by omega)).1
      v_off := fun j hj => (hclean j (by omega)).2.1
      q_cubic := fun j hj => (hσ j (by omega)).2.2.2.1
      q_off := fun j hj => (hσ j (by omega)).2.2.2.2
      q_pos := fun j hj => (hσ j (by omega)).1
      q_len := fun j hj => (hσ j (by omega)).2.1
      rung := fun j hj => (hσ j (by omega)).2.2.1 }
  obtain ⟨r, hr, y, hy, hexc⟩ := R.run_exceptional
  have hr24 : r < 24 := by omega
  have hσr := hσ r hr24
  refine ⟨1 + 24 * b + r, y, σ r, ?_, ?_, ?_, hexc, hσr.1, hσr.2.1, hy, hσr.2.2.1,
    hσr.2.2.2.2, (hclean r hr24).2.1, hσr.2.2.2.1, (hclean r hr24).1, by omega⟩
  · omega
  · omega
  · have := hσr.2.1
    omega

/-- Two rungs whose partners are within two on the second walk are within four on the first. -/
theorem rungs_close_aux (H : CountHyp G LengthOK Cubic w1 w2) {p p' a a' : ℕ}
    (hp : p < w1.length) (hp' : p' < w1.length) (ha : a < w2.length) (ha' : a' < w2.length)
    (hqa : w2.getVert a ∉ w1.support) (hqa' : w2.getVert a' ∉ w1.support)
    (r1 : G.Adj (w1.getVert p) (w2.getVert a)) (r2 : G.Adj (w1.getVert p') (w2.getVert a'))
    (hlt : a < a') (hle : a' ≤ a + 2) : p ≤ p' + 4 ∧ p' ≤ p + 4 := by
  have step1 : G.Adj (w2.getVert a) (w2.getVert (a + 1)) := w2.adj_getVert_succ (by omega)
  have hcases : a' = a + 1 ∨ a' = a + 2 := by omega
  rcases hcases with h | h
  · subst h
    let d : G.Walk (w1.getVert p) (w1.getVert p') :=
      SimpleGraph.Walk.cons r1 (SimpleGraph.Walk.cons step1 (SimpleGraph.Walk.cons r2.symm .nil))
    have hd : ∀ ε ∈ d.edges, ε ≠ s(a1, b1) := by
      intro ε hε
      simp only [d, SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil, List.mem_cons,
        List.not_mem_nil, or_false] at hε
      rcases hε with rfl | rfl | rfl
      · exact (edge_ne_of_notMem hqa).2
      · exact (edge_ne_of_notMem hqa).1
      · exact (edge_ne_of_notMem hqa').1
    have := idx_dist_le H.det1 (le_of_lt hp) (le_of_lt hp') d hd
    simp only [d, SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_nil] at this
    omega
  · subst h
    have step2 : G.Adj (w2.getVert (a + 1)) (w2.getVert (a + 2)) := w2.adj_getVert_succ (by omega)
    let d : G.Walk (w1.getVert p) (w1.getVert p') :=
      SimpleGraph.Walk.cons r1 (SimpleGraph.Walk.cons step1 (SimpleGraph.Walk.cons step2
        (SimpleGraph.Walk.cons r2.symm .nil)))
    have hd : ∀ ε ∈ d.edges, ε ≠ s(a1, b1) := by
      intro ε hε
      simp only [d, SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil, List.mem_cons,
        List.not_mem_nil, or_false] at hε
      rcases hε with rfl | rfl | rfl | rfl
      · exact (edge_ne_of_notMem hqa).2
      · exact (edge_ne_of_notMem hqa).1
      · exact (edge_ne_of_notMem hqa').2
      · exact (edge_ne_of_notMem hqa').1
    have := idx_dist_le H.det1 (le_of_lt hp) (le_of_lt hp') d hd
    simp only [d, SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_nil] at this
    omega


theorem rungs_close (H : CountHyp G LengthOK Cubic w1 w2) {p p' a a' : ℕ}
    (hp : p < w1.length) (hp' : p' < w1.length) (ha0 : 0 < a) (ha : a < w2.length)
    (ha' : a' < w2.length)
    (hqa : w2.getVert a ∉ w1.support) (hqa' : w2.getVert a' ∉ w1.support)
    (hca : Cubic (w2.getVert a))
    (hvp : w1.getVert p ∉ w2.support) (hvp' : w1.getVert p' ∉ w2.support)
    (r1 : G.Adj (w1.getVert p) (w2.getVert a)) (r2 : G.Adj (w1.getVert p') (w2.getVert a'))
    (h1 : a ≤ a' + 2) (h2 : a' ≤ a + 2) :
    (p ≤ p' + 4 ∧ p' ≤ p + 4) ∨ p = p' := by
  rcases lt_trichotomy a a' with h | h | h
  · left; exact rungs_close_aux H hp hp' ha ha' hqa hqa' r1 r2 h h2
  · right
    subst h
    have := nbr_outside_unique Cubic H.stub H.hp2 ha0 ha hca hvp hvp' r1.symm r2.symm
    exact getVert_inj H.hp1 (le_of_lt hp) (le_of_lt hp') this
  · left
    have := rungs_close_aux H hp' hp ha' ha hqa' hqa r2 r1 h h1
    omega

/-- **The count.**  For the two geodesic walks with `X` the non-cubic vertices and `U` the cubic
vertices off both walks: `⌊(|w₁| − 1)/24⌋ ≤ 8|X| + 6|U| + |ovDiv w₁ w₂| + 14`, `ovDiv` the meeting points (interior positions of `w₁` on `w₂` with a neighbour on `w₂` outside `w₁`). -/
theorem ladder_count (H : CountHyp G LengthOK Cubic w1 w2) (X U : Finset V)
    (hX : ∀ z, ¬ Cubic z → z ∈ X)
    (hU : ∀ z, Cubic z → z ∉ w1.support → z ∉ w2.support → z ∈ U) :
    (w1.length - 1) / 24 ≤ 8 * X.card + 6 * U.card + (ovDiv w1 w2).card + 14 := by
  classical
  set K := (w1.length - 1) / 24 with hK
  have hKlen : 24 * K + 1 ≤ w1.length ∨ K = 0 := by
    by_cases h0 : K = 0
    · right; exact h0
    · left; omega
  have hE := excPos_card_le H X U hX hU
  have hB := badSet_card_le H X U hX hU
  -- clean and dirty blocks
  let Cb : Finset ℕ := (Finset.range K).filter fun b => ∀ j < 24, Clean Cubic w1 w2 (1 + 24 * b + j)
  let Db : Finset ℕ := (Finset.range K).filter fun b => ¬ ∀ j < 24, Clean Cubic w1 w2 (1 + 24 * b + j)
  have hsplit : K = Cb.card + Db.card := by
    have := Finset.card_filter_add_card_filter_not (s := Finset.range K)
      (fun b => ∀ j < 24, Clean Cubic w1 w2 (1 + 24 * b + j))
    rw [Finset.card_range] at this
    exact this.symm
  -- dirty blocks inject into bad indices
  have hDb : Db.card ≤ (badSet Cubic w1 w2).card := by
    have hex : ∀ b ∈ Db, ∃ t, 1 + 24 * b ≤ t ∧ t < 1 + 24 * b + 24 ∧ ¬ Clean Cubic w1 w2 t := by
      intro b hb
      simp only [Db, Finset.mem_filter, Finset.mem_range] at hb
      push Not at hb
      obtain ⟨j, hj, hnc⟩ := hb.2
      exact ⟨1 + 24 * b + j, by omega, by omega, hnc⟩
    choose! t ht using hex
    apply Finset.card_le_card_of_injOn t
    · intro b hb
      have hb' := Finset.mem_coe.1 hb
      have := ht b hb'
      simp only [Db, Finset.mem_filter, Finset.mem_range] at hb'
      simp only [badSet, Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq]
      have hlen : 24 * K + 1 ≤ w1.length := by
        rcases hKlen with h | h
        · exact h
        · omega
      refine ⟨by omega, by omega, this.2.2⟩
    · intro b hb b' hb' h
      have h1 := ht b (Finset.mem_coe.1 hb)
      have h2 := ht b' (Finset.mem_coe.1 hb')
      omega
  -- clean blocks inject into exceptional positions
  have hCb : Cb.card ≤ (excPos Cubic w1 w2).card := by
    have hex : ∀ b ∈ Cb, ∃ p y a, BlockProp Cubic w1 w2 b p y a := by
      intro b hb
      simp only [Cb, Finset.mem_filter, Finset.mem_range] at hb
      have hlen : 24 * K + 1 ≤ w1.length := by
        rcases hKlen with h | h
        · exact h
        · omega
      exact block_exc H (by omega) hb.2
    choose! p y a hpya using hex
    apply Finset.card_le_card_of_injOn y
    · intro b hb
      have hbc := Finset.mem_coe.1 hb
      have h := hpya b hbc
      simp only [excPos, Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq]
      exact ⟨by have := h.2.2.1; omega, h.2.2.2.1⟩
    · intro b hb b' hb' hyy
      have h1 := hpya b (Finset.mem_coe.1 hb)
      have h2 := hpya b' (Finset.mem_coe.1 hb')
      obtain ⟨hp1, hp2, hy, hexc, ha0, ha, hyrel, hadj, hqoff, hvoff, hcub, hvcub, hplen⟩ := h1
      obtain ⟨hp1', hp2', hy', hexc', ha0', ha', hyrel', hadj', hqoff', hvoff', hcub', hvcub',
        hplen'⟩ := h2
      have hclose := rungs_close H (p := p b) (p' := p b') (a := a b) (a' := a b') hplen hplen'
        ha0 ha ha' hqoff hqoff' hcub hvoff hvoff' hadj hadj'
        (by omega) (by omega)
      by_contra hne
      have : b < b' ∨ b' < b := lt_or_gt_of_ne hne
      rcases hclose with hc | hc <;> omega
  omega

end Count

end Hypostructure.Graph.LadderCount
