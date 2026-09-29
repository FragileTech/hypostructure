import Hypostructure.Graph.TwoGeodesics
import Hypostructure.Graph.LadderCount

/-!
# Counting the meeting points of two geodesic paths (generic; `[144a]`, G audit S144a)

Vocabulary-free.  Continues `TwoGeodesics.lean`.  A *meeting point* of `w₁` with `w₂` is an
interior position of `w₁` on `w₂` with a neighbour on `w₂` off `w₁` (`LadderCount.ovDiv`).  Each
meeting point bounds a bubble (a maximal run of `w₁` off `w₂`) on one side, every bubble
contains an exceptional position, and the bubbles are disjoint: so there are at most
`2·|Exc| + 4` meeting points, and the exceptional positions are at most `4|X| + 3|U| + 6`.
-/

namespace Hypostructure.Graph.TwoGeodesics

open Hypostructure.Graph.PathChords
open Hypostructure.Graph.WalkIndex
open Hypostructure.Graph.LadderRun
open Hypostructure.Graph.LadderCount

universe u

section Count

variable {V : Type u} {G : SimpleGraph V} [DecidableEq V] {a1 b1 a2 b2 : V}
variable {LengthOK : ℕ → Prop} {Cubic : V → Prop} {w1 : G.Walk a1 b1} {w2 : G.Walk a2 b2}

open Classical in
/-- the exceptional positions of `w₁` -/
noncomputable def excPos1 (Cubic : V → Prop) (w1 : G.Walk a1 b1) (S : Finset V) : Finset ℕ :=
  (Finset.range (w1.length + 1)).filter fun s => ExcS Cubic w1 S s

/-- **A meeting point is next to an off position, or is an end of `w₂`.** -/
theorem meeting_side (H : Geo2 G LengthOK Cubic w1 w2) {t : ℕ} (ht0 : 0 < t)
    (htl : t < w1.length) (hin : w1.getVert t ∈ w2.support) {y : ℕ} (hyl : y ≤ w2.length)
    (hadj : G.Adj (w1.getVert t) (w2.getVert y)) (hyoff : w2.getVert y ∉ w1.support) :
    w1.getVert (t - 1) ∉ w2.support ∨ w1.getVert (t + 1) ∉ w2.support ∨ w1.getVert t = a2 ∨
      w1.getVert t = b2 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hm, hp, hna, hnb⟩ := hcon
  obtain ⟨P0, hP0, hP0l⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.1 hin
  obtain ⟨Pm, hPm, hPml⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.1 hm
  obtain ⟨Pp, hPp, hPpl⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.1 hp
  have i1 := common_iso H (t := t - 1) (t' := t) (p := Pm) (p' := P0) (by omega) (by omega)
    hPml hP0l hPm.symm hP0.symm
  have i2 := common_iso H (t := t) (t' := t + 1) (p := P0) (p' := Pp) (by omega) (by omega)
    hP0l hPpl hP0.symm hPp.symm
  have i3 := common_iso H (t := t - 1) (t' := t + 1) (p := Pm) (p' := Pp) (by omega) (by omega)
    hPml hPpl hPm.symm hPp.symm
  have hP0pos : 0 < P0 := by
    rcases Nat.eq_zero_or_pos P0 with h | h
    · exfalso; apply hna; rw [← hP0, h, SimpleGraph.Walk.getVert_zero]
    · exact h
  have hP0lt : P0 < w2.length := by
    rcases lt_or_eq_of_le hP0l with h | h
    · exact h
    · exfalso; apply hnb; rw [← hP0, h, SimpleGraph.Walk.getVert_length]
  have hyin : w2.getVert y ∈ w2.support := SimpleGraph.Walk.getVert_mem_support _ _
  have hadj' : G.Adj (w2.getVert P0) (w2.getVert y) := by rw [hP0]; exact hadj
  rcases induced_nbrs H.hp2 H.det2 hP0pos hP0lt hyin hadj' with h | h
  · apply hyoff
    have : P0 - 1 = Pm ∨ P0 - 1 = Pp := by omega
    rcases this with e | e
    · rw [h, e, hPm]; exact SimpleGraph.Walk.getVert_mem_support _ _
    · rw [h, e, hPp]; exact SimpleGraph.Walk.getVert_mem_support _ _
  · apply hyoff
    have : P0 + 1 = Pm ∨ P0 + 1 = Pp := by omega
    rcases this with e | e
    · rw [h, e, hPm]; exact SimpleGraph.Walk.getVert_mem_support _ _
    · rw [h, e, hPp]; exact SimpleGraph.Walk.getVert_mem_support _ _

theorem mem_ovDiv {t : ℕ} :
    t ∈ ovDiv w1 w2 ↔ t < w1.length ∧ 0 < t ∧ w1.getVert t ∈ w2.support ∧
      ∃ y, y ≤ w2.length ∧ G.Adj (w1.getVert t) (w2.getVert y) ∧ w2.getVert y ∉ w1.support := by
  simp only [ovDiv, Finset.mem_filter, Finset.mem_range]

/-- **The meeting points are at most `2|Exc| + 4`.** -/
theorem ovDiv_card_le (H : Geo2 G LengthOK Cubic w1 w2) (S : Finset V)
    (hX : ∀ z, ¬ Cubic z → z ∈ S)
    (hU : ∀ z, Cubic z → z ∉ w1.support → z ∉ w2.support → z ∈ S)
    (ha : a2 ∈ S) (hb : b2 ∈ S) :
    (ovDiv w1 w2).card ≤ 2 * (excPos1 Cubic w1 S).card + 4 := by
  classical
  set Exc := excPos1 Cubic w1 S with hExc
  set T0 := ovDiv w1 w2 with hT0
  let com : ℕ → Prop := fun x => w1.getVert x ∈ w2.support
  let R := T0.filter (fun t => ¬ com (t + 1))
  let Lf := T0.filter (fun t => com (t + 1) ∧ ¬ com (t - 1))
  let Sp := T0.filter (fun t => w1.getVert t = a2 ∨ w1.getVert t = b2)
  have hsub : T0 ⊆ R ∪ Lf ∪ Sp := by
    intro t ht
    obtain ⟨htl, ht0, hin, y, hyl, hadj, hyoff⟩ := mem_ovDiv.1 ht
    rcases meeting_side H ht0 htl hin hyl hadj hyoff with h | h | h | h
    · by_cases hc : com (t + 1)
      · simp only [R, Lf, Sp, Finset.mem_union, Finset.mem_filter]
        left; right; exact ⟨ht, hc, h⟩
      · simp only [R, Lf, Sp, Finset.mem_union, Finset.mem_filter]
        left; left; exact ⟨ht, hc⟩
    · simp only [R, Lf, Sp, Finset.mem_union, Finset.mem_filter]
      left; left; exact ⟨ht, h⟩
    · simp only [R, Lf, Sp, Finset.mem_union, Finset.mem_filter]
      right; exact ⟨ht, Or.inl h⟩
    · simp only [R, Lf, Sp, Finset.mem_union, Finset.mem_filter]
      right; exact ⟨ht, Or.inr h⟩
  have hSp : Sp.card ≤ 2 := by
    have : Sp.card ≤ ({a2, b2} : Finset V).card := by
      apply Finset.card_le_card_of_injOn (fun t => w1.getVert t)
      · intro t ht
        have := (Finset.mem_filter.1 (Finset.mem_coe.1 ht)).2
        simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
          Set.mem_singleton_iff]
        exact this
      · intro t1 h1 t2 h2 h
        have m1 := mem_ovDiv.1 (Finset.mem_filter.1 (Finset.mem_coe.1 h1)).1
        have m2 := mem_ovDiv.1 (Finset.mem_filter.1 (Finset.mem_coe.1 h2)).1
        exact getVert_inj H.hp1 (by omega) (by omega) h
    exact le_trans this Finset.card_le_two
  -- right bubbles
  let R' := R.filter (fun t => ∃ t', t < t' ∧ t' ≤ w1.length ∧ com t')
  have hR'' : (R.filter (fun t => ¬ ∃ t', t < t' ∧ t' ≤ w1.length ∧ com t')).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha' b hb'
    simp only [Finset.mem_filter] at ha' hb'
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have m := mem_ovDiv.1 (Finset.mem_filter.1 hb'.1).1
      exact ha'.2 ⟨b, h, by omega, m.2.2.1⟩
    · have m := mem_ovDiv.1 (Finset.mem_filter.1 ha'.1).1
      exact hb'.2 ⟨a, h, by omega, m.2.2.1⟩
  have hR' : R'.card ≤ Exc.card := by
    have hex : ∀ t ∈ R', ∃ g ∈ Exc, t < g ∧ ∀ t2 ∈ R', t < t2 → g < t2 := by
      intro t ht
      simp only [R', R, Finset.mem_filter] at ht
      obtain ⟨⟨htT, hnc⟩, t0, ht0lt, ht0l, ht0c⟩ := ht
      obtain ⟨htl, htpos, hin, -⟩ := mem_ovDiv.1 htT
      let Q := (Finset.range (w1.length + 1)).filter (fun x => t < x ∧ com x)
      have hQ : Q.Nonempty := ⟨t0, by simp only [Q, Finset.mem_filter, Finset.mem_range]; exact ⟨by omega, ht0lt, ht0c⟩⟩
      set t' := Q.min' hQ with ht'
      have ht'mem : t' ∈ Q := Finset.min'_mem Q hQ
      simp only [Q, Finset.mem_filter, Finset.mem_range] at ht'mem
      have hmin : ∀ x, t < x → x ≤ w1.length → com x → t' ≤ x := by
        intro x hx1 hx2 hx3
        exact Finset.min'_le Q x (by simp only [Q, Finset.mem_filter, Finset.mem_range]; exact ⟨by omega, hx1, hx3⟩)
      have hgap : t + 2 ≤ t' := by
        have : t' ≠ t + 1 := fun h => hnc (h ▸ ht'mem.2.2)
        omega
      obtain ⟨P, hP, hPl⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.1 hin
      obtain ⟨P', hP', hP'l⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.1 ht'mem.2.2
      obtain ⟨s, hs1, hs2, hsE⟩ := bubble_exc H S hX hU ha hb hgap (by omega) hPl hP'l hP.symm
        hP'.symm (fun x hx1 hx2 hc => by
          have := hmin x hx1 (by omega) hc
          omega)
      refine ⟨s, ?_, hs1, ?_⟩
      · simp only [hExc, excPos1, Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, hsE⟩
      · intro t2 ht2 hlt
        simp only [R', R, Finset.mem_filter] at ht2
        have m2 := mem_ovDiv.1 ht2.1.1
        have := hmin t2 hlt (by omega) m2.2.2.1
        omega
    choose! g hg using hex
    apply Finset.card_le_card_of_injOn g
    · intro t ht
      exact Finset.mem_coe.2 (hg t (Finset.mem_coe.1 ht)).1
    · intro t1 h1 t2 h2 heq
      have g1 := hg t1 (Finset.mem_coe.1 h1)
      have g2 := hg t2 (Finset.mem_coe.1 h2)
      by_contra hne
      rcases lt_or_gt_of_ne hne with h | h
      · have := g1.2.2 t2 (Finset.mem_coe.1 h2) h
        have := g2.2.1
        omega
      · have := g2.2.2 t1 (Finset.mem_coe.1 h1) h
        have := g1.2.1
        omega
  -- left bubbles
  let Lf' := Lf.filter (fun t => ∃ t'', t'' < t ∧ com t'')
  have hL'' : (Lf.filter (fun t => ¬ ∃ t'', t'' < t ∧ com t'')).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha' b hb'
    simp only [Finset.mem_filter] at ha' hb'
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have m := mem_ovDiv.1 (Finset.mem_filter.1 ha'.1).1
      exact hb'.2 ⟨a, h, m.2.2.1⟩
    · have m := mem_ovDiv.1 (Finset.mem_filter.1 hb'.1).1
      exact ha'.2 ⟨b, h, m.2.2.1⟩
  have hL' : Lf'.card ≤ Exc.card := by
    have hex : ∀ t ∈ Lf', ∃ g ∈ Exc, g < t ∧ ∀ t1 ∈ Lf', t1 < t → t1 < g := by
      intro t ht
      simp only [Lf', Lf, Finset.mem_filter] at ht
      obtain ⟨⟨htT, hc1, hnc⟩, t0, ht0lt, ht0c⟩ := ht
      obtain ⟨htl, htpos, hin, -⟩ := mem_ovDiv.1 htT
      let Q := (Finset.range (w1.length + 1)).filter (fun x => x < t ∧ com x)
      have hQ : Q.Nonempty := ⟨t0, by simp only [Q, Finset.mem_filter, Finset.mem_range]; exact ⟨by omega, ht0lt, ht0c⟩⟩
      set t'' := Q.max' hQ with ht''
      have ht''mem : t'' ∈ Q := Finset.max'_mem Q hQ
      simp only [Q, Finset.mem_filter, Finset.mem_range] at ht''mem
      have hmax : ∀ x, x < t → com x → x ≤ t'' := by
        intro x hx1 hx3
        exact Finset.le_max' Q x (by simp only [Q, Finset.mem_filter, Finset.mem_range]; exact ⟨by omega, hx1, hx3⟩)
      have hgap : t'' + 2 ≤ t := by
        have : t'' ≠ t - 1 := fun h => hnc (h ▸ ht''mem.2.2)
        omega
      obtain ⟨P, hP, hPl⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.1 ht''mem.2.2
      obtain ⟨P', hP', hP'l⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.1 hin
      obtain ⟨s, hs1, hs2, hsE⟩ := bubble_exc H S hX hU ha hb hgap (by omega) hPl hP'l hP.symm
        hP'.symm (fun x hx1 hx2 hc => by
          have := hmax x hx2 hc
          omega)
      refine ⟨s, ?_, hs2, ?_⟩
      · simp only [hExc, excPos1, Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, hsE⟩
      · intro t1 ht1 hlt
        simp only [Lf', Lf, Finset.mem_filter] at ht1
        have m1 := mem_ovDiv.1 ht1.1.1
        have := hmax t1 hlt m1.2.2.1
        omega
    choose! g hg using hex
    apply Finset.card_le_card_of_injOn g
    · intro t ht
      exact Finset.mem_coe.2 (hg t (Finset.mem_coe.1 ht)).1
    · intro t1 h1 t2 h2 heq
      have g1 := hg t1 (Finset.mem_coe.1 h1)
      have g2 := hg t2 (Finset.mem_coe.1 h2)
      by_contra hne
      rcases lt_or_gt_of_ne hne with h | h
      · have := g2.2.2 t1 (Finset.mem_coe.1 h1) h
        have := g1.2.1
        omega
      · have := g1.2.2 t2 (Finset.mem_coe.1 h2) h
        have := g2.2.1
        omega
  have cR : R'.card + (R.filter (fun t => ¬ ∃ t', t < t' ∧ t' ≤ w1.length ∧ com t')).card =
      R.card := Finset.card_filter_add_card_filter_not _
  have cL : Lf'.card + (Lf.filter (fun t => ¬ ∃ t'', t'' < t ∧ com t'')).card = Lf.card :=
    Finset.card_filter_add_card_filter_not _
  have hcard : T0.card ≤ (R ∪ Lf ∪ Sp).card := Finset.card_le_card hsub
  have u1 := Finset.card_union_le (R ∪ Lf) Sp
  have u2 := Finset.card_union_le R Lf
  omega

/-- the hypotheses of the count give those of the pair -/
theorem Geo2.ofCount (H : CountHyp G LengthOK Cubic w1 w2)
    (E1 : ∀ ε ∈ w2.edges, ε ≠ s(a1, b1)) (E2 : ∀ ε ∈ w1.edges, ε ≠ s(a2, b2)) :
    Geo2 G LengthOK Cubic w1 w2 :=
  { stub := H.stub, avoids := H.avoids, ok4 := H.ok4, hp1 := H.hp1, hp2 := H.hp2,
    det1 := H.det1, det2 := H.det2, E1 := E1, E2 := E2 }

/-- **The exceptional positions are at most `4|X| + 3|U| + 6`.** -/
theorem excPos1_card_le (H : CountHyp G LengthOK Cubic w1 w2) (X U : Finset V)
    (hX : ∀ z, ¬ Cubic z → z ∈ X) :
    (excPos1 Cubic w1 (X ∪ U ∪ {a2, b2})).card ≤ 4 * X.card + 3 * U.card + 6 := by
  classical
  let S : Finset V := X ∪ U ∪ {a2, b2}
  let S' : Finset V := S.filter (· ∉ w1.support)
  let B1 : Finset ℕ := (Finset.range (w1.length + 1)).filter fun y => ¬ Cubic (w1.getVert y)
  have hsub : excPos1 Cubic w1 S ⊆ B1 ∪ S'.biUnion (fun s => nbrPos w1 s) := by
    intro s hs
    simp only [excPos1, Finset.mem_filter, Finset.mem_range] at hs
    obtain ⟨hsl, hexc⟩ := hs
    simp only [Finset.mem_union, B1, Finset.mem_filter, Finset.mem_range, Finset.mem_biUnion]
    rcases hexc with h | ⟨z, hz, hzo, hadj⟩
    · left; exact ⟨hsl, h⟩
    · right
      refine ⟨z, ?_, ?_⟩
      · simp only [S', Finset.mem_filter]; exact ⟨hz, hzo⟩
      · simp only [nbrPos, Finset.mem_filter, Finset.mem_range]
        exact ⟨hsl, hadj.symm⟩
  have hB1 : B1.card ≤ X.card := by
    apply Finset.card_le_card_of_injOn (fun y => w1.getVert y)
    · intro y hy
      simp only [B1, Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hy
      exact hX _ hy.2
    · intro y hy y' hy' h
      simp only [B1, Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hy hy'
      exact getVert_inj H.hp1 (by omega) (by omega) h
  have hS' : ∀ s ∈ S', (nbrPos w1 s).card ≤ 3 := by
    intro s hs
    simp only [S', Finset.mem_filter] at hs
    exact nbrPos_le_three H.stub H.hp1 H.hub1 H.ok4 H.match_ hs.2
  have hbi : (S'.biUnion (fun s => nbrPos w1 s)).card ≤ 3 * S'.card := by
    calc (S'.biUnion (fun s => nbrPos w1 s)).card ≤ ∑ s ∈ S', (nbrPos w1 s).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ s ∈ S', 3 := Finset.sum_le_sum hS'
      _ = 3 * S'.card := by simp [mul_comm]
  have hSc : S'.card ≤ X.card + U.card + 2 := by
    calc S'.card ≤ S.card := Finset.card_filter_le _ _
      _ ≤ (X ∪ U).card + ({a2, b2} : Finset V).card := Finset.card_union_le _ _
      _ ≤ X.card + U.card + 2 := by
        have h1 := Finset.card_union_le X U
        have h2 : ({a2, b2} : Finset V).card ≤ 2 := Finset.card_le_two
        omega
  calc (excPos1 Cubic w1 S).card
      ≤ (B1 ∪ S'.biUnion (fun s => nbrPos w1 s)).card := Finset.card_le_card hsub
    _ ≤ B1.card + (S'.biUnion (fun s => nbrPos w1 s)).card := Finset.card_union_le _ _
    _ ≤ 4 * X.card + 3 * U.card + 6 := by omega

/-- **The ladder count with the meeting points absorbed.**  For two geodesic paths (neither
using the other's end edge): `⌊(|w₁| − 1)/24⌋ ≤ 16|X| + 12|U| + 30`, where `X` contains the
non-cubic vertices and `U` the cubic vertices off both paths. -/
theorem ladder_count_geo (H : CountHyp G LengthOK Cubic w1 w2)
    (E1 : ∀ ε ∈ w2.edges, ε ≠ s(a1, b1)) (E2 : ∀ ε ∈ w1.edges, ε ≠ s(a2, b2))
    (X U : Finset V) (hX : ∀ z, ¬ Cubic z → z ∈ X)
    (hU : ∀ z, Cubic z → z ∉ w1.support → z ∉ w2.support → z ∈ U) :
    (w1.length - 1) / 24 ≤ 16 * X.card + 12 * U.card + 30 := by
  classical
  have geo := Geo2.ofCount H E1 E2
  have hS := ovDiv_card_le geo (X ∪ U ∪ {a2, b2})
    (fun z hz => by simp only [Finset.mem_union]; exact Or.inl (Or.inl (hX z hz)))
    (fun z hz n1 n2 => by simp only [Finset.mem_union]; exact Or.inl (Or.inr (hU z hz n1 n2)))
    (by simp) (by simp)
  have hE := excPos1_card_le H X U hX
  have hL := ladder_count H X U hX hU
  omega

end Count

end Hypostructure.Graph.TwoGeodesics
