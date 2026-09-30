import Hypostructure.Graph.WindowPacking
import Hypostructure.Graph.LadderRun

/-!
# Induced windows along a geodesic path; the local packing exchange

Vocabulary-free.  `w : a ⇝ b` is a path of a finite object, shortest among the paths avoiding
the edge `s(a, b)` (`PathChords.GeodesicDetours s(a, b) w`).  Every edge between two vertices
of `w` is then an edge of `w` or `s(a, b)` (`LadderRun.idx_dist_le`), so:

* `seg_window`: the `L` consecutive vertices `w(s), …, w(s + L − 1)` induce a window of order
  `L`, unless they are all of `w` (`s = 0` and `s + L = |w| + 1`);
* `segFamily_packing`, `length_div_le`: the segments starting at `0, L, 2L, …` are pairwise
  disjoint windows, so `⌊|w|/L⌋ ≤ ν_L`; for two such paths with disjoint supports,
  `⌊|w₁|/L⌋ + ⌊|w₂|/L⌋ ≤ ν_L` (`two_length_div_le`);
* `exchange_card_le` (local packing exchange): for a maximum packing `P`, a subfamily `S ⊆ P`
  and a packing `Q` whose members avoid every member of `P ∖ S`, `|Q| ≤ |S|`;
  `exchange_single`: two disjoint windows cannot both avoid every member of `P` but one.
-/

namespace Hypostructure.Graph.WalkWindows

open Hypostructure.Graph.PathChords

universe u

variable {object : FiniteObject.{u}}

/-- The `L` consecutive vertices `w(s), …, w(s + L − 1)` of a walk. -/
def seg {a b : object.Vertex} (w : object.graph.Walk a b) (s L : ℕ) :
    Finset object.Vertex := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  exact (Finset.range L).image fun k => w.getVert (s + k)

theorem mem_seg {a b : object.Vertex} {w : object.graph.Walk a b} {s L : ℕ}
    {v : object.Vertex} : v ∈ seg w s L ↔ ∃ k < L, w.getVert (s + k) = v := by
  unfold seg
  simp [Finset.mem_image, Finset.mem_range]

theorem seg_subset_support {a b : object.Vertex} (w : object.graph.Walk a b) (s L : ℕ)
    {v : object.Vertex} (h : v ∈ seg w s L) : v ∈ w.support := by
  obtain ⟨k, -, rfl⟩ := mem_seg.1 h
  exact SimpleGraph.Walk.getVert_mem_support _ _

theorem getVert_mem_seg {a b : object.Vertex} (w : object.graph.Walk a b) {s L k : ℕ}
    (hk : k < L) : w.getVert (s + k) ∈ seg w s L :=
  mem_seg.2 ⟨k, hk, rfl⟩

theorem seg_nonempty {a b : object.Vertex} (w : object.graph.Walk a b) (s : ℕ) {L : ℕ}
    (hL : 0 < L) : (seg w s L).Nonempty :=
  ⟨_, getVert_mem_seg w (k := 0) hL⟩

/-- Two positions of a path carrying the same vertex are equal. -/
theorem idx_eq {a b : object.Vertex} {w : object.graph.Walk a b} (hp : w.IsPath) {i j : ℕ}
    (hi : i ≤ w.length) (hj : j ≤ w.length) (h : w.getVert i = w.getVert j) : i = j :=
  LadderRun.getVert_inj hp hi hj h

/-- **A segment that is not the whole path induces a window.** -/
theorem seg_window {a b : object.Vertex} {w : object.graph.Walk a b} (hp : w.IsPath)
    (det : GeodesicDetours s(a, b) w) {s L : ℕ} (hs : s + L ≤ w.length + 1)
    (hend : ¬ (s = 0 ∧ s + L = w.length + 1)) :
    object.InducesWindow L (seg w s L) := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  have inj : ∀ i j, i < L → j < L → w.getVert (s + i) = w.getVert (s + j) → i = j := by
    intro i j hi hj h
    have := idx_eq hp (by omega) (by omega) h
    omega
  have noPort : ∀ i j, i < L → j < L →
      s(w.getVert (s + i), w.getVert (s + j)) ≠ s(a, b) := by
    intro i j hi hj h
    rw [Sym2.eq_iff] at h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have e1 := idx_eq hp (by omega) (Nat.zero_le _)
        (h1.trans (SimpleGraph.Walk.getVert_zero w).symm)
      have e2 := idx_eq hp (by omega) le_rfl
        (h2.trans (SimpleGraph.Walk.getVert_length w).symm)
      exact hend ⟨by omega, by omega⟩
    · have e1 := idx_eq hp (by omega) le_rfl
        (h1.trans (SimpleGraph.Walk.getVert_length w).symm)
      have e2 := idx_eq hp (by omega) (Nat.zero_le _)
        (h2.trans (SimpleGraph.Walk.getVert_zero w).symm)
      exact hend ⟨by omega, by omega⟩
  refine ⟨⟨⟨⟨fun i => ⟨w.getVert (s + i.1), getVert_mem_seg w i.2⟩, ?_⟩, ?_⟩⟩, ?_⟩
  · intro i j h
    exact Fin.ext (inj i.1 j.1 i.2 j.2 (congrArg Subtype.val h))
  · intro i j
    change object.graph.Adj (w.getVert (s + i.1)) (w.getVert (s + j.1)) ↔
      (SimpleGraph.pathGraph L).Adj i j
    rw [SimpleGraph.pathGraph_adj]
    constructor
    · intro hadj
      have hne : i.1 ≠ j.1 := by
        intro e
        apply hadj.ne
        rw [e]
      let r : object.graph.Walk (w.getVert (s + i.1)) (w.getVert (s + j.1)) :=
        SimpleGraph.Walk.cons hadj .nil
      have hr : ∀ ε ∈ r.edges, ε ≠ s(a, b) := by
        intro ε hε
        simp only [r, SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil, List.mem_cons,
          List.not_mem_nil, or_false] at hε
        subst hε
        exact noPort i.1 j.1 i.2 j.2
      have hd := LadderRun.idx_dist_le det (by omega) (by omega) r hr
      simp only [r, SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_nil] at hd
      omega
    · rintro (h | h)
      · have hlt : s + i.1 < w.length := by omega
        have := w.adj_getVert_succ hlt
        rw [show s + i.1 + 1 = s + j.1 by omega] at this
        exact this
      · have hlt : s + j.1 < w.length := by omega
        have := w.adj_getVert_succ hlt
        rw [show s + j.1 + 1 = s + i.1 by omega] at this
        exact this.symm
  · unfold seg
    rw [Finset.card_image_of_injOn, Finset.card_range]
    intro i hi j hj h
    exact inj i j (Finset.mem_range.1 hi) (Finset.mem_range.1 hj) h

/-- Segments `L·k`, `k < ⌊|w|/L⌋`, fit strictly inside the path. -/
theorem block_le {L len k : ℕ} (hk : k < len / L) : L * k + L ≤ len := by
  have h1 : L * (k + 1) ≤ L * (len / L) := Nat.mul_le_mul_left _ hk
  have h2 : L * (len / L) ≤ len := Nat.mul_div_le len L
  rw [Nat.mul_succ] at h1
  omega

theorem block_eq {L k k' i j : ℕ} (hi : i < L) (hj : j < L) (h : L * k + i = L * k' + j) :
    k = k' := by
  rcases lt_trichotomy k k' with hk | hk | hk
  · have : L * (k + 1) ≤ L * k' := Nat.mul_le_mul_left _ hk
    rw [Nat.mul_succ] at this
    omega
  · exact hk
  · have : L * (k' + 1) ≤ L * k := Nat.mul_le_mul_left _ hk
    rw [Nat.mul_succ] at this
    omega

/-- The segments starting at `0, L, 2L, …` that fit in the path. -/
def segFamily {a b : object.Vertex} (w : object.graph.Walk a b) (L : ℕ) :
    Finset (Finset object.Vertex) := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  exact (Finset.range (w.length / L)).image fun k => seg w (L * k) L

theorem mem_segFamily {a b : object.Vertex} {w : object.graph.Walk a b} {L : ℕ}
    {X : Finset object.Vertex} :
    X ∈ segFamily w L ↔ ∃ k < w.length / L, seg w (L * k) L = X := by
  unfold segFamily
  simp [Finset.mem_image, Finset.mem_range]

theorem segFamily_subset_support {a b : object.Vertex} {w : object.graph.Walk a b} {L : ℕ}
    {X : Finset object.Vertex} (hX : X ∈ segFamily w L) {v : object.Vertex} (hv : v ∈ X) :
    v ∈ w.support := by
  obtain ⟨k, -, rfl⟩ := mem_segFamily.1 hX
  exact seg_subset_support w _ _ hv

/-- Distinct blocks are disjoint. -/
theorem seg_block_disjoint {a b : object.Vertex} {w : object.graph.Walk a b} (hp : w.IsPath)
    {L k k' : ℕ} (hk : k < w.length / L) (hk' : k' < w.length / L) (ne : k ≠ k') :
    Disjoint (seg w (L * k) L) (seg w (L * k') L) := by
  rw [Finset.disjoint_left]
  intro v hv hv'
  obtain ⟨i, hi, rfl⟩ := mem_seg.1 hv
  obtain ⟨j, hj, e⟩ := mem_seg.1 hv'
  have b1 := block_le hk
  have b2 := block_le hk'
  have := idx_eq hp (by omega) (by omega) e.symm
  exact ne (block_eq hi hj this)

/-- **The blocks of a geodesic path form a window packing of size `⌊|w|/L⌋`.** -/
theorem segFamily_packing {a b : object.Vertex} {w : object.graph.Walk a b} (hp : w.IsPath)
    (det : GeodesicDetours s(a, b) w) {L : ℕ} (hL : 0 < L) :
    object.IsWindowPacking L (segFamily w L) ∧ (segFamily w L).card = w.length / L := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro X hX
    obtain ⟨k, hk, rfl⟩ := mem_segFamily.1 hX
    have := block_le hk
    exact seg_window hp det (by omega) (by omega)
  · intro X hX Y hY ne
    obtain ⟨k, hk, rfl⟩ := mem_segFamily.1 hX
    obtain ⟨k', hk', rfl⟩ := mem_segFamily.1 hY
    exact seg_block_disjoint hp hk hk' (fun e => ne (by rw [e]))
  · letI : DecidableEq object.Vertex := object.vertices.decEq
    unfold segFamily
    rw [Finset.card_image_of_injOn, Finset.card_range]
    intro k hk k' hk' e
    by_contra ne
    have d := seg_block_disjoint hp (Finset.mem_range.1 hk) (Finset.mem_range.1 hk') ne
    have e' : seg w (L * k) L = seg w (L * k') L := e
    rw [e'] at d
    obtain ⟨v, hv⟩ := seg_nonempty w (L * k') hL
    exact Finset.disjoint_left.1 d hv hv

/-- **`⌊|w|/L⌋ ≤ ν_L`.** -/
theorem length_div_le {a b : object.Vertex} {w : object.graph.Walk a b} (hp : w.IsPath)
    (det : GeodesicDetours s(a, b) w) {L : ℕ} (hL : 0 < L) :
    w.length / L ≤ object.windowPackingNumber L := by
  have h := segFamily_packing hp det hL
  rw [← h.2]
  exact object.card_le_windowPackingNumber h.1

/-- **Two geodesic paths with disjoint supports: `⌊|w₁|/L⌋ + ⌊|w₂|/L⌋ ≤ ν_L`.** -/
theorem two_length_div_le {a1 b1 a2 b2 : object.Vertex} {w1 : object.graph.Walk a1 b1}
    {w2 : object.graph.Walk a2 b2} (hp1 : w1.IsPath) (det1 : GeodesicDetours s(a1, b1) w1)
    (hp2 : w2.IsPath) (det2 : GeodesicDetours s(a2, b2) w2)
    (disj : ∀ v, v ∈ w1.support → v ∉ w2.support) {L : ℕ} (hL : 0 < L) :
    w1.length / L + w2.length / L ≤ object.windowPackingNumber L := by
  classical
  have h1 := segFamily_packing hp1 det1 hL
  have h2 := segFamily_packing hp2 det2 hL
  have cross : ∀ X ∈ segFamily w1 L, ∀ Y ∈ segFamily w2 L, Disjoint X Y := by
    intro X hX Y hY
    rw [Finset.disjoint_left]
    intro v hv hv'
    exact disj v (segFamily_subset_support hX hv) (segFamily_subset_support hY hv')
  have famDisj : Disjoint (segFamily w1 L) (segFamily w2 L) := by
    rw [Finset.disjoint_left]
    intro X hX hX'
    obtain ⟨k, -, rfl⟩ := mem_segFamily.1 hX
    obtain ⟨v, hv⟩ := seg_nonempty w1 (L * k) hL
    exact Finset.disjoint_left.1 (cross _ hX _ hX') hv hv
  have valid : object.IsWindowPacking L (segFamily w1 L ∪ segFamily w2 L) := by
    refine ⟨?_, ?_⟩
    · intro X hX
      rcases Finset.mem_union.1 hX with h | h
      · exact h1.1.1 X h
      · exact h2.1.1 X h
    · intro X hX Y hY ne
      rcases Finset.mem_union.1 hX with hX | hX <;> rcases Finset.mem_union.1 hY with hY | hY
      · exact h1.1.2 X hX Y hY ne
      · exact cross X hX Y hY
      · exact (cross Y hY X hX).symm
      · exact h2.1.2 X hX Y hY ne
  have := object.card_le_windowPackingNumber valid
  rw [Finset.card_union_of_disjoint famDisj, h1.2, h2.2] at this
  exact this

/-- **Local packing exchange.**  For a maximum packing `P`, a subfamily `S ⊆ P`, and a packing
`Q` whose members avoid every member of `P` outside `S`: `|Q| ≤ |S|` (`(P ∖ S) ∪ Q` is a
packing).  Generic packing exchange. -/
theorem exchange_card_le {L : ℕ} (hL : 0 < L) {P S Q : Finset (Finset object.Vertex)}
    (valid : object.IsWindowPacking L P) (attains : P.card = object.windowPackingNumber L)
    (sub : S ⊆ P) (qValid : object.IsWindowPacking L Q)
    (avoid' : ∀ q ∈ Q, ∀ p ∈ P, p ∉ S → Disjoint q p) : Q.card ≤ S.card := by
  classical
  have avoid : ∀ q ∈ Q, ∀ p ∈ P \ S, Disjoint q p := fun q hq p hp =>
    avoid' q hq p (Finset.mem_sdiff.1 hp).1 (Finset.mem_sdiff.1 hp).2
  have famDisj : Disjoint (P \ S) Q := by
    rw [Finset.disjoint_left]
    intro X hX hQ
    obtain ⟨v, hv⟩ := object.nonempty_of_inducesWindow hL (qValid.1 X hQ)
    exact Finset.disjoint_left.1 (avoid X hQ X hX) hv hv
  have union : object.IsWindowPacking L ((P \ S) ∪ Q) := by
    refine ⟨?_, ?_⟩
    · intro X hX
      rcases Finset.mem_union.1 hX with h | h
      · exact valid.1 X (Finset.mem_sdiff.1 h).1
      · exact qValid.1 X h
    · intro X hX Y hY ne
      rcases Finset.mem_union.1 hX with hX | hX <;> rcases Finset.mem_union.1 hY with hY | hY
      · exact valid.2 X (Finset.mem_sdiff.1 hX).1 Y (Finset.mem_sdiff.1 hY).1 ne
      · exact (avoid Y hY X hX).symm
      · exact avoid X hX Y hY
      · exact qValid.2 X hX Y hY ne
  have bound := object.card_le_windowPackingNumber union
  rw [Finset.card_union_of_disjoint famDisj] at bound
  have split := Finset.card_sdiff_add_card_eq_card sub
  omega

/-- **Exchange at one member.**  Two disjoint windows cannot both avoid every member of a
maximum packing `P` other than one member `X`. -/
theorem exchange_single {L : ℕ} (hL : 0 < L) {P : Finset (Finset object.Vertex)}
    (valid : object.IsWindowPacking L P) (attains : P.card = object.windowPackingNumber L)
    {X : Finset object.Vertex} (hX : X ∈ P) {q1 q2 : Finset object.Vertex}
    (win1 : object.InducesWindow L q1) (win2 : object.InducesWindow L q2)
    (d : Disjoint q1 q2) (a1 : ∀ p ∈ P, p ≠ X → Disjoint q1 p)
    (a2 : ∀ p ∈ P, p ≠ X → Disjoint q2 p) : False := by
  classical
  have ne : q1 ≠ q2 := by
    intro e
    obtain ⟨v, hv⟩ := object.nonempty_of_inducesWindow hL win1
    exact Finset.disjoint_left.1 d hv (e ▸ hv)
  have qValid : object.IsWindowPacking L {q1, q2} := by
    refine ⟨?_, ?_⟩
    · intro q hq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with rfl | rfl
      · exact win1
      · exact win2
    · intro l hl r hr lr
      simp only [Finset.mem_insert, Finset.mem_singleton] at hl hr
      rcases hl with rfl | rfl <;> rcases hr with rfl | rfl
      · exact absurd rfl lr
      · exact d
      · exact d.symm
      · exact absurd rfl lr
  have avoid : ∀ q ∈ ({q1, q2} : Finset (Finset object.Vertex)), ∀ p ∈ P, p ∉ ({X} : Finset (Finset object.Vertex)) →
      Disjoint q p := by
    intro q hq p pP pX
    have pX' : p ≠ X := fun e => pX (Finset.mem_singleton.2 e)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl
    · exact a1 p pP pX'
    · exact a2 p pP pX'
  have := exchange_card_le hL valid attains (Finset.singleton_subset_iff.2 hX) qValid avoid
  rw [Finset.card_pair ne, Finset.card_singleton] at this
  omega

end Hypostructure.Graph.WalkWindows
