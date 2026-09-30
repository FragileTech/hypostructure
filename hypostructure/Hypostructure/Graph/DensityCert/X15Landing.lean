import Hypostructure.Graph.DensityCert.Basic
import Hypostructure.Graph.DensityCert.X15LandingData

/-!
# How a copy of `X15` lands on an induced 13-vertex path

Let `X` be a copy of `X15` in `G` (vertex set `X`, induced) and `p₀ … p₁₂` an
induced path of `G` disjoint from `X`.  Suppose the only vertices of `X` with a
neighbour on the path are the images of the three degree-2 vertices `4, 6, 9`
of `X15`, each with at most one such neighbour, that `G[X ∪ p]` has no cycle of
length 4, 8, 16 or 32, and that `X ∪ p` does not contain two vertex-disjoint
induced 13-vertex paths.  Then:

* the three exit vertices are not all adjacent to the path;
* two exit vertices adjacent to `p i` and `p j` have `|i − j| ≥ 10`.

Moreover each exit vertex is the end of an induced 11-vertex path of `X15`.
All three facts are finite computations on `X15` and the path, checked by
`native_decide` and transported along the embedding.
-/

namespace Hypostructure.Graph.DensityCert

/-- The three degree-2 vertices of `X15`. -/
def x15Exits : List ℕ := [4, 6, 9]

/-- `S` is the vertex set of an induced path on 13 vertices of `G`. -/
def IsInducedThirteen {V : Type*} (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∃ l : List V, IsIndPath G l ∧ l.length = 13 ∧ ∀ x, x ∈ S ↔ x ∈ l


namespace X15Land

theorem x15_n : CG.x15.n = 15 := by decide

/-! ### The glued graph `H(c₄, c₆, c₉)` on `0 … 27`

Vertices `0 … 14` are `X15`, `15 + k` is `p k`; the exit `a ∈ {4, 6, 9}` is
joined to `p (c_a)` (no edge when `c_a = 13`). -/

/-- Edge between the `X15` vertex `u` and `p k`. -/
def hX (c4 c6 c9 u k : ℕ) : Bool :=
  (u == 4 && c4 == k) || (u == 6 && c6 == k) || (u == 9 && c9 == k)

/-- Adjacency of the glued graph. -/
def hA (c4 c6 c9 u v : ℕ) : Bool :=
  if u < 15 then (if v < 15 then CG.x15.A u v else hX c4 c6 c9 u (v - 15))
  else if v < 15 then hX c4 c6 c9 v (u - 15) else (u + 1 == v || v + 1 == u)

/-- Checker: `w` is a cycle of forbidden length of the glued graph. -/
def chkCyc (c4 c6 c9 : ℕ) (w : List ℕ) : Bool :=
  decide w.Nodup && w.all (· < 28) && decide (forbiddenLen w.length) &&
    (List.range (w.length - 1)).all (fun i => hA c4 c6 c9 (w.getD i 0) (w.getD (i + 1) 0)) &&
    hA c4 c6 c9 (w.getD (w.length - 1) 0) (w.getD 0 0)

/-- Checker: `w` is an induced 13-vertex path of the glued graph. -/
def chkPath (c4 c6 c9 : ℕ) (w : List ℕ) : Bool :=
  decide w.Nodup && w.all (· < 28) && w.length == 13 &&
    (List.range 13).all fun i => (List.range 13).all fun j =>
      hA c4 c6 c9 (w.getD i 0) (w.getD j 0) == (i + 1 == j || j + 1 == i)

/-- A witness: a forbidden cycle, or two disjoint induced 13-vertex paths. -/
inductive Wit
  | cyc (l : List ℕ)
  | pack (l₁ l₂ : List ℕ)

/-- Checker for a witness. -/
def chkWit (c4 c6 c9 : ℕ) : Wit → Bool
  | .cyc l => chkCyc c4 c6 c9 l
  | .pack l₁ l₂ => chkPath c4 c6 c9 l₁ && chkPath c4 c6 c9 l₂ && l₁.all fun x => !l₂.contains x

/-- Decode one line of `x15LandData`. -/
def parseEntry (s : String) : ℕ × ℕ × ℕ × Wit :=
  let cs := s.toList
  let ns := (cs.drop 4).map fun ch => ch.toNat - 48
  let d := fun i => (cs.getD i '0').toNat - 48
  (d 0, d 1, d 2, if cs.getD 3 'C' == 'C' then .cyc ns else .pack (ns.take 13) (ns.drop 13))

/-- The witness table. -/
def table : List (ℕ × ℕ × ℕ × Wit) := (x15LandData.splitOn "\n").map parseEntry

/-- Some witness of the table (keyed by the configuration or by one of its
two-exit sub-configurations) is valid for the configuration. -/
def good (c4 c6 c9 : ℕ) : Bool :=
  table.any fun t => (t.1 == c4 || t.1 == 13) && (t.2.1 == c6 || t.2.1 == 13) &&
    (t.2.2.1 == c9 || t.2.2.1 == 13) && chkWit c4 c6 c9 t.2.2.2

/-- The configurations to be excluded. -/
def Bad (c4 c6 c9 : ℕ) : Prop :=
  (c4 < 13 ∧ c6 < 13 ∧ c9 < 13) ∨ (c4 < 13 ∧ c6 < 13 ∧ Nat.dist c4 c6 < 10) ∨
    (c4 < 13 ∧ c9 < 13 ∧ Nat.dist c4 c9 < 10) ∨ (c6 < 13 ∧ c9 < 13 ∧ Nat.dist c6 c9 < 10)

instance (c4 c6 c9 : ℕ) : Decidable (Bad c4 c6 c9) := by unfold Bad; infer_instance

/-- The certificate: every bad configuration has a valid witness. -/
theorem cert : ∀ c4 < 14, ∀ c6 < 14, ∀ c9 < 14, Bad c4 c6 c9 → good c4 c6 c9 = true := by
  native_decide

/-! ### Soundness of the checkers -/

theorem getD_eq {w : List ℕ} {i : ℕ} (h : i < w.length) : w.getD i 0 = w[i] := by
  simp [List.getD_eq_getElem?_getD, h]

section Sound

variable {V : Type*} {G : SimpleGraph V} {F : ℕ → V} {c4 c6 c9 : ℕ}

theorem chkCyc_sound
    (hF : ∀ u v, u < 28 → v < 28 → (G.Adj (F u) (F v) ↔ hA c4 c6 c9 u v = true))
    (hinj : ∀ u v, u < 28 → v < 28 → F u = F v → u = v) {w : List ℕ}
    (h : chkCyc c4 c6 c9 w = true) :
    (∀ x ∈ w, x < 28) ∧ IsCycleList G (w.map F) ∧ forbiddenLen (w.map F).length := by
  simp only [chkCyc, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at h
  obtain ⟨⟨⟨⟨hnd, hlt⟩, hfl⟩, hadj⟩, hlast⟩ := h
  have hlen : 3 ≤ w.length := by unfold forbiddenLen at hfl; omega
  refine ⟨hlt, ⟨hnd.map_on fun x hx y hy hxy => hinj x y (hlt x hx) (hlt y hy) hxy,
    by simpa using hlen, fun i hi => ?_, fun _ => ?_⟩, by simpa using hfl⟩
  · simp only [List.length_map] at hi
    simp only [List.getElem_map]
    have := hadj i (by omega)
    rw [getD_eq (by omega), getD_eq (by omega)] at this
    exact (hF _ _ (hlt _ (List.getElem_mem _)) (hlt _ (List.getElem_mem _))).2 this
  · simp only [List.length_map, List.getElem_map]
    rw [getD_eq (by omega), getD_eq (by omega)] at hlast
    exact (hF _ _ (hlt _ (List.getElem_mem _)) (hlt _ (List.getElem_mem _))).2 hlast

theorem chkPath_sound
    (hF : ∀ u v, u < 28 → v < 28 → (G.Adj (F u) (F v) ↔ hA c4 c6 c9 u v = true))
    (hinj : ∀ u v, u < 28 → v < 28 → F u = F v → u = v) {w : List ℕ}
    (h : chkPath c4 c6 c9 w = true) :
    (∀ x ∈ w, x < 28) ∧ IsIndPath G (w.map F) ∧ (w.map F).length = 13 := by
  simp only [chkPath, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range, beq_iff_eq] at h
  obtain ⟨⟨⟨hnd, hlt⟩, hlen⟩, hadj⟩ := h
  refine ⟨hlt, ⟨hnd.map_on fun x hx y hy hxy => hinj x y (hlt x hx) (hlt y hy) hxy,
    fun i j hi hj => ?_⟩, by simpa using hlen⟩
  simp only [List.length_map] at hi hj
  simp only [List.getElem_map]
  have := hadj i (by omega) j (by omega)
  rw [getD_eq (by omega), getD_eq (by omega)] at this
  rw [hF _ _ (hlt _ (List.getElem_mem _)) (hlt _ (List.getElem_mem _)), this]
  simp

end Sound

/-! ### Induced 11-vertex arms of the exits -/

/-- An induced 11-vertex path of `X15` ending at the exit `a`. -/
def arm (a : ℕ) : List ℕ :=
  if a = 4 then [0, 5, 9, 3, 12, 2, 13, 6, 1, 10, 4]
  else if a = 6 then [7, 2, 12, 3, 9, 5, 11, 4, 10, 1, 6]
  else [2, 13, 6, 1, 10, 4, 11, 0, 8, 3, 9]

/-- The arm as a map `Fin 11 → Fin 15`. -/
def armF (a : ℕ) (i : Fin 11) : Fin CG.x15.n :=
  ⟨(arm a).getD i.1 0 % CG.x15.n, Nat.mod_lt _ (by rw [x15_n]; omega)⟩

theorem arm_ok : ∀ a : Fin CG.x15.n, a.1 ∈ x15Exits →
    Function.Injective (armF a.1) ∧
      (∀ i j, CG.x15.graph.Adj (armF a.1 i) (armF a.1 j) ↔ i.1 + 1 = j.1 ∨ j.1 + 1 = i.1) ∧
      armF a.1 ⟨10, by omega⟩ = a := by
  native_decide

theorem degIn_eq {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj] (W : Finset V) (v : V) :
    degIn G W v = (W.filter fun w => G.Adj v w).card := by
  unfold degIn
  congr 1
  exact Finset.filter_congr_decidable _ _ _

theorem deg_ok : ∀ a : Fin CG.x15.n,
    (a.1 ∈ x15Exits → (Finset.univ.filter fun w => CG.x15.graph.Adj a w).card = 2) ∧
      (a.1 ∉ x15Exits → (Finset.univ.filter fun w => CG.x15.graph.Adj a w).card = 3) := by
  native_decide

/-- Two distinct exits landing at positions `i, j` with `|i − j| < 10` give a
bad configuration. -/
theorem pair_bad {c4 c6 c9 x y i j : ℕ} (hx : x = 4 ∨ x = 6 ∨ x = 9)
    (hy : y = 4 ∨ y = 6 ∨ y = 9) (hxy : x ≠ y) (hi : i < 13) (hj : j < 13)
    (cx : (if x = 4 then c4 else if x = 6 then c6 else c9) = i)
    (cy : (if y = 4 then c4 else if y = 6 then c6 else c9) = j)
    (hd : ¬ 10 ≤ Nat.dist i j) : Bad c4 c6 c9 := by
  unfold Bad
  unfold Nat.dist at hd
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
    simp only [if_true, if_false, show (6 : ℕ) ≠ 4 by decide, show (9 : ℕ) ≠ 4 by decide,
      show (9 : ℕ) ≠ 6 by decide] at cx cy <;> subst cx cy <;> first | omega | (unfold Nat.dist; omega)

end X15Land

open X15Land in
theorem x15_exit_landings {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (X : Finset V) (e : CG.x15.graph ↪g G) (he : ∀ v, v ∈ X ↔ ∃ i, e i = v)
    (p : Fin 13 → V) (hp : Function.Injective p)
    (hpind : ∀ i j, G.Adj (p i) (p j) ↔ i.1 + 1 = j.1 ∨ j.1 + 1 = i.1)
    (hdisj : ∀ k, p k ∉ X)
    (hexit : ∀ i : Fin CG.x15.n, ∀ k, G.Adj (e i) (p k) → i.1 ∈ x15Exits)
    (hone : ∀ i : Fin CG.x15.n, ∀ k k', G.Adj (e i) (p k) → G.Adj (e i) (p k') → k = k')
    (hcyc : ∀ l : List V, (∀ x ∈ l, x ∈ X ∨ ∃ k, p k = x) → IsCycleList G l →
      ¬ forbiddenLen l.length)
    (hpack : ∀ S T : Finset V, Disjoint S T →
      (∀ x ∈ S, x ∈ X ∨ ∃ k, p k = x) → (∀ x ∈ T, x ∈ X ∨ ∃ k, p k = x) →
      IsInducedThirteen G S → IsInducedThirteen G T → False) :
    (∀ i j k : Fin 13, ∀ a b c : Fin CG.x15.n, a ≠ b → a ≠ c → b ≠ c →
      G.Adj (e a) (p i) → G.Adj (e b) (p j) → G.Adj (e c) (p k) → False) ∧
    (∀ a b : Fin CG.x15.n, a ≠ b → ∀ i j : Fin 13,
      G.Adj (e a) (p i) → G.Adj (e b) (p j) → 10 ≤ Nat.dist i.1 j.1) := by
  classical
  have hn := x15_n
  obtain ⟨F, hFe, hFp⟩ : ∃ F : ℕ → V,
      (∀ (u : ℕ) (h : u < 15), F u = e ⟨u, lt_of_lt_of_eq h hn.symm⟩) ∧
      ∀ (v : ℕ) (h1 : 15 ≤ v) (h2 : v < 28), F v = p ⟨v - 15, by omega⟩ := by
    refine ⟨fun u => if h : u < 15 then e ⟨u, lt_of_lt_of_eq h hn.symm⟩
      else if h2 : u - 15 < 13 then p ⟨u - 15, h2⟩ else p 0, fun u h => ?_, fun v h1 h2 => ?_⟩
    · simp only [dif_pos h]
    · simp only [dif_neg (show ¬ v < 15 by omega), dif_pos (show v - 15 < 13 by omega)]
  have hFa : ∀ a : Fin CG.x15.n, F a.1 = e a := by
    intro a; rw [hFe a.1 (lt_of_lt_of_eq a.2 hn)]
  -- the configuration read off from `G`
  obtain ⟨cf, hcf, hcf13⟩ : ∃ cf : ℕ → ℕ,
      (∀ a : Fin CG.x15.n, ∀ k : Fin 13, G.Adj (e a) (p k) ↔ cf a.1 = k.1) ∧ ∀ u, cf u ≤ 13 := by
    refine ⟨fun u =>
      if h : ∃ k : Fin 13, G.Adj (F u) (p k) then (Classical.choose h).1 else 13, ?_, ?_⟩
    intro a k
    have hex : (∃ k : Fin 13, G.Adj (F a.1) (p k)) ↔ ∃ k : Fin 13, G.Adj (e a) (p k) := by
      rw [hFa]
    constructor
    · intro hk
      have h : ∃ k : Fin 13, G.Adj (F a.1) (p k) := hex.2 ⟨k, hk⟩
      have hs : G.Adj (e a) (p (Classical.choose h)) := by
        have := Classical.choose_spec h
        generalize Classical.choose h = k0 at this ⊢
        rwa [hFa] at this
      simp only [dif_pos h]
      rw [hone a _ _ hs hk]
    · intro hk
      by_cases h : ∃ k : Fin 13, G.Adj (F a.1) (p k)
      · simp only [dif_pos h] at hk
        have := Classical.choose_spec h
        generalize Classical.choose h = k0 at this hk
        rwa [hFa, Fin.ext hk] at this
      · simp only [dif_neg h] at hk
        omega
    intro u
    by_cases h : ∃ k : Fin 13, G.Adj (F u) (p k)
    · simp only [dif_pos h]; omega
    · simp only [dif_neg h]; omega
  have hmix : ∀ (u : ℕ) (hu : u < 15) (k : Fin 13),
      G.Adj (F u) (p k) ↔ hX (cf 4) (cf 6) (cf 9) u k.1 = true := by
    intro u hu k
    have h1 := hcf ⟨u, lt_of_lt_of_eq hu hn.symm⟩ k
    rw [← hFe u hu] at h1
    rw [h1]
    rcases (show u = 4 ∨ u = 6 ∨ u = 9 ∨ (u ≠ 4 ∧ u ≠ 6 ∧ u ≠ 9) by omega) with
      rfl | rfl | rfl | ⟨h4, h6, h9⟩
    · simp [hX]
    · simp [hX]
    · simp [hX]
    · have hno : ¬ G.Adj (F u) (p k) := by
        intro hadj
        rw [hFe u hu] at hadj
        have := hexit _ _ hadj
        simp [x15Exits] at this
        omega
      rw [← h1]
      simp [hX, h4, h6, h9, hno]
  have hFadj : ∀ u v, u < 28 → v < 28 →
      (G.Adj (F u) (F v) ↔ hA (cf 4) (cf 6) (cf 9) u v = true) := by
    intro u v hu hv
    by_cases hu' : u < 15 <;> by_cases hv' : v < 15
    · rw [hFe u hu', hFe v hv', e.map_adj_iff, CG.graph_adj]
      simp only [hA, if_pos hu', if_pos hv']
    · rw [hFp v (by omega) hv, hmix u hu']
      simp only [hA, if_pos hu', if_neg hv']
    · rw [hFp u (by omega) hu, G.adj_comm, hmix v hv']
      simp only [hA, if_neg hu', if_pos hv']
    · rw [hFp u (by omega) hu, hFp v (by omega) hv, hpind]
      simp only [hA, if_neg hu', if_neg hv', Bool.or_eq_true, beq_iff_eq]
      omega
  have hinj : ∀ u v, u < 28 → v < 28 → F u = F v → u = v := by
    intro u v hu hv huv
    by_cases hu' : u < 15 <;> by_cases hv' : v < 15
    · rw [hFe u hu', hFe v hv'] at huv
      simpa using e.injective huv
    · rw [hFe u hu', hFp v (by omega) hv] at huv
      exact absurd ((he _).2 ⟨_, huv⟩) (hdisj _)
    · rw [hFp u (by omega) hu, hFe v hv'] at huv
      exact absurd ((he _).2 ⟨_, huv.symm⟩) (hdisj _)
    · rw [hFp u (by omega) hu, hFp v (by omega) hv] at huv
      have := congrArg Fin.val (hp huv)
      simp only at this
      omega
  have hmem : ∀ u, u < 28 → F u ∈ X ∨ ∃ k, p k = F u := by
    intro u hu
    by_cases hu' : u < 15
    · exact Or.inl ((he _).2 ⟨_, (hFe u hu').symm⟩)
    · exact Or.inr ⟨_, (hFp u (by omega) hu).symm⟩
  have hmemL : ∀ l : List ℕ, (∀ x ∈ l, x < 28) →
      ∀ x ∈ l.map F, x ∈ X ∨ ∃ k, p k = x := by
    intro l hl x hx
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hx
    exact hmem u (hl u hu)
  have noGood : good (cf 4) (cf 6) (cf 9) = true → False := by
    intro h
    unfold good at h
    rw [List.any_eq_true] at h
    obtain ⟨t, -, ht⟩ := h
    simp only [Bool.and_eq_true] at ht
    have hw := ht.2
    generalize t.2.2.2 = w at hw
    cases w with
    | cyc l =>
      obtain ⟨hl, hc, hfl⟩ := chkCyc_sound hFadj hinj hw
      exact hcyc _ (hmemL l hl) hc hfl
    | pack l₁ l₂ =>
      simp only [chkWit, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at hw
      obtain ⟨⟨h1, h2⟩, hd⟩ := hw
      obtain ⟨hl1, hp1, hlen1⟩ := chkPath_sound hFadj hinj h1
      obtain ⟨hl2, hp2, hlen2⟩ := chkPath_sound hFadj hinj h2
      refine hpack (l₁.map F).toFinset (l₂.map F).toFinset ?_
        (fun x hx => hmemL l₁ hl1 x (List.mem_toFinset.1 hx))
        (fun x hx => hmemL l₂ hl2 x (List.mem_toFinset.1 hx))
        ⟨_, hp1, hlen1, fun x => List.mem_toFinset⟩ ⟨_, hp2, hlen2, fun x => List.mem_toFinset⟩
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      obtain ⟨u, hu, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hx1)
      obtain ⟨v, hv, hvu⟩ := List.mem_map.1 (List.mem_toFinset.1 hx2)
      have := hinj v u (hl2 v hv) (hl1 u hu) hvu
      subst this
      have h' := hd v hu
      simp [hv] at h'
  have hBad : Bad (cf 4) (cf 6) (cf 9) → False := fun hb =>
    noGood (cert _ (by have := hcf13 4; omega) _ (by have := hcf13 6; omega) _
      (by have := hcf13 9; omega) hb)
  have hex3 : ∀ a : Fin CG.x15.n, ∀ k : Fin 13, G.Adj (e a) (p k) →
      (a.1 = 4 ∨ a.1 = 6 ∨ a.1 = 9) ∧ cf a.1 = k.1 := by
    intro a k h
    have := hexit a k h
    simp only [x15Exits, List.mem_cons, List.not_mem_nil, or_false] at this
    exact ⟨this, (hcf a k).1 h⟩
  refine ⟨fun i j k a b c hab hac hbc ha hb hc => hBad ?_, fun a b hab i j ha hb => ?_⟩
  · obtain ⟨ea, ca⟩ := hex3 a i ha
    obtain ⟨eb, cb⟩ := hex3 b j hb
    obtain ⟨ec, cc⟩ := hex3 c k hc
    have hab' : a.1 ≠ b.1 := fun h => hab (Fin.ext h)
    have hac' : a.1 ≠ c.1 := fun h => hac (Fin.ext h)
    have hbc' : b.1 ≠ c.1 := fun h => hbc (Fin.ext h)
    have key : ∀ y, y = a.1 ∨ y = b.1 ∨ y = c.1 → cf y < 13 := by
      rintro y (rfl | rfl | rfl)
      · rw [ca]; exact i.2
      · rw [cb]; exact j.2
      · rw [cc]; exact k.2
    exact Or.inl ⟨key 4 (by omega), key 6 (by omega), key 9 (by omega)⟩
  · by_contra hlt
    obtain ⟨ea, ca⟩ := hex3 a i ha
    obtain ⟨eb, cb⟩ := hex3 b j hb
    have hab' : a.1 ≠ b.1 := fun h => hab (Fin.ext h)
    apply hBad
    refine pair_bad ea eb hab' i.2 j.2 ?_ ?_ hlt
    · rcases ea with h | h | h <;> simp only [h] <;> simp [← ca, h]
    · rcases eb with h | h | h <;> simp only [h] <;> simp [← cb, h]

/-- Each exit vertex of `X15` ends an induced path on 11 vertices. -/
theorem x15_exit_arm (a : Fin CG.x15.n) (ha : a.1 ∈ x15Exits) :
    ∃ α : Fin 11 → Fin CG.x15.n, Function.Injective α ∧
      (∀ i j, CG.x15.graph.Adj (α i) (α j) ↔ i.1 + 1 = j.1 ∨ j.1 + 1 = i.1) ∧
      α ⟨10, by omega⟩ = a := by
  obtain ⟨h1, h2, h3⟩ := X15Land.arm_ok a ha
  exact ⟨_, h1, h2, h3⟩

/-- The degree-2 vertices of `X15` are exactly `4, 6, 9`; every other vertex has
three neighbours in `X15`. -/
theorem x15_degree (a : Fin CG.x15.n) :
    (a.1 ∈ x15Exits → degIn CG.x15.graph Finset.univ a = 2) ∧
    (a.1 ∉ x15Exits → degIn CG.x15.graph Finset.univ a = 3) := by
  rw [X15Land.degIn_eq]
  exact X15Land.deg_ok a

end Hypostructure.Graph.DensityCert
