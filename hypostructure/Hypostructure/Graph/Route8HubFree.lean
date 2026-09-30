import Hypostructure.Graph.DensityCert.Main
import Hypostructure.Graph.DensityCert.X15Landing
import Hypostructure.Graph.CleanLanding
import Hypostructure.Graph.JointObject
import Hypostructure.Graph.HubWindow
import Hypostructure.Graph.Route8Supply

/-!
# Hub-free components of the remainder: the density theorem and the `X15` landings

Let `R` be the remainder of a window packing of order `13` in a graph `G` with minimum
degree `≥ 3`, no cycle of dyadic length and no induced `P13` inside `R`, and let `S` be the
vertex set of a connected component of `G[R]` with ambient surplus `Σ_{v∈S}(d(v) − 3) = 0`
(a *hub-free* component).  Then:

* every vertex of `S` has degree exactly `3` in `G` (`degree_eq_of_ambientSurplus_eq_zero`);
* `G[S]` is connected (`connIn_pieceSupport`) and admissible for the density theorem
  (`admIn_of_hubFree`): subcubic, no cycle of length `4, 8, 16, 32`, no induced `P13`;
* the excess `|S| − 4·|∂S|` equals `8e(G[S]) − 11|S|` (`excess_eq_dIn`);
* hence (density theorem) the excess is `≤ 0` or `G[S]` is a copy of `X15`
  (`hubFree_density`), and a copy of `X15` has excess `3` (`excess_x15`);
* in a copy of `X15` with all degrees `3`, the three exit vertices (the degree-`2` vertices
  of `X15`) have exactly one neighbour outside the copy and every other vertex has none
  (`exit_of_adj_outside`, `outside_unique`, `exists_outside`).

The long landings of a hub-free copy of `X15` are in `Route8X15Landing`.
-/

namespace Hypostructure.Graph.Route8HubFree

open Hypostructure
open Hypostructure.Graph
open Hypostructure.Graph.DensityCert
open scoped BigOperators

universe u

variable {object : FiniteObject.{u}}

/-! ## Connectivity -/

/-- A walk whose vertices lie in `S` witnesses reachability inside `S`. -/
theorem reachIn_of_walk {S : Finset object.Vertex} :
    ∀ {a b : object.Vertex} (w : object.graph.Walk a b),
      (∀ x ∈ w.support, x ∈ S) → ReachIn object.graph S a b
  | _, _, .nil, _ => Relation.ReflTransGen.refl
  | a, _, .cons (v := c) h p, hw => by
    have ha : a ∈ S := hw a (by simp)
    have hc : c ∈ S := hw c (by simp [p.start_mem_support])
    exact Relation.ReflTransGen.head ⟨ha, hc, h⟩
      (reachIn_of_walk p fun x hx => hw x (by simp [hx]))

/-- A component of `G[R]` induces a connected subgraph. -/
theorem connIn_pieceSupport (R : Finset object.Vertex)
    {X : SupportComponents.Connected.Component object R}
    (hX : X ∈ object.canonicalPieces R) :
    ConnIn object.graph (object.pieceSupport R X) := by
  have h := SupportComponents.Connected.connectedOn_of_mem_order object R
    ((object.mem_canonicalPieces R).1 hX)
  refine ⟨h.1, fun u hu v hv => ?_⟩
  obtain ⟨w, _, hw⟩ := h.2 hu hv
  exact reachIn_of_walk w hw

/-! ## Cycles and induced paths -/

/-- The forbidden lengths are dyadic. -/
theorem dyadic_of_forbiddenLen {k : ℕ} (h : forbiddenLen k) : HubWin.Dyadic k := by
  rcases h with rfl | rfl | rfl | rfl
  · exact ⟨2, le_rfl, rfl⟩
  · exact ⟨3, by norm_num, rfl⟩
  · exact ⟨4, by norm_num, rfl⟩
  · exact ⟨5, by norm_num, rfl⟩

/-- With no cycle of dyadic length, no cycle list has a forbidden length. -/
theorem not_forbiddenLen_of_isCycleList
    (avoid : ¬ HasCycleWithLength Core.DyadicLength.PowerOfTwoLength object)
    {l : List object.Vertex} (hl : IsCycleList object.graph l) :
    ¬ forbiddenLen l.length := by
  intro hf
  obtain ⟨hnd, hlen, hch, hcl⟩ := hl
  match l, hnd, hlen, hch, hcl, hf with
  | a :: t, hnd, hlen, hch, hcl, hf =>
    have chain : List.IsChain object.graph.Adj (a :: t) := List.isChain_iff_getElem.2 hch
    have close : object.graph.Adj ((a :: t).getLast (List.cons_ne_nil _ _)) a := by
      rw [List.getLast_eq_getElem]
      exact hcl (by simp)
    obtain ⟨c, hc, hclen⟩ :=
      HubWin.list_cycle a t hnd chain (by simp at hlen; omega) close
    exact JointObject.noDyadic avoid c hc (by rw [hclen]; simpa using dyadic_of_forbiddenLen hf)

/-- An induced path on `13` vertices as an index sequence `g 0, …, g 12`. -/
theorem exists_inducedSeq_of_isIndPath [Fintype object.Vertex] [DecidableEq object.Vertex]
    [DecidableRel object.graph.Adj]
    {l : List object.Vertex} (hl : IsIndPath object.graph l) (h13 : l.length = 13) :
    ∃ g : ℕ → object.Vertex, WindowCombination.InducedSeq object.graph 12 g ∧
      ∀ t ≤ 12, g t ∈ l := by
  have h0 : 0 < l.length := by omega
  refine ⟨fun t => l.getD t (l[0]'h0), ⟨fun a ha b hb e => ?_, fun a ha b hb => ?_⟩,
    fun t ht => ?_⟩
  · simp only [List.getD_eq_getElem _ _ (show a < l.length by omega),
      List.getD_eq_getElem _ _ (show b < l.length by omega)] at e
    exact (hl.1.getElem_inj_iff).1 e
  · simp only [List.getD_eq_getElem _ _ (show a < l.length by omega),
      List.getD_eq_getElem _ _ (show b < l.length by omega)]
    exact hl.2 a b (by omega) (by omega)
  · simp only [List.getD_eq_getElem _ _ (show t < l.length by omega)]
    exact List.getElem_mem _

/-! ## Degrees -/

/-- Zero ambient surplus on the baseline: every vertex has degree exactly `δ`. -/
theorem degree_eq_of_ambientSurplus_eq_zero {S : Finset object.Vertex} {δ : ℕ}
    (base : ∀ v, δ ≤ object.degree v) (hσ : object.ambientSurplus S δ = 0) :
    ∀ v ∈ S, object.degree v = δ := by
  intro v hv
  have h := (Finset.sum_eq_zero_iff.1 hσ) v hv
  have := base v
  omega

/-- A finite set of neighbours has at most `degree` elements. -/
theorem card_le_degree {v : object.Vertex} (T : Finset object.Vertex)
    (hT : ∀ w ∈ T, object.graph.Adj v w) : T.card ≤ object.degree v := by
  letI : FinEnum object.Vertex := object.vertices
  rw [FiniteObject.degree_eq_ncard_neighborSet, ← Set.ncard_coe_finset]
  exact Set.ncard_le_ncard (fun w hw => hT w hw) (Set.toFinite _)

/-- Every neighbour of `v` lies in `T` ⇒ `degree ≤ |T|`. -/
theorem degree_le_card {v : object.Vertex} (T : Finset object.Vertex)
    (hT : ∀ w, object.graph.Adj v w → w ∈ T) : object.degree v ≤ T.card := by
  letI : FinEnum object.Vertex := object.vertices
  rw [FiniteObject.degree_eq_ncard_neighborSet, ← Set.ncard_coe_finset]
  exact Set.ncard_le_ncard (fun w hw => hT w hw) (Set.toFinite _)

theorem degIn_le_degree (S : Finset object.Vertex) (v : object.Vertex) :
    degIn object.graph S v ≤ object.degree v := by
  classical
  unfold degIn
  exact card_le_degree _ fun w hw => by
    simp only [Finset.mem_filter] at hw
    exact hw.2

/-! ## Admissibility and the excess -/

/-- A hub-free component of the remainder is admissible. -/
theorem admIn_of_hubFree {S R : Finset object.Vertex} (hSR : S ⊆ R)
    (hdeg : ∀ v ∈ S, object.degree v = 3)
    (avoid : ¬ HasCycleWithLength Core.DyadicLength.PowerOfTwoLength object)
    (free : ∀ l : List object.Vertex, IsIndPath object.graph l → (∀ x ∈ l, x ∈ R) →
      l.length ≠ 13) :
    AdmIn object.graph S :=
  ⟨fun v hv => (degIn_le_degree S v).trans (hdeg v hv).le,
    fun _ _ hl => not_forbiddenLen_of_isCycleList avoid hl,
    fun l hin hl => free l hl fun x hx => hSR (hin x hx)⟩

/-- The internal degree is the number of neighbours inside the support. -/
theorem internalDegree_eq_card_filter [DecidableRel object.graph.Adj]
    (S : Finset object.Vertex) (v : object.Vertex) :
    object.internalDegree S v = (S.filter fun w => object.graph.Adj v w).card := by
  classical
  unfold FiniteObject.internalDegree
  congr 1
  ext w
  simp [SimpleGraph.mem_neighborFinset, and_comm]

open Classical in
/-- The ordered adjacent pairs of `S` are counted by the internal degrees. -/
theorem card_adjPairs_eq_sum_internalDegree (S : Finset object.Vertex) :
    (((S ×ˢ S).filter fun p : object.Vertex × object.Vertex =>
        object.graph.Adj p.1 p.2).card : ℤ) =
      ∑ v ∈ S, (object.internalDegree S v : ℤ) := by
  classical
  rw [Finset.card_filter, Finset.sum_product]
  push_cast
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [internalDegree_eq_card_filter, Finset.card_filter]
  push_cast
  rfl

/-- On a support where every vertex has degree `3`, the excess `|S| − 4|∂S|` is
`8e(G[S]) − 11|S|`. -/
theorem excess_eq_dIn {S : Finset object.Vertex} (hdeg : ∀ v ∈ S, object.degree v = 3) :
    (S.card : ℤ) - 4 * ((Route8.cutEdges object S).card : ℤ) = dIn object.graph S := by
  have hle : ∀ v ∈ S, object.internalDegree S v ≤ 3 := fun v hv =>
    (object.internalDegree_le_degree S v).trans (hdeg v hv).le
  have hcut : ((Route8.cutEdges object S).card : ℤ) =
      ∑ v ∈ S, ((3 : ℤ) - (object.internalDegree S v : ℤ)) := by
    rw [Route8.card_cutEdges_eq_boundaryIncidence, FiniteObject.boundaryIncidence,
      Nat.cast_sum]
    refine Finset.sum_congr rfl fun v hv => ?_
    rw [hdeg v hv, Nat.cast_sub (hle v hv)]
    rfl
  unfold dIn
  rw [card_adjPairs_eq_sum_internalDegree, hcut, Finset.sum_sub_distrib]
  simp only [Finset.sum_const, nsmul_eq_mul]
  ring

/-- **The density theorem at a hub-free component**: its excess is `≤ 0`, or it is a copy of
`X15`. -/
theorem hubFree_density (R : Finset object.Vertex)
    {X : SupportComponents.Connected.Component object R}
    (hX : X ∈ object.canonicalPieces R)
    (hdeg : ∀ v ∈ object.pieceSupport R X, object.degree v = 3)
    (avoid : ¬ HasCycleWithLength Core.DyadicLength.PowerOfTwoLength object)
    (free : ∀ l : List object.Vertex, IsIndPath object.graph l → (∀ x ∈ l, x ∈ R) →
      l.length ≠ 13) :
    ((object.pieceSupport R X).card : ℤ) -
        4 * ((Route8.cutEdges object (object.pieceSupport R X)).card : ℤ) ≤ 0 ∨
      EmbOnto CG.x15.graph object.graph (object.pieceSupport R X) := by
  letI : FinEnum object.Vertex := object.vertices
  rw [excess_eq_dIn hdeg]
  exact density_le_of_admissible_in object.graph _ (connIn_pieceSupport R hX)
    (admIn_of_hubFree (object.pieceSupport_subset R X) hdeg avoid free)

/-! ## Copies of `X15` -/

/-- The degree sum of `X15` is `42` (three exits of degree `2`, twelve vertices of
degree `3`). -/
theorem sum_degIn_x15 : ∑ a : Fin CG.x15.n, degIn CG.x15.graph Finset.univ a = 42 := by
  have h : ∀ a : Fin CG.x15.n, degIn CG.x15.graph Finset.univ a =
      if a.1 ∈ x15Exits then 2 else 3 := by
    intro a
    by_cases ha : a.1 ∈ x15Exits
    · rw [if_pos ha, (x15_degree a).1 ha]
    · rw [if_neg ha, (x15_degree a).2 ha]
  rw [Finset.sum_congr rfl fun a _ => h a]
  decide

section Copy

variable {S : Finset object.Vertex} (e : CG.x15.graph ↪g object.graph)
  (he : ∀ v, v ∈ S ↔ ∃ i, e i = v)
include he

/-- Inside a copy of `X15`, the neighbours of `e a` are the images of the neighbours of `a`. -/
theorem adj_iff_of_mem {a : Fin CG.x15.n} {w : object.Vertex} (hw : w ∈ S) :
    object.graph.Adj (e a) w ↔ ∃ b, CG.x15.graph.Adj a b ∧ e b = w := by
  obtain ⟨b, rfl⟩ := (he w).1 hw
  constructor
  · intro h
    exact ⟨b, e.map_adj_iff.1 h, rfl⟩
  · rintro ⟨c, hc, hcb⟩
    rw [← hcb]
    exact e.map_adj_iff.2 hc

omit he in
/-- The neighbours of `a` in `X15`, mapped into G. -/
theorem card_nbrs (a : Fin CG.x15.n) :
    ((Finset.univ.filter fun b => CG.x15.graph.Adj a b).map e.toEmbedding).card =
      degIn CG.x15.graph Finset.univ a := by
  classical
  rw [Finset.card_map]
  unfold degIn
  apply congrArg
  ext b
  simp

theorem nbrs_subset (a : Fin CG.x15.n) :
    ∀ w ∈ (Finset.univ.filter fun b => CG.x15.graph.Adj a b).map e.toEmbedding,
      w ∈ S ∧ object.graph.Adj (e a) w := by
  intro w hw
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and] at hw
  obtain ⟨b, hb, rfl⟩ := hw
  exact ⟨(he _).2 ⟨b, rfl⟩, e.map_adj_iff.2 hb⟩

/-- The internal degree of `e a` in the copy is the degree of `a` in `X15`. -/
theorem internalDegree_emb (a : Fin CG.x15.n) :
    object.internalDegree S (e a) = degIn CG.x15.graph Finset.univ a := by
  classical
  rw [internalDegree_eq_card_filter, ← card_nbrs e a]
  congr 1
  ext w
  simp only [Finset.mem_filter, Finset.mem_map, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hw, h⟩
    obtain ⟨b, hb, rfl⟩ := (adj_iff_of_mem e he hw).1 h
    exact ⟨b, hb, rfl⟩
  · rintro ⟨b, hb, rfl⟩
    exact ⟨(he _).2 ⟨b, rfl⟩, e.map_adj_iff.2 hb⟩

theorem support_eq_map : S = Finset.univ.map e.toEmbedding := by
  ext v
  simp [he v]

/-- **A copy of `X15` with all degrees `3` has excess `3`.** -/
theorem excess_x15 (hdeg : ∀ v ∈ S, object.degree v = 3) :
    (S.card : ℤ) - 4 * ((Route8.cutEdges object S).card : ℤ) = 3 := by
  rw [excess_eq_dIn hdeg]
  unfold dIn
  rw [card_adjPairs_eq_sum_internalDegree, support_eq_map e he, Finset.sum_map,
    Finset.card_map]
  simp only [RelEmbedding.coe_toEmbedding]
  rw [← support_eq_map e he]
  simp only [internalDegree_emb e he]
  have h42 : ((∑ a : Fin CG.x15.n, degIn CG.x15.graph Finset.univ a : ℕ) : ℤ) = 42 := by
    exact_mod_cast sum_degIn_x15
  have hn : (Finset.univ : Finset (Fin CG.x15.n)).card = 15 := by
    rw [Finset.card_univ, Fintype.card_fin]; rfl
  rw [← Nat.cast_sum, h42, hn]
  norm_num

/-- Neighbour count at a vertex of a copy of `X15` with all degrees `3`: its degree in
`X15` plus any set of neighbours outside the copy is at most `3`. -/
theorem degIn_add_card_le (hdeg : ∀ v ∈ S, object.degree v = 3) (a : Fin CG.x15.n)
    (T : Finset object.Vertex) (hT : ∀ w ∈ T, w ∉ S ∧ object.graph.Adj (e a) w) :
    degIn CG.x15.graph Finset.univ a + T.card ≤ 3 := by
  classical
  have hdisj : Disjoint
      ((Finset.univ.filter fun b => CG.x15.graph.Adj a b).map e.toEmbedding) T :=
    Finset.disjoint_left.2 fun w hw hwT => (hT w hwT).1 (nbrs_subset e he a w hw).1
  rw [← card_nbrs e a, ← Finset.card_union_of_disjoint hdisj,
    ← hdeg (e a) ((he _).2 ⟨a, rfl⟩)]
  refine card_le_degree _ fun w hw => ?_
  rcases Finset.mem_union.1 hw with h | h
  · exact (nbrs_subset e he a w h).2
  · exact (hT w h).2

/-- Only the exits of `X15` have a neighbour outside the copy. -/
theorem exit_of_adj_outside (hdeg : ∀ v ∈ S, object.degree v = 3) (a : Fin CG.x15.n)
    {w : object.Vertex} (hw : w ∉ S) (hadj : object.graph.Adj (e a) w) :
    a.1 ∈ x15Exits := by
  by_contra ha
  have h := degIn_add_card_le e he hdeg a {w} (by simpa using ⟨hw, hadj⟩)
  rw [(x15_degree a).2 ha, Finset.card_singleton] at h
  omega

/-- A vertex of the copy has at most one neighbour outside it. -/
theorem outside_unique (hdeg : ∀ v ∈ S, object.degree v = 3) (a : Fin CG.x15.n)
    {w w' : object.Vertex} (hw : w ∉ S) (hw' : w' ∉ S) (hadj : object.graph.Adj (e a) w)
    (hadj' : object.graph.Adj (e a) w') : w = w' := by
  classical
  by_contra hne
  have h := degIn_add_card_le e he hdeg a {w, w'} (by
    intro x hx
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact ⟨hw, hadj⟩
    · rw [Finset.mem_singleton.1 hx]; exact ⟨hw', hadj'⟩)
  rw [Finset.card_pair hne] at h
  by_cases ha : a.1 ∈ x15Exits
  · rw [(x15_degree a).1 ha] at h; omega
  · rw [(x15_degree a).2 ha] at h; omega

/-- Every exit of the copy has a neighbour outside it. -/
theorem exists_outside (hdeg : ∀ v ∈ S, object.degree v = 3) (a : Fin CG.x15.n)
    (ha : a.1 ∈ x15Exits) : ∃ w, object.graph.Adj (e a) w ∧ w ∉ S := by
  classical
  by_contra h
  push Not at h
  have hle := degree_le_card
    ((Finset.univ.filter fun b => CG.x15.graph.Adj a b).map e.toEmbedding) fun w hw => by
      obtain ⟨b, hb, rfl⟩ := (adj_iff_of_mem e he (h w hw)).1 hw
      simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨b, hb, rfl⟩
  rw [card_nbrs e a, (x15_degree a).1 ha, hdeg (e a) ((he _).2 ⟨a, rfl⟩)] at hle
  omega

end Copy

/-- The vertex set of an induced `13`-vertex path is an induced window of order `13`. -/
theorem inducesWindow_of_isInducedThirteen {T : Finset object.Vertex}
    (h : IsInducedThirteen object.graph T) : object.InducesWindow 13 T := by
  obtain ⟨l, hl, hlen, hmem⟩ := h
  obtain ⟨W, hW, hWmem⟩ := PackingExchange.exists_inducesWindow_of_pathMap
    (q := fun i : Fin 13 => l[i.1]'(by omega))
    (fun i j hij => Fin.ext ((hl.1.getElem_inj_iff).1 hij))
    (fun i j => hl.2 i j (by omega) (by omega))
  have hWT : W = T := by
    ext v
    rw [hWmem, hmem, List.mem_iff_getElem]
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i.1, by omega, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, by omega⟩, rfl⟩
  exact hWT ▸ hW

end Hypostructure.Graph.Route8HubFree
