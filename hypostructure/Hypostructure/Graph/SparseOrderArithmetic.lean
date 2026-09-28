import Hypostructure.Graph.SparseUpperEnvelope
import Hypostructure.Graph.Progress
import Hypostructure.Core.CeilSqrt
import Mathlib.Tactic

/-!
# Sparse order arithmetic

Counting facts for a finite object with the cubic baseline and a tight
endpoint on every edge, and the arithmetic that combines them:

* the dart identity `σ + 6|H| + lowDarts = 3n`, `|H| ≤ σ`, `2m = 3n + σ`
  (`surplus_dart_identity`);
* the envelope sharpened by the absent quadrilateral: `m + 3 ≤ 2n`
  (`edgeCount_add_three_le_of_noC4`), and, from the six-vertex extremal
  count `ex(6, C₄) = 7` (a finite check), `m + 4 ≤ 2n`
  (`edgeCount_add_four_le_of_noC4`);
* the order of a minimal object is a lower bound on the order of every
  object with the same baseline that avoids the target
  (`vertexCount_le_of_minimal`);
* the square-root chain `C·c + 1 ≤ σ`, `σ + 4 ≤ n`, `n ≤ c²` ⟹
  `C(C+1) + 5 ≤ n`, its exact numeric projection (`budgetNumerics_iff`), and
  the pair-count deficit bound `pairDeficit_lower`.

Nothing here knows a presentation, a ledger, or a manuscript.
-/

namespace Hypostructure.Graph.SparseOrderArithmetic

open Hypostructure
open Hypostructure.Graph

universe u

/-- **The dart identity of a cubic-baseline object with a tight endpoint on
every edge.**  With `H = {deg ≠ 3}` and `lowDarts` the darts with both ends of
degree `3`: `σ + 6|H| + lowDarts = 3n`, `|H| ≤ σ`, and `2m = 3n + σ`
(`σ = 2m − 3n`). -/
theorem surplus_dart_identity (object : FiniteObject.{u})
    (baseline : MinimumDegreeAtLeast 3 object)
    (tight : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3) :
    letI : FinEnum object.Vertex := object.vertices
    letI : DecidableRel object.graph.Adj := object.decideAdj
    object.degreeSurplus 3 +
        6 * (Finset.univ.filter fun v => object.degree v ≠ 3).card +
        (Finset.univ.filter fun d : object.graph.Dart =>
          object.degree d.fst = 3 ∧ object.degree d.snd = 3).card =
      3 * object.vertexCount ∧
    (Finset.univ.filter fun v => object.degree v ≠ 3).card ≤ object.degreeSurplus 3 ∧
    2 * object.edgeCount = 3 * object.vertexCount + object.degreeSurplus 3 := by
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  classical
  set H := Finset.univ.filter fun v => object.degree v ≠ 3 with hH
  set L := Finset.univ.filter fun v => object.degree v = 3 with hL
  have fiber : ∀ S : Finset object.Vertex,
      (Finset.univ.filter fun d : object.graph.Dart => d.fst ∈ S).card =
        S.sum object.degree := by
    intro S
    rw [Finset.card_eq_sum_card_fiberwise
      (f := fun d : object.graph.Dart => d.fst) (t := S)
      (by intro d hd; simpa using hd)]
    refine Finset.sum_congr rfl fun v hv => ?_
    have : (Finset.univ.filter fun d : object.graph.Dart => d.fst ∈ S).filter
        (fun d => d.fst = v) =
        Finset.univ.filter fun d : object.graph.Dart => d.fst = v := by
      ext d; constructor
      · intro h; simp at h ⊢; exact h.2
      · intro h; simp at h ⊢; exact ⟨h ▸ hv, h⟩
    rw [this, SimpleGraph.dart_fst_fiber_card_eq_degree]
    unfold Graph.FiniteObject.degree
    congr 1
  have lower : ∀ v, 3 ≤ object.degree v := fun v =>
    baseline.trans (object.minDegree_le_degree v)
  -- darts leaving H all land in L
  have hHL : (Finset.univ.filter fun d : object.graph.Dart => d.fst ∈ H).card =
      (Finset.univ.filter fun d : object.graph.Dart => d.fst ∈ H ∧ d.snd ∈ L).card := by
    congr 1
    ext d
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hH, hL]
    constructor
    · intro h
      refine ⟨h, ?_⟩
      rcases tight d with t | t
      · exact absurd t h
      · exact t
    · exact fun h => h.1
  have hLsplit : (Finset.univ.filter fun d : object.graph.Dart => d.fst ∈ L).card =
      (Finset.univ.filter fun d : object.graph.Dart => d.fst ∈ L ∧ d.snd ∈ H).card +
      (Finset.univ.filter fun d : object.graph.Dart =>
          object.degree d.fst = 3 ∧ object.degree d.snd = 3).card := by
    have := Finset.card_filter_add_card_filter_not
      (s := Finset.univ.filter fun d : object.graph.Dart => d.fst ∈ L)
      (fun d => d.snd ∈ H)
    rw [← this, Finset.filter_filter, Finset.filter_filter]
    congr 2
    · ext d; simp [hH, hL]
  have hsym : (Finset.univ.filter fun d : object.graph.Dart => d.fst ∈ H ∧ d.snd ∈ L).card =
      (Finset.univ.filter fun d : object.graph.Dart => d.fst ∈ L ∧ d.snd ∈ H).card := by
    refine Finset.card_nbij' (fun d => d.symm) (fun d => d.symm) ?_ ?_ ?_ ?_
    · intro d hd
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hd ⊢
      simpa using And.comm.mp hd
    · intro d hd
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hd ⊢
      simpa using And.comm.mp hd
    · intro d _; simp
    · intro d _; simp
  have hand : (Finset.univ : Finset object.Vertex).sum object.degree =
      2 * object.edgeCount := by
    have := object.graph.sum_degrees_eq_twice_card_edges
    unfold Graph.FiniteObject.degree Graph.FiniteObject.edgeCount
    convert this
  have split : (Finset.univ : Finset object.Vertex).sum object.degree =
      H.sum object.degree + L.sum object.degree := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun v => object.degree v ≠ 3)]
    congr 1
    simp only [not_not, hL]
  have lsum : L.sum object.degree = 3 * L.card := by
    rw [Finset.sum_congr rfl (g := fun _ => 3) (by intro v hv; simpa [hL] using hv)]
    simp [mul_comm]
  have hsum : 4 * H.card ≤ H.sum object.degree := by
    have : ∀ v ∈ H, 4 ≤ object.degree v := by
      intro v hv
      have := lower v
      have hv' : object.degree v ≠ 3 := by simpa [hH] using hv
      omega
    calc 4 * H.card = H.sum (fun _ => 4) := by simp [mul_comm]
      _ ≤ H.sum object.degree := Finset.sum_le_sum this
  have cards : H.card + L.card = object.vertexCount := by
    have := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset object.Vertex)) (fun v => object.degree v ≠ 3)
    simp only [not_not] at this
    rw [hH, hL, this]
    simp [Graph.FiniteObject.vertexCount, FinEnum.card_eq_fintypeCard]
  have fH := fiber H
  have fL := fiber L
  unfold Graph.FiniteObject.degreeSurplus
  omega


/-- **The order of a minimal object bounds every competitor.**  If every
lexicographically smaller object with the baseline hits the target, and `G`
does not, then every object `H` with the baseline that avoids the target has
at least as many vertices as `G`. -/
theorem vertexCount_le_of_minimal {Baseline Target : FiniteObject.{u} → Prop}
    {object : FiniteObject.{u}}
    (minimal : ∀ H : FiniteObject.{u}, H.LexicographicallySmaller object →
      Baseline H → Target H)
    (H : FiniteObject.{u}) (baseline : Baseline H) (avoid : ¬ Target H) :
    object.vertexCount ≤ H.vertexCount := by
  by_contra h
  push Not at h
  exact avoid (minimal H (FiniteObject.lexicographicallySmaller_of_vertexCount_lt h) baseline)

/-- The √-chain: `C·c + 1 ≤ σ`, `σ + 4 ≤ n`, `n ≤ c²` force `C·(C+1) + 5 ≤ n`. -/
theorem sqrt_chain (C c n σ : Nat) (h1 : C * c + 1 ≤ σ) (h2 : σ + 4 ≤ n)
    (h3 : n ≤ c ^ 2) : C + 1 ≤ c ∧ C * (C + 1) + 5 ≤ n := by
  have hc : C + 1 ≤ c := by
    by_contra small
    push Not at small
    have : c * c ≤ C * c := Nat.mul_le_mul_right c (by omega)
    nlinarith
  exact ⟨hc, by nlinarith [Nat.mul_le_mul_left C hc]⟩


/-- The numeric shape of a sparse surplus configuration of order `n`: surplus
`σ`, high-degree count `h`, low darts `low`, edges `m`, and `ν` disjoint
windows of order `order`, with scale `C`. -/
def BudgetNumerics (order C n σ h low m ν : Nat) : Prop :=
  C * Core.ceilSqrt n + 1 ≤ σ ∧ σ + 6 * h + low = 3 * n ∧ σ + 4 ≤ n ∧ h ≤ σ ∧
    2 * m = 3 * n + σ ∧ 1 ≤ ν ∧ order * ν ≤ n ∧ n ≤ Core.ceilSqrt n ^ 2 ∧
    (C * Core.ceilSqrt n + 5) + (σ - (C * Core.ceilSqrt n + 1)) +
      2 * (2 * n - 2 - m) = n ∧
    C * (C + 1) + 5 ≤ n ∧ n + 2 ≤ 2 * (m + 1 - n) ∧ m + 2 ≤ 2 * n

/-- The budget's `n`-projection is exactly `{n : C⌈√n⌉ + 5 ≤ n}`. -/
theorem budgetNumerics_iff (order C n : Nat) (hC : 5 ≤ C) (hOrder : order ≤ C) :
    (∃ σ h low m ν, BudgetNumerics order C n σ h low m ν) ↔
      C * Core.ceilSqrt n + 5 ≤ n := by
  constructor
  · rintro ⟨σ, h, low, m, ν, h1, -, h3, -⟩
    omega
  · intro hn
    have sq := Core.le_ceilSqrt_sq n
    have chain := sqrt_chain C (Core.ceilSqrt n) n (n - 4) (by omega) (by omega) sq
    refine ⟨n - 4, 1, 2 * n - 2, 2 * n - 2, 1, ?_⟩
    refine ⟨by omega, by omega, by omega, by omega, by omega, le_rfl, ?_, sq, by omega,
      chain.2, by omega, by omega⟩
    nlinarith [chain.2]

/-- The capped-pair-count deficit, lower bound (pure integer arithmetic). -/
theorem pairDeficit_lower (σ c n E T M S C L : ℤ)
    (hc : 1 ≤ c) (hM : 0 ≤ M) (hS : 0 ≤ S) (hC : 0 ≤ C)
    (hσ : C * c + 1 ≤ σ) (_hn0 : 0 ≤ n) (hn : n ≤ c ^ 2)
    (hL : L + 1 ≤ c) (_hL0 : 0 ≤ L + 1)
    (hE : E ≤ S * n + (L + 1) * σ) (hT : T ≤ 8 * n + σ)
    (ha : 1 + 2 * c + 2 * M ≤ C * c) :
    c ^ 2 * (C ^ 2 - 3 * C - 2 * M * C - 2 * S - 16 * M) ≤
      σ * (σ - 1) - 2 * E - 2 * M * T := by
  have σ0 : 0 ≤ σ := by nlinarith
  have e1 : 2 * E ≤ 2 * S * c ^ 2 + 2 * c * σ := by nlinarith
  have e2 : 2 * M * T ≤ 16 * M * c ^ 2 + 2 * M * σ := by nlinarith
  set a := 1 + 2 * c + 2 * M
  set x := C * c
  have step2 : x * (x - a) ≤ σ * (σ - a) := by
    have : 0 ≤ (σ - x) * (σ + x - a) := by
      apply mul_nonneg <;> nlinarith
    nlinarith
  have cc : c ≤ c ^ 2 := by nlinarith
  have step3 : c ^ 2 * (C ^ 2 - 3 * C - 2 * M * C) ≤ x * (x - a) := by
    have h1 : C * c ≤ C * c ^ 2 := by nlinarith
    have h2 : M * C * c ≤ M * C * c ^ 2 := by
      have : 0 ≤ M * C := mul_nonneg hM hC
      nlinarith
    simp only [x, a]
    nlinarith
  nlinarith

section Surplus

variable (G : FiniteObject.{u})

end Surplus

section Surplus

variable (G : FiniteObject.{u})

theorem sum_degree_eq :
    letI : FinEnum G.Vertex := G.vertices
    Finset.univ.sum G.degree = 2 * G.edgeCount := by
  letI : FinEnum G.Vertex := G.vertices
  letI : DecidableRel G.graph.Adj := G.decideAdj
  have := G.graph.sum_degrees_eq_twice_card_edges
  unfold Graph.FiniteObject.degree Graph.FiniteObject.edgeCount
  convert this

theorem card_univ_eq :
    letI : FinEnum G.Vertex := G.vertices
    (Finset.univ : Finset G.Vertex).card = G.vertexCount := by
  letI : FinEnum G.Vertex := G.vertices
  simp [Graph.FiniteObject.vertexCount, FinEnum.card_eq_fintypeCard]

/-- `σ = Σ_v (deg v − 3)` under `δ ≥ 3`. -/
theorem sigma_eq_sum (baseline : ∀ v, 3 ≤ G.degree v) :
    letI : FinEnum G.Vertex := G.vertices
    G.degreeSurplus 3 = Finset.univ.sum (fun v => G.degree v - 3) := by
  letI : FinEnum G.Vertex := G.vertices
  have e1 : Finset.univ.sum (fun v => G.degree v - 3 + 3) = Finset.univ.sum G.degree :=
    Finset.sum_congr rfl (fun v _ => by have := baseline v; omega)
  rw [Finset.sum_add_distrib] at e1
  have hs := sum_degree_eq G
  have hc := card_univ_eq G
  simp only [Finset.sum_const, smul_eq_mul] at e1
  unfold Graph.FiniteObject.degreeSurplus
  rw [hc] at e1
  omega

/-- For every vertex set `T`: `Σ_{v∈T} (deg v − 3) ≤ σ`. -/
theorem sum_sub_le_sigma (baseline : ∀ v, 3 ≤ G.degree v) (T : Finset G.Vertex) :
    T.sum (fun v => G.degree v - 3) ≤ G.degreeSurplus 3 := by
  letI : FinEnum G.Vertex := G.vertices
  rw [sigma_eq_sum G baseline]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ T)
    (fun _ _ _ => Nat.zero_le _)


end Surplus

/-- Generic: under `δ ≥ 3` and "every edge has a cubic endpoint", with
`H = {deg ≠ 3}`: `σ = Σ_H (deg − 3)`, `σ ≤ |H|·(n − |H| − 3)`, and `σ > 0 ⇒ |H| ≥ 1`. -/
theorem high_generic (G : Graph.FiniteObject.{u}) (baseline : ∀ v, 3 ≤ G.degree v)
    (tight : ∀ d : G.graph.Dart, G.degree d.fst = 3 ∨ G.degree d.snd = 3)
    (σpos : 0 < G.degreeSurplus 3) :
    letI : FinEnum G.Vertex := G.vertices
    1 ≤ (Finset.univ.filter fun v => G.degree v ≠ 3).card ∧
      G.degreeSurplus 3 ≤ (Finset.univ.filter fun v => G.degree v ≠ 3).card *
        (G.vertexCount - (Finset.univ.filter fun v => G.degree v ≠ 3).card - 3) := by
  letI : FinEnum G.Vertex := G.vertices
  letI : DecidableRel G.graph.Adj := G.decideAdj
  set H := Finset.univ.filter fun v => G.degree v ≠ 3 with hH
  set L := Finset.univ.filter fun v => G.degree v = 3 with hL
  have hsum := sigma_eq_sum G baseline
  have split : Finset.univ.sum (fun v => G.degree v - 3) =
      H.sum (fun v => G.degree v - 3) := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun v => G.degree v ≠ 3)]
    have : (Finset.univ.filter fun v => ¬ G.degree v ≠ 3).sum
        (fun v => G.degree v - 3) = 0 := by
      apply Finset.sum_eq_zero
      intro v hv
      simp at hv
      omega
    rw [this, add_zero]
  have degH : ∀ v ∈ H, G.degree v ≤ L.card := by
    intro v hv
    have hv3 : G.degree v ≠ 3 := by simpa [hH] using hv
    have sub : G.graph.neighborFinset v ⊆ L := by
      intro y hy
      rw [SimpleGraph.mem_neighborFinset] at hy
      simp only [hL, Finset.mem_filter, Finset.mem_univ, true_and]
      rcases tight ⟨(v, y), hy⟩ with t | t
      · exact absurd t hv3
      · exact t
    have := Finset.card_le_card sub
    have hdeg : G.degree v = (G.graph.neighborFinset v).card := by
      rw [Graph.FiniteObject.degree_eq_ncard_neighborSet,
        ← Set.ncard_coe_finset, SimpleGraph.coe_neighborFinset]
    omega
  have cards : H.card + L.card = G.vertexCount := by
    have := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset G.Vertex)) (fun v => G.degree v ≠ 3)
    simp only [not_not] at this
    rw [hH, hL, this]
    exact card_univ_eq G
  have bound : H.sum (fun v => G.degree v - 3) ≤ H.card * (G.vertexCount - H.card - 3) := by
    calc H.sum (fun v => G.degree v - 3) ≤ H.sum (fun _ => G.vertexCount - H.card - 3) :=
          Finset.sum_le_sum (fun v hv => by have := degH v hv; omega)
      _ = H.card * (G.vertexCount - H.card - 3) := by simp
  have σeq : G.degreeSurplus 3 = H.sum (fun v => G.degree v - 3) := by
    rw [hsum, split]
  have hpos : 1 ≤ H.card := by
    by_contra h0
    have : H = ∅ := Finset.card_eq_zero.1 (by omega)
    rw [this, Finset.sum_empty] at σeq
    omega
  exact ⟨hpos, σeq ▸ bound⟩


end Hypostructure.Graph.SparseOrderArithmetic

namespace Hypostructure.Graph.FiniteObject

open scoped BigOperators

universe u
set_option linter.unusedSimpArgs false

variable {object : FiniteObject.{u}}

attribute [local instance] envelopeVertexDecEq
attribute [local instance] FiniteObject.decideAdj

/-- Four distinct vertices around a quadrilateral give an accepted cycle. -/
theorem hasC4_of_square {L : Nat → Prop} (hL4 : L 4) {x y z w : object.Vertex}
    (hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w) (hyz : y ≠ z) (hyw : y ≠ w) (hzw : z ≠ w)
    (a1 : object.graph.Adj x z) (a2 : object.graph.Adj z y)
    (a3 : object.graph.Adj y w) (a4 : object.graph.Adj w x) :
    HasCycleWithLength L object := by
  let p : object.graph.Walk z x := .cons a2 (.cons a3 (.cons a4 .nil))
  refine ⟨⟨x, .cons a1 p, ?_, ?_⟩⟩
  · rw [SimpleGraph.Walk.cons_isCycle_iff]
    constructor
    · apply SimpleGraph.Walk.IsPath.mk'
      simp [p, hxy, hxz, hxw, hyz, hyw, hzw, hxy.symm, hxz.symm, hxw.symm, hyz.symm,
        hyw.symm, hzw.symm]
    · simp [p, hxy, hxz, hxw, hyz, hyw, hzw, hxy.symm, hxz.symm, hxw.symm, hyz.symm,
        hyw.symm, hzw.symm]
  · exact hL4

/-- A 4-vertex support of a quadrilateral-free object carries at most 4 edges
(at most 8 ordered incidences). -/
theorem card_localIncidences_four
    {L : Nat → Prop} (hL4 : L 4) (noC4 : ¬ HasCycleWithLength L object)
    (support : Finset object.Vertex) (four : support.card = 4) :
    (object.localIncidences support).card ≤ 8 := by
  obtain ⟨a, t, ha, rfl, ht⟩ := Finset.card_eq_succ.mp four
  obtain ⟨b, c, d, hbc, hbd, hcd, rfl⟩ := Finset.card_eq_three.mp ht
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ha
  obtain ⟨hab, hac, had⟩ := ha
  rw [card_localIncidences]
  simp only [localDegree, Finset.card_filter]
  have n1 : a ∉ ({b, c, d} : Finset object.Vertex) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hab, hac, had⟩
  have n2 : b ∉ ({c, d} : Finset object.Vertex) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hbc, hbd⟩
  have n3 : c ∉ ({d} : Finset object.Vertex) := by
    simp only [Finset.mem_singleton]; exact hcd
  simp only [Finset.sum_insert n1, Finset.sum_insert n2, Finset.sum_insert n3,
    Finset.sum_singleton, SimpleGraph.irrefl, if_false]
  have sAB := object.graph.adj_comm b a
  have sAC := object.graph.adj_comm c a
  have sAD := object.graph.adj_comm d a
  have sBC := object.graph.adj_comm c b
  have sBD := object.graph.adj_comm d b
  have sCD := object.graph.adj_comm d c
  simp only [sAB, sAC, sAD, sBC, sBD, sCD]
  have q1 : ¬ (object.graph.Adj a b ∧ object.graph.Adj b c ∧ object.graph.Adj c d ∧
      object.graph.Adj a d) := fun ⟨e1, e2, e3, e4⟩ =>
    noC4 (hasC4_of_square hL4 hac hab had hbc.symm hcd hbd e1 e2 e3 e4.symm)
  have q2 : ¬ (object.graph.Adj a b ∧ object.graph.Adj b d ∧ object.graph.Adj c d ∧
      object.graph.Adj a c) := fun ⟨e1, e2, e3, e4⟩ =>
    noC4 (hasC4_of_square hL4 had hab hac hbd.symm hcd.symm hbc e1 e2 e3.symm e4.symm)
  have q3 : ¬ (object.graph.Adj a c ∧ object.graph.Adj b c ∧ object.graph.Adj b d ∧
      object.graph.Adj a d) := fun ⟨e1, e2, e3, e4⟩ =>
    noC4 (hasC4_of_square hL4 hab hac had hbc hbd hcd e1 e2.symm e3 e4.symm)
  by_cases e1 : object.graph.Adj a b <;> by_cases e2 : object.graph.Adj a c <;>
    by_cases e3 : object.graph.Adj a d <;> by_cases e4 : object.graph.Adj b c <;>
    by_cases e5 : object.graph.Adj b d <;> by_cases e6 : object.graph.Adj c d <;>
    simp_all

/-- The degeneracy count with a 4-vertex base: a 2-degenerate support of at
least 4 vertices in a quadrilateral-free object has `|inc| + 8 ≤ 4N`. -/
theorem card_localIncidences_le_of_degenerate_noC4
    {L : Nat → Prop} (hL4 : L 4) (noC4 : ¬ HasCycleWithLength L object)
    (support : Finset object.Vertex)
    (sparse : ∀ inner ⊆ support, inner.Nonempty →
      ∃ vertex ∈ inner, object.localDegree inner vertex ≤ 2)
    (large : 4 ≤ support.card) :
    (object.localIncidences support).card + 8 ≤ 4 * support.card := by
  induction support using Finset.strongInduction with
  | _ support ih =>
      by_cases base : support.card = 4
      · have := card_localIncidences_four hL4 noC4 support base
        omega
      · obtain ⟨vertex, member, small⟩ :=
          sparse support (Finset.Subset.refl _) (Finset.card_pos.1 (by omega))
        have erasedCard : (support.erase vertex).card + 1 = support.card :=
          Finset.card_erase_add_one member
        have smaller := ih (support.erase vertex) (Finset.erase_ssubset member)
          (fun inner subset nonempty =>
            sparse inner (subset.trans (Finset.erase_subset _ _)) nonempty)
          (by omega)
        have deletion := object.card_localIncidences_erase support member
        omega

/-- **The sharpened envelope**: no proper `δ ≥ 3` subgraph, a vertex of
degree 3, and no quadrilateral give `m + 3 ≤ 2n`. -/
theorem edgeCount_add_three_le_of_noC4 (object : FiniteObject.{u})
    {L : Nat → Prop} (hL4 : L 4) (noC4 : ¬ HasCycleWithLength L object)
    (noProperBaseline : ∀ subgraph : ProperSubgraph object,
      ¬ MinimumDegreeAtLeast 3 subgraph.value)
    {tight : object.Vertex} (atBaseline : object.degree tight = 3)
    (five : 5 ≤ object.vertexCount) :
    object.edgeCount + 3 ≤ 2 * object.vertexCount := by
  set support := object.vertexFinset.erase tight with supportDef
  have supportCard : support.card + 1 = object.vertexCount := by
    rw [supportDef, Finset.card_erase_add_one (object.mem_vertexFinset tight),
      card_vertexFinset]
  have degenerate : ∀ inner ⊆ support, inner.Nonempty →
      ∃ vertex ∈ inner, object.localDegree inner vertex ≤ 2 := by
    rintro inner subset ⟨witness, inside⟩
    have counted : inner.card ≤ support.card := Finset.card_le_card subset
    have strict : inner.card < object.vertexCount := by omega
    have failure :=
      noProperBaseline (ProperSubgraph.ofInducedSupport object inner strict)
    have nonempty : Nonempty (object.induce inner).Vertex := ⟨⟨witness, inside⟩⟩
    letI : FinEnum (object.induce inner).Vertex := (object.induce inner).vertices
    obtain ⟨minimal, attains⟩ :=
      (object.induce inner).graph.exists_minimal_degree_vertex
    refine ⟨minimal.1, minimal.2, ?_⟩
    have degreeEq : object.localDegree inner minimal.1 =
        (object.induce inner).minDegree := by
      rw [← object.degree_induce_eq_localDegree inner minimal]
      exact attains.symm
    have small : ¬ (3 ≤ (object.induce inner).minDegree) := failure
    omega
  have peel := card_localIncidences_le_of_degenerate_noC4 hL4 noC4 support degenerate
    (by omega)
  have deletion := object.card_localIncidences_erase object.vertexFinset
    (object.mem_vertexFinset tight)
  rw [card_localIncidences_vertexFinset, localDegree_vertexFinset, atBaseline,
    ← supportDef] at deletion
  omega

/-! ### The six-vertex extremal count `ex(6, C₄) = 7`

A quadrilateral-free graph on six vertices has at most seven edges.  The
fifteen vertex pairs of `Fin 6` are coded by `sixPairCode`/`sixPairDecode`;
`sixFill b` is the graph with edge bits `b`, and the bound is checked over all
`2¹⁵` bit vectors. -/

/-- The fifteen unordered pairs of `Fin 6`, in lexicographic order. -/
def sixPairDecode : Fin 15 → Fin 6 × Fin 6 :=
  ![(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (1, 3), (1, 4), (1, 5),
    (2, 3), (2, 4), (2, 5), (3, 4), (3, 5), (4, 5)]

/-- The code of an (unordered) pair of `Fin 6`. -/
def sixPairCode (i j : Fin 6) : Fin 15 :=
  let a := min i.val j.val
  let b := max i.val j.val
  ⟨(5 * a - a * (a - 1) / 2 + (b - a - 1)) % 15, Nat.mod_lt _ (by decide)⟩

theorem sixPair_decode_code : ∀ i j : Fin 6, i ≠ j →
    ((sixPairDecode (sixPairCode i j)).1 = i ∧ (sixPairDecode (sixPairCode i j)).2 = j) ∨
      ((sixPairDecode (sixPairCode i j)).1 = j ∧
        (sixPairDecode (sixPairCode i j)).2 = i) := by
  decide

/-- The six-vertex graph with edge bits `b`. -/
def sixFill (b : Fin 15 → Bool) (i j : Fin 6) : Bool :=
  if i = j then false else b (sixPairCode i j)

/-- **`ex(6, C₄) = 7`, as ordered incidences**: in every quadrilateral-free
graph on six vertices (no two distinct vertices with two common neighbours) the
number of ordered adjacent pairs is at most `14`. -/
theorem sixFill_incidences_le :
    ∀ b : Fin 15 → Bool,
      (∀ i j : Fin 6, i ≠ j →
        (Finset.univ.filter fun k => sixFill b i k = true ∧ sixFill b j k = true).card ≤ 1) →
      (Finset.univ.filter fun p : Fin 6 × Fin 6 => sixFill b p.1 p.2 = true).card ≤ 14 := by
  native_decide

/-- A symmetric irreflexive table on `Fin 6` is `sixFill` of its fifteen pair
bits. -/
theorem sixFill_restrict (A : Fin 6 → Fin 6 → Bool) (symm : ∀ i j, A i j = A j i)
    (irrefl : ∀ i, A i i = false) :
    sixFill (fun k => A (sixPairDecode k).1 (sixPairDecode k).2) = A := by
  funext i j
  unfold sixFill
  split
  · next h => subst h; exact (irrefl i).symm
  · next h =>
      show A _ _ = A i j
      rcases sixPair_decode_code i j h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2]
      · rw [h1, h2, symm]

/-- **Six vertices of a quadrilateral-free object carry at most seven edges**
(at most fourteen ordered incidences). -/
theorem card_localIncidences_six {L : Nat → Prop} (hL4 : L 4)
    (noC4 : ¬ HasCycleWithLength L object)
    (support : Finset object.Vertex) (six : support.card = 6) :
    (object.localIncidences support).card ≤ 14 := by
  classical
  let eq : support ≃ Fin 6 := support.equivFin.trans (finCongr six)
  let e : Fin 6 → object.Vertex := fun i => (eq.symm i).1
  have eInj : Function.Injective e := by
    intro i j h
    exact eq.symm.injective (Subtype.ext h)
  have eMem : ∀ i, e i ∈ support := fun i => (eq.symm i).2
  have eSurj : ∀ x ∈ support, ∃ i, e i = x := fun x hx =>
    ⟨eq ⟨x, hx⟩, by simp [e]⟩
  let A : Fin 6 → Fin 6 → Bool := fun i j => decide (object.graph.Adj (e i) (e j))
  have symm : ∀ i j, A i j = A j i := by
    intro i j
    simp only [A, object.graph.adj_comm]
  have irrefl : ∀ i, A i i = false := by
    intro i
    simp [A]
  have fill := sixFill_restrict A symm irrefl
  have c4 : ∀ i j : Fin 6, i ≠ j →
      (Finset.univ.filter fun k => A i k = true ∧ A j k = true).card ≤ 1 := by
    intro i j hij
    by_contra many
    push Not at many
    obtain ⟨k, hk, l, hl, hkl⟩ := Finset.one_lt_card.mp many
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, A, decide_eq_true_eq] at hk hl
    have ne : ∀ {a b : Fin 6}, object.graph.Adj (e a) (e b) → a ≠ b := by
      intro a b h hab
      subst hab
      exact object.graph.irrefl h
    apply noC4
    exact hasC4_of_square hL4 (x := e i) (y := e j) (z := e k) (w := e l)
      (fun h => hij (eInj h)) (fun h => ne hk.1 (eInj h))
      (fun h => ne hl.1 (eInj h)) (fun h => ne hk.2 (eInj h))
      (fun h => ne hl.2 (eInj h)) (fun h => hkl (eInj h))
      hk.1 hk.2.symm hl.2 hl.1.symm
  have bound := sixFill_incidences_le (fun k => A (sixPairDecode k).1 (sixPairDecode k).2)
    (by rw [fill]; exact c4)
  rw [fill] at bound
  have cardEq : (object.localIncidences support).card =
      (Finset.univ.filter fun p : Fin 6 × Fin 6 => A p.1 p.2 = true).card := by
    symm
    refine Finset.card_bij (fun p _ => (e p.1, e p.2)) ?_ ?_ ?_
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, A,
        decide_eq_true_eq] at hp
      rw [mem_localIncidences_iff]
      exact ⟨eMem _, eMem _, hp⟩
    · intro p _ q _ h
      simp only [Prod.mk.injEq] at h
      exact Prod.ext (eInj h.1) (eInj h.2)
    · intro pair hpair
      rw [mem_localIncidences_iff] at hpair
      obtain ⟨mem1, mem2, adj⟩ := hpair
      obtain ⟨i, hi⟩ := eSurj _ mem1
      obtain ⟨j, hj⟩ := eSurj _ mem2
      refine ⟨(i, j), ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and, A, decide_eq_true_eq]
        rw [hi, hj]; exact adj
      · simp [hi, hj]
  rw [cardEq]
  exact bound

/-- The degeneracy count with a six-vertex base: a 2-degenerate support of at
least six vertices in a quadrilateral-free object has `|inc| + 10 ≤ 4N`. -/
theorem card_localIncidences_le_of_degenerate_six {L : Nat → Prop} (hL4 : L 4)
    (noC4 : ¬ HasCycleWithLength L object)
    (support : Finset object.Vertex)
    (sparse : ∀ inner ⊆ support, inner.Nonempty →
      ∃ vertex ∈ inner, object.localDegree inner vertex ≤ 2)
    (large : 6 ≤ support.card) :
    (object.localIncidences support).card + 10 ≤ 4 * support.card := by
  induction support using Finset.strongInduction with
  | _ support ih =>
      by_cases base : support.card = 6
      · have := card_localIncidences_six hL4 noC4 support base
        omega
      · obtain ⟨vertex, member, small⟩ :=
          sparse support (Finset.Subset.refl _) (Finset.card_pos.1 (by omega))
        have erasedCard : (support.erase vertex).card + 1 = support.card :=
          Finset.card_erase_add_one member
        have smaller := ih (support.erase vertex) (Finset.erase_ssubset member)
          (fun inner subset nonempty =>
            sparse inner (subset.trans (Finset.erase_subset _ _)) nonempty)
          (by omega)
        have deletion := object.card_localIncidences_erase support member
        omega

/-- **The envelope sharpened by `ex(6, C₄) = 7`**: no proper `δ ≥ 3`
subgraph, a vertex of degree `3`, no quadrilateral, and at least seven
vertices give `m + 4 ≤ 2n`. -/
theorem edgeCount_add_four_le_of_noC4 (object : FiniteObject.{u})
    {L : Nat → Prop} (hL4 : L 4)
    (noC4 : ¬ HasCycleWithLength L object)
    (noProperBaseline : ∀ subgraph : ProperSubgraph object,
      ¬ MinimumDegreeAtLeast 3 subgraph.value)
    {tight : object.Vertex} (atBaseline : object.degree tight = 3)
    (seven : 7 ≤ object.vertexCount) :
    object.edgeCount + 4 ≤ 2 * object.vertexCount := by
  set support := object.vertexFinset.erase tight with supportDef
  have supportCard : support.card + 1 = object.vertexCount := by
    rw [supportDef, Finset.card_erase_add_one (object.mem_vertexFinset tight),
      card_vertexFinset]
  have degenerate : ∀ inner ⊆ support, inner.Nonempty →
      ∃ vertex ∈ inner, object.localDegree inner vertex ≤ 2 := by
    rintro inner subset ⟨witness, inside⟩
    have counted : inner.card ≤ support.card := Finset.card_le_card subset
    have strict : inner.card < object.vertexCount := by omega
    have failure :=
      noProperBaseline (ProperSubgraph.ofInducedSupport object inner strict)
    have nonempty : Nonempty (object.induce inner).Vertex := ⟨⟨witness, inside⟩⟩
    letI : FinEnum (object.induce inner).Vertex := (object.induce inner).vertices
    obtain ⟨minimal, attains⟩ :=
      (object.induce inner).graph.exists_minimal_degree_vertex
    refine ⟨minimal.1, minimal.2, ?_⟩
    have degreeEq : object.localDegree inner minimal.1 =
        (object.induce inner).minDegree := by
      rw [← object.degree_induce_eq_localDegree inner minimal]
      exact attains.symm
    have small : ¬ (3 ≤ (object.induce inner).minDegree) := failure
    omega
  have peel := card_localIncidences_le_of_degenerate_six hL4 noC4 support degenerate
    (by omega)
  have deletion := object.card_localIncidences_erase object.vertexFinset
    (object.mem_vertexFinset tight)
  rw [card_localIncidences_vertexFinset, localDegree_vertexFinset, atBaseline,
    ← supportDef] at deletion
  omega

end Hypostructure.Graph.FiniteObject
