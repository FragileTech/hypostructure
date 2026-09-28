import Hypostructure.Graph.JointSystem
import Hypostructure.Graph.HubWindow
import Hypostructure.Graph.WindowCombination
import Hypostructure.Graph.RemainderPaths
import Hypostructure.Graph.WindowJoinIdentity
import Hypostructure.Graph.SparseUpperEnvelope
import Hypostructure.Graph.BoundaryDemand
import Hypostructure.Core.DyadicLength
import Hypostructure.Graph.DensityOverload
import Hypostructure.Graph.SparseOrderArithmetic
import Hypostructure.Graph.Contraction

/-!
# Hubs, windows and remainder paths of a finite object

The Mathlib-level results of `JointSystem`, `HubWindow`, `WindowCombination` and
`RemainderPaths`, read at a `FiniteObject` with the cubic baseline, its own vertex schedule
and adjacency decision, and any window packing of order `13`.  Every hypothesis is an
explicit property of the object (baseline, independent high vertices, no proper subgraph
at the baseline, no dyadic cycle, the packing and its maximality); nothing here names a
presentation, a ledger or a manuscript.

* the object in Mathlib form: hubs `H = {deg ≠ 3}`, no `C₄`, no `C₈`, every proper vertex
  set spans a vertex of internal degree `≤ 2`, `σ = ∑_H (deg − 3)`, window degrees;
* the hub–window budget at a packing (`hubWindowBudget`, `hubBudget_rs`, `offPath_identity`),
  the remainder slack (`remainderSlack`) and hanging windows (`hanging`);
* windows against the big-hub neighbourhood (`windowU`, `windowU_rs`), the V-shape/hub
  relation (`vshape`) and few windows (`fewWindows`);
* the remainder has no induced `P13` under maximality (`remainder_noP13`), bags have at most
  `6142` vertices (`bag_card`), and paths and cycles inside it are bounded by its hubs
  (`remainder_path_bound`, `remainder_cycle_bound`).
-/

open Finset
open Hypostructure Hypostructure.Graph
open Hypostructure.Graph.WindowCombination

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Hypostructure.Graph.JointObject

universe u

attribute [local instance] Graph.FiniteObject.vertices Graph.FiniteObject.decideAdj

/-- The high vertices of `object` are pairwise non-adjacent (raw form). -/
abbrev SlackIndependent (object : Graph.FiniteObject.{u}) : Prop :=
  ∀ left right : object.Vertex, 3 < object.degree left → 3 < object.degree right →
    ¬ object.graph.Adj left right

/-- No proper subgraph of `object` meets the cubic baseline (raw form). -/
abbrev NoProperCubic (object : Graph.FiniteObject.{u}) : Prop :=
  ∀ sub : ProperSubgraph object, ¬ MinimumDegreeAtLeast 3 sub.value

/-- The darts of `object` with both ends of degree `3`. -/
noncomputable abbrev lowDartCount (object : Graph.FiniteObject.{u}) : Nat :=
  (Finset.univ.filter fun d : object.graph.Dart =>
    object.degree d.fst = 3 ∧ object.degree d.snd = 3).card

section Bridge


variable {object : Graph.FiniteObject.{u}}

theorem vertexCount_eq (object : Graph.FiniteObject.{u}) :
    object.vertexCount = Fintype.card object.Vertex :=
  FinEnum.card_eq_fintypeCard

theorem deg_ge (base : MinimumDegreeAtLeast 3 object) (v : object.Vertex) :
    3 ≤ object.graph.degree v :=
  le_trans base (object.minDegree_le_degree v)

/-- The hubs `H = {deg ≠ 3}` (with `δ ≥ 3`: `{deg ≥ 4}`). -/
noncomputable def hubs (object : Graph.FiniteObject.{u}) : Finset object.Vertex :=
  univ.filter (fun v => object.graph.degree v ≠ 3)

theorem mem_hubs {v : object.Vertex} : v ∈ hubs object ↔ object.graph.degree v ≠ 3 := by
  simp [hubs]

theorem hubs_indep (base : MinimumDegreeAtLeast 3 object)
    (slack : SlackIndependent object) :
    ∀ a ∈ hubs object, ∀ b ∈ hubs object, ¬ object.graph.Adj a b := by
  intro a ha b hb
  rw [mem_hubs] at ha hb
  have h1 := deg_ge base a
  have h2 := deg_ge base b
  exact slack a b (show 3 < object.degree a by change 3 < object.graph.degree a; omega)
    (show 3 < object.degree b by change 3 < object.graph.degree b; omega)

theorem cubic_of_not_hub {v : object.Vertex} (hv : v ∉ hubs object) :
    object.graph.degree v = 3 := by
  rw [mem_hubs] at hv; omega

/-! ## No dyadic cycle, in Mathlib form -/

theorem noDyadic (avoid : ¬ HasCycleWithLength Core.DyadicLength.PowerOfTwoLength object)
    {w : object.Vertex} (c : object.graph.Walk w w) (hc : c.IsCycle) :
    ¬ Hypostructure.Graph.HubWin.Dyadic c.length := by
  rintro ⟨k, hk, e⟩
  apply avoid
  exact ⟨⟨w, c, hc, ⟨⟨k, by have := (Nat.lt_two_pow_self (n := k)); omega⟩, hk, e⟩⟩⟩

/-- **No `C₄`** (codegree `≤ 1`). -/
theorem c4Free (avoid : ¬ HasCycleWithLength Core.DyadicLength.PowerOfTwoLength object)
    (a b c c' : object.Vertex) (hab : a ≠ b) (hac : object.graph.Adj a c)
    (hbc : object.graph.Adj b c) (hac' : object.graph.Adj a c') (hbc' : object.graph.Adj b c') :
    c = c' := by
  by_contra hne
  have hnd : [a, c, b, c'].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, and_true]
    exact ⟨⟨(object.graph.ne_of_adj hac), hab, (object.graph.ne_of_adj hac')⟩,
      ⟨(object.graph.ne_of_adj hbc).symm, hne⟩, (object.graph.ne_of_adj hbc'), by simp⟩
  have hch : List.IsChain object.graph.Adj [a, c, b, c'] := by
    simp only [List.isChain_cons_cons, List.isChain_singleton, and_true]
    exact ⟨hac, hbc.symm, hbc'⟩
  obtain ⟨cyc, hcyc, hlen⟩ := Hypostructure.Graph.HubWin.list_cycle a [c, b, c'] hnd hch (by simp)
    (by simpa using hac'.symm)
  exact noDyadic avoid cyc hcyc ⟨2, le_rfl, by simpa using hlen⟩

/-- **No `C₈`**, in the `Fin 8` form of `Hypostructure.Graph.JointSystem.NoCycleLen`. -/
theorem noC8 (avoid : ¬ HasCycleWithLength Core.DyadicLength.PowerOfTwoLength object)
    (f : Fin 8 → object.Vertex) (hinj : Function.Injective f)
    (hadj : ∀ i : Fin 8, object.graph.Adj (f i) (f (i + 1))) : False := by
  have hnd : [f 0, f 1, f 2, f 3, f 4, f 5, f 6, f 7].Nodup := by
    have := List.nodup_ofFn.2 hinj
    simpa [List.ofFn_succ] using this
  have hch : List.IsChain object.graph.Adj [f 0, f 1, f 2, f 3, f 4, f 5, f 6, f 7] := by
    simp only [List.isChain_cons_cons, List.isChain_singleton, and_true]
    exact ⟨hadj 0, hadj 1, hadj 2, hadj 3, hadj 4, hadj 5, hadj 6⟩
  obtain ⟨cyc, hcyc, hlen⟩ := Hypostructure.Graph.HubWin.list_cycle (f 0) [f 1, f 2, f 3, f 4, f 5, f 6, f 7]
    hnd hch (by simp) (by simpa using hadj 7)
  exact noDyadic avoid cyc hcyc ⟨3, by norm_num, by simpa using hlen⟩

/-! ## noProperBaseline in induced form -/

theorem localDegree_eq (S : Finset object.Vertex) (v : object.Vertex) :
    object.localDegree S v = (object.graph.neighborFinset v ∩ S).card := by
  unfold FiniteObject.localDegree
  congr 1; ext w; simp [and_comm]

/-- **Every nonempty proper vertex set spans a vertex of internal degree `≤ 2`.** -/
theorem properTwoLow
    (noProper : NoProperCubic object) :
    ∀ S : Finset object.Vertex, S.Nonempty → S ≠ univ →
      ∃ v ∈ S, (object.graph.neighborFinset v ∩ S).card ≤ 2 := by
  intro S ⟨x, hx⟩ hS
  have strict : S.card < object.vertexCount := by
    rw [vertexCount_eq, ← card_univ]; exact card_lt_card (ssubset_univ_iff.2 hS)
  have failure := noProper (ProperSubgraph.ofInducedSupport object S strict)
  haveI : Nonempty (object.induce S).Vertex := ⟨⟨x, hx⟩⟩
  obtain ⟨m, hm⟩ := (object.induce S).graph.exists_minimal_degree_vertex
  refine ⟨m.1, m.2, ?_⟩
  have e := object.degree_induce_eq_localDegree S m
  rw [localDegree_eq] at e
  have small : ¬ (3 ≤ (object.induce S).minDegree) := failure
  have e2 : (object.induce S).minDegree = (object.induce S).degree m := hm
  omega

/-- **Density** (`slack S ≥ 0` for proper `S`, `|S| ≥ 2`). -/
theorem density
    (noProper : NoProperCubic object) :
    ∀ S : Finset object.Vertex, S ≠ univ → 2 ≤ S.card →
      ∑ u ∈ S, (object.graph.neighborFinset u ∩ S).card + 6 ≤ 4 * S.card :=
  Hypostructure.Graph.HubWin.degenerate_internal_sum_le object.graph (properTwoLow noProper)

/-- **Every cubic vertex has a cubic neighbour** (noProperBaseline at `V ∖ {v}`). -/
theorem cubic_nbr (base : MinimumDegreeAtLeast 3 object)
    (noProper : NoProperCubic object)
    {v : object.Vertex} (hv : object.graph.degree v = 3) :
    ∃ u, object.graph.Adj v u ∧ object.graph.degree u = 3 := by
  by_contra hno
  push Not at hno
  have hS : (univ.erase v).Nonempty := by
    have : 0 < object.graph.degree v := by omega
    obtain ⟨u, hu⟩ := object.graph.degree_pos_iff_exists_adj v |>.1 this
    exact ⟨u, mem_erase.2 ⟨(object.graph.ne_of_adj hu).symm, mem_univ _⟩⟩
  obtain ⟨w, hw, hwl⟩ := properTwoLow noProper (univ.erase v) hS (fun h => by
    have := mem_univ v; rw [← h] at this; simp at this)
  have hwv : w ≠ v := (mem_erase.1 hw).1
  have hsub : object.graph.neighborFinset w ∩ univ.erase v
      = (object.graph.neighborFinset w).erase v := by
    ext x; simp [and_comm]
  rw [hsub] at hwl
  have hmw := deg_ge base w
  by_cases hadj : object.graph.Adj v w
  · have h4 : object.graph.degree w ≠ 3 := hno w hadj
    have hmem : v ∈ object.graph.neighborFinset w := by simpa using hadj.symm
    rw [card_erase_of_mem hmem, object.graph.card_neighborFinset_eq_degree] at hwl
    omega
  · have hmem : v ∉ object.graph.neighborFinset w := by
      simpa [object.graph.adj_comm] using hadj
    rw [erase_eq_of_notMem hmem, object.graph.card_neighborFinset_eq_degree] at hwl
    omega

/-! ## σ as the hub excess -/

theorem degreeSurplus_eq (base : MinimumDegreeAtLeast 3 object) :
    object.degreeSurplus 3 = ∑ v ∈ hubs object, (object.graph.degree v - 3) := by
  have hs := object.graph.sum_degrees_eq_twice_card_edges
  have he : object.edgeCount = object.graph.edgeFinset.card := rfl
  have h1 : ∑ v, object.graph.degree v = ∑ v, (object.graph.degree v - 3) + 3 * Fintype.card object.Vertex := by
    rw [mul_comm, ← smul_eq_mul, ← card_univ, ← sum_const, ← sum_add_distrib]
    exact sum_congr rfl (fun v _ => by have := deg_ge base v; omega)
  have h2 : ∑ v, (object.graph.degree v - 3) = ∑ v ∈ hubs object, (object.graph.degree v - 3) := by
    rw [hubs, sum_filter]
    apply sum_congr rfl; intro v _
    split_ifs with h
    · rfl
    · push Not at h; rw [h]; rfl
  unfold FiniteObject.degreeSurplus
  rw [vertexCount_eq, he, ← h2]
  omega

/-! ## The canonical windows as induced paths -/

/-- A window of `P₀` is the image of an induced 13-vertex path. -/
theorem window_seq {P : Finset object.Vertex} (hP : object.InducesWindow 13 P) :
    ∃ g : ℕ → object.Vertex,
      (∀ a < 13, ∀ b < 13, g a = g b → a = b) ∧
      (∀ a < 13, ∀ b < 13, (object.graph.Adj (g a) (g b) ↔ (a + 1 = b ∨ b + 1 = a))) ∧
      P = (range 13).image g := by
  obtain ⟨⟨f⟩, hcard⟩ := hP
  let g : ℕ → object.Vertex := fun t => if h : t < 13 then (f ⟨t, h⟩).1 else (f ⟨0, by omega⟩).1
  have hg : ∀ t (h : t < 13), g t = (f ⟨t, h⟩).1 := fun t h => by simp [g, h]
  have hinj : ∀ a < 13, ∀ b < 13, g a = g b → a = b := by
    intro a ha b hb e
    rw [hg a ha, hg b hb] at e
    have := f.injective (Subtype.ext e)
    simpa using this
  have hadj : ∀ a < 13, ∀ b < 13,
      (object.graph.Adj (g a) (g b) ↔ (a + 1 = b ∨ b + 1 = a)) := by
    intro a ha b hb
    rw [hg a ha, hg b hb]
    have := f.map_rel_iff (a := ⟨a, ha⟩) (b := ⟨b, hb⟩)
    rw [SimpleGraph.pathGraph_adj] at this
    rw [← this]
    rfl
  refine ⟨g, hinj, hadj, ?_⟩
  symm
  apply eq_of_subset_of_card_le
  · intro v hv
    obtain ⟨t, ht, rfl⟩ := mem_image.1 hv
    rw [hg t (mem_range.1 ht)]
    exact (f ⟨t, mem_range.1 ht⟩).2
  · rw [card_image_of_injOn (fun a ha b hb e => hinj a (mem_range.1 ha) b (mem_range.1 hb) e),
      card_range]
    exact hcard.le

/-- **Window degrees.**  `|P| = 13`, `∑_{v∈P} #(N v ∩ P) = 24`, internal degrees in `{1,2}`. -/
theorem window_degrees {P : Finset object.Vertex} (hP : object.InducesWindow 13 P) :
    P.card = 13 ∧ ∑ v ∈ P, (object.graph.neighborFinset v ∩ P).card = 24 ∧
      ∀ v ∈ P, (object.graph.neighborFinset v ∩ P).card = 1 ∨
        (object.graph.neighborFinset v ∩ P).card = 2 := by
  have hcard := hP.2
  obtain ⟨g, hinj, hadj, rfl⟩ := window_seq hP
  have hinjOn : Set.InjOn g ((range 13 : Finset ℕ) : Set ℕ) :=
    fun a ha b hb e => hinj a (mem_range.1 ha) b (mem_range.1 hb) e
  have hloc : ∀ t < 13, (object.graph.neighborFinset (g t) ∩ (range 13).image g).card
      = ((range 13).filter (fun u => t + 1 = u ∨ u + 1 = t)).card := by
    intro t ht
    have : object.graph.neighborFinset (g t) ∩ (range 13).image g
        = ((range 13).filter (fun u => t + 1 = u ∨ u + 1 = t)).image g := by
      ext v
      simp only [mem_inter, SimpleGraph.mem_neighborFinset, mem_image, mem_filter, mem_range]
      constructor
      · rintro ⟨hv, u, hu, rfl⟩
        exact ⟨u, ⟨hu, (hadj t ht u hu).1 hv⟩, rfl⟩
      · rintro ⟨u, ⟨hu, hr⟩, rfl⟩
        exact ⟨(hadj t ht u hu).2 hr, u, hu, rfl⟩
    rw [this, card_image_of_injOn (hinjOn.mono (by intro x hx; simp at hx ⊢; exact hx.1))]
  refine ⟨hcard, ?_, ?_⟩
  · rw [sum_image hinjOn]
    rw [sum_congr rfl (fun t ht => hloc t (mem_range.1 ht))]
    decide
  · intro v hv
    obtain ⟨t, ht, rfl⟩ := mem_image.1 hv
    rw [hloc t (mem_range.1 ht)]
    have ht' := mem_range.1 ht
    interval_cases t <;> decide

end Bridge

/-! ## Quantities at a packing -/

section Quantities

/-- `h_W = |H ∩ W|`. -/
noncomputable def hubsW (object : Graph.FiniteObject.{u}) (packing : Finset (Finset object.Vertex)) :
    ℕ := ((hubs object).filter (fun v => ∃ P ∈ packing, v ∈ P)).card

/-- `h_R = |H ∩ R|`. -/
noncomputable def hubsR (object : Graph.FiniteObject.{u}) (packing : Finset (Finset object.Vertex)) :
    ℕ := ((hubs object).filter (fun v => ∀ P ∈ packing, v ∉ P)).card

/-- `ε = ∑_P #{hubs at an end of P}` (internal degree `1` in `P`). -/
noncomputable def hubEnds (object : Graph.FiniteObject.{u}) (packing : Finset (Finset object.Vertex)) :
    ℕ := ∑ P ∈ packing,
      ((P ∩ hubs object).filter (fun v => (object.graph.neighborFinset v ∩ P).card = 1)).card

/-- `I`: cubic vertices with no cubic neighbour inside their own window (all cubic `R`). -/
noncomputable def isoCubic (object : Graph.FiniteObject.{u}) (packing : Finset (Finset object.Vertex)) :
    ℕ := ((hubs object)ᶜ.filter (fun v => ∀ P ∈ packing, v ∈ P →
      (object.graph.neighborFinset v ∩ (P \ hubs object)).card = 0)).card

/-- `I_W`: the window part of `I`. -/
noncomputable def isoCubicW (object : Graph.FiniteObject.{u})
    (packing : Finset (Finset object.Vertex)) : ℕ :=
  ((hubs object)ᶜ.filter (fun v => (∃ P ∈ packing, v ∈ P) ∧ ∀ P ∈ packing, v ∈ P →
      (object.graph.neighborFinset v ∩ (P \ hubs object)).card = 0)).card

/-- The slack `4|S| − 6 − 2e(S)` of a vertex set of G. -/
noncomputable def slackG (object : Graph.FiniteObject.{u}) (S : Finset object.Vertex) : ℤ :=
  Hypostructure.Graph.HubWin.slack object.graph S

end Quantities

section Windows

variable {object : Graph.FiniteObject.{u}}

theorem mem_windowSupport {packing : Finset (Finset object.Vertex)} {v : object.Vertex} :
    v ∈ FiniteObject.windowSupport packing ↔ ∃ P ∈ packing, v ∈ P := by
  simp [FiniteObject.windowSupport]

theorem mem_remainderSupport {packing : Finset (Finset object.Vertex)} {v : object.Vertex} :
    v ∈ object.remainderSupport packing ↔ ∀ P ∈ packing, v ∉ P := by
  simp [FiniteObject.remainderSupport, mem_windowSupport]

theorem hubs_split (packing : Finset (Finset object.Vertex)) :
    hubsW object packing + hubsR object packing = (hubs object).card := by
  unfold hubsW hubsR
  rw [← card_filter_add_card_filter_not (s := hubs object) (fun v => ∃ P ∈ packing, v ∈ P)]
  congr 2; ext v; simp


theorem remainder_card {packing : Finset (Finset object.Vertex)}
    (valid : object.IsWindowPacking 13 packing) :
    (object.remainderSupport packing).card + 13 * packing.card = object.vertexCount := by
  have hW := object.windowSupport_card_eq valid
  have e : object.remainderSupport packing = univ \ FiniteObject.windowSupport packing := by
    ext v; simp [mem_remainderSupport, mem_windowSupport]
  rw [e, card_sdiff_of_subset (subset_univ _), card_univ, vertexCount_eq]
  have := card_le_univ (FiniteObject.windowSupport packing)
  have hW' : (FiniteObject.windowSupport packing).card = 13 * packing.card := by
    convert hW using 2
  omega

theorem iso_split {packing : Finset (Finset object.Vertex)} :
    isoCubic object packing
      = isoCubicW object packing
        + ((hubs object)ᶜ.filter (fun v => ∀ P ∈ packing, v ∉ P)).card := by
  unfold isoCubic isoCubicW
  rw [← card_filter_add_card_filter_not
    (s := (hubs object)ᶜ.filter (fun v => ∀ P ∈ packing, v ∈ P →
      (object.graph.neighborFinset v ∩ (P \ hubs object)).card = 0))
    (fun v => ∃ P ∈ packing, v ∈ P)]
  congr 2
  · ext v; simp only [mem_filter]; tauto
  · ext v; simp only [mem_filter, not_exists, not_and]
    constructor
    · rintro ⟨⟨h1, -⟩, h2⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨h1, fun P hP hv => absurd hv (h2 P hP)⟩, h2⟩

/-- Every cubic vertex of `R` is isolated: `#(R ∖ H) + h_R = r`. -/
theorem remainder_cubic_split (packing : Finset (Finset object.Vertex)) :
    ((hubs object)ᶜ.filter (fun v => ∀ P ∈ packing, v ∉ P)).card + hubsR object packing
      = (object.remainderSupport packing).card := by
  have h := card_filter_add_card_filter_not (s := object.remainderSupport packing)
    (fun v => v ∉ hubs object)
  rw [← h]
  unfold hubsR
  congr 2
  · ext v; simp [mem_remainderSupport, and_comm]
  · ext v; simp [mem_remainderSupport, and_comm]

end Windows

/-! ## Item 1 -/

section Item1

variable (object : Graph.FiniteObject.{u})

/-- **Hub–window budget** for any window packing of order 13 (dart identity ⊕ induced windows
⊕ independent hubs ⊕ every cubic vertex has a cubic neighbour):
`24ν + 2ε + I + 6|H| + σ ≤ 3n + 4h_W`. -/
theorem hubWindowBudget (packing : Finset (Finset object.Vertex))
    (base : MinimumDegreeAtLeast 3 object)
    (noProper : NoProperCubic object)
    (slack : SlackIndependent object)
    (valid : object.IsWindowPacking 13 packing) :
    24 * packing.card + 2 * hubEnds object packing + isoCubic object packing
      + 6 * (hubs object).card
      + object.degreeSurplus 3
      ≤ 3 * object.vertexCount + 4 * hubsW object packing := by
  have hind := hubs_indep base slack
  have hcub : ∀ v ∉ hubs object, object.graph.degree v = 3 := fun v hv => cubic_of_not_hub hv
  have hdegH : ∀ h ∈ hubs object, 3 ≤ object.graph.degree h := fun h _ => deg_ge base h
  have hL := Hypostructure.Graph.HubWin.intL_sigma object.graph (hubs object) hind hcub hdegH
  have hσ := degreeSurplus_eq base
  have hcn : ∀ v ∉ hubs object, ∃ u, object.graph.Adj v u ∧ u ∉ hubs object := by
    intro v hv
    obtain ⟨u, hu, hu3⟩ := cubic_nbr base noProper (cubic_of_not_hub hv)
    exact ⟨u, hu, by rw [mem_hubs]; omega⟩
  have hdisj : ∀ P ∈ packing, ∀ Q ∈ packing, P ≠ Q → Disjoint (id P) (id Q) :=
    fun P hP Q hQ hne => valid.2 P hP Q hQ hne
  have hsplit := Hypostructure.Graph.HubWin.LL_split object.graph (hubs object) packing id hdisj hcn
  have hwin : ∀ P ∈ packing, ∑ v ∈ P \ hubs object,
      (object.graph.neighborFinset v ∩ (P \ hubs object)).card + 4 * (P ∩ hubs object).card
      = 24 + 2 * ((P ∩ hubs object).filter
          (fun v => (object.graph.neighborFinset v ∩ P).card = 1)).card := by
    intro P hP
    obtain ⟨-, h24, h12⟩ := window_degrees (valid.1 P hP)
    exact Hypostructure.Graph.HubWin.window_LL_exact object.graph (hubs object) P hind h24 h12
  have hsum := sum_congr rfl hwin
  rw [sum_add_distrib, sum_add_distrib, sum_const, smul_eq_mul, ← mul_sum, ← mul_sum] at hsum
  have hWc : ∑ P ∈ packing, (P ∩ hubs object).card = hubsW object packing := by
    unfold hubsW
    rw [← card_biUnion]
    · congr 1; ext v; simp only [mem_biUnion, mem_inter, mem_filter]
      constructor
      · rintro ⟨P, hP, hv, hh⟩; exact ⟨hh, P, hP, hv⟩
      · rintro ⟨hh, P, hP, hv⟩; exact ⟨P, hP, hv, hh⟩
    · intro P hP Q hQ hne
      exact Disjoint.mono inter_subset_left inter_subset_left (valid.2 P hP Q hQ hne)
  rw [hWc] at hsum
  have hn := vertexCount_eq object
  unfold hubEnds isoCubic
  simp only [id] at hsplit
  omega

/-- **Item 1, `(r, s)` form**: `r = |R|`, `s = n − σ`, `h = h_W + h_R`:
`2h + 3h_R + 2ε + I_W ≤ 2ν + r + s`. -/
theorem hubBudget_rs (packing : Finset (Finset object.Vertex))
    (base : MinimumDegreeAtLeast 3 object)
    (noProper : NoProperCubic object)
    (slack : SlackIndependent object)
    (valid : object.IsWindowPacking 13 packing) :
    2 * ((hubs object).card : ℤ)
      + 3 * hubsR object packing + 2 * hubEnds object packing + isoCubicW object packing
      ≤ 2 * packing.card + (object.remainderSupport packing).card
        + ((object.vertexCount : ℤ) - object.degreeSurplus 3) := by
  have h1 := hubWindowBudget object packing base noProper slack valid
  have hr := remainder_card valid
  have hsp := hubs_split (object := object) packing
  have hiso := iso_split (object := object) (packing := packing)
  have hRc := remainder_cubic_split (object := object) packing
  omega

/-- **All windows' `L–L` path darts**: `∑_P #LL(P) + 4h_W = 24ν + 2ε`. -/
theorem windows_LL_sum (packing : Finset (Finset object.Vertex))
    (base : MinimumDegreeAtLeast 3 object)
    (slack : SlackIndependent object)
    (valid : object.IsWindowPacking 13 packing) :
    ∑ P ∈ packing, ∑ v ∈ P \ hubs object,
        (object.graph.neighborFinset v ∩ (P \ hubs object)).card + 4 * hubsW object packing
      = 24 * packing.card + 2 * hubEnds object packing := by
  have hind := hubs_indep base slack
  have hwin : ∀ P ∈ packing, ∑ v ∈ P \ hubs object,
      (object.graph.neighborFinset v ∩ (P \ hubs object)).card + 4 * (P ∩ hubs object).card
      = 24 + 2 * ((P ∩ hubs object).filter
          (fun v => (object.graph.neighborFinset v ∩ P).card = 1)).card := by
    intro P hP
    obtain ⟨-, h24, h12⟩ := window_degrees (valid.1 P hP)
    exact Hypostructure.Graph.HubWin.window_LL_exact object.graph (hubs object) P hind h24 h12
  have hsum := sum_congr rfl hwin
  rw [sum_add_distrib, sum_add_distrib, sum_const, smul_eq_mul, ← mul_sum, ← mul_sum] at hsum
  have hWc : ∑ P ∈ packing, (P ∩ hubs object).card = hubsW object packing := by
    unfold hubsW
    rw [← card_biUnion]
    · congr 1; ext v; simp only [mem_biUnion, mem_inter, mem_filter]
      constructor
      · rintro ⟨P, hP, hv, hh⟩; exact ⟨hh, P, hP, hv⟩
      · rintro ⟨hh, P, hP, hv⟩; exact ⟨P, hP, hv, hh⟩
    · intro P hP Q hQ hne
      exact Disjoint.mono inter_subset_left inter_subset_left (valid.2 P hP Q hQ hne)
  rw [hWc] at hsum
  unfold hubEnds
  omega

/-- **Item 2 (exact).**  The ledger's `lowDarts` is `2e(L)`, and the `L–L` darts off the
window paths number exactly `2X = 2ν + 2r + s − 2h − 4h_R − 2ε`. -/
theorem offPath_identity (packing : Finset (Finset object.Vertex))
    (base : MinimumDegreeAtLeast 3 object)
    (slack : SlackIndependent object)
    (valid : object.IsWindowPacking 13 packing)
    (dart : object.degreeSurplus 3 + 2 * 3 * (hubs object).card + lowDartCount object = 3 * object.vertexCount) :
    (lowDartCount object : ℤ)
        - ∑ P ∈ packing, ∑ v ∈ P \ hubs object,
            ((object.graph.neighborFinset v ∩ (P \ hubs object)).card : ℤ)
      = 2 * packing.card + 2 * (object.remainderSupport packing).card
        + ((object.vertexCount : ℤ) - object.degreeSurplus 3)
        - 2 * ((hubs object).card : ℤ)
        - 4 * hubsR object packing - 2 * hubEnds object packing := by
  have hind := hubs_indep base slack
  have hcub : ∀ v ∉ hubs object, object.graph.degree v = 3 := fun v hv => cubic_of_not_hub hv
  have hdegH : ∀ h ∈ hubs object, 3 ≤ object.graph.degree h := fun h _ => deg_ge base h
  have hL := Hypostructure.Graph.HubWin.intL_sigma object.graph (hubs object) hind hcub hdegH
  have hσ := degreeSurplus_eq base
  have hS := windows_LL_sum object packing base slack valid
  have hr := remainder_card valid
  have hsp := hubs_split (object := object) packing
  have hn := vertexCount_eq object
  have d : object.degreeSurplus 3 + 2 * 3 * (hubs object).card
      + lowDartCount object = 3 * object.vertexCount := dart
  have e : (∑ P ∈ packing, ∑ v ∈ P \ hubs object,
      ((object.graph.neighborFinset v ∩ (P \ hubs object)).card : ℤ))
      = ((∑ P ∈ packing, ∑ v ∈ P \ hubs object,
        (object.graph.neighborFinset v ∩ (P \ hubs object)).card : ℕ) : ℤ) := by push_cast; rfl
  rw [e]
  omega

end Item1

/-! ## Item 3: the remainder slack and hanging windows -/

theorem boundary_eq (object : Graph.FiniteObject.{u}) (S : Finset object.Vertex) :
    ∑ u ∈ S, ((object.graph.neighborFinset u \ S).card : ℤ) = object.boundaryIncidence S := by
  unfold FiniteObject.boundaryIncidence
  push_cast
  apply sum_congr rfl; intro u _
  have e : object.internalDegree S u = (object.graph.neighborFinset u ∩ S).card := by
    unfold FiniteObject.internalDegree; congr 1
  have h1 := card_sdiff_add_card_inter (object.graph.neighborFinset u) S
  rw [object.graph.card_neighborFinset_eq_degree] at h1
  have h2 : object.internalDegree S u ≤ object.degree u := object.internalDegree_le_degree S u
  rw [e] at h2 ⊢
  change ((object.graph.neighborFinset u \ S).card : ℤ)
    = ((object.graph.degree u - (object.graph.neighborFinset u ∩ S).card : ℕ) : ℤ)
  rw [Nat.cast_sub (by change _ ≤ object.graph.degree u at h2; exact h2)]
  omega

theorem surplus_eq (object : Graph.FiniteObject.{u}) (base : MinimumDegreeAtLeast 3 object)
    (S : Finset object.Vertex) :
    ∑ u ∈ S, ((object.graph.degree u : ℤ) - 3) = object.ambientSurplus S 3 := by
  unfold FiniteObject.ambientSurplus
  push_cast
  apply sum_congr rfl; intro u _
  have := deg_ge base u
  change ((object.graph.degree u : ℤ) - 3) = ((object.graph.degree u - 3 : ℕ) : ℤ)
  omega

/-- **The remainder slack** (slack formula ⊕ join identity ⊕ `σ = σ_W + σ_R`):
`slack(R) = s + 2ν + 2σ_W − 2e× − 6`, with `s = n − σ` and `2e× = |crossWindowIncidences|`. -/
theorem remainderSlack (object : Graph.FiniteObject.{u}) (packing : Finset (Finset object.Vertex))
    (base : MinimumDegreeAtLeast 3 object) (valid : object.IsWindowPacking 13 packing)
    (join : (object.windowRemainderIncidences packing).card + (2 * (13 - 1) * packing.card
      + (object.crossWindowIncidences packing).card)
      = 3 * (13 * packing.card) + object.ambientSurplus (FiniteObject.windowSupport packing) 3) :
    slackG object (object.remainderSupport packing)
      = ((object.vertexCount : ℤ) - object.degreeSurplus 3) + 2 * packing.card
        + 2 * object.ambientSurplus (FiniteObject.windowSupport packing) 3
        - (object.crossWindowIncidences packing).card - 6 := by
  have hf := Hypostructure.Graph.HubWin.slack_formula object.graph (object.remainderSupport packing)
  rw [boundary_eq, surplus_eq object base] at hf
  rw [object.card_windowRemainderIncidences] at join
  have hsplit := object.ambientSurplus_windowSupport_add_remainderSupport packing 3
    (fun v => deg_ge base v)
  have hr := remainder_card valid
  unfold slackG
  rw [hf]
  push_cast
  omega

/-- **Hanging windows.**  `Ws ⊆ packing` disjoint from `K`, every edge leaving each window
of `Ws` going into `K`, `K ∪ ⋃Ws ≠ V`: `∑_{P ∈ Ws} (2 + 2σ_P) ≤ slack(K)`. -/
theorem hanging (object : Graph.FiniteObject.{u}) (packing : Finset (Finset object.Vertex))
    (base : MinimumDegreeAtLeast 3 object)
    (noProper : NoProperCubic object)
    (valid : object.IsWindowPacking 13 packing)
    (K : Finset object.Vertex) (Ws : Finset (Finset object.Vertex))
    (hWs : Ws ⊆ packing) (hne : Ws.Nonempty) (hK : ∀ P ∈ Ws, Disjoint K P)
    (hout : ∀ P ∈ Ws, ∀ v ∈ P, object.graph.neighborFinset v ⊆ K ∪ P)
    (hproper : K ∪ Ws.biUnion id ≠ univ) :
    ∑ P ∈ Ws, (2 + 2 * (object.ambientSurplus P 3 : ℤ)) ≤ slackG object K := by
  have hb := Hypostructure.Graph.HubWin.hanging_bound object.graph K id (fun v => deg_ge base v) (density noProper)
    Ws hne (fun P hP Q hQ h => valid.2 P (hWs hP) Q (hWs hQ) h) hK
    (fun P hP => (window_degrees (valid.1 P (hWs hP))).1)
    (fun P hP => (window_degrees (valid.1 P (hWs hP))).2.1) hout hproper
  unfold slackG
  simp only [id] at hb
  have e : ∀ P ∈ Ws, (2 + 2 * (object.ambientSurplus P 3 : ℤ))
      = 2 + 2 * ∑ v ∈ P, ((object.graph.degree v : ℤ) - 3) := by
    intro P _; rw [surplus_eq object base]
  rw [sum_congr rfl e]
  exact hb


/-! ## Windows against the big hubs -/

section

variable {object : Graph.FiniteObject.{u}}

/-- `Σ_P |A ∩ P| ≤ |A|` over a packing (disjoint members). -/
theorem sum_inter_le (packing : Finset (Finset object.Vertex))
    (hdisj : ∀ P ∈ packing, ∀ Q ∈ packing, P ≠ Q → Disjoint P Q) (A : Finset object.Vertex) :
    ∑ P ∈ packing, (A ∩ P).card ≤ A.card := by
  classical
  rw [← card_biUnion (fun P hP Q hQ hne =>
    Disjoint.mono inter_subset_right inter_subset_right (hdisj P hP Q hQ hne))]
  apply card_le_card
  intro v hv
  obtain ⟨P, -, hv⟩ := mem_biUnion.1 hv
  exact (mem_inter.1 hv).1

/-- `|A| ≤ Σ_P |A ∩ P| + |R|`. -/
theorem card_le_windows_add_remainder (packing : Finset (Finset object.Vertex))
    (hdisj : ∀ P ∈ packing, ∀ Q ∈ packing, P ≠ Q → Disjoint P Q) (A : Finset object.Vertex) :
    A.card ≤ ∑ P ∈ packing, (A ∩ P).card + (object.remainderSupport packing).card := by
  classical
  rw [← card_biUnion (fun P hP Q hQ hne =>
    Disjoint.mono inter_subset_right inter_subset_right (hdisj P hP Q hQ hne))]
  calc A.card ≤ (packing.biUnion (fun P => A ∩ P) ∪ object.remainderSupport packing).card := by
        apply card_le_card
        intro v hv
        by_cases hW : ∃ P ∈ packing, v ∈ P
        · obtain ⟨P, hP, hvP⟩ := hW
          exact mem_union_left _ (mem_biUnion.2 ⟨P, hP, mem_inter.2 ⟨hv, hvP⟩⟩)
        · push Not at hW
          exact mem_union_right _ (mem_remainderSupport.2 hW)
    _ ≤ _ := card_union_le _ _

/-- A window's `U`-positions against `X2 ∪ B`, in Finset form. -/
theorem window_U_card {P : Finset object.Vertex} (hP : object.InducesWindow 13 P)
    (U B X2 : Finset object.Vertex)
    (hX2 : ∀ x, x ∉ B → ∀ a b, a ≠ b → a ∈ U → b ∈ U → object.graph.Adj x a →
      object.graph.Adj x b → x ∈ X2) :
    (U ∩ P).card ≤ 7 + (X2 ∩ P).card + (B ∩ P).card := by
  classical
  obtain ⟨g, hinj, hadj, rfl⟩ := window_seq hP
  have hinjOn : Set.InjOn g ((range 13 : Finset ℕ) : Set ℕ) :=
    fun a ha b hb e => hinj a (mem_range.1 ha) b (mem_range.1 hb) e
  have h := Hypostructure.Graph.HubWin.window_U object.graph U B X2 g hinj
    (fun i hi => (hadj i (by omega) (i + 1) (by omega)).2 (Or.inl rfl)) hX2
  have e1 : ∀ A : Finset object.Vertex,
      (A ∩ (range 13).image g).card = ((range 13).filter (fun t => g t ∈ A)).card := by
    intro A
    rw [← card_image_of_injOn (hinjOn.mono (by intro x hx; simp at hx ⊢; exact hx.1))]
    congr 1; ext v; simp only [mem_inter, mem_image, mem_filter, mem_range]
    constructor
    · rintro ⟨hv, t, ht, rfl⟩; exact ⟨t, ⟨ht, hv⟩, rfl⟩
    · rintro ⟨t, ⟨ht, hv⟩, rfl⟩; exact ⟨hv, t, ht, rfl⟩
  rw [e1 U, e1 X2, e1 B]
  have e2 := e1 (X2 ∪ B)
  have e3 : ((X2 ∪ B) ∩ (range 13).image g).card ≤
      (X2 ∩ (range 13).image g).card + (B ∩ (range 13).image g).card := by
    rw [union_inter_distrib_right]; exact card_union_le _ _
  rw [e1 X2, e1 B] at e3
  omega

end

/-- The arithmetic of the window–`U` bound: per-window sums, `|X2| ≤ 12(k² − k)`, Bonferroni
`2∑_B deg + k ≤ 2|U| + k²`, `∑_H deg = 3h + σ`, `∑_H deg + 4k = ∑_B deg + 4h`,
`r + 13ν = n`, `σ + s = n` give `12ν + 31k ≤ 2s + 2h + 25k²`. -/
theorem windowU_arith (ν r n s σ h k kk U X2 a x bw SB SH : ℕ)
    (hsum : a ≤ ν * 7 + x + bw) (hX : x ≤ X2) (hB : bw ≤ k) (hU : U ≤ a + r)
    (hr : r + 13 * ν = n) (hX2c : X2 ≤ 12 * (kk - k)) (hkk : k ≤ kk)
    (hbon : 2 * SB + k ≤ 2 * U + kk) (hSH : SH = 3 * h + σ) (hsplit : SH + 4 * k = SB + 4 * h)
    (hs : σ + s = n) : 12 * ν + 31 * k ≤ 2 * s + 2 * h + 25 * kk := by
  omega


/-- Arithmetic of the few-windows bound.  `t_sum`, `t_upper`, `|X2| ≤ 12(k² − k)`,
Bonferroni, the hub sums, item 1 (`2h + 3h_R + 2ε + I_W ≤ 2ν + r + s`), `n = r + 13ν`,
`σ + s = n`, `|Bᶜ| + k = n` give `22ν + 93k + 6h_R + 4ε + 2I_W ≤ 6s + 75k²`. -/
theorem fewWindows_arith (ν r n s σ h k kk U X2 T SB SH hR ε IW Bc : ℕ)
    (htsum : T + SB = 3 * U) (htup : T ≤ Bc + 3 * X2) (hBc : Bc + k = n)
    (hX2c : X2 ≤ 12 * (kk - k)) (hkk : k ≤ kk) (hbon : 2 * SB + k ≤ 2 * U + kk)
    (hSH : SH = 3 * h + σ) (hsplit : SH + 4 * k = SB + 4 * h)
    (hitem1 : 2 * (h : ℤ) + 3 * hR + 2 * ε + IW ≤ 2 * ν + r + ((n : ℤ) - σ))
    (hr : r + 13 * ν = n) (hs : σ + s = n) :
    22 * (ν : ℤ) + 93 * k + 6 * hR + 4 * ε + 2 * IW ≤ 6 * s + 75 * kk := by
  omega


/-- Arithmetic of the V-shape/hub relation (no window input). -/
theorem vshape_arith (n σ h k kk U X2 T SB SH Bc : ℕ)
    (htsum : T + SB = 3 * U) (htup : T ≤ Bc + 3 * X2) (hBc : Bc + k = n)
    (hX2c : X2 ≤ 12 * (kk - k)) (hkk : k ≤ kk) (hbon : 2 * SB + k ≤ 2 * U + kk)
    (hSH : SH = 3 * h + σ) (hsplit : SH + 4 * k = SB + 4 * h) :
    4 * σ + 93 * k ≤ 2 * n + 75 * kk + 4 * h := by
  omega



/-! ### Joint hypotheses in Mathlib form -/

section JointHyps

variable {object : Graph.FiniteObject.{u}}

theorem jmin (base : MinimumDegreeAtLeast 3 object) :
    ∀ v, 3 ≤ @SimpleGraph.degree _ object.graph v
      (@SimpleGraph.neighborSetFintype _ _ _
        (fun a b => Classical.propDecidable (object.graph.Adj a b)) v) := by
  intro v; convert deg_ge (base) v using 2

theorem jind (base : MinimumDegreeAtLeast 3 object) (slack : SlackIndependent object) :
    ∀ a b, 4 ≤ @SimpleGraph.degree _ object.graph a
      (@SimpleGraph.neighborSetFintype _ _ _
        (fun a b => Classical.propDecidable (object.graph.Adj a b)) a) →
      4 ≤ @SimpleGraph.degree _ object.graph b
      (@SimpleGraph.neighborSetFintype _ _ _
        (fun a b => Classical.propDecidable (object.graph.Adj a b)) b) →
      ¬ object.graph.Adj a b := by
  intro a b ha hb
  have ha' : 4 ≤ object.graph.degree a := by convert ha using 2
  have hb' : 4 ≤ object.graph.degree b := by convert hb using 2
  exact hubs_indep base (slack) a (by rw [mem_hubs]; omega) b (by rw [mem_hubs]; omega)

theorem jC4 (avoid : ¬ HasCycleWithLength Core.DyadicLength.PowerOfTwoLength object) : Hypostructure.Graph.JointSystem.C4Free object.graph :=
  fun a b c c' h1 h2 h3 h4 h5 => c4Free (avoid) a b c c' h1 h2 h3 h4 h5

theorem jC8 (avoid : ¬ HasCycleWithLength Core.DyadicLength.PowerOfTwoLength object) : Hypostructure.Graph.JointSystem.NoCycleLen object.graph 8 :=
  fun f hf hadj => noC8 (avoid) f hf hadj

theorem Hset_card_eq (base : MinimumDegreeAtLeast 3 object) :
    (Hypostructure.Graph.JointSystem.Hset object.graph).card
      = (hubs object).card := by
  congr 1; ext v
  simp only [Hypostructure.Graph.JointSystem.Hset, mem_filter, mem_univ, true_and, mem_hubs]
  have := deg_ge base v
  constructor
  · intro h4 h3
    have : 4 ≤ object.graph.degree v := by convert h4 using 2
    omega
  · intro h3
    have : 4 ≤ object.graph.degree v := by omega
    convert this using 2

theorem sigma_eq (base : MinimumDegreeAtLeast 3 object) :
    Hypostructure.Graph.JointSystem.sigma object.graph = object.degreeSurplus 3 := by
  rw [degreeSurplus_eq base, Hypostructure.Graph.JointSystem.sigma, hubs, sum_filter]
  apply sum_congr rfl; intro v _
  have hv := deg_ge base v
  split_ifs with h
  · congr 1; convert rfl
  · push Not at h
    have : object.graph.degree v - 3 = 0 := by omega
    rw [← this]; congr 1; convert rfl

end JointHyps

section BigHubs

variable {object : Graph.FiniteObject.{u}}

/-- **Windows × big hubs × V-shapes.**  With `k = |B|`, `h = |H|`,
`s = n − σ` (`Hypostructure.Graph.JointSystem.sigma`):
`12ν + 31k ≤ 2s + 2h + 25k²`. -/
theorem windowU {packing : Finset (Finset object.Vertex)}
    (base : MinimumDegreeAtLeast 3 object)
    (slack : SlackIndependent object)
    (avoid : ¬ HasCycleWithLength Core.DyadicLength.PowerOfTwoLength object)
    (valid : object.IsWindowPacking 13 packing)
    (s : ℕ) (hs : Hypostructure.Graph.JointSystem.sigma object.graph + s = Fintype.card object.Vertex) :
    12 * packing.card + 31 * (Hypostructure.Graph.JointSystem.Bset object.graph).card
      ≤ 2 * s + 2 * (Hypostructure.Graph.JointSystem.Hset object.graph).card
        + 25 * ((Hypostructure.Graph.JointSystem.Bset object.graph).card
          * (Hypostructure.Graph.JointSystem.Bset object.graph).card) := by
  have base := base
  have avoid := avoid
  have valid := valid
  have hmin : ∀ v, 3 ≤ object.graph.degree v := fun v => deg_ge base v
  have hind : ∀ a b, 4 ≤ object.graph.degree a → 4 ≤ object.graph.degree b →
      ¬ object.graph.Adj a b := fun a b ha hb =>
    hubs_indep base (slack) a (by rw [mem_hubs]; omega) b (by rw [mem_hubs]; omega)
  have hC4 : Hypostructure.Graph.JointSystem.C4Free object.graph := fun a b c c' h1 h2 h3 h4 h5 =>
    c4Free avoid a b c c' h1 h2 h3 h4 h5
  have hC8 : Hypostructure.Graph.JointSystem.NoCycleLen object.graph 8 := fun f hf hadj =>
    noC8 avoid f hf hadj
  have hmin' : ∀ v, 3 ≤ @SimpleGraph.degree _ object.graph v
      (@SimpleGraph.neighborSetFintype _ _ _ (Classical.decRel _) v) := by
    intro v; convert hmin v using 2
  have hind' : ∀ a b, 4 ≤ @SimpleGraph.degree _ object.graph a
      (@SimpleGraph.neighborSetFintype _ _ _ (Classical.decRel _) a) →
      4 ≤ @SimpleGraph.degree _ object.graph b
      (@SimpleGraph.neighborSetFintype _ _ _ (Classical.decRel _) b) →
      ¬ object.graph.Adj a b := by
    intro a b ha hb; exact hind a b (by convert ha using 2) (by convert hb using 2)
  have hX2 : ∀ x, x ∉ Hypostructure.Graph.JointSystem.Bset object.graph → ∀ a b, a ≠ b →
      a ∈ Hypostructure.Graph.JointSystem.Uset object.graph → b ∈ Hypostructure.Graph.JointSystem.Uset object.graph →
      object.graph.Adj x a → object.graph.Adj x b →
      x ∈ Hypostructure.Graph.JointSystem.X2 object.graph := by
    intro x hx a b hab ha hb hxa hxb
    simp only [Hypostructure.Graph.JointSystem.X2, mem_filter, mem_compl]
    refine ⟨fun h => hx (by simpa [Hypostructure.Graph.JointSystem.Bset] using h), ?_⟩
    refine le_trans (le_of_eq (card_pair hab).symm) (card_le_card ?_)
    intro y hy
    simp only [mem_insert, mem_singleton] at hy
    rcases hy with rfl | rfl
    · simp only [mem_inter, SimpleGraph.mem_neighborFinset]; exact ⟨hxa, ha⟩
    · simp only [mem_inter, SimpleGraph.mem_neighborFinset]; exact ⟨hxb, hb⟩
  have hdisj : ∀ P ∈ packing, ∀ Q ∈ packing, P ≠ Q → Disjoint P Q :=
    fun P hP Q hQ hne => valid.2 P hP Q hQ hne
  have hper : ∀ P ∈ packing,
      (Hypostructure.Graph.JointSystem.Uset object.graph ∩ P).card
        ≤ 7 + (Hypostructure.Graph.JointSystem.X2 object.graph ∩ P).card
          + (Hypostructure.Graph.JointSystem.Bset object.graph ∩ P).card :=
    fun P hP => window_U_card (valid.1 P hP) _ _ _ hX2
  have hsum := sum_le_sum hper
  rw [sum_add_distrib, sum_add_distrib, sum_const, smul_eq_mul] at hsum
  have hX := sum_inter_le packing hdisj (Hypostructure.Graph.JointSystem.X2 object.graph)
  have hB := sum_inter_le packing hdisj (Hypostructure.Graph.JointSystem.Bset object.graph)
  have hU := card_le_windows_add_remainder packing hdisj
    (Hypostructure.Graph.JointSystem.Uset object.graph)
  have hr := remainder_card valid
  rw [vertexCount_eq] at hr
  exact windowU_arith _ _ _ s _ _ _ _ _ _ _ _ _ _ _ hsum hX hB hU hr
    (Hypostructure.Graph.JointSystem.X2_card hmin' hind' hC4 hC8) (Nat.le_mul_self _)
    (Hypostructure.Graph.JointSystem.bonferroni hC4 _) (Hypostructure.Graph.JointSystem.hub_sum hmin')
    (Hypostructure.Graph.JointSystem.hub_sum_split (G := object.graph)) hs

/-- **Combined with the hub budget**: `23ν + 31k ≤ n + 3s + 25k²`. -/
theorem windowU_rs {packing : Finset (Finset object.Vertex)}
    (base : MinimumDegreeAtLeast 3 object) (noProper : NoProperCubic object)
    (slack : SlackIndependent object)
    (avoid : ¬ HasCycleWithLength Core.DyadicLength.PowerOfTwoLength object)
    (valid : object.IsWindowPacking 13 packing)
    (s : ℕ) (hs : Hypostructure.Graph.JointSystem.sigma object.graph + s = Fintype.card object.Vertex) :
    23 * packing.card + 31 * (Hypostructure.Graph.JointSystem.Bset object.graph).card
      ≤ Fintype.card object.Vertex + 3 * s
        + 25 * ((Hypostructure.Graph.JointSystem.Bset object.graph).card
          * (Hypostructure.Graph.JointSystem.Bset object.graph).card) := by
  have h1 := windowU base slack avoid valid s hs
  have h2 := hubBudget_rs object packing base noProper slack valid
  have hr := remainder_card valid
  have hn := vertexCount_eq object
  have hH := Hset_card_eq base
  have hσ := sigma_eq base
  have hRc := remainder_cubic_split (object := object) packing
  have hsp := hubs_split (object := object) packing
  rw [hH] at h1
  rw [hσ] at hs
  omega


/-- **Few windows** (joint: V-shapes/no `C₈` ⊕ no `C₄` ⊕ noProperBaseline ⊕
slackIndependent ⊕ the canonical windows ⊕ the dart identity):
`22ν + 93k + 6h_R + 4ε + 2I_W ≤ 6s + 75k²`, `k = |B|`, `s = n − σ`.  In particular
`ν ≤ (6s + 75k²)/22 ≤ (6s + 18.75 s²)/22`: the canonical windows cover `O(s²)` vertices. -/
theorem fewWindows {packing : Finset (Finset object.Vertex)}
    (base : MinimumDegreeAtLeast 3 object) (noProper : NoProperCubic object)
    (slack : SlackIndependent object)
    (avoid : ¬ HasCycleWithLength Core.DyadicLength.PowerOfTwoLength object)
    (valid : object.IsWindowPacking 13 packing)
    (s : ℕ) (hs : Hypostructure.Graph.JointSystem.sigma object.graph + s = Fintype.card object.Vertex) :
    22 * (packing.card : ℤ) + 93 * (Hypostructure.Graph.JointSystem.Bset object.graph).card
      + 6 * hubsR object packing
      + 4 * hubEnds object packing
      + 2 * isoCubicW object packing
      ≤ 6 * s + 75 * ((Hypostructure.Graph.JointSystem.Bset object.graph).card
          * (Hypostructure.Graph.JointSystem.Bset object.graph).card : ℕ) := by
  have hmin := jmin base
  have hind := jind base slack
  have htsum := Hypostructure.Graph.JointSystem.t_sum hmin hind
  have htup := Hypostructure.Graph.JointSystem.t_upper (G := object.graph)
  have hX2c := Hypostructure.Graph.JointSystem.X2_card hmin hind (jC4 avoid) (jC8 avoid)
  have hbon := Hypostructure.Graph.JointSystem.bonferroni (jC4 avoid) (Hypostructure.Graph.JointSystem.Bset object.graph)
  have hSH := Hypostructure.Graph.JointSystem.hub_sum hmin
  have hsplit := Hypostructure.Graph.JointSystem.hub_sum_split (G := object.graph)
  have h1 := hubBudget_rs object packing base noProper slack valid
  have hr := remainder_card (valid)
  have hn := vertexCount_eq object
  have hH := Hset_card_eq base
  have hσ := sigma_eq base
  simp only [card_compl] at htup
  have hBc := Nat.sub_add_cancel (card_le_univ (Hypostructure.Graph.JointSystem.Bset object.graph))
  rw [← hH, ← hσ, hn] at h1
  rw [hn] at hr
  exact fewWindows_arith _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ htsum htup hBc hX2c
    (Nat.le_mul_self _) hbon hSH hsplit h1 hr hs


/-- **The V-shape/hub relation** (`t_sum ⊕ t_upper ⊕ |X2| ≤ 12(k²−k) ⊕
Bonferroni ⊕ hub sums`): `4σ + 93k ≤ 2n + 75k² + 4h`.  With `5h + σ ≤ 2n` this is
`Hypostructure.Graph.JointSystem.high_surplus_bound`; with item 1 it is `fewWindows`. -/
theorem vshape (base : MinimumDegreeAtLeast 3 object)
    (slack : SlackIndependent object)
    (avoid : ¬ HasCycleWithLength Core.DyadicLength.PowerOfTwoLength object) :
    4 * Hypostructure.Graph.JointSystem.sigma object.graph + 93 * (Hypostructure.Graph.JointSystem.Bset object.graph).card
      ≤ 2 * Fintype.card object.Vertex
        + 75 * ((Hypostructure.Graph.JointSystem.Bset object.graph).card
          * (Hypostructure.Graph.JointSystem.Bset object.graph).card)
        + 4 * (Hypostructure.Graph.JointSystem.Hset object.graph).card := by
  have hmin := jmin base
  have hind := jind base slack
  have htsum := Hypostructure.Graph.JointSystem.t_sum hmin hind
  have htup := Hypostructure.Graph.JointSystem.t_upper (G := object.graph)
  have hX2c := Hypostructure.Graph.JointSystem.X2_card hmin hind (jC4 avoid) (jC8 avoid)
  have hbon := Hypostructure.Graph.JointSystem.bonferroni (jC4 avoid) (Hypostructure.Graph.JointSystem.Bset object.graph)
  have hSH := Hypostructure.Graph.JointSystem.hub_sum hmin
  have hsplit := Hypostructure.Graph.JointSystem.hub_sum_split (G := object.graph)
  simp only [card_compl] at htup
  have hBc := Nat.sub_add_cancel (card_le_univ (Hypostructure.Graph.JointSystem.Bset object.graph))
  exact vshape_arith _ _ _ _ _ _ _ _ _ _ _ htsum htup hBc hX2c (Nat.le_mul_self _) hbon hSH hsplit

end BigHubs


/-! ## The facts at the object -/

section Facts

variable {object : Graph.FiniteObject.{u}}

/-- No accepted cycle under a dyadic length law is no dyadic cycle. -/
theorem avoid_dyadic {LengthOK : Nat → Prop} (avoid : ¬ HasCycleWithLength LengthOK object)
    (law : ∀ length, LengthOK length ↔ Core.DyadicLength.PowerOfTwoLength length) :
    ¬ HasCycleWithLength Core.DyadicLength.PowerOfTwoLength object := by
  rintro ⟨c⟩
  exact avoid ⟨⟨c.vertex, c.walk, c.isCycle, (law _).2 c.length_ok⟩⟩

/-- `ProperTwoLow` in `JointSystem`'s spelling. -/
theorem jdeg (noProper : NoProperCubic object) :
    Hypostructure.Graph.JointSystem.ProperTwoLow object.graph := by
  intro S hS hne
  obtain ⟨v, hv, hle⟩ := properTwoLow noProper S hS hne
  refine ⟨v, hv, le_trans (le_of_eq ?_) hle⟩
  congr 1; ext w; simp [SimpleGraph.mem_neighborFinset]

/-- Every edge has an endpoint of degree `3` (independent high vertices). -/
theorem tight_of_slack (base : MinimumDegreeAtLeast 3 object) (slack : SlackIndependent object) :
    ∀ dart : object.graph.Dart, object.degree dart.fst = 3 ∨ object.degree dart.snd = 3 := by
  intro d
  have h1 : 3 ≤ object.degree d.fst := deg_ge base d.fst
  have h2 : 3 ≤ object.degree d.snd := deg_ge base d.snd
  by_contra hne
  push Not at hne
  exact slack d.fst d.snd (by omega) (by omega) d.adj

/-- The dart identity `σ + 6|H| + lowDarts = 3n`. -/
theorem dart_identity (base : MinimumDegreeAtLeast 3 object) (slack : SlackIndependent object) :
    object.degreeSurplus 3 + 2 * 3 * (hubs object).card + lowDartCount object =
      3 * object.vertexCount := by
  obtain ⟨ident, -, -⟩ := SparseOrderArithmetic.surplus_dart_identity object base
    (tight_of_slack base slack)
  have e : (hubs object).card =
      (Finset.univ.filter fun v => object.degree v ≠ 3).card := rfl
  rw [e]
  unfold lowDartCount
  omega

/-! ### Hubs and cubic vertices -/

/-- **Cubic neighbours** of the object. -/
abbrev CubicNeighbourSupply (object : Graph.FiniteObject.{u}) : Prop :=
  Hypostructure.Graph.JointSystem.CubicSupply object.graph

theorem cubicNeighbourSupply (base : MinimumDegreeAtLeast 3 object)
    (noProper : NoProperCubic object) : CubicNeighbourSupply object :=
  Hypostructure.Graph.JointSystem.cubicSupply (jmin base) (jdeg noProper)

/-- **`5|H| + σ ≤ 2n`.** -/
abbrev HubCountBound (object : Graph.FiniteObject.{u}) : Prop :=
  5 * (hubs object).card + object.degreeSurplus 3 ≤ 2 * object.vertexCount

theorem hubCountBound (base : MinimumDegreeAtLeast 3 object) (noProper : NoProperCubic object)
    (slack : SlackIndependent object) : HubCountBound object := by
  have h := Hypostructure.Graph.JointSystem.five_hub_bound (jmin base) (jind base slack)
    (jdeg noProper)
  rw [Hset_card_eq base, sigma_eq base, ← vertexCount_eq] at h
  exact h

/-- **Parity of `L–L` edges on walks.** -/
abbrev LowEdgeParity (object : Graph.FiniteObject.{u}) : Prop :=
  Hypostructure.Graph.JointSystem.LowEdgeParity object.graph

theorem lowEdgeParity (base : MinimumDegreeAtLeast 3 object) (slack : SlackIndependent object) :
    LowEdgeParity object :=
  Hypostructure.Graph.JointSystem.lowEdgeParity (jind base slack)

/-- **Hub domination and `2|B| + σ ≤ n`.** -/
abbrev BigHubBound (object : Graph.FiniteObject.{u}) : Prop :=
  Hypostructure.Graph.JointSystem.HubDomination object.graph ∧
    2 * (Hypostructure.Graph.JointSystem.Bset object.graph).card + object.degreeSurplus 3 ≤
      object.vertexCount

theorem bigHubBound (base : MinimumDegreeAtLeast 3 object) (noProper : NoProperCubic object)
    (slack : SlackIndependent object) : BigHubBound object := by
  refine ⟨Hypostructure.Graph.JointSystem.hubDomination (jmin base) (jdeg noProper), ?_⟩
  have h := Hypostructure.Graph.JointSystem.big_hub_bound (jmin base) (jind base slack)
    (jdeg noProper)
  rw [sigma_eq base, ← vertexCount_eq] at h
  exact h

/-- **V-shape caps and `4σ + 93|B| ≤ 2n + 75|B|² + 4|H|`.** -/
abbrev BigHubVShapes (object : Graph.FiniteObject.{u}) : Prop :=
  Hypostructure.Graph.JointSystem.VShapeCaps object.graph ∧
    4 * object.degreeSurplus 3 + 93 * (Hypostructure.Graph.JointSystem.Bset object.graph).card ≤
      2 * object.vertexCount +
        75 * ((Hypostructure.Graph.JointSystem.Bset object.graph).card *
          (Hypostructure.Graph.JointSystem.Bset object.graph).card) +
        4 * (hubs object).card

theorem bigHubVShapes (base : MinimumDegreeAtLeast 3 object) (slack : SlackIndependent object)
    (avoid : ¬ HasCycleWithLength Core.DyadicLength.PowerOfTwoLength object) :
    BigHubVShapes object := by
  refine ⟨Hypostructure.Graph.JointSystem.vShapeCaps (jmin base) (jind base slack) (jC4 avoid)
    (jC8 avoid), ?_⟩
  have h := vshape base slack avoid
  rw [Hset_card_eq base, sigma_eq base, ← vertexCount_eq] at h
  exact h

/-- **The high-surplus bound**: `24σ + 465|B| ≤ 18n + 375|B|²`, and `8n ≤ 32s + 125s²` at
`s = n − σ`. -/
abbrev HighSurplusBound (object : Graph.FiniteObject.{u}) : Prop :=
  24 * object.degreeSurplus 3 + 465 * (Hypostructure.Graph.JointSystem.Bset object.graph).card ≤
      18 * object.vertexCount +
        375 * ((Hypostructure.Graph.JointSystem.Bset object.graph).card *
          (Hypostructure.Graph.JointSystem.Bset object.graph).card) ∧
    ∀ s, object.degreeSurplus 3 + s = object.vertexCount →
      8 * object.vertexCount ≤ 32 * s + 125 * (s * s)

theorem highSurplusBound (base : MinimumDegreeAtLeast 3 object)
    (noProper : NoProperCubic object) (slack : SlackIndependent object)
    (avoid : ¬ HasCycleWithLength Core.DyadicLength.PowerOfTwoLength object) :
    HighSurplusBound object := by
  have h1 := Hypostructure.Graph.JointSystem.high_surplus_bound (jmin base) (jind base slack)
    (jC4 avoid) (jC8 avoid) (jdeg noProper)
  rw [sigma_eq base, ← vertexCount_eq] at h1
  refine ⟨h1, fun s hs => ?_⟩
  have h2 := Hypostructure.Graph.JointSystem.high_surplus_closure (jmin base) (jind base slack)
    (jC4 avoid) (jC8 avoid) (jdeg noProper) s (by rw [sigma_eq base, ← vertexCount_eq]; exact hs)
  rw [← vertexCount_eq] at h2
  exact h2

/-! ### Density -/

/-- **Two edges leave every nonempty proper vertex set** of a connected bridgeless object. -/
theorem two_le_boundary (connected : object.graph.Connected)
    (bridgeless : ∀ contraction : EdgeContraction object, contraction.HasReturn)
    (S : Finset object.Vertex) (hne : S.Nonempty) (hS : S ≠ univ) :
    2 ≤ ∑ u ∈ S, (object.graph.neighborFinset u \ S).card := by
  classical
  obtain ⟨a, ha⟩ := hne
  obtain ⟨b, hb⟩ : ∃ b, b ∉ S := by
    by_contra h; push Not at h; exact hS (eq_univ_iff_forall.2 h)
  obtain ⟨w⟩ := connected.preconnected a b
  obtain ⟨d, -, hd1, hd2⟩ := w.exists_boundary_dart (↑S : Set object.Vertex) ha hb
  let contraction : EdgeContraction object := ⟨d.fst, d.snd, d.adj⟩
  obtain ⟨path⟩ := bridgeless contraction
  obtain ⟨d', -, hd1', hd2'⟩ :=
    path.1.exists_boundary_dart (↑S : Set object.Vertex) hd1 hd2
  have hadj' := (contraction.severed_adj).1 d'.adj
  have hmem : ∀ x y, x ∈ S → y ∉ S → object.graph.Adj x y →
      y ∈ object.graph.neighborFinset x \ S := fun x y _ hy hxy =>
    mem_sdiff.2 ⟨(SimpleGraph.mem_neighborFinset _ _ _).2 hxy, hy⟩
  by_cases hx : d'.fst = d.fst
  · have hy : d'.snd ≠ d.snd := by
      intro hy; apply hadj'.2; rw [hx, hy]
    have h2 : 2 ≤ (object.graph.neighborFinset d.fst \ S).card := by
      refine one_lt_card.2 ⟨d'.snd, ?_, d.snd, hmem _ _ hd1 hd2 d.adj, hy⟩
      rw [← hx]; exact hmem _ _ hd1' hd2' hadj'.1
    exact h2.trans (single_le_sum (f := fun u => (object.graph.neighborFinset u \ S).card)
      (fun _ _ => Nat.zero_le _) hd1)
  · have hsub : ({d.fst, d'.fst} : Finset object.Vertex) ⊆ S := by
      intro x hxm; simp only [mem_insert, mem_singleton] at hxm
      rcases hxm with rfl | rfl
      · exact hd1
      · exact hd1'
    have hle := sum_le_sum_of_subset (f := fun u => (object.graph.neighborFinset u \ S).card) hsub
    rw [sum_pair (Ne.symm hx)] at hle
    have p1 : 1 ≤ (object.graph.neighborFinset d.fst \ S).card :=
      card_pos.2 ⟨_, hmem _ _ hd1 hd2 d.adj⟩
    have p2 : 1 ≤ (object.graph.neighborFinset d'.fst \ S).card :=
      card_pos.2 ⟨_, hmem _ _ hd1' hd2' hadj'.1⟩
    omega

/-- **Density in excess form**: proper sets span few edges (`int S + 6 ≤ 4|S|`), equivalently
the surplus of `S` is at most `|S| + bd S − 6`; at least two edges leave every nonempty proper
set; and a set containing `N[h]` whose other vertices are cubic has slack `≥ |S| − d_h − 1`. -/
abbrev DensityExcess (object : Graph.FiniteObject.{u}) : Prop :=
  (∀ S : Finset object.Vertex, S ≠ univ → 2 ≤ S.card →
      ∑ u ∈ S, (object.graph.neighborFinset u ∩ S).card + 6 ≤ 4 * S.card) ∧
    (∀ S : Finset object.Vertex, S ≠ univ → 2 ≤ S.card →
      ∑ u ∈ S, ((object.graph.degree u : ℤ) - 3) ≤
        S.card + ∑ u ∈ S, ((object.graph.neighborFinset u \ S).card : ℤ) - 6) ∧
    (∀ S : Finset object.Vertex, S.Nonempty → S ≠ univ →
      2 ≤ ∑ u ∈ S, (object.graph.neighborFinset u \ S).card) ∧
    (∀ (h : object.Vertex) (S : Finset object.Vertex), h ∈ S →
      object.graph.neighborFinset h ⊆ S → (∀ u ∈ S, u ≠ h → object.graph.degree u = 3) →
      S ≠ univ →
      object.graph.degree h + 1 ≤ S.card ∧
        ((∑ u ∈ S, (object.graph.neighborFinset u ∩ S).card : ℕ) : ℤ) +
          ((S.card : ℤ) - (object.graph.degree h + 1)) + 6 ≤ 4 * (S.card : ℤ))

theorem densityExcess (noProper : NoProperCubic object) (connected : object.graph.Connected)
    (bridgeless : ∀ contraction : EdgeContraction object, contraction.HasReturn) :
    DensityExcess object := by
  have hdens := density noProper
  have hcut := two_le_boundary connected bridgeless
  refine ⟨hdens, fun S hS h2 => ?_, hcut, fun h S hh hN h3 hS => ?_⟩
  · exact (Hypostructure.Graph.DensityOverload.density_iff_excess object.graph S).1
      (hdens S hS h2)
  · exact Hypostructure.Graph.DensityOverload.single_hub_density_automatic object.graph S h hh hN
      h3 (hcut S ⟨h, hh⟩ hS)

/-- **Length-3 pairs at a hub**: at a hub whose second neighbourhood is cubic, at most
`4d` ordered non-adjacent pairs of `N(h)` are joined by a length-3 path avoiding `h`, and at
least `d(d − 2) − 4d` have no such path. -/
abbrev HubLengthThreePairs (object : Graph.FiniteObject.{u}) : Prop :=
  ∀ h : object.Vertex, 3 < object.graph.degree h →
    (∀ u ∈ Hypostructure.Graph.DensityOverload.secondNbhd object.graph h,
      object.graph.degree u = 3) →
    (Hypostructure.Graph.DensityOverload.len3Pairs object.graph h).card ≤
        4 * object.graph.degree h ∧
      object.graph.degree h * (object.graph.degree h - 2) ≤
        ((Hypostructure.Graph.DensityOverload.nonadjPairs object.graph h).filter fun p =>
            ¬ ∃ u v, u ≠ h ∧ v ≠ h ∧ object.graph.Adj p.1 u ∧ object.graph.Adj u v ∧
              object.graph.Adj v p.2).card + 4 * object.graph.degree h

theorem hubLengthThreePairs (base : MinimumDegreeAtLeast 3 object)
    (slack : SlackIndependent object)
    (avoid : ¬ HasCycleWithLength Core.DyadicLength.PowerOfTwoLength object) :
    HubLengthThreePairs object := by
  intro h hh hP
  have hC4 : Hypostructure.Graph.DensityOverload.C4Free object.graph :=
    fun a b c c' h1 h2 h3 h4 h5 => c4Free avoid a b c c' h1 h2 h3 h4 h5
  have hA : ∀ x ∈ object.graph.neighborFinset h, object.graph.degree x = 3 := by
    intro x hx
    have hxh : object.graph.Adj h x := (SimpleGraph.mem_neighborFinset _ _ _).1 hx
    have := deg_ge base x
    by_contra hne
    exact slack h x hh (by change 3 < object.graph.degree x; omega) hxh
  exact ⟨Hypostructure.Graph.DensityOverload.len3Pairs_le_four_d object.graph hC4 h hA hP,
    Hypostructure.Graph.DensityOverload.long_pairs_card_ge object.graph hC4 h hA hP⟩

/-! ### Windows of a packing -/

/-- **The hub–window budget at a packing of order `13`.** -/
abbrev HubWindowBudget (object : Graph.FiniteObject.{u})
    (packing : Finset (Finset object.Vertex)) : Prop :=
  24 * packing.card + 2 * hubEnds object packing + isoCubic object packing
      + 6 * (hubs object).card + object.degreeSurplus 3
      ≤ 3 * object.vertexCount + 4 * hubsW object packing ∧
    2 * ((hubs object).card : ℤ) + 3 * hubsR object packing + 2 * hubEnds object packing
        + isoCubicW object packing
      ≤ 2 * packing.card + (object.remainderSupport packing).card
        + ((object.vertexCount : ℤ) - object.degreeSurplus 3) ∧
    ∑ P ∈ packing, ∑ v ∈ P \ hubs object,
        (object.graph.neighborFinset v ∩ (P \ hubs object)).card + 4 * hubsW object packing
      = 24 * packing.card + 2 * hubEnds object packing ∧
    (lowDartCount object : ℤ)
        - ∑ P ∈ packing, ∑ v ∈ P \ hubs object,
            ((object.graph.neighborFinset v ∩ (P \ hubs object)).card : ℤ)
      = 2 * packing.card + 2 * (object.remainderSupport packing).card
        + ((object.vertexCount : ℤ) - object.degreeSurplus 3)
        - 2 * ((hubs object).card : ℤ) - 4 * hubsR object packing - 2 * hubEnds object packing

theorem hubWindowBudget_holds {packing : Finset (Finset object.Vertex)}
    (base : MinimumDegreeAtLeast 3 object) (noProper : NoProperCubic object)
    (slack : SlackIndependent object) (valid : object.IsWindowPacking 13 packing) :
    HubWindowBudget object packing :=
  ⟨hubWindowBudget object packing base noProper slack valid,
    hubBudget_rs object packing base noProper slack valid,
    windows_LL_sum object packing base slack valid,
    offPath_identity object packing base slack valid (dart_identity base slack)⟩

/-- **The remainder slack, the hanging windows and the window density at a packing of
order `13`.** -/
abbrev RemainderSlack (object : Graph.FiniteObject.{u})
    (packing : Finset (Finset object.Vertex)) : Prop :=
  slackG object (object.remainderSupport packing)
      = ((object.vertexCount : ℤ) - object.degreeSurplus 3) + 2 * packing.card
        + 2 * object.ambientSurplus (FiniteObject.windowSupport packing) 3
        - (object.crossWindowIncidences packing).card - 6 ∧
    (∀ (K : Finset object.Vertex) (Ws : Finset (Finset object.Vertex)),
      Ws ⊆ packing → Ws.Nonempty → (∀ P ∈ Ws, Disjoint K P) →
      (∀ P ∈ Ws, ∀ v ∈ P, object.graph.neighborFinset v ⊆ K ∪ P) →
      K ∪ Ws.biUnion id ≠ univ →
      ∑ P ∈ Ws, (2 + 2 * (object.ambientSurplus P 3 : ℤ)) ≤ slackG object K) ∧
    ((object.remainderSupport packing).Nonempty → packing.Nonempty →
      (object.crossWindowIncidences packing).card + 6 ≤ 28 * packing.card ∧
        object.ambientSurplus (FiniteObject.windowSupport packing) 3 + 6 ≤
          (object.windowRemainderIncidences packing).card + 13 * packing.card)

/-- **Window density**: with a nonempty remainder and at least one window, density at
`W` gives `2e× + 6 ≤ 28ν` and `σ_W + 6 ≤ e(R, W) + 13ν`. -/
theorem windowDensity {packing : Finset (Finset object.Vertex)}
    (base : MinimumDegreeAtLeast 3 object) (noProper : NoProperCubic object)
    (valid : object.IsWindowPacking 13 packing)
    (hR : (object.remainderSupport packing).Nonempty) (hν : packing.Nonempty) :
    (object.crossWindowIncidences packing).card + 6 ≤ 28 * packing.card ∧
      object.ambientSurplus (FiniteObject.windowSupport packing) 3 + 6 ≤
        (object.windowRemainderIncidences packing).card + 13 * packing.card := by
  obtain ⟨r, hr⟩ := hR
  have hW : FiniteObject.windowSupport packing ≠ univ := by
    intro h
    have hrW : r ∈ FiniteObject.windowSupport packing := by rw [h]; exact mem_univ r
    exact (mem_remainderSupport.1 hr) _ (mem_windowSupport.1 hrW).choose_spec.1
      (mem_windowSupport.1 hrW).choose_spec.2
  have hcard : (FiniteObject.windowSupport packing).card = 13 * packing.card := by
    have := object.windowSupport_card_eq valid
    convert this using 2
  have hν1 : 1 ≤ packing.card := card_pos.2 hν
  have hdens := density noProper (FiniteObject.windowSupport packing) hW (by omega)
  have hmass := object.sum_internalDegree_windowSupport valid
  have e : ∀ u, object.internalDegree (FiniteObject.windowSupport packing) u =
      (object.graph.neighborFinset u ∩ FiniteObject.windowSupport packing).card := by
    intro u; unfold FiniteObject.internalDegree; congr 1
  rw [Finset.sum_congr rfl (fun u _ => e u)] at hmass
  have hjoin := object.exact_window_join_identity (order := 13) (threshold := 3) valid
    (fun v => deg_ge base v)
  omega

theorem remainderSlack_holds {packing : Finset (Finset object.Vertex)}
    (base : MinimumDegreeAtLeast 3 object) (noProper : NoProperCubic object)
    (valid : object.IsWindowPacking 13 packing) :
    RemainderSlack object packing :=
  ⟨remainderSlack object packing base valid
      (object.exact_window_join_identity valid (fun v => deg_ge base v)),
    fun K Ws hWs hne hK hout hproper =>
      hanging object packing base noProper valid K Ws hWs hne hK hout hproper,
    fun hR hν => windowDensity base noProper valid hR hν⟩

/-- **Windows against the big hubs**, `k = |B|`, `s = n − σ`. -/
abbrev WindowHubBounds (object : Graph.FiniteObject.{u})
    (packing : Finset (Finset object.Vertex)) : Prop :=
  ∀ s, object.degreeSurplus 3 + s = object.vertexCount →
    12 * packing.card + 31 * (Hypostructure.Graph.JointSystem.Bset object.graph).card
        ≤ 2 * s + 2 * (hubs object).card
          + 25 * ((Hypostructure.Graph.JointSystem.Bset object.graph).card
            * (Hypostructure.Graph.JointSystem.Bset object.graph).card) ∧
      23 * packing.card + 31 * (Hypostructure.Graph.JointSystem.Bset object.graph).card
        ≤ object.vertexCount + 3 * s
          + 25 * ((Hypostructure.Graph.JointSystem.Bset object.graph).card
            * (Hypostructure.Graph.JointSystem.Bset object.graph).card) ∧
      22 * (packing.card : ℤ) + 93 * (Hypostructure.Graph.JointSystem.Bset object.graph).card
          + 6 * hubsR object packing + 4 * hubEnds object packing
          + 2 * isoCubicW object packing
        ≤ 6 * s + 75 * ((Hypostructure.Graph.JointSystem.Bset object.graph).card
            * (Hypostructure.Graph.JointSystem.Bset object.graph).card : ℕ)

theorem windowHubBounds {packing : Finset (Finset object.Vertex)}
    (base : MinimumDegreeAtLeast 3 object) (noProper : NoProperCubic object)
    (slack : SlackIndependent object)
    (avoid : ¬ HasCycleWithLength Core.DyadicLength.PowerOfTwoLength object)
    (valid : object.IsWindowPacking 13 packing) :
    WindowHubBounds object packing := by
  intro s hs
  have hs' : Hypostructure.Graph.JointSystem.sigma object.graph + s =
      Fintype.card object.Vertex := by rw [sigma_eq base, ← vertexCount_eq]; exact hs
  have h1 := windowU base slack avoid valid s hs'
  have h2 := windowU_rs base noProper slack avoid valid s hs'
  have h3 := fewWindows base noProper slack avoid valid s hs'
  rw [Hset_card_eq base] at h1
  rw [← vertexCount_eq] at h2
  exact ⟨h1, h2, h3⟩

end Facts

/-! ## Paths inside the remainder -/

section Remainder

variable {object : Graph.FiniteObject.{u}}

/-- The remainder `R = V ∖ ⋃ packing` as a set. -/
noncomputable abbrev Rset (object : Graph.FiniteObject.{u})
    (packing : Finset (Finset object.Vertex)) : Set object.Vertex :=
  ↑(object.remainderSupport packing)

/-- The hubs as a set. -/
noncomputable abbrev hubSet (object : Graph.FiniteObject.{u}) : Set object.Vertex :=
  ↑(hubs object)

/-- Maximality of a packing of order `13`: every induced window meets a member. -/
abbrev PackingMaximal (object : Graph.FiniteObject.{u})
    (packing : Finset (Finset object.Vertex)) : Prop :=
  ∀ window : Finset object.Vertex, object.InducesWindow 13 window →
    ∃ member ∈ packing, ¬ Disjoint window member

/-- An induced 13-vertex sequence spans an induced window. -/
theorem window_of_seq (g : ℕ → object.Vertex) (hg : InducedSeq object.graph 12 g) :
    object.InducesWindow 13 ((range 13).image g) := by
  have hinj : ∀ a < 13, ∀ b < 13, g a = g b → a = b := fun a ha b hb e =>
    hg.1 a (by omega) b (by omega) e
  refine ⟨⟨{ toFun := fun i => ⟨g i.1, mem_image_of_mem g (mem_range.2 i.2)⟩,
              inj' := fun i j e => Fin.ext (hinj i.1 i.2 j.1 j.2 (congrArg Subtype.val e)),
              map_rel_iff' := ?_ }⟩, ?_⟩
  · intro i j
    change object.graph.Adj (g i.1) (g j.1) ↔ (SimpleGraph.pathGraph 13).Adj i j
    rw [SimpleGraph.pathGraph_adj]
    exact hg.2 i.1 (by omega) j.1 (by omega)
  · rw [card_image_of_injOn (fun a ha b hb e => hinj a (mem_range.1 ha) b (mem_range.1 hb) e),
      card_range]

/-- **`R` has no induced `P13`** (maximality of the packing). -/
theorem remainder_noP13 (object : Graph.FiniteObject.{u})
    {packing : Finset (Finset object.Vertex)} (hmax : PackingMaximal object packing) :
    NoInducedP13In object.graph (Rset object packing) := by
  intro g hg
  by_contra hall
  push Not at hall
  obtain ⟨P, hP, hnd⟩ := hmax _ (window_of_seq g hg)
  rw [not_disjoint_iff] at hnd
  obtain ⟨v, hvW, hvP⟩ := hnd
  obtain ⟨t, ht, rfl⟩ := mem_image.1 hvW
  have hR : g t ∈ object.remainderSupport packing := hall t (by simp at ht; omega)
  exact (mem_remainderSupport.1 hR) P hP hvP

/-- Every vertex of a walk is reached along its prefix. -/
theorem reach_prefix {S : Set object.Vertex} {v w : object.Vertex} {k : ℕ}
    (h : Reach object.graph S v w k) :
    ∃ g : ℕ → object.Vertex, SWalk object.graph S k g ∧ g 0 = v ∧ g k = w ∧
      ∀ i ≤ k, Reach object.graph S v (g i) i := by
  obtain ⟨g, hw, h0, hk⟩ := h
  exact ⟨g, hw, h0, hk, fun i hi =>
    ⟨g, ⟨fun t ht => hw.1 t (by omega), fun t ht => hw.2 t (by omega)⟩, h0, rfl⟩⟩

/-- **Bags have at most 6142 vertices.** -/
theorem bag_card {packing : Finset (Finset object.Vertex)} (hmax : PackingMaximal object packing)
    (base : MinimumDegreeAtLeast 3 object) :
    ∀ v ∈ Rset object packing, v ∉ hubSet object → ∀ T : Finset object.Vertex,
      (∀ w ∈ T, ∃ k, Reach object.graph (Rset object packing \ hubSet object) v w k) →
      T.card ≤ 6142 := by
  classical
  intro v hvR hvH T hT
  set K : Finset object.Vertex :=
    univ.filter (fun w => ∃ k, Reach object.graph (Rset object packing \ hubSet object) v w k) with hK
  have hTK : T ⊆ K := fun w hw => by simp [hK, hT w hw]
  have hmemK : ∀ w ∈ K, w ∈ Rset object packing ∧ w ∉ hubSet object := by
    intro w hw
    simp only [hK, mem_filter, mem_univ, true_and] at hw
    obtain ⟨k, g, hwk, h0, hk⟩ := hw
    have := hwk.2 k le_rfl
    rw [hk] at this
    exact this
  have hvK : v ∈ K := by
    simp only [hK, mem_filter, mem_univ, true_and]
    exact ⟨0, fun _ => v, ⟨fun t ht => absurd ht (Nat.not_lt_zero t),
      fun t _ => ⟨hvR, hvH⟩⟩, rfl, rfl⟩
  have hno : NoInducedP13In object.graph (↑K : Set object.Vertex) := by
    intro g hg
    obtain ⟨t, ht, hts⟩ := remainder_noP13 object hmax g hg
    exact ⟨t, ht, fun hK' => hts (hmemK _ (Finset.mem_coe.1 hK')).1⟩
  have hconn : ∀ w ∈ K, ∃ k, Reach object.graph (↑K : Set object.Vertex) v w k := by
    intro w hw
    have hw' := hw
    simp only [hK, mem_filter, mem_univ, true_and] at hw'
    obtain ⟨k, hRk⟩ := hw'
    obtain ⟨g, hwk, h0, hk, hpre⟩ := reach_prefix hRk
    refine ⟨k, g, ⟨hwk.1, fun t ht => ?_⟩, h0, hk⟩
    simp only [hK, Finset.coe_filter, mem_univ, true_and, Set.mem_setOf_eq]
    exact ⟨t, hpre t ht⟩
  have hdeg : ∀ w ∈ K, 3 ≤ object.graph.degree w := fun w _ => deg_ge base w
  have hsum : ∑ w ∈ K, (object.graph.degree w - 3) = 0 := by
    apply sum_eq_zero
    intro w hw
    have := cubic_of_not_hub (object := object) (v := w) (fun h => (hmemK w hw).2 h)
    omega
  have hc := component_card_le object.graph K hno v hvK hconn hdeg
  rw [hsum] at hc
  have := card_le_card hTK
  norm_num at hc
  omega

/-- Hubs met by an `R`-path are at most `h_R`. -/
theorem path_hubs_le {packing : Finset (Finset object.Vertex)} {m : ℕ} {g : ℕ → object.Vertex} (hp : Hypostructure.Graph.RemainderPaths.PathSeq object.graph (Rset object packing) m g) :
    ((range (m + 1)).filter (fun t => g t ∈ hubSet object)).card ≤ hubsR object packing := by
  classical
  unfold hubsR
  refine le_trans (le_of_eq ?_) (card_le_card (s := ((range (m + 1)).filter
    (fun t => g t ∈ hubSet object)).image g) ?_)
  · rw [card_image_of_injOn]
    intro a ha b hb e
    simp only [coe_filter, mem_range, Set.mem_setOf_eq] at ha hb
    exact hp.1 a (by omega) b (by omega) e
  · intro v hv
    obtain ⟨t, ht, rfl⟩ := mem_image.1 hv
    simp only [mem_filter, mem_range] at ht
    have hR : g t ∈ object.remainderSupport packing := hp.2.2 t (by omega)
    simp only [mem_filter]
    exact ⟨Finset.mem_coe.1 ht.2, mem_remainderSupport.1 hR⟩

/-! ### Paths and cycles inside `R` -/

/-- **Path bound inside `R`.**  A path of G inside `R` with `m` edges through
`k` hubs: `m + 1 ≤ 6143 k + 6142`, and `m + 1 ≤ 6143 h_R + 6142`. -/
theorem remainder_path_bound {packing : Finset (Finset object.Vertex)} (hmax : PackingMaximal object packing) (base : MinimumDegreeAtLeast 3 object) {m : ℕ}
    {g : ℕ → object.Vertex} (hp : Hypostructure.Graph.RemainderPaths.PathSeq object.graph (Rset object packing) m g) :
    m + 1 ≤ 6143 * ((range (m + 1)).filter (fun t => g t ∈ hubSet object)).card + 6142 ∧
      m + 1 ≤ 6143 * hubsR object packing + 6142 := by
  classical
  have hb := Hypostructure.Graph.RemainderPaths.bag_path_bound (H := hubSet object) 6142 (bag_card hmax base) hp
  have hk := path_hubs_le hp
  refine ⟨hb, ?_⟩
  have := Nat.mul_le_mul_left 6143 hk
  omega

/-- **Cycle bound inside `R`.**  A cycle of G inside `R` of length `n` has
`n ≤ 6143 h_R + 6142`. -/
theorem remainder_cycle_bound {packing : Finset (Finset object.Vertex)} (hmax : PackingMaximal object packing) (base : MinimumDegreeAtLeast 3 object) {n : ℕ}
    {c : ℕ → object.Vertex} (hc : CycleSeq object.graph n c) (hn : 1 ≤ n)
    (hcR : ∀ t < n, c t ∈ Rset object packing) :
    n ≤ 6143 * hubsR object packing + 6142 := by
  have hp : Hypostructure.Graph.RemainderPaths.PathSeq object.graph (Rset object packing) (n - 1) c :=
    ⟨fun a ha b hb e => hc.1 a (by omega) b (by omega) e,
      fun t ht => hc.2.1 t (by omega), fun t ht => hcR t (by omega)⟩
  have := (remainder_path_bound hmax base hp).2
  omega

/-- **Long chord / long cycle inside `R`.**  A path of G inside `R` with
`m ≥ 12` edges carries a chord closing a cycle of G inside `R` of length `L ≥ 3` with
`m + 11 ≤ 11 L`. -/
theorem remainder_long_cycle {packing : Finset (Finset object.Vertex)} (hmax : PackingMaximal object packing) (base : MinimumDegreeAtLeast 3 object) {m : ℕ}
    {g : ℕ → object.Vertex} (hp : Hypostructure.Graph.RemainderPaths.PathSeq object.graph (Rset object packing) m g)
    (hm : 12 ≤ m) :
    ∃ L c, 3 ≤ L ∧ m + 11 ≤ 11 * L ∧ CycleSeq object.graph L c ∧
      ∀ t < L, c t ∈ Rset object packing :=
  Hypostructure.Graph.RemainderPaths.long_cycle (remainder_noP13 object hmax) hp hm

/-- **Induced extraction inside `R`.**  A path of G inside `R` whose adjacencies
all have span `≤ s` has at most `11 s` edges. -/
theorem remainder_span_bound {packing : Finset (Finset object.Vertex)} (hmax : PackingMaximal object packing) (base : MinimumDegreeAtLeast 3 object) {m : ℕ}
    {g : ℕ → object.Vertex} (hp : Hypostructure.Graph.RemainderPaths.PathSeq object.graph (Rset object packing) m g)
    (s : ℕ) (hs : ∀ a b, a < b → b ≤ m → object.graph.Adj (g a) (g b) → b - a ≤ s) :
    m ≤ 11 * s :=
  Hypostructure.Graph.RemainderPaths.span_path_bound (remainder_noP13 object hmax) hp s hs

end Remainder


/-! ### The remainder of a maximal packing and the window-free sets -/

section RemainderFacts

variable {object : Graph.FiniteObject.{u}}

/-- A cycle sequence of length `n ≥ 3` is a Mathlib cycle of length `n`. -/
theorem cycleSeq_walk {n : ℕ} {c : ℕ → object.Vertex} (hc : CycleSeq object.graph n c)
    (hn : 3 ≤ n) : ∃ w : object.graph.Walk (c 0) (c 0), w.IsCycle ∧ w.length = n := by
  have e : (c 0 :: (List.range (n - 1)).map (fun t => c (t + 1))) = (List.range n).map c := by
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    simp only [Nat.add_sub_cancel]
    rfl
  obtain ⟨w, hw, hlen⟩ := Hypostructure.Graph.HubWin.list_cycle (G := object.graph) (c 0)
    ((List.range (n - 1)).map (fun t => c (t + 1)))
    (by
      rw [e]
      refine List.Nodup.map_on ?_ List.nodup_range
      intro a ha b hb hab
      exact hc.1 a (List.mem_range.1 ha) b (List.mem_range.1 hb) hab)
    (by
      rw [e, List.isChain_map, List.isChain_range]
      intro m hm
      exact hc.2.1 m (by omega))
    (by simp; omega)
    (by
      have : ((c 0 :: (List.range (n - 1)).map (fun t => c (t + 1))).getLast
          (List.cons_ne_nil _ _)) = c (n - 1) := by
        simp only [e]
        rw [List.getLast_map, List.getLast_range]
      rw [this]; exact hc.2.2)
  exact ⟨w, hw, by rw [hlen]; simp; omega⟩

/-- No dyadic cycle, in sequence form. -/
theorem noPow2 (avoid : ¬ HasCycleWithLength Core.DyadicLength.PowerOfTwoLength object) :
    NoPow2Cycles object.graph := by
  intro m hm c hc
  have h4 : 4 ≤ 2 ^ m := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  obtain ⟨w, hw, hlen⟩ := cycleSeq_walk hc (by omega)
  exact noDyadic avoid w hw ⟨m, hm, hlen⟩

/-- Every induced `P13` of the object meets the packed windows. -/
theorem seq_meets_windows {packing : Finset (Finset object.Vertex)}
    (hmax : PackingMaximal object packing) :
    ∀ g, InducedSeq object.graph 12 g →
      ∃ t ≤ 12, g t ∈ (↑(FiniteObject.windowSupport packing) : Set object.Vertex) := by
  intro g hg
  obtain ⟨P, hP, hnd⟩ := hmax _ (window_of_seq g hg)
  rw [not_disjoint_iff] at hnd
  obtain ⟨v, hvW, hvP⟩ := hnd
  obtain ⟨t, ht, rfl⟩ := mem_image.1 hvW
  exact ⟨t, by simp at ht; omega, Finset.mem_coe.2 (mem_windowSupport.2 ⟨P, hP, hvP⟩)⟩

/-- **Paths and cycles inside the remainder of a maximal packing**: no induced `P13`; bags of
at most `6142` vertices; paths through `k` hubs have at most `6143k + 6142` vertices (at
most `6143 h_R + 6142`), and so do cycles; a path with `m ≥ 12` edges closes a cycle of
length `L`, `m + 11 ≤ 11L`; span `≤ s` gives `m ≤ 11s`; circumference `L` gives
`m ≤ 11(L − 1)`; and the remainder is `12`-degenerate. -/
abbrev RemainderPathBounds (object : Graph.FiniteObject.{u})
    (packing : Finset (Finset object.Vertex)) : Prop :=
  NoInducedP13In object.graph (Rset object packing) ∧
    (∀ v ∈ Rset object packing, v ∉ hubSet object → ∀ T : Finset object.Vertex,
      (∀ w ∈ T, ∃ k, Reach object.graph (Rset object packing \ hubSet object) v w k) →
      T.card ≤ 6142) ∧
    (∀ (m : ℕ) (g : ℕ → object.Vertex),
      Hypostructure.Graph.RemainderPaths.PathSeq object.graph (Rset object packing) m g →
      m + 1 ≤ 6143 * ((range (m + 1)).filter (fun t => g t ∈ hubSet object)).card + 6142 ∧
        m + 1 ≤ 6143 * hubsR object packing + 6142) ∧
    (∀ (n : ℕ) (c : ℕ → object.Vertex), CycleSeq object.graph n c → 1 ≤ n →
      (∀ t < n, c t ∈ Rset object packing) → n ≤ 6143 * hubsR object packing + 6142) ∧
    (∀ (m : ℕ) (g : ℕ → object.Vertex),
      Hypostructure.Graph.RemainderPaths.PathSeq object.graph (Rset object packing) m g →
      12 ≤ m → ∃ L c, 3 ≤ L ∧ m + 11 ≤ 11 * L ∧ CycleSeq object.graph L c ∧
        ∀ t < L, c t ∈ Rset object packing) ∧
    (∀ (m : ℕ) (g : ℕ → object.Vertex),
      Hypostructure.Graph.RemainderPaths.PathSeq object.graph (Rset object packing) m g →
      ∀ s, (∀ a b, a < b → b ≤ m → object.graph.Adj (g a) (g b) → b - a ≤ s) → m ≤ 11 * s) ∧
    (∀ L, (∀ n c, CycleSeq object.graph n c → (∀ t < n, c t ∈ Rset object packing) → 3 ≤ n →
        n ≤ L) →
      ∀ (m : ℕ) (g : ℕ → object.Vertex),
        Hypostructure.Graph.RemainderPaths.PathSeq object.graph (Rset object packing) m g →
        m ≤ 11 ∨ m ≤ 11 * (L - 1)) ∧
    (∀ X : Finset object.Vertex, (∀ v ∈ X, v ∈ Rset object packing) → X.Nonempty →
      ∃ v ∈ X, (object.graph.neighborFinset v ∩ X).card ≤ 12)

theorem remainderPathBounds {packing : Finset (Finset object.Vertex)}
    (hmax : PackingMaximal object packing) (base : MinimumDegreeAtLeast 3 object)
    (avoid : ¬ HasCycleWithLength Core.DyadicLength.PowerOfTwoLength object) :
    RemainderPathBounds object packing := by
  have hno := remainder_noP13 object hmax
  refine ⟨hno, bag_card hmax base, fun m g hp => remainder_path_bound hmax base hp,
    fun n c hc hn hcR => remainder_cycle_bound hmax base hc hn hcR,
    fun m g hp hm => remainder_long_cycle hmax base hp hm,
    fun m g hp s hs => remainder_span_bound hmax base hp s hs,
    fun L hcirc m g hp => Hypostructure.Graph.RemainderPaths.path_le_of_circumference hno L
      hcirc hp,
    fun X hXS hne => ?_⟩
  exact Hypostructure.Graph.RemainderPaths.low_vertex
    (fun a b c c' h1 h2 h3 h4 h5 => c4Free avoid a b c c' h1 h2 h3 h4 h5)
    (Hypostructure.Graph.RemainderPaths.noInducedPath_of_P13 hno) X hXS hne

/-- **Window-free sets of a maximal packing** (`W` the packed windows): short induced walks
inside any window-free set; the hub-pair dichotomy (a short bypass avoiding `W ∪ {h}`, or
every walk meets `W ∪ {h}`); chords of long window-free paths and their residues (open at a
hub, or closed by an outside path); one chord per `13` consecutive vertices; the
outside-return dichotomy; window-free connected sets have at most `1 + 2047(3 + σ_K)`
vertices (`1 + 2047 d_b` with one hub `b`); a connected set is window-free with short
induced walks, crosses into `W` along an edge, or lies in `W`. -/
abbrev WindowFreeGeometry (object : Graph.FiniteObject.{u})
    (packing : Finset (Finset object.Vertex)) : Prop :=
  (∀ S : Set object.Vertex, (∀ v ∈ S, v ∉ (↑(FiniteObject.windowSupport packing) : Set _)) →
    ∀ u v, (∃ k, Reach object.graph S u v k) →
      ∃ k g, k ≤ 11 ∧ SWalk object.graph S k g ∧ g 0 = u ∧ g k = v ∧
        InducedSeq object.graph k g ∧ ∀ k' < k, ¬ Reach object.graph S u v k') ∧
  (∀ h x y : object.Vertex, object.graph.Adj h x → object.graph.Adj h y → x ≠ y →
    ¬ object.graph.Adj x y →
    (∃ k g, SWalk object.graph
        {v | v ∉ (↑(FiniteObject.windowSupport packing) : Set object.Vertex) ∧ v ≠ h} k g ∧
      g 0 = x ∧ g k = y ∧ InducedSeq object.graph k g ∧
      CycleSeq object.graph (k + 2) (hubCycle h g) ∧
      k ∈ ({3, 4, 5, 7, 8, 9, 10, 11} : Finset ℕ) ∧
      ((¬ ∃ u w, u ≠ h ∧ w ≠ h ∧ object.graph.Adj x u ∧ object.graph.Adj u w ∧
        object.graph.Adj w y) → k ≠ 3)) ∨
    (∀ k (g : ℕ → object.Vertex), (∀ t < k, object.graph.Adj (g t) (g (t + 1))) →
      g 0 = x → g k = y →
      ∃ t ≤ k, g t ∈ (↑(FiniteObject.windowSupport packing) : Set object.Vertex) ∨
        g t = h)) ∧
  (∀ S : Set object.Vertex, (∀ v ∈ S, v ∉ (↑(FiniteObject.windowSupport packing) : Set _)) →
    ∀ (h : object.Vertex), h ∉ S → ∀ (L : ℕ) (g : ℕ → object.Vertex), SWalk object.graph S L g →
      (∀ a ≤ L, ∀ b ≤ L, g a = g b → a = b) →
      object.graph.Adj h (g 0) → object.graph.Adj h (g L) → 12 ≤ L →
      ∃ i j, i + 2 ≤ j ∧ j ≤ 12 ∧ object.graph.Adj (g i) (g j) ∧
        ∀ m, 2 ≤ m → j - i + 1 ≠ 2 ^ m ∧ L - (j - i) + 3 ≠ 2 ^ m) ∧
  (∀ S : Set object.Vertex, (∀ v ∈ S, v ∉ (↑(FiniteObject.windowSupport packing) : Set _)) →
    ∀ (k : ℕ) (g : ℕ → object.Vertex), SWalk object.graph S k g →
      (∀ a ≤ k, ∀ b ≤ k, g a = g b → a = b) →
      (k + 1) / 13 ≤ ((range (k + 1) ×ˢ range (k + 1)).filter
        (fun p : ℕ × ℕ => p.1 + 2 ≤ p.2 ∧ object.graph.Adj (g p.1) (g p.2))).card) ∧
  (∀ S : Set object.Vertex, (∀ v ∈ S, v ∉ (↑(FiniteObject.windowSupport packing) : Set _)) →
    ∀ (L T : ℕ) (g q : ℕ → object.Vertex), SWalk object.graph S L g →
      (∀ a ≤ L, ∀ b ≤ L, g a = g b → a = b) →
      (∀ t < T, object.graph.Adj (q t) (q (t + 1))) →
      (∀ a b, 0 < a → a < T → 0 < b → b < T → q a = q b → a = b) →
      (∀ t, 0 < t → t < T → ∀ s ≤ L, q t ≠ g s) →
      q 0 = g L → q T = g 0 → 1 ≤ T → 12 ≤ L →
      ∃ i j, i + 2 ≤ j ∧ j ≤ 12 ∧ object.graph.Adj (g i) (g j) ∧
        ∀ m, 2 ≤ m → j - i + 1 ≠ 2 ^ m ∧ L - (j - i) + 1 + T ≠ 2 ^ m) ∧
  (∀ S : Set object.Vertex, (∀ v ∈ S, v ∉ (↑(FiniteObject.windowSupport packing) : Set _)) →
    ∀ a b : object.Vertex,
      (∃ k ≤ 11, ∃ g, SWalk object.graph S k g ∧ g 0 = b ∧ g k = a ∧
        InducedSeq object.graph k g) ∨
      (∀ k (g : ℕ → object.Vertex), (∀ t < k, object.graph.Adj (g t) (g (t + 1))) →
        g 0 = b → g k = a → ∃ t ≤ k, g t ∉ S)) ∧
  (∀ K : Finset object.Vertex,
    (∀ v ∈ K, v ∉ (↑(FiniteObject.windowSupport packing) : Set object.Vertex)) →
    ∀ r ∈ K, (∀ v ∈ K, ∃ k, Reach object.graph (↑K : Set object.Vertex) r v k) →
      K.card ≤ 1 + (3 + ∑ v ∈ K, (object.graph.degree v - 3)) * (2 ^ 11 - 1) ∧
      ∀ b ∈ K, (∀ v ∈ K, v ≠ b → object.graph.degree v = 3) →
        K.card ≤ 1 + 2047 * object.graph.degree b) ∧
  (∀ Z : Set object.Vertex, (∀ u ∈ Z, ∀ v ∈ Z, ∃ k, Reach object.graph Z u v k) →
    (∀ u ∈ Z, ∀ v ∈ Z, ∃ k ≤ 11, ∃ g, SWalk object.graph Z k g ∧ g 0 = u ∧ g k = v ∧
        InducedSeq object.graph k g) ∨
      (∃ a b, a ∈ Z ∧ b ∈ Z ∧ a ∉ (↑(FiniteObject.windowSupport packing) : Set object.Vertex) ∧
        b ∈ (↑(FiniteObject.windowSupport packing) : Set object.Vertex) ∧
        object.graph.Adj a b) ∨
      (∀ v ∈ Z, v ∈ (↑(FiniteObject.windowSupport packing) : Set object.Vertex)))

theorem windowFreeGeometry {packing : Finset (Finset object.Vertex)}
    (hmax : PackingMaximal object packing) (base : MinimumDegreeAtLeast 3 object)
    (avoid : ¬ HasCycleWithLength Core.DyadicLength.PowerOfTwoLength object) :
    WindowFreeGeometry object packing := by
  have hW := seq_meets_windows hmax
  have hcyc := noPow2 avoid
  have hfree : ∀ S : Set object.Vertex,
      (∀ v ∈ S, v ∉ (↑(FiniteObject.windowSupport packing) : Set object.Vertex)) →
      NoInducedP13In object.graph S := fun S hS => noP13_of_disjoint object.graph _ hW S hS
  refine ⟨fun S hS u v h => short_walk object.graph (hfree S hS) h,
    fun h x y hx hy hxy hnadj => hub_pair_dichotomy object.graph _ hW hcyc hx hy hxy hnadj,
    fun S hS h hh L g hw hinj hx hy hL =>
      forced_path_chord object.graph (hfree S hS) hcyc hh hw hinj hx hy hL,
    fun S hS k g hw hinj => chord_count object.graph (hfree S hS) hw hinj,
    fun S hS L T g q hw hinj hq hqinj hqd h0 hT hT1 hL =>
      closed_path_chord object.graph (hfree S hS) hcyc hw hinj hq hqinj hqd h0 hT hT1 hL,
    fun S hS a b => outside_return_dichotomy object.graph (hfree S hS) a b,
    fun K hK r hr hconn => ⟨?_, fun b hb hcub => ?_⟩,
    fun Z hconn => carrier_position object.graph _ hW Z hconn⟩
  · exact component_card_le object.graph K (hfree _ hK) r hr hconn (fun v _ => deg_ge base v)
  · exact component_single_hub object.graph K (hfree _ hK) r hr hconn (fun v _ => deg_ge base v)
      b hb hcub

/-- **Attachments to induced `P13`s**: a vertex off an induced `P13` has at most `7`
neighbours on it, and every vertex of an induced `P13` has a neighbour off it. -/
abbrev InducedPathAttachment (object : Graph.FiniteObject.{u}) : Prop :=
  ∀ g : ℕ → object.Vertex, InducedSeq object.graph 12 g →
    (∀ v, (∀ t ≤ 12, g t ≠ v) →
      ((range 13).filter (fun t => object.graph.Adj v (g t))).card ≤ 7) ∧
    ∀ i ≤ 12, ∃ w, object.graph.Adj (g i) w ∧ ∀ t ≤ 12, w ≠ g t

theorem inducedPathAttachment (base : MinimumDegreeAtLeast 3 object)
    (avoid : ¬ HasCycleWithLength Core.DyadicLength.PowerOfTwoLength object) :
    InducedPathAttachment object := by
  intro g hg
  refine ⟨fun v hv => attach_le_seven object.graph
    (fun a b c c' h1 h2 h3 h4 h5 => c4Free avoid a b c c' h1 h2 h3 h4 h5) hg hv,
    fun i hi => ?_⟩
  by_contra hno
  push Not at hno
  have hle := interior_not_in_window object.graph hg hi (fun w hw => by
    obtain ⟨t, ht, e⟩ := hno w hw
    exact ⟨t, ht, e⟩)
  have := deg_ge base (g i)
  omega

end RemainderFacts

end Hypostructure.Graph.JointObject
