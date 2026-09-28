import Hypostructure.Graph.JointObject
import Hypostructure.Graph.HubLink.Chain
import Hypostructure.Graph.HubLink.Rainbow
import Hypostructure.Graph.HubLink.SlotC8
import Hypostructure.Graph.HubLink.Overload
import Hypostructure.Graph.HubLink.Greedy
import Hypostructure.Graph.HubLink.SlotCover

/-!
# Links between the hubs of the remainder of a maximal packing

A `FiniteObject` with the cubic baseline and a maximal window packing of order `13`; `R` its
remainder, `H` the hubs (`deg ≠ 3`), `Q = R ∖ H`, a **bag** a connected component of
`G[Q]`, `S_R = H ∩ R`.  `LinkVia h h' b`: distinct hubs and an edge `x y` of `G[Q]` inside
bag `b` with `x ∼ h`, `y ∼ h'`, `h` the only hub of `x` and `h'` the only hub of `y`.

* `chain_contra`: a hub chain in `R` with induced segments has fewer than `13` vertices;
* `no_rainbow`: no five hubs of `R` linked consecutively through four distinct bags;
* `cap`: through one bag a hub has at most `6142` link partners;
* `link_degenerate`, `strong_degenerate`, `link_pairs`, `strong_pairs`, `weak_capacity`: the
  link graph on `S_R` is `18429`-degenerate, the strong link graph `3`-degenerate;
* `closure_out_edges`, `closure_disjoint`, `closed_reaches_W`, `closed_classes_le`: bag-link
  classes of hubs of `R` reach the rest of the object only through the packed windows;
* the object-level fact bundles `HubLinkStructure`, `HubClassCounts`, `SlotRelation`,
  `ClosedClasses`, with their proofs.

Nothing here names a presentation, a ledger or a manuscript.
-/

open Finset Classical
open Hypostructure Hypostructure.Graph
open Hypostructure.Graph.WindowCombination Hypostructure.Graph.JointObject
open Hypostructure.Graph.HubLink

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Hypostructure.Graph.HubLinkObject

universe u

attribute [local instance] Graph.FiniteObject.vertices Graph.FiniteObject.decideAdj

section Defs

variable (object : Graph.FiniteObject.{u}) (packing : Finset (Finset object.Vertex))

/-- `Q = R ∖ H`, the cubic vertices of the remainder. -/
noncomputable def Q : Finset object.Vertex := object.remainderSupport packing \ hubs object

/-- `S_R = H ∩ R`. -/
noncomputable def SR : Finset object.Vertex :=
  (hubs object).filter (fun v => ∀ P ∈ packing, v ∉ P)

/-- `G[Q]`, on all vertices. -/
def gammaQ : SimpleGraph object.Vertex where
  Adj u v := object.graph.Adj u v ∧ u ∈ Q object packing ∧ v ∈ Q object packing
  symm := ⟨fun _ _ ⟨h, a, b⟩ => ⟨h.symm, b, a⟩⟩
  loopless := ⟨fun v ⟨h, _, _⟩ => object.graph.irrefl h⟩

/-- The bag of `v`: its component in `G[Q]`. -/
noncomputable def bag (v : object.Vertex) : (gammaQ object packing).ConnectedComponent :=
  (gammaQ object packing).connectedComponentMk v

/-- `h` is the only hub adjacent to `x`. -/
def OneHub (x h : object.Vertex) : Prop :=
  ∀ w ∈ hubs object, object.graph.Adj x w → w = h

/-- **Link through a bag.** -/
def LinkVia (h h' : object.Vertex) (b : (gammaQ object packing).ConnectedComponent) : Prop :=
  h ∈ hubs object ∧ h' ∈ hubs object ∧ h ≠ h' ∧
    ∃ x y, object.graph.Adj h x ∧ object.graph.Adj h' y ∧ object.graph.Adj x y ∧
      x ∈ Q object packing ∧ y ∈ Q object packing ∧ OneHub object x h ∧ OneHub object y h' ∧
      bag object packing x = b

end Defs

section Basic

variable {object : Graph.FiniteObject.{u}} {packing : Finset (Finset object.Vertex)}

theorem SR_card : (SR object packing).card = hubsR object packing := rfl

theorem mem_SR {v : object.Vertex} : v ∈ SR object packing ↔ v ∈ hubs object ∧ v ∈ object.remainderSupport packing := by
  simp [SR, mem_remainderSupport]

theorem mem_Q {v : object.Vertex} :
    v ∈ Q object packing ↔ v ∈ object.remainderSupport packing ∧ v ∉ hubs object := by
  simp [Q]

theorem bag_eq_of_adj {x y : object.Vertex} (hx : x ∈ Q object packing) (hy : y ∈ Q object packing)
    (hxy : object.graph.Adj x y) : bag object packing x = bag object packing y :=
  SimpleGraph.ConnectedComponent.eq.2 (SimpleGraph.Adj.reachable ⟨hxy, hx, hy⟩)

theorem LinkVia.symm {h h' : object.Vertex} {b} (l : LinkVia object packing h h' b) :
    LinkVia object packing h' h b := by
  obtain ⟨hh, hh', hne, x, y, a1, a2, a3, hx, hy, o1, o2, hb⟩ := l
  exact ⟨hh', hh, hne.symm, y, x, a2, a1, a3.symm, hy, hx, o2, o1,
    (bag_eq_of_adj hx hy a3).symm.trans hb⟩

/-- A bag is `R ∖ H`-connected: reachability in `G[Q]` as a `Reach` sequence. -/
theorem reach_of_bag {v w : object.Vertex} (hv : v ∈ Q object packing) (hw : w ∈ Q object packing)
    (e : bag object packing v = bag object packing w) :
    ∃ k, Reach object.graph (Rset object packing \ hubSet object) v w k := by
  obtain ⟨p⟩ := SimpleGraph.ConnectedComponent.exact e
  have hmem : ∀ z ∈ Q object packing, z ∈ Rset object packing \ hubSet object := by
    intro z hz
    rw [mem_Q] at hz
    exact ⟨Finset.mem_coe.2 hz.1, fun h => hz.2 (Finset.mem_coe.1 h)⟩
  refine ⟨p.length, fun i => p.getVert i, ⟨fun t ht => (p.adj_getVert_succ ht).1, ?_⟩,
    p.getVert_zero, p.getVert_length⟩
  intro t ht
  by_cases hlt : t < p.length
  · exact hmem _ (p.adj_getVert_succ hlt).2.1
  · have : t = p.length := by omega
    subst this
    show p.getVert p.length ∈ _
    rw [p.getVert_length]; exact hmem _ hw

/-- **A bag has at most 6142 vertices** (`bag_card`). -/
theorem fibre_card (hmax : JointObject.PackingMaximal object packing) (base : MinimumDegreeAtLeast 3 object)
    (b : (gammaQ object packing).ConnectedComponent) :
    (univ.filter (fun y => y ∈ Q object packing ∧ bag object packing y = b)).card ≤ 6142 := by
  by_cases hne : (univ.filter (fun y => y ∈ Q object packing ∧ bag object packing y = b)).Nonempty
  · obtain ⟨v, hv⟩ := hne
    simp only [mem_filter, mem_univ, true_and] at hv
    have hvQ := mem_Q.1 hv.1
    refine bag_card hmax base v (Finset.mem_coe.2 hvQ.1) (fun h => hvQ.2 (Finset.mem_coe.1 h)) _ ?_
    intro w hw
    simp only [mem_filter, mem_univ, true_and] at hw
    exact reach_of_bag hv.1 hw.1 (hv.2.trans hw.2.symm)
  · rw [not_nonempty_iff_eq_empty.1 hne]; simp

/-- The hub of a vertex (if any). -/
noncomputable def hubOf (y : object.Vertex) : object.Vertex :=
  if hex : ∃ w, w ∈ hubs object ∧ object.graph.Adj y w then Classical.choose hex else y

theorem hubOf_eq {y h : object.Vertex} (hh : h ∈ hubs object) (hy : object.graph.Adj y h)
    (o : OneHub object y h) : hubOf y = h := by
  have hex : ∃ w, w ∈ hubs object ∧ object.graph.Adj y w := ⟨h, hh, hy⟩
  rw [hubOf, dif_pos hex]
  exact o _ (Classical.choose_spec hex).1 (Classical.choose_spec hex).2

/-- **Through one bag a hub has at most 6142 link partners.** -/
theorem cap (hmax : JointObject.PackingMaximal object packing) (base : MinimumDegreeAtLeast 3 object) :
    ∀ h b, (univ.filter (fun h' => LinkVia object packing h h' b)).card ≤ 6142 := by
  intro h b
  calc _ ≤ ((univ.filter (fun y => y ∈ Q object packing ∧ bag object packing y = b)).image hubOf).card :=
        card_le_card ?_
    _ ≤ _ := card_image_le
    _ ≤ 6142 := fibre_card hmax base b
  · intro h' hh'
    simp only [mem_filter, mem_univ, true_and] at hh'
    obtain ⟨-, hh', -, x, y, a1, a2, a3, hx, hy, o1, o2, hb⟩ := hh'
    refine mem_image.2 ⟨y, ?_, hubOf_eq hh' a2.symm o2⟩
    simp only [mem_filter, mem_univ, true_and]
    exact ⟨hy, (bag_eq_of_adj hx hy a3).symm.trans hb⟩

end Basic

/-! ## Chains in `R` -/

section Chains

variable {object : Graph.FiniteObject.{u}} {packing : Finset (Finset object.Vertex)}

/-- **No long hub chain in `R`.**  A hub chain (`HubLink.chain_P13` hypotheses) with all its
vertices in `R` and at least 13 vertices contradicts `remainder_noP13`. -/
theorem chain_contra (hmax : JointObject.PackingMaximal object packing) (ℓ m : ℕ) (hℓ : 1 ≤ ℓ) (hm : 1 ≤ m) (hlen : 12 ≤ (ℓ + 1) * (m - 1))
    (h : ℕ → object.Vertex) (c : ℕ → ℕ → object.Vertex)
    (hH : ∀ i < m, ∀ j < m, i ≠ j → ¬ object.graph.Adj (h i) (h j) ∧ h i ≠ h j)
    (hseg : ∀ i, i + 1 < m → ∀ a < ℓ, ∀ b < ℓ,
      (object.graph.Adj (c i a) (c i b) ↔ (a + 1 = b ∨ b + 1 = a)) ∧ (c i a = c i b → a = b))
    (hhc : ∀ i, i + 1 < m → ∀ a < ℓ, ∀ j < m,
      (object.graph.Adj (c i a) (h j) ↔ ((j = i ∧ a = 0) ∨ (j = i + 1 ∧ a + 1 = ℓ))) ∧
        c i a ≠ h j)
    (hcross : ∀ i, i + 1 < m → ∀ j, j + 1 < m → i ≠ j → ∀ a < ℓ, ∀ b < ℓ,
      ¬ object.graph.Adj (c i a) (c j b) ∧ c i a ≠ c j b)
    (hR : ∀ i < m, h i ∈ object.remainderSupport packing)
    (hcR : ∀ i, i + 1 < m → ∀ a < ℓ, c i a ∈ object.remainderSupport packing) : False := by
  have hg := chain_P13 object.graph ℓ m hℓ hm hlen h c hH hseg hhc hcross
  obtain ⟨t, ht, hnot⟩ := remainder_noP13 object hmax _ hg
  apply hnot
  rcases chainSeq_view ℓ m h c hm (show t ≤ (ℓ + 1) * (m - 1) by omega) with
    ⟨i, hi, -, e⟩ | ⟨i, a, hi, ha, -, e⟩
  · rw [e]; exact Finset.mem_coe.2 (hR i hi)
  · rw [e]; exact Finset.mem_coe.2 (hcR i hi a ha)

/-- **Item 4 at G**: five hubs of `R`, consecutive pairs linked by edges `x_i y_i` of `G[Q]`
(`x_i`'s only hub `h_i`, `y_i`'s only hub `h_{i+1}`) in pairwise distinct bags: impossible. -/
theorem link_chain_contra (hmax : JointObject.PackingMaximal object packing) (hind : ∀ a ∈ hubs object, ∀ b ∈ hubs object, ¬ object.graph.Adj a b)
    (h : ℕ → object.Vertex) (b : ℕ → (gammaQ object packing).ConnectedComponent)
    (x y : ℕ → object.Vertex)
    (hS : ∀ i < 5, h i ∈ SR object packing) (hinj : ∀ i < 5, ∀ j < 5, h i = h j → i = j)
    (hb : ∀ i < 4, ∀ j < 4, b i = b j → i = j)
    (hl : ∀ i < 4, object.graph.Adj (h i) (x i) ∧ object.graph.Adj (h (i + 1)) (y i) ∧
      object.graph.Adj (x i) (y i) ∧ x i ∈ Q object packing ∧ y i ∈ Q object packing ∧
      OneHub object (x i) (h i) ∧ OneHub object (y i) (h (i + 1)) ∧ bag object packing (x i) = b i) :
    False := by
  let c : ℕ → ℕ → object.Vertex := fun i a => if a = 0 then x i else y i
  have hcQ : ∀ i < 4, ∀ a < 2, c i a ∈ Q object packing ∧ bag object packing (c i a) = b i := by
    intro i hi a ha
    obtain ⟨-, -, a3, hx, hy, -, -, hbx⟩ := hl i hi
    interval_cases a
    · exact ⟨hx, hbx⟩
    · exact ⟨hy, (bag_eq_of_adj hx hy a3).symm.trans hbx⟩
  have hSH : ∀ j < 5, h j ∈ hubs object := fun j hj => (mem_SR.1 (hS j hj)).1
  refine chain_contra hmax 2 5 (by norm_num) (by norm_num) (by norm_num) h c ?_ ?_ ?_ ?_ ?_ ?_
  · intro i hi j hj hij
    exact ⟨hind _ (hSH i hi) _ (hSH j hj), fun e => hij (hinj i hi j hj e)⟩
  · intro i hi a ha a' ha'
    obtain ⟨-, -, a3, -, -, -, -, -⟩ := hl i (by omega)
    have hxy : x i ≠ y i := object.graph.ne_of_adj a3
    interval_cases a <;> interval_cases a' <;>
      simp [c, a3, a3.symm, hxy, hxy.symm]
  · intro i hi a ha j hj
    obtain ⟨a1, a2, a3, hx, hy, o1, o2, -⟩ := hl i (by omega)
    have hne : c i a ≠ h j := by
      intro e
      have := (mem_Q.1 (hcQ i (by omega) a ha).1).2
      rw [e] at this; exact this (hSH j hj)
    refine ⟨?_, hne⟩
    interval_cases a
    · show object.graph.Adj (x i) (h j) ↔ _
      constructor
      · intro hadj
        left; exact ⟨hinj j hj i (by omega) (o1 _ (hSH j hj) hadj), rfl⟩
      · rintro (⟨rfl, -⟩ | ⟨-, hc⟩)
        · exact a1.symm
        · omega
    · show object.graph.Adj (y i) (h j) ↔ _
      constructor
      · intro hadj
        right; exact ⟨hinj j hj (i + 1) (by omega) (o2 _ (hSH j hj) hadj), rfl⟩
      · rintro (⟨-, hc⟩ | ⟨rfl, -⟩)
        · omega
        · exact a2.symm
  · intro i hi j hj hij a ha a' ha'
    obtain ⟨hQ1, hb1⟩ := hcQ i (by omega) a ha
    obtain ⟨hQ2, hb2⟩ := hcQ j (by omega) a' ha'
    refine ⟨fun hadj => hij (hb i (by omega) j (by omega) ?_), fun e => hij (hb i (by omega) j
      (by omega) ?_)⟩
    · rw [← hb1, ← hb2]; exact bag_eq_of_adj hQ1 hQ2 hadj
    · rw [← hb1, ← hb2, e]
  · intro i hi; exact (mem_SR.1 (hS i hi)).2
  · intro i hi a ha; exact (mem_Q.1 (hcQ i (by omega) a ha).1).1

/-- Five-entry sequences. -/
def five {α : Type*} (a₀ a₁ a₂ a₃ a₄ : α) : ℕ → α
  | 0 => a₀
  | 1 => a₁
  | 2 => a₂
  | 3 => a₃
  | _ => a₄

/-- **No rainbow 5-path of links among the hubs of `R`.** -/
theorem no_rainbow (hmax : JointObject.PackingMaximal object packing) (hind : ∀ a ∈ hubs object, ∀ b ∈ hubs object, ¬ object.graph.Adj a b) :
    ¬ Rainbow5 (LinkVia object packing) (SR object packing) := by
  rintro ⟨h₁, h₂, h₃, h₄, h₅, b₁, b₂, b₃, b₄, m1, m2, m3, m4, m5,
    n12, n13, n14, n15, n23, n24, n25, n34, n35, n45,
    c12, c13, c14, c23, c24, c34, l1, l2, l3, l4⟩
  obtain ⟨-, -, -, x₁, y₁, p1, q1, r1, sx1, sy1, o1, o1', e1⟩ := l1
  obtain ⟨-, -, -, x₂, y₂, p2, q2, r2, sx2, sy2, o2, o2', e2⟩ := l2
  obtain ⟨-, -, -, x₃, y₃, p3, q3, r3, sx3, sy3, o3, o3', e3⟩ := l3
  obtain ⟨-, -, -, x₄, y₄, p4, q4, r4, sx4, sy4, o4, o4', e4⟩ := l4
  refine link_chain_contra hmax hind (five h₁ h₂ h₃ h₄ h₅) (five b₁ b₂ b₃ b₄ b₄)
    (five x₁ x₂ x₃ x₄ x₄) (five y₁ y₂ y₃ y₄ y₄) ?_ ?_ ?_ ?_
  · intro i hi; interval_cases i <;> assumption
  · intro i hi j hj e
    interval_cases i <;> interval_cases j <;> simp only [five] at e <;>
      first | rfl | exact absurd e (by assumption) | exact absurd e.symm (by assumption)
  · intro i hi j hj e
    interval_cases i <;> interval_cases j <;> simp only [five] at e <;>
      first | rfl | exact absurd e (by assumption) | exact absurd e.symm (by assumption)
  · intro i hi
    interval_cases i
    · exact ⟨p1, q1, r1, sx1, sy1, o1, o1', e1⟩
    · exact ⟨p2, q2, r2, sx2, sy2, o2, o2', e2⟩
    · exact ⟨p3, q3, r3, sx3, sy3, o3, o3', e3⟩
    · exact ⟨p4, q4, r4, sx4, sy4, o4, o4', e4⟩

end Chains

/-! ## Degeneracy of the link graph -/

section Degenerate

variable {object : Graph.FiniteObject.{u}} {packing : Finset (Finset object.Vertex)}

/-- **Link degeneracy**: every nonempty set of hubs of `R` has a hub with at most
`3·6142 + 3 = 18429` link partners inside it. -/
theorem link_degenerate (hmax : JointObject.PackingMaximal object packing) (base : MinimumDegreeAtLeast 3 object)
    (hind : ∀ a ∈ hubs object, ∀ b ∈ hubs object, ¬ object.graph.Adj a b) :
    ∀ T ⊆ SR object packing, T.Nonempty → ∃ h ∈ T, (part (LinkVia object packing) T h).card ≤ 18429 :=
  part_degenerate (LinkVia object packing) 6142 (cap hmax base) (SR object packing) (no_rainbow hmax hind)

/-- **Strong degeneracy**: every nonempty set of hubs of `R` has a hub with at most 3 strong
partners (linked through `≥ 4` bags) inside it. -/
theorem strong_degenerate (hmax : JointObject.PackingMaximal object packing)
    (hind : ∀ a ∈ hubs object, ∀ b ∈ hubs object, ¬ object.graph.Adj a b) :
    ∀ T ⊆ SR object packing, T.Nonempty → ∃ h ∈ T, (spart (LinkVia object packing) T h).card ≤ 3 :=
  spart_degenerate (LinkVia object packing) (SR object packing) (no_rainbow hmax hind)

/-- **Linked pairs**: `Σ_{h∈S_R} #partners_{S_R}(h) ≤ 36858 h_R`. -/
theorem link_pairs (hmax : JointObject.PackingMaximal object packing) (base : MinimumDegreeAtLeast 3 object)
    (hind : ∀ a ∈ hubs object, ∀ b ∈ hubs object, ¬ object.graph.Adj a b) :
    ∑ h ∈ SR object packing, (part (LinkVia object packing) (SR object packing) h).card
      ≤ 36858 * hubsR object packing := by
  have := degenerate_sum (fun h h' => ∃ b, LinkVia object packing h h' b)
    (fun a b ⟨c, l⟩ => ⟨c, l.symm⟩) 18429 (SR object packing) (link_degenerate hmax base hind)
  rw [SR_card] at this
  simpa [part] using this

/-- **Strong pairs**: `Σ_{h∈S_R} #strong partners_{S_R}(h) ≤ 6 h_R`. -/
theorem strong_pairs (hmax : JointObject.PackingMaximal object packing)
    (hind : ∀ a ∈ hubs object, ∀ b ∈ hubs object, ¬ object.graph.Adj a b) :
    ∑ h ∈ SR object packing, (spart (LinkVia object packing) (SR object packing) h).card
      ≤ 6 * hubsR object packing := by
  have := degenerate_sum (fun h h' => SLk (LinkVia object packing) h h')
    (fun a b ⟨B, hB, l⟩ => ⟨B, hB, fun c hc => (l c hc).symm⟩) 3 (SR object packing)
    (strong_degenerate hmax hind)
  rw [SR_card] at this
  simpa [spart] using this

/-- The vertices `x ∈ N(h) ∩ Q` linked to `h'` (the `x`-side of the pair's links). -/
noncomputable def linkX (object : Graph.FiniteObject.{u}) (packing : Finset (Finset object.Vertex)) (h h' : object.Vertex) :
    Finset object.Vertex :=
  univ.filter (fun x => ∃ y, object.graph.Adj h x ∧ object.graph.Adj h' y ∧
    object.graph.Adj x y ∧ x ∈ Q object packing ∧ y ∈ Q object packing ∧ OneHub object x h ∧
    OneHub object y h')

/-- **Weak capacity**: a pair of hubs linked through fewer than 4 bags carries at most
`3·6142` linked vertices. -/
theorem weak_capacity (hmax : JointObject.PackingMaximal object packing) (base : MinimumDegreeAtLeast 3 object) {h h' : object.Vertex}
    (hh : h ∈ hubs object) (hh' : h' ∈ hubs object) (hne : h ≠ h')
    (hweak : ¬ SLk (LinkVia object packing) h h') : (linkX object packing h h').card ≤ 3 * 6142 := by
  set B := (linkX object packing h h').image (bag object packing) with hBdef
  have hBl : ∀ c ∈ B, LinkVia object packing h h' c := by
    intro c hc
    obtain ⟨x, hx, rfl⟩ := mem_image.1 hc
    simp only [linkX, mem_filter, mem_univ, true_and] at hx
    obtain ⟨y, a1, a2, a3, sx, sy, o1, o2⟩ := hx
    exact ⟨hh, hh', hne, x, y, a1, a2, a3, sx, sy, o1, o2, rfl⟩
  have hB3 : B.card ≤ 3 := by
    by_contra hc; push Not at hc
    exact hweak ⟨B, by omega, hBl⟩
  have hsub : linkX object packing h h' ⊆
      B.biUnion (fun c => univ.filter (fun y => y ∈ Q object packing ∧ bag object packing y = c)) := by
    intro x hx
    refine mem_biUnion.2 ⟨bag object packing x, mem_image_of_mem _ hx, ?_⟩
    simp only [linkX, mem_filter, mem_univ, true_and] at hx ⊢
    obtain ⟨y, a1, a2, a3, sx, -⟩ := hx
    exact ⟨sx, by trivial⟩
  calc (linkX object packing h h').card ≤ _ := card_le_card hsub
    _ ≤ ∑ c ∈ B, (univ.filter (fun y => y ∈ Q object packing ∧ bag object packing y = c)).card :=
        card_biUnion_le
    _ ≤ ∑ c ∈ B, 6142 := sum_le_sum (fun c _ => fibre_card hmax base c)
    _ = B.card * 6142 := by rw [sum_const, smul_eq_mul]
    _ ≤ 3 * 6142 := Nat.mul_le_mul_right _ hB3

end Degenerate


section Connect

variable {object : Graph.FiniteObject.{u}} {packing : Finset (Finset object.Vertex)}

/-- `h` and `h'` meet a common bag. -/
def BagLink (object : Graph.FiniteObject.{u}) (packing : Finset (Finset object.Vertex)) (h h' : object.Vertex) : Prop :=
  ∃ u v, u ∈ Q object packing ∧ v ∈ Q object packing ∧ object.graph.Adj h u ∧ object.graph.Adj h' v ∧
    bag object packing u = bag object packing v

theorem LinkVia.bagLink {h h' : object.Vertex} {b} (l : LinkVia object packing h h' b) :
    BagLink object packing h h' := by
  obtain ⟨-, -, -, x, y, a1, a2, a3, hx, hy, -, -, -⟩ := l
  exact ⟨x, y, hx, hy, a1, a2, bag_eq_of_adj hx hy a3⟩

/-- `T ⊆ S_R` with no bag-link to `S_R ∖ T`. -/
def Closed (object : Graph.FiniteObject.{u}) (packing : Finset (Finset object.Vertex)) (T : Finset object.Vertex) : Prop :=
  T ⊆ SR object packing ∧ ∀ h ∈ T, ∀ h' ∈ SR object packing, BagLink object packing h h' → h' ∈ T

/-- `T` and every bag meeting `N(T)`. -/
noncomputable def closure (object : Graph.FiniteObject.{u}) (packing : Finset (Finset object.Vertex)) (T : Finset object.Vertex) :
    Finset object.Vertex :=
  T ∪ (Q object packing).filter (fun v => ∃ h ∈ T, ∃ u ∈ Q object packing,
    object.graph.Adj h u ∧ bag object packing u = bag object packing v)

theorem closure_sub_R {T : Finset object.Vertex} (hT : Closed object packing T) :
    closure object packing T ⊆ object.remainderSupport packing := by
  intro v hv
  rcases mem_union.1 hv with h | h
  · exact (mem_SR.1 (hT.1 h)).2
  · exact (mem_Q.1 (mem_filter.1 h).1).1

/-- **Every edge leaving the closure of a closed set ends in `W`.** -/
theorem closure_out_edges
    (hind : ∀ a ∈ hubs object, ∀ b ∈ hubs object, ¬ object.graph.Adj a b)
    {T : Finset object.Vertex} (hT : Closed object packing T) {x w : object.Vertex}
    (hx : x ∈ closure object packing T) (hxw : object.graph.Adj x w) (hw : w ∉ closure object packing T) :
    w ∉ object.remainderSupport packing := by
  intro hwR
  rcases mem_union.1 hx with hxT | hxQ
  · -- `x` is a hub of `T`: `w` is cubic, in `Q`, meeting `N(x)`
    have hxH := (mem_SR.1 (hT.1 hxT)).1
    have hwH : w ∉ hubs object := fun h => hind x hxH w h hxw
    have hwQ : w ∈ Q object packing := mem_Q.2 ⟨hwR, hwH⟩
    exact hw (mem_union_right _ (mem_filter.2 ⟨hwQ, x, hxT, w, hwQ, hxw, rfl⟩))
  · obtain ⟨hxQ', h, hhT, u, huQ, hhu, hbu⟩ := mem_filter.1 hxQ
    by_cases hwH : w ∈ hubs object
    · -- `w` is a hub of `R` bag-linked to `h`
      have hwS : w ∈ SR object packing := mem_SR.2 ⟨hwH, hwR⟩
      have hl : BagLink object packing h w := ⟨u, x, huQ, hxQ', hhu, hxw.symm, hbu⟩
      exact hw (mem_union_left _ (hT.2 h hhT w hwS hl))
    · have hwQ : w ∈ Q object packing := mem_Q.2 ⟨hwR, hwH⟩
      exact hw (mem_union_right _ (mem_filter.2 ⟨hwQ, h, hhT, u, huQ, hhu,
        hbu.trans (bag_eq_of_adj hxQ' hwQ hxw)⟩))

/-- **Disjoint closed sets have disjoint closures.** -/
theorem closure_disjoint {T T' : Finset object.Vertex} (hT : Closed object packing T)
    (hT' : Closed object packing T') (hd : Disjoint T T') :
    Disjoint (closure object packing T) (closure object packing T') := by
  rw [disjoint_left]
  intro v hv hv'
  rcases mem_union.1 hv with h1 | h1 <;> rcases mem_union.1 hv' with h2 | h2
  · exact disjoint_left.1 hd h1 h2
  · -- `v ∈ T` is a hub, but `h2` puts it in `Q`
    exact (mem_Q.1 (mem_filter.1 h2).1).2 (mem_SR.1 (hT.1 h1)).1
  · exact (mem_Q.1 (mem_filter.1 h1).1).2 (mem_SR.1 (hT'.1 h2)).1
  · obtain ⟨hvQ, h, hhT, u, huQ, hhu, hbu⟩ := mem_filter.1 h1
    obtain ⟨-, h', hhT', u', huQ', hhu', hbu'⟩ := mem_filter.1 h2
    have hl : BagLink object packing h h' := ⟨u, u', huQ, huQ', hhu, hhu', hbu.trans hbu'.symm⟩
    exact disjoint_left.1 hd (hT.2 h hhT h' (hT'.1 hhT') hl) hhT'

end Connect

section ClosedClasses

variable {object : Graph.FiniteObject.{u}} {packing : Finset (Finset object.Vertex)}

/-- **A nonempty closed set reaches `W`.** -/
theorem closed_reaches_W (base : MinimumDegreeAtLeast 3 object) (noProper : NoProperCubic object)
    (hind : ∀ a ∈ hubs object, ∀ b ∈ hubs object, ¬ object.graph.Adj a b)
    (valid : object.IsWindowPacking 13 packing) (hW : packing.Nonempty)
    {T : Finset object.Vertex} (hT : Closed object packing T) (hne : T.Nonempty) :
    ∃ x ∈ closure object packing T, ∃ w, object.graph.Adj x w ∧
      (x, w) ∈ object.windowRemainderIncidences packing := by
  have base := base
  have hsub := closure_sub_R hT
  -- a window vertex lies outside the closure
  obtain ⟨P, hP⟩ := hW
  have hPc := (window_degrees (valid.1 P hP)).1
  obtain ⟨z, hz⟩ : P.Nonempty := by rw [← card_pos]; omega
  have hzR : z ∉ object.remainderSupport packing :=
    fun h => (mem_remainderSupport.1 h) P hP hz
  have hne' : closure object packing T ≠ univ := by
    intro e; exact hzR (hsub (e ▸ mem_univ z))
  obtain ⟨h0, h0T⟩ := hne
  obtain ⟨v, hv, hle⟩ := properTwoLow noProper (closure object packing T)
    ⟨h0, mem_union_left _ h0T⟩ hne'
  -- `v` has a neighbour outside the closure
  have hdv := deg_ge base v
  have hex : ∃ w, object.graph.Adj v w ∧ w ∉ closure object packing T := by
    by_contra hall
    push Not at hall
    have : object.graph.neighborFinset v ⊆
        object.graph.neighborFinset v ∩ closure object packing T := by
      intro w hw
      exact mem_inter.2 ⟨hw, hall w (by simpa using hw)⟩
    have := card_le_card this
    rw [object.graph.card_neighborFinset_eq_degree] at this
    omega
  obtain ⟨w, hvw, hw⟩ := hex
  have hwR := closure_out_edges hind hT hv hvw hw
  refine ⟨v, hv, w, hvw, ?_⟩
  have hvR := hsub hv
  unfold FiniteObject.windowRemainderIncidences
  simp only [mem_biUnion, mem_image, mem_inter, SimpleGraph.mem_neighborFinset]
  refine ⟨v, hvR, w, ⟨hvw, ?_⟩, rfl⟩
  have : ∃ P ∈ packing, w ∈ P := by
    by_contra hno; push Not at hno; exact hwR (mem_remainderSupport.2 hno)
  exact mem_windowSupport.2 this

/-- **Item 3 at `[20a]`**: pairwise disjoint nonempty closed sets of hubs of `R` number at most
`e(R, W)`; and `e(R, W) + 2e× = 15ν + σ_W` (the join identity). -/
theorem closed_classes_le (base : MinimumDegreeAtLeast 3 object) (noProper : NoProperCubic object)
    (hind : ∀ a ∈ hubs object, ∀ b ∈ hubs object, ¬ object.graph.Adj a b)
    (valid : object.IsWindowPacking 13 packing) (hW : packing.Nonempty)
    (𝒯 : Finset (Finset object.Vertex))
    (hcl : ∀ T ∈ 𝒯, Closed object packing T ∧ T.Nonempty)
    (hdisj : ∀ T ∈ 𝒯, ∀ T' ∈ 𝒯, T ≠ T' → Disjoint T T') :
    𝒯.card ≤ (object.windowRemainderIncidences packing).card := by
  · have pick : ∀ T ∈ 𝒯, ∃ e : object.Vertex × object.Vertex,
        e.1 ∈ closure object packing T ∧
          e ∈ object.windowRemainderIncidences packing := by
      intro T hT
      obtain ⟨x, hx, w, -, hmem⟩ := closed_reaches_W base noProper hind valid hW (hcl T hT).1 (hcl T hT).2
      exact ⟨(x, w), hx, hmem⟩
    rcases 𝒯.eq_empty_or_nonempty with h𝒯 | ⟨T0, hT0⟩
    · rw [h𝒯]; simp
    haveI : Nonempty (object.Vertex × object.Vertex) :=
      ⟨(pick T0 hT0).choose⟩
    choose! f hf1 hf2 using pick
    refine card_le_card_of_injOn f (fun T hT => hf2 T hT) ?_
    intro T hT T' hT' e
    by_contra hne
    have hd := closure_disjoint (hcl T hT).1 (hcl T' hT').1 (hdisj T hT T' hT' hne)
    have h1 := hf1 T hT
    have h2 := hf1 T' hT'
    rw [show f T = f T' from e] at h1
    exact disjoint_left.1 hd h1 h2
end ClosedClasses



section TwoDefs

variable (object : Graph.FiniteObject.{u}) (packing : Finset (Finset object.Vertex))

/-- Common-neighbour link. -/
def Lk2 (a b x : object.Vertex) : Prop :=
  a ∈ hubs object ∧ b ∈ hubs object ∧ a ≠ b ∧ x ∈ Q object packing ∧ object.graph.Adj a x ∧
    object.graph.Adj b x ∧ ∀ w ∈ hubs object, object.graph.Adj x w → w = a ∨ w = b

/-- The forbid map of `Lk2`: a cubic `x` forbids itself and its neighbours. -/
noncomputable def F2 (x : object.Vertex) : Finset object.Vertex :=
  if x ∈ hubs object then {x} else insert x (object.graph.neighborFinset x)

/-- Two-hop link at the centre `c`. -/
def LkJ (c a b : object.Vertex) (B : (gammaQ object packing).ConnectedComponent) : Prop :=
  a ∈ hubs object ∧ b ∈ hubs object ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
    ∃ y x z, object.graph.Adj a y ∧ object.graph.Adj y x ∧ object.graph.Adj x z ∧
      object.graph.Adj z b ∧ ¬ object.graph.Adj y z ∧ y ∈ Q object packing ∧ x ∈ Q object packing ∧
      z ∈ Q object packing ∧ OneHub object y a ∧ OneHub object x c ∧ OneHub object z b ∧
      bag object packing x = B

end TwoDefs

section Two

variable {object : Graph.FiniteObject.{u}} {packing : Finset (Finset object.Vertex)}

theorem Lk2.symm {a b x : object.Vertex} (l : Lk2 object packing a b x) : Lk2 object packing b a x := by
  obtain ⟨ha, hb, hne, hx, a1, a2, hw⟩ := l
  exact ⟨hb, ha, hne.symm, hx, a2, a1, fun w hw' hxw => (hw w hw' hxw).symm⟩

theorem cap2 : ∀ a x, (univ.filter (fun b => Lk2 object packing a b x)).card ≤ 1 := by
  intro a x
  rw [card_le_one]
  intro b hb b' hb'
  simp only [mem_filter, mem_univ, true_and] at hb hb'
  rcases hb'.2.2.2.2.2.2 b hb.2.1 hb.2.2.2.2.2.1.symm with e | e
  · exact absurd e.symm hb.2.2.1
  · exact e

theorem F2_card (base : MinimumDegreeAtLeast 3 object) (x : object.Vertex) :
    (F2 object x).card ≤ 4 := by
  unfold F2
  split_ifs with hx
  · simp
  · refine (card_insert_le _ _).trans ?_
    rw [object.graph.card_neighborFinset_eq_degree, cubic_of_not_hub hx]

theorem mem_Q_not_hub {x : object.Vertex} (hx : x ∈ Q object packing) : x ∉ hubs object :=
  (mem_Q.1 hx).2

/-- **Seven common-neighbour-linked hubs of `R` form an induced `P13`.** -/
theorem no_path2 (hmax : JointObject.PackingMaximal object packing) (hind : ∀ a ∈ hubs object, ∀ b ∈ hubs object, ¬ object.graph.Adj a b) :
    ∀ h b, ¬ FPath (Lk2 object packing) (F2 object) (SR object packing) 6 h b := by
  rintro h x ⟨hS, hinj, hl, hav⟩
  have hSH : ∀ j ≤ 6, h j ∈ hubs object := fun j hj => (mem_SR.1 (hS j hj)).1
  refine chain_contra hmax 1 7 le_rfl (by norm_num) (by norm_num) h (fun i _ => x i)
    ?_ ?_ ?_ ?_ ?_ ?_
  · intro i hi j hj hij
    exact ⟨hind _ (hSH i (by omega)) _ (hSH j (by omega)),
      fun e => hij (hinj i (by omega) j (by omega) e)⟩
  · intro i hi a ha b hb
    have : a = 0 := by omega
    have : b = 0 := by omega
    subst_vars
    simp
  · intro i hi a ha j hj
    have ha0 : a = 0 := by omega
    subst ha0
    obtain ⟨-, -, -, hxQ, a1, a2, hw⟩ := hl i (by omega)
    refine ⟨⟨fun hadj => ?_, ?_⟩, fun e => mem_Q_not_hub hxQ (e ▸ hSH j (by omega))⟩
    · rcases hw _ (hSH j (by omega)) hadj with e | e
      · left; exact ⟨hinj j (by omega) i (by omega) e, rfl⟩
      · right; exact ⟨hinj j (by omega) (i + 1) (by omega) e, rfl⟩
    · rintro (⟨rfl, -⟩ | ⟨rfl, -⟩)
      · exact a1.symm
      · exact a2.symm
  · intro i hi j hj hij a ha b hb
    have key : ∀ i j, i + 1 < 7 → j < i → ¬ object.graph.Adj (x i) (x j) ∧ x i ≠ x j := by
      intro i j hi hji
      have hn := hav i (by omega) j hji
      have hxQ := (hl j (by omega)).2.2.2.1
      simp only [F2, mem_Q_not_hub hxQ, if_false, mem_insert, SimpleGraph.mem_neighborFinset,
        not_or] at hn
      exact ⟨fun h' => hn.2 h'.symm, hn.1⟩
    rcases lt_or_gt_of_ne hij with hlt | hlt
    · have := key j i hj hlt
      exact ⟨fun h' => this.1 h'.symm, fun e => this.2 e.symm⟩
    · exact key i j hi hlt
  · intro i hi; exact (mem_SR.1 (hS i (by omega))).2
  · intro i hi a ha; exact (mem_Q.1 (hl i (by omega)).2.2.2.1).1

/-- **Common-neighbour degeneracy**: every nonempty set of hubs of `R` has one with at most 25
common-neighbour partners in it. -/
theorem degenerate2 (hmax : JointObject.PackingMaximal object packing) (base : MinimumDegreeAtLeast 3 object)
    (hind : ∀ a ∈ hubs object, ∀ b ∈ hubs object, ¬ object.graph.Adj a b) :
    ∀ T ⊆ SR object packing, T.Nonempty → ∃ h ∈ T, (part (Lk2 object packing) T h).card ≤ 25 := by
  intro T hTS hT
  obtain ⟨t, ht⟩ := hT
  haveI : Nonempty object.Vertex := ⟨t⟩
  have := greedy_degenerate (Lk2 object packing) 1 4 (fun a x => cap2 a x) (F2 object)
    (F2_card base) (SR object packing) 5 (no_path2 hmax hind) T hTS ⟨t, ht⟩
  simpa using this

/-- **Common-neighbour pairs**: `Σ_{a∈S_R} #partners ≤ 50 h_R`. -/
theorem sum2 (hmax : JointObject.PackingMaximal object packing) (base : MinimumDegreeAtLeast 3 object)
    (hind : ∀ a ∈ hubs object, ∀ b ∈ hubs object, ¬ object.graph.Adj a b) :
    ∑ h ∈ SR object packing, (part (Lk2 object packing) (SR object packing) h).card
      ≤ 50 * hubsR object packing := by
  have := degenerate_sum (fun h h' => ∃ x, Lk2 object packing h h' x)
    (fun a b ⟨c, l⟩ => ⟨c, l.symm⟩) 25 (SR object packing) (degenerate2 hmax base hind)
  rw [SR_card] at this
  simpa [part] using this

end Two

section J

variable {object : Graph.FiniteObject.{u}} {packing : Finset (Finset object.Vertex)}

theorem LkJ.symm {c a b : object.Vertex} {B} (l : LkJ object packing c a b B) : LkJ object packing c b a B := by
  obtain ⟨ha, hb, hab, hac, hbc, y, x, z, a1, a2, a3, a4, n, sy, sx, sz, o1, o2, o3, e⟩ := l
  exact ⟨hb, ha, hab.symm, hbc, hac, z, x, y, a4.symm, a3.symm, a2.symm, a1.symm,
    fun h => n h.symm, sz, sx, sy, o3, o2, o1, e⟩

theorem capJ (hmax : JointObject.PackingMaximal object packing) (base : MinimumDegreeAtLeast 3 object) (c : object.Vertex) :
    ∀ a B, (univ.filter (fun b => LkJ object packing c a b B)).card ≤ 6142 := by
  intro a B
  calc _ ≤ ((univ.filter (fun y => y ∈ Q object packing ∧ bag object packing y = B)).image hubOf).card :=
        card_le_card ?_
    _ ≤ _ := card_image_le
    _ ≤ 6142 := fibre_card hmax base B
  intro b hb
  simp only [mem_filter, mem_univ, true_and] at hb
  obtain ⟨-, hbH, -, -, -, y, x, z, a1, a2, a3, a4, n, sy, sx, sz, o1, o2, o3, e⟩ := hb
  refine mem_image.2 ⟨z, ?_, hubOf_eq hbH a4 o3⟩
  simp only [mem_filter, mem_univ, true_and]
  exact ⟨sz, (bag_eq_of_adj sx sz a3).symm.trans e⟩

/-- **Four two-hop-linked hubs of `R` (at a common centre, three distinct bags) form an induced
`P13`.** -/
theorem no_pathJ (hmax : JointObject.PackingMaximal object packing) (hind : ∀ a ∈ hubs object, ∀ b ∈ hubs object, ¬ object.graph.Adj a b)
    (c : object.Vertex) :
    ∀ h B, ¬ FPath (LkJ object packing c) (fun B => {B}) (SR object packing) 3 h B := by
  rintro h B ⟨hS, hinj, hl, hav⟩
  have hSH : ∀ j ≤ 3, h j ∈ hubs object := fun j hj => (mem_SR.1 (hS j hj)).1
  have hnc : ∀ j ≤ 3, h j ≠ c := by
    intro j hj
    by_cases e : j = 3
    · subst e; exact (hl 2 (by omega)).2.2.2.2.1
    · exact (hl j (by omega)).2.2.2.1
  have ex : ∀ i, i < 3 → ∃ y x z, object.graph.Adj (h i) y ∧ object.graph.Adj y x ∧
      object.graph.Adj x z ∧ object.graph.Adj z (h (i + 1)) ∧ ¬ object.graph.Adj y z ∧
      y ∈ Q object packing ∧ x ∈ Q object packing ∧ z ∈ Q object packing ∧ OneHub object y (h i) ∧
      OneHub object x c ∧ OneHub object z (h (i + 1)) ∧ bag object packing x = B i :=
    fun i hi => (hl i hi).2.2.2.2.2
  haveI : Nonempty object.Vertex := ⟨c⟩
  choose! y x z hyxz using ex
  let cc : ℕ → ℕ → object.Vertex := fun i a => if a = 0 then y i else if a = 1 then x i else z i
  have hbag : ∀ i < 3, ∀ a < 3, cc i a ∈ Q object packing ∧ bag object packing (cc i a) = B i := by
    intro i hi a ha
    obtain ⟨a1, a2, a3, a4, n, sy, sx, sz, o1, o2, o3, e⟩ := hyxz i hi
    interval_cases a
    · exact ⟨sy, (bag_eq_of_adj sy sx a2).trans e⟩
    · exact ⟨sx, e⟩
    · exact ⟨sz, (bag_eq_of_adj sx sz a3).symm.trans e⟩
  refine chain_contra hmax 3 4 (by norm_num) (by norm_num) (by norm_num) h cc ?_ ?_ ?_ ?_ ?_ ?_
  · intro i hi j hj hij
    exact ⟨hind _ (hSH i (by omega)) _ (hSH j (by omega)),
      fun e => hij (hinj i (by omega) j (by omega) e)⟩
  · intro i hi a ha b hb
    obtain ⟨a1, a2, a3, a4, n, sy, sx, sz, o1, o2, o3, e⟩ := hyxz i (by omega)
    have hyx : y i ≠ x i := object.graph.ne_of_adj a2
    have hxz : x i ≠ z i := object.graph.ne_of_adj a3
    have hyz : y i ≠ z i := by
      intro e'
      have := o1 _ (hSH (i + 1) (by omega)) (e' ▸ a4)
      exact absurd (hinj (i + 1) (by omega) i (by omega) this) (by omega)
    have n' : ¬ object.graph.Adj (z i) (y i) := fun h' => n h'.symm
    interval_cases a <;> interval_cases b <;>
      simp [cc, a2, a2.symm, a3, a3.symm, n, n', hyx, hyx.symm, hxz, hxz.symm, hyz, hyz.symm]
  · intro i hi a ha j hj
    obtain ⟨a1, a2, a3, a4, n, sy, sx, sz, o1, o2, o3, e⟩ := hyxz i (by omega)
    have hne : cc i a ≠ h j := by
      intro e'
      exact mem_Q_not_hub (hbag i (by omega) a ha).1 (e' ▸ hSH j (by omega))
    refine ⟨?_, hne⟩
    interval_cases a
    · show object.graph.Adj (y i) (h j) ↔ _
      constructor
      · intro hadj; left; exact ⟨hinj j (by omega) i (by omega) (o1 _ (hSH j (by omega)) hadj), rfl⟩
      · rintro (⟨rfl, -⟩ | ⟨-, hc⟩)
        · exact a1.symm
        · omega
    · show object.graph.Adj (x i) (h j) ↔ _
      constructor
      · intro hadj; exact absurd (o2 _ (hSH j (by omega)) hadj) (hnc j (by omega))
      · rintro (⟨-, hc⟩ | ⟨-, hc⟩) <;> omega
    · show object.graph.Adj (z i) (h j) ↔ _
      constructor
      · intro hadj
        right; exact ⟨hinj j (by omega) (i + 1) (by omega) (o3 _ (hSH j (by omega)) hadj), rfl⟩
      · rintro (⟨-, hc⟩ | ⟨rfl, -⟩)
        · omega
        · exact a4
  · intro i hi j hj hij a ha b hb
    obtain ⟨hQ1, hb1⟩ := hbag i (by omega) a ha
    obtain ⟨hQ2, hb2⟩ := hbag j (by omega) b hb
    have hBne : B i ≠ B j := by
      rcases lt_or_gt_of_ne hij with hlt | hlt
      · have := hav j (by omega) i hlt
        simp only [mem_singleton] at this
        exact fun e => this e.symm
      · have := hav i (by omega) j hlt
        simpa using this
    refine ⟨fun hadj => hBne ?_, fun e => hBne ?_⟩
    · rw [← hb1, ← hb2]; exact bag_eq_of_adj hQ1 hQ2 hadj
    · rw [← hb1, ← hb2, e]
  · intro i hi; exact (mem_SR.1 (hS i (by omega))).2
  · intro i hi a ha; exact (mem_Q.1 (hbag i (by omega) a ha).1).1

/-- **Two-hop degeneracy at a centre `c`.** -/
theorem degenerateJ (hmax : JointObject.PackingMaximal object packing) (base : MinimumDegreeAtLeast 3 object)
    (hind : ∀ a ∈ hubs object, ∀ b ∈ hubs object, ¬ object.graph.Adj a b) (c : object.Vertex) :
    ∀ T ⊆ SR object packing, T.Nonempty → ∃ h ∈ T, (part (LkJ object packing c) T h).card ≤ 12286 := by
  intro T hTS hT
  obtain ⟨t, ht⟩ := hT
  haveI : Nonempty (gammaQ object packing).ConnectedComponent :=
    ⟨(gammaQ object packing).connectedComponentMk t⟩
  have := greedy_degenerate (LkJ object packing c) 6142 1 (capJ hmax base c) (fun B => {B})
    (fun B => by simp) (SR object packing) 2 (no_pathJ hmax hind c) T hTS ⟨t, ht⟩
  simpa using this

/-- **Two-hop pairs at `c` inside any `S ⊆ S_R`**: `Σ_{a∈S} #partners_S ≤ 24572 |S|`. -/
theorem sumJ (hmax : JointObject.PackingMaximal object packing) (base : MinimumDegreeAtLeast 3 object)
    (hind : ∀ a ∈ hubs object, ∀ b ∈ hubs object, ¬ object.graph.Adj a b) (c : object.Vertex)
    (S : Finset object.Vertex) (hS : S ⊆ SR object packing) :
    ∑ a ∈ S, (part (LkJ object packing c) S a).card ≤ 24572 * S.card := by
  have := degenerate_sum (fun a b => ∃ B, LkJ object packing c a b B)
    (fun a b ⟨B, l⟩ => ⟨B, l.symm⟩) 12286 S
    (fun T hT hne => degenerateJ hmax base hind c T (hT.trans hS) hne)
  simpa [part] using this

end J


section Near

variable (object : Graph.FiniteObject.{u}) (packing : Finset (Finset object.Vertex))

/-- `W`. -/
noncomputable def Wset : Finset object.Vertex := FiniteObject.windowSupport packing

/-- `D₁`: vertices of `R` with a neighbour in `W`. -/
noncomputable def D1 : Finset object.Vertex :=
  (object.remainderSupport packing).filter (fun v => ∃ w ∈ Wset object packing, object.graph.Adj v w)

/-- `D₂`: vertices with a cubic neighbour in `D₁`. -/
noncomputable def D2 : Finset object.Vertex :=
  univ.filter (fun v => ∃ z ∈ D1 object packing, z ∉ hubs object ∧ object.graph.Adj v z)

/-- The near-window set `B_W = W ∪ D₁ ∪ D₂`. -/
noncomputable def Bw : Finset object.Vertex := Wset object packing ∪ D1 object packing ∪ D2 object packing

variable {object packing}

theorem notB_R {v : object.Vertex} (hv : v ∉ Bw object packing) :
    v ∈ object.remainderSupport packing := by
  refine mem_remainderSupport.2 (fun P hP hvP => hv ?_)
  exact mem_union_left _ (mem_union_left _ (mem_windowSupport.2 ⟨P, hP, hvP⟩))

theorem notB_nbr {v u : object.Vertex} (hv : v ∉ Bw object packing) (hvu : object.graph.Adj v u) :
    u ∈ object.remainderSupport packing := by
  refine mem_remainderSupport.2 (fun P hP huP => hv ?_)
  refine mem_union_left _ (mem_union_right _ (mem_filter.2 ⟨notB_R hv, u, ?_, hvu⟩))
  exact mem_windowSupport.2 ⟨P, hP, huP⟩

theorem notB_nbr2 {v z w : object.Vertex} (hv : v ∉ Bw object packing) (hvz : object.graph.Adj v z)
    (hz : z ∉ hubs object) (hzw : object.graph.Adj z w) :
    w ∈ object.remainderSupport packing := by
  refine mem_remainderSupport.2 (fun P hP hwP => hv ?_)
  refine mem_union_right _ (mem_filter.2 ⟨mem_univ _, z, ?_, hz, hvz⟩)
  exact mem_filter.2 ⟨notB_nbr hv hvz, w, mem_windowSupport.2 ⟨P, hP, hwP⟩, hzw⟩

theorem Wset_card (valid : object.IsWindowPacking 13 packing) :
    (Wset object packing).card = 13 * packing.card := by
  have hW := object.windowSupport_card_eq valid
  unfold Wset
  convert hW using 2

theorem D1_card :
    (D1 object packing).card ≤ (object.windowRemainderIncidences packing).card := by
  calc (D1 object packing).card
      ≤ ((object.windowRemainderIncidences packing).image Prod.fst).card := card_le_card ?_
    _ ≤ _ := card_image_le
  · intro v hv
    obtain ⟨hvR, w, hwW, hvw⟩ := mem_filter.1 hv
    refine mem_image.2 ⟨(v, w), ?_, rfl⟩
    unfold FiniteObject.windowRemainderIncidences
    simp only [mem_biUnion, mem_image, mem_inter, SimpleGraph.mem_neighborFinset]
    exact ⟨v, hvR, w, ⟨hvw, hwW⟩, rfl⟩

theorem D2_card (base : MinimumDegreeAtLeast 3 object) :
    (D2 object packing).card ≤ 3 * (D1 object packing).card := by
  have hsub : D2 object packing ⊆ ((D1 object packing).filter (· ∉ hubs object)).biUnion
      (fun z => object.graph.neighborFinset z) := by
    intro v hv
    obtain ⟨-, z, hz, hzH, hvz⟩ := mem_filter.1 hv
    exact mem_biUnion.2 ⟨z, mem_filter.2 ⟨hz, hzH⟩, by simpa using hvz.symm⟩
  calc _ ≤ _ := card_le_card hsub
    _ ≤ ∑ z ∈ (D1 object packing).filter (· ∉ hubs object), (object.graph.neighborFinset z).card :=
        card_biUnion_le
    _ = ∑ z ∈ (D1 object packing).filter (· ∉ hubs object), 3 := by
        apply sum_congr rfl; intro z hz
        rw [object.graph.card_neighborFinset_eq_degree]
        exact cubic_of_not_hub (mem_filter.1 hz).2
    _ ≤ 3 * (D1 object packing).card := by
        rw [sum_const, smul_eq_mul, mul_comm]
        exact Nat.mul_le_mul_left _ (card_filter_le _ _)

/-- **`|B_W| ≤ 13ν + 4e(R,W)`.** -/
theorem Bw_card (base : MinimumDegreeAtLeast 3 object)
    (valid : object.IsWindowPacking 13 packing) :
    (Bw object packing).card
      ≤ 13 * packing.card + 4 * (object.windowRemainderIncidences packing).card := by
  have h1 := card_union_le (Wset object packing ∪ D1 object packing) (D2 object packing)
  have h2 := card_union_le (Wset object packing) (D1 object packing)
  have h3 := Wset_card valid
  have h4 := D1_card (object := object) (packing := packing)
  have h5 := D2_card (packing := packing) base
  unfold Bw
  omega

end Near

section Counts

variable {object : Graph.FiniteObject.{u}} {packing : Finset (Finset object.Vertex)}

theorem hubs_eq_Hset (hmax : JointObject.PackingMaximal object packing) (base : MinimumDegreeAtLeast 3 object)
    (noProper : NoProperCubic object) (slack : SlackIndependent object)
    (avoid : ¬ HasCycleWithLength Core.DyadicLength.PowerOfTwoLength object)
    (valid : object.IsWindowPacking 13 packing) :
    hubs object = JointSystem.Hset object.graph := by
  have base := base
  ext v
  simp only [JointSystem.Hset, mem_filter, mem_univ, true_and, mem_hubs]
  have := deg_ge base v
  constructor
  · intro h3
    have : 4 ≤ object.graph.degree v := by omega
    convert this using 2
  · intro h4 h3
    have : 4 ≤ object.graph.degree v := by convert h4 using 2
    omega

theorem mem_Hset_iff {v : object.Vertex} :
    v ∈ JointSystem.Hset object.graph ↔
      4 ≤ @SimpleGraph.degree _ object.graph v
        (@SimpleGraph.neighborSetFintype _ _ _ (fun a b => Classical.propDecidable _) v) := by
  simp [JointSystem.Hset]

theorem onehub_of_tc (hmax : JointObject.PackingMaximal object packing) (base : MinimumDegreeAtLeast 3 object)
    (noProper : NoProperCubic object) (slack : SlackIndependent object)
    (avoid : ¬ HasCycleWithLength Core.DyadicLength.PowerOfTwoLength object)
    (valid : object.IsWindowPacking 13 packing) {y a : object.Vertex}
    (ht : tc object.graph y = 1) (ha : a ∈ JointSystem.Hset object.graph)
    (hya : object.graph.Adj y a) : OneHub object y a := by
  intro w hw hyw
  rw [hubs_eq_Hset hmax base noProper slack avoid valid] at hw
  simp only [JointSystem.Hset, mem_filter, mem_univ, true_and] at ha hw
  exact tc_one_unique ht ha hya hw hyw

theorem Q_of_cubic (hmax : JointObject.PackingMaximal object packing) (base : MinimumDegreeAtLeast 3 object)
    (noProper : NoProperCubic object) (slack : SlackIndependent object)
    (avoid : ¬ HasCycleWithLength Core.DyadicLength.PowerOfTwoLength object)
    (valid : object.IsWindowPacking 13 packing) {v : object.Vertex}
    (hvR : v ∈ object.remainderSupport packing)
    (hv : v ∉ JointSystem.Hset object.graph) : v ∈ Q object packing :=
  mem_Q.2 ⟨hvR, by rw [hubs_eq_Hset hmax base noProper slack avoid valid]; exact hv⟩

theorem not_Hset_of_deg3 {v : object.Vertex}
    (hv : v ∈ JointSystem.Lset object.graph) :
    v ∉ JointSystem.Hset object.graph := by
  simp only [JointSystem.Lset, JointSystem.Hset, mem_filter, mem_univ, true_and] at hv ⊢
  omega

theorem hubs_of_Hset (hmax : JointObject.PackingMaximal object packing) (base : MinimumDegreeAtLeast 3 object)
    (noProper : NoProperCubic object) (slack : SlackIndependent object)
    (avoid : ¬ HasCycleWithLength Core.DyadicLength.PowerOfTwoLength object)
    (valid : object.IsWindowPacking 13 packing) {v : object.Vertex}
    (hv : v ∈ JointSystem.Hset object.graph) : v ∈ hubs object := by
  rw [hubs_eq_Hset hmax base noProper slack avoid valid]; exact hv

theorem Hset_of_hubs (hmax : JointObject.PackingMaximal object packing) (base : MinimumDegreeAtLeast 3 object)
    (noProper : NoProperCubic object) (slack : SlackIndependent object)
    (avoid : ¬ HasCycleWithLength Core.DyadicLength.PowerOfTwoLength object)
    (valid : object.IsWindowPacking 13 packing) {v : object.Vertex}
    (hv : v ∈ hubs object) : v ∈ JointSystem.Hset object.graph := by
  rw [← hubs_eq_Hset hmax base noProper slack avoid valid]; exact hv

theorem notHubs_of_L (hmax : JointObject.PackingMaximal object packing) (base : MinimumDegreeAtLeast 3 object)
    (noProper : NoProperCubic object) (slack : SlackIndependent object)
    (avoid : ¬ HasCycleWithLength Core.DyadicLength.PowerOfTwoLength object)
    (valid : object.IsWindowPacking 13 packing) {v : object.Vertex}
    (hv : v ∈ JointSystem.Lset object.graph) : v ∉ hubs object := by
  rw [hubs_eq_Hset hmax base noProper slack avoid valid]; exact not_Hset_of_deg3 hv

/-- `P = Σ_{h∈S_R} #LinkVia-partners`. -/
noncomputable abbrev Psum (object : Graph.FiniteObject.{u}) (packing : Finset (Finset object.Vertex)) : ℕ :=
  ∑ h ∈ SR object packing, (part (LinkVia object packing) (SR object packing) h).card

/-- **Item 1**: `|A₂ ∖ B_W| ≤ Σ_{S_R} #Lk2-partners`. -/
theorem a2_count (hmax : JointObject.PackingMaximal object packing) (base : MinimumDegreeAtLeast 3 object)
    (noProper : NoProperCubic object) (slack : SlackIndependent object)
    (avoid : ¬ HasCycleWithLength Core.DyadicLength.PowerOfTwoLength object)
    (valid : object.IsWindowPacking 13 packing) :
    ((Aset object.graph 2).filter (· ∉ Bw object packing)).card
      ≤ ∑ a ∈ SR object packing, (part (Lk2 object packing) (SR object packing) a).card := by
  have avoid := avoid
  have hsub : (Aset object.graph 2).filter (· ∉ Bw object packing) ⊆
      (SR object packing).biUnion (fun a =>
        (part (Lk2 object packing) (SR object packing) a).biUnion
        (fun b => univ.filter (fun x => object.graph.Adj a x ∧
          object.graph.Adj b x))) := by
    intro x hx
    obtain ⟨hxA, hxB⟩ := mem_filter.1 hx
    obtain ⟨hxL, a, b, hab, haH, hbH, hxa, hxb, hw⟩ := A2_hubs hxA
    have hxQ := Q_of_cubic hmax base noProper slack avoid valid (notB_R hxB) (not_Hset_of_deg3 hxL)
    have hl : Lk2 object packing a b x := ⟨hubs_of_Hset hmax base noProper slack avoid valid haH, hubs_of_Hset hmax base noProper slack avoid valid hbH, hab,
      hxQ, hxa.symm, hxb.symm, fun w hw' hxw => hw w (Hset_of_hubs hmax base noProper slack avoid valid hw') hxw⟩
    refine mem_biUnion.2 ⟨a, mem_SR.2 ⟨hubs_of_Hset hmax base noProper slack avoid valid haH, notB_nbr hxB hxa⟩,
      mem_biUnion.2 ⟨b, mem_part.2 ⟨mem_SR.2 ⟨hubs_of_Hset hmax base noProper slack avoid valid hbH, notB_nbr hxB hxb⟩,
        hab.symm, x, hl⟩, mem_filter.2 ⟨mem_univ _, hxa.symm, hxb.symm⟩⟩⟩
  calc _ ≤ _ := card_le_card hsub
    _ ≤ _ := card_biUnion_le
    _ ≤ ∑ a ∈ SR object packing, ∑ b ∈ part (Lk2 object packing) (SR object packing) a, 1 := by
        apply sum_le_sum; intro a ha
        refine card_biUnion_le.trans (sum_le_sum (fun b hb => ?_))
        have hne : a ≠ b := (mem_part.1 hb).2.1.symm
        rw [card_le_one]
        intro c hc c' hc'
        simp only [mem_filter, mem_univ, true_and] at hc hc'
        exact c4Free avoid a b c c' hne hc.1 hc.2 hc'.1 hc'.2
    _ = _ := by simp only [sum_const, smul_eq_mul, mul_one]

/-- **Item 2**: `|MLall ∖ B_W| ≤ 2P`. -/
theorem ml_count (hmax : JointObject.PackingMaximal object packing) (base : MinimumDegreeAtLeast 3 object)
    (noProper : NoProperCubic object) (slack : SlackIndependent object)
    (avoid : ¬ HasCycleWithLength Core.DyadicLength.PowerOfTwoLength object)
    (valid : object.IsWindowPacking 13 packing) :
    ((MLall object.graph).filter (· ∉ Bw object packing)).card
      ≤ 2 * Psum object packing := by
  have hsub : (MLall object.graph).filter (· ∉ Bw object packing) ⊆
      (SR object packing).biUnion (fun h =>
        (part (LinkVia object packing) (SR object packing) h).biUnion
          (fun c => univ.filter (MLat object.graph h c))) := by
    intro x hx
    obtain ⟨hxM, hxB⟩ := mem_filter.1 hx
    obtain ⟨hxA, h, c, hhH, hcH, hne, hml⟩ := mem_MLall hxM
    obtain ⟨hxL, hx1⟩ := A1_L hxA
    have hml' := hml
    obtain ⟨hxh, hx3, -, z, hxz, hzc, tz, hz3⟩ := hml'
    have hzL := deg3_L hz3
    have hxQ := Q_of_cubic hmax base noProper slack avoid valid (notB_R hxB) (not_Hset_of_deg3 hxL)
    have hzQ := Q_of_cubic hmax base noProper slack avoid valid (notB_nbr hxB hxz) (not_Hset_of_deg3 hzL)
    refine mem_biUnion.2 ⟨h, mem_SR.2 ⟨hubs_of_Hset hmax base noProper slack avoid valid hhH, notB_nbr hxB hxh⟩,
      mem_biUnion.2 ⟨c, mem_part.2 ⟨mem_SR.2 ⟨hubs_of_Hset hmax base noProper slack avoid valid hcH,
        notB_nbr2 hxB hxz (notHubs_of_L hmax base noProper slack avoid valid hzL) hzc⟩, hne.symm, bag object packing x,
        hubs_of_Hset hmax base noProper slack avoid valid hhH, hubs_of_Hset hmax base noProper slack avoid valid hcH, hne, x, z, hxh.symm, hzc.symm, hxz,
        hxQ, hzQ, onehub_of_tc hmax base noProper slack avoid valid hx1 hhH hxh, onehub_of_tc hmax base noProper slack avoid valid tz hcH hzc, rfl⟩,
        mem_filter.2 ⟨mem_univ _, hml⟩⟩⟩
  calc _ ≤ _ := card_le_card hsub
    _ ≤ _ := card_biUnion_le
    _ ≤ ∑ h ∈ SR object packing,
          ∑ c ∈ part (LinkVia object packing) (SR object packing) h, 2 := by
        apply sum_le_sum; intro h hh
        refine card_biUnion_le.trans (sum_le_sum (fun c hc => ?_))
        have hhH := Hset_of_hubs hmax base noProper slack avoid valid (mem_SR.1 hh).1
        have hcH := Hset_of_hubs hmax base noProper slack avoid valid (mem_SR.1 (mem_part.1 hc).1).1
        exact ml_fibre ((jmin base)) ((jind base slack)) ((jC4 avoid)) ((jC8 avoid))
          (Hset_deg hhH) (Hset_deg hcH) (mem_part.1 hc).2.1.symm
    _ = _ := by simp only [sum_const, smul_eq_mul, Psum, mul_sum, mul_comm]

/-- **Item 3**: `|LLall ∖ B_W| ≤ 2P + 49144 P`. -/
theorem ll_count (hmax : JointObject.PackingMaximal object packing) (base : MinimumDegreeAtLeast 3 object)
    (noProper : NoProperCubic object) (slack : SlackIndependent object)
    (avoid : ¬ HasCycleWithLength Core.DyadicLength.PowerOfTwoLength object)
    (valid : object.IsWindowPacking 13 packing) :
    ((LLall object.graph).filter (· ∉ Bw object packing)).card
      ≤ 2 * Psum object packing + 49144 * Psum object packing := by
  have base := base
  have hind := (hubs_indep base slack)
  set Ltri := (SR object packing).biUnion (fun a =>
      (part (LinkVia object packing) (SR object packing) a).biUnion
        (fun b => univ.filter (LLat object.graph a b))) with hLtri
  set Lnon := (SR object packing).biUnion (fun c =>
      (part (LinkVia object packing) (SR object packing) c).biUnion (fun a =>
        (part (LkJ object packing c) (part (LinkVia object packing) (SR object packing) c) a).biUnion
          (fun b => univ.filter (LLat object.graph a b)))) with hLnon
  have hsub : (LLall object.graph).filter (· ∉ Bw object packing) ⊆ Ltri ∪ Lnon := by
    intro x hx
    obtain ⟨hxM, hxB⟩ := mem_filter.1 hx
    obtain ⟨hxA, a, b, haH, hbH, hab, hll⟩ := mem_LLall hxM
    obtain ⟨hxL, hx1⟩ := A1_L hxA
    have hll' := hll
    obtain ⟨hx3, nxa, nxb, y, z, hxy, hxz, hya, hzb, ty, tz, hy3, hz3⟩ := hll'
    have hyL := deg3_L hy3
    have hzL := deg3_L hz3
    have hxQ := Q_of_cubic hmax base noProper slack avoid valid (notB_R hxB) (not_Hset_of_deg3 hxL)
    have hyQ := Q_of_cubic hmax base noProper slack avoid valid (notB_nbr hxB hxy) (not_Hset_of_deg3 hyL)
    have hzQ := Q_of_cubic hmax base noProper slack avoid valid (notB_nbr hxB hxz) (not_Hset_of_deg3 hzL)
    have haS : a ∈ SR object packing :=
      mem_SR.2 ⟨hubs_of_Hset hmax base noProper slack avoid valid haH, notB_nbr2 hxB hxy (notHubs_of_L hmax base noProper slack avoid valid hyL) hya⟩
    have hbS : b ∈ SR object packing :=
      mem_SR.2 ⟨hubs_of_Hset hmax base noProper slack avoid valid hbH, notB_nbr2 hxB hxz (notHubs_of_L hmax base noProper slack avoid valid hzL) hzb⟩
    have oy := onehub_of_tc hmax base noProper slack avoid valid ty haH hya
    have oz := onehub_of_tc hmax base noProper slack avoid valid tz hbH hzb
    have hLL : x ∈ univ.filter (LLat object.graph a b) := mem_filter.2 ⟨mem_univ _, hll⟩
    by_cases hyz : object.graph.Adj y z
    · refine mem_union_left _ (mem_biUnion.2 ⟨a, haS, mem_biUnion.2 ⟨b, mem_part.2 ⟨hbS,
        hab.symm, bag object packing y, hubs_of_Hset hmax base noProper slack avoid valid haH, hubs_of_Hset hmax base noProper slack avoid valid hbH, hab,
        y, z, hya.symm, hzb.symm, hyz, hyQ, hzQ, oy, oz, rfl⟩, hLL⟩⟩)
    · obtain ⟨c, hcH, hxc, hcu⟩ := A1_hub hxA
      have ox : OneHub object x c := fun w hw hxw => hcu w (Hset_of_hubs hmax base noProper slack avoid valid hw) hxw
      have hac : a ≠ c := fun e => nxa (e ▸ hxc)
      have hbc : b ≠ c := fun e => nxb (e ▸ hxc)
      have hcS : c ∈ SR object packing := mem_SR.2 ⟨hubs_of_Hset hmax base noProper slack avoid valid hcH, notB_nbr hxB hxc⟩
      have haP : a ∈ part (LinkVia object packing) (SR object packing) c :=
        mem_part.2 ⟨haS, hac, bag object packing x, hubs_of_Hset hmax base noProper slack avoid valid hcH,
          hubs_of_Hset hmax base noProper slack avoid valid haH, hac.symm, x, y, hxc.symm, hya.symm, hxy, hxQ, hyQ, ox, oy, rfl⟩
      have hbP : b ∈ part (LinkVia object packing) (SR object packing) c :=
        mem_part.2 ⟨hbS, hbc, bag object packing x, hubs_of_Hset hmax base noProper slack avoid valid hcH,
          hubs_of_Hset hmax base noProper slack avoid valid hbH, hbc.symm, x, z, hxc.symm, hzb.symm, hxz, hxQ, hzQ, ox, oz, rfl⟩
      refine mem_union_right _ (mem_biUnion.2 ⟨c, hcS, mem_biUnion.2 ⟨a, haP,
        mem_biUnion.2 ⟨b, mem_part.2 ⟨hbP, hab.symm, bag object packing x,
          hubs_of_Hset hmax base noProper slack avoid valid haH, hubs_of_Hset hmax base noProper slack avoid valid hbH, hab, hac, hbc, y, x, z, hya.symm,
          hxy.symm, hxz, hzb, hyz, hyQ, hxQ, hzQ, oy, ox, oz, rfl⟩, hLL⟩⟩⟩)
  have fib : ∀ a b, a ∈ SR object packing → b ∈ SR object packing → a ≠ b →
      (univ.filter (LLat object.graph a b)).card ≤ 2 := by
    intro a b ha hb hab
    exact ll_fibre ((jmin base)) ((jind base slack)) ((jC8 avoid))
      (Hset_deg (Hset_of_hubs hmax base noProper slack avoid valid (mem_SR.1 ha).1))
      (Hset_deg (Hset_of_hubs hmax base noProper slack avoid valid (mem_SR.1 hb).1)) hab
  have cTri : Ltri.card ≤ 2 * Psum object packing := by
    calc Ltri.card ≤ _ := card_biUnion_le
      _ ≤ ∑ a ∈ SR object packing,
            ∑ b ∈ part (LinkVia object packing) (SR object packing) a, 2 := by
          apply sum_le_sum; intro a ha
          exact card_biUnion_le.trans (sum_le_sum (fun b hb =>
            fib a b ha (mem_part.1 hb).1 (mem_part.1 hb).2.1.symm))
      _ = _ := by simp only [sum_const, smul_eq_mul, Psum, mul_sum, mul_comm]
  have cNon : Lnon.card ≤ 49144 * Psum object packing := by
    calc Lnon.card ≤ _ := card_biUnion_le
      _ ≤ ∑ c ∈ SR object packing, 49144 *
            (part (LinkVia object packing) (SR object packing) c).card := by
          apply sum_le_sum; intro c hc
          set S := part (LinkVia object packing) (SR object packing) c with hS
          have hSS : S ⊆ SR object packing := part_subset
          calc _ ≤ _ := card_biUnion_le
            _ ≤ ∑ a ∈ S, 2 * (part (LkJ object packing c) S a).card := by
                apply sum_le_sum; intro a ha
                refine card_biUnion_le.trans ?_
                calc _ ≤ ∑ b ∈ part (LkJ object packing c) S a, 2 :=
                      sum_le_sum (fun b hb => fib a b (hSS ha) (hSS (mem_part.1 hb).1)
                        (mem_part.1 hb).2.1.symm)
                  _ = _ := by rw [sum_const, smul_eq_mul, mul_comm]
            _ = 2 * ∑ a ∈ S, (part (LkJ object packing c) S a).card := by rw [mul_sum]
            _ ≤ 2 * (24572 * S.card) := Nat.mul_le_mul_left _ (sumJ hmax base hind c S hSS)
            _ = 49144 * S.card := by ring
      _ = _ := by rw [Psum, mul_sum]
  calc _ ≤ (Ltri ∪ Lnon).card := card_le_card hsub
    _ ≤ Ltri.card + Lnon.card := card_union_le _ _
    _ ≤ _ := by omega

theorem split_Bw {s : Finset object.Vertex} :
    s.card ≤ (s.filter (· ∉ Bw object packing)).card + (Bw object packing).card := by
  have : s ⊆ s.filter (· ∉ Bw object packing) ∪ Bw object packing := by
    intro x hx
    by_cases h : x ∈ Bw object packing
    · exact mem_union_right _ h
    · exact mem_union_left _ (mem_filter.2 ⟨hx, h⟩)
  exact (card_le_card this).trans (card_union_le _ _)

/-- **The slot relation, linear in `h_R`, at `[20a]`**:
`4σ + 15|H| ≤ 3n + (300 + 49148·36858) h_R + 8|B_W|`, `|B_W| ≤ 13ν + 4e(R,W)`,
`e(R,W) + 2e× = 15ν + σ_W`. -/
theorem slot_linear_at20a (hmax : JointObject.PackingMaximal object packing) (base : MinimumDegreeAtLeast 3 object)
    (noProper : NoProperCubic object) (slack : SlackIndependent object)
    (avoid : ¬ HasCycleWithLength Core.DyadicLength.PowerOfTwoLength object)
    (valid : object.IsWindowPacking 13 packing) :
    4 * JointSystem.sigma object.graph
        + 15 * (JointSystem.Hset object.graph).card
      ≤ 3 * Fintype.card object.Vertex
        + (300 + 49148 * 36858) * hubsR object packing
        + 8 * (Bw object packing).card ∧
    (Bw object packing).card ≤ 13 * packing.card
        + 4 * (object.windowRemainderIncidences packing).card ∧
    (object.windowRemainderIncidences packing).card
        + (object.crossWindowIncidences packing).card
      = 15 * packing.card
        + object.ambientSurplus (FiniteObject.windowSupport packing) 3 := by
  have base := base
  have hind := (hubs_indep base slack)
  have hsc := slot_classes ((jmin base)) ((jind base slack)) ((jdeg noProper)) ((jC4 avoid))
  have e2 := split_Bw (packing := packing) (s := Aset object.graph 2)
  have eM := split_Bw (packing := packing) (s := MLall object.graph)
  have eL := split_Bw (packing := packing) (s := LLall object.graph)
  have c2 := a2_count hmax base noProper slack avoid valid
  have s2 := sum2 hmax base hind
  have cM := ml_count hmax base noProper slack avoid valid
  have cL := ll_count hmax base noProper slack avoid valid
  have hP : Psum object packing ≤ 36858 * hubsR object packing :=
    link_pairs hmax base hind
  have hB := Bw_card base (valid)
  refine ⟨by omega, hB, ?_⟩
  have join := object.exact_window_join_identity (order := 13) (threshold := 3) valid
    (fun v => deg_ge base v)
  change (object.windowRemainderIncidences packing).card
    + (2 * (13 - 1) * packing.card
      + (object.crossWindowIncidences packing).card)
    = 3 * (13 * packing.card)
      + object.ambientSurplus (FiniteObject.windowSupport packing) 3
    at join
  omega

end Counts



/-! ## The facts at the object -/

section Facts

variable {object : Graph.FiniteObject.{u}}

/-- **The link structure of the hubs of `R`**: long hub chains in `R` are impossible; no
rainbow five-path of links; no five hubs of `R` strongly linked in a path; the link graph on
`S_R` is `18429`-degenerate (`Σ #partners ≤ 36858 h_R`) and the strong link graph
`3`-degenerate (`Σ ≤ 6 h_R`); a non-strong pair carries at most `3·6142` linked vertices. -/
abbrev HubLinkStructure (object : Graph.FiniteObject.{u})
    (packing : Finset (Finset object.Vertex)) : Prop :=
  (∀ (ℓ m : ℕ), 1 ≤ ℓ → 1 ≤ m → 12 ≤ (ℓ + 1) * (m - 1) →
    ∀ (h : ℕ → object.Vertex) (c : ℕ → ℕ → object.Vertex),
    (∀ i < m, ∀ j < m, i ≠ j → ¬ object.graph.Adj (h i) (h j) ∧ h i ≠ h j) →
    (∀ i, i + 1 < m → ∀ a < ℓ, ∀ b < ℓ,
      (object.graph.Adj (c i a) (c i b) ↔ (a + 1 = b ∨ b + 1 = a)) ∧ (c i a = c i b → a = b)) →
    (∀ i, i + 1 < m → ∀ a < ℓ, ∀ j < m,
      (object.graph.Adj (c i a) (h j) ↔ ((j = i ∧ a = 0) ∨ (j = i + 1 ∧ a + 1 = ℓ))) ∧
        c i a ≠ h j) →
    (∀ i, i + 1 < m → ∀ j, j + 1 < m → i ≠ j → ∀ a < ℓ, ∀ b < ℓ,
      ¬ object.graph.Adj (c i a) (c j b) ∧ c i a ≠ c j b) →
    (∀ i < m, h i ∈ object.remainderSupport packing) →
    (∀ i, i + 1 < m → ∀ a < ℓ, c i a ∈ object.remainderSupport packing) → False) ∧
  ¬ Rainbow5 (LinkVia object packing) (SR object packing) ∧
  (∀ h₁ h₂ h₃ h₄ h₅ : object.Vertex, h₁ ∈ SR object packing → h₂ ∈ SR object packing →
    h₃ ∈ SR object packing → h₄ ∈ SR object packing → h₅ ∈ SR object packing →
    h₁ ≠ h₂ → h₁ ≠ h₃ → h₁ ≠ h₄ → h₁ ≠ h₅ → h₂ ≠ h₃ → h₂ ≠ h₄ → h₂ ≠ h₅ → h₃ ≠ h₄ →
    h₃ ≠ h₅ → h₄ ≠ h₅ →
    SLk (LinkVia object packing) h₁ h₂ → SLk (LinkVia object packing) h₂ h₃ →
    SLk (LinkVia object packing) h₃ h₄ → SLk (LinkVia object packing) h₄ h₅ → False) ∧
  (∀ T ⊆ SR object packing, T.Nonempty →
    ∃ h ∈ T, (part (LinkVia object packing) T h).card ≤ 18429) ∧
  (∀ T ⊆ SR object packing, T.Nonempty →
    ∃ h ∈ T, (spart (LinkVia object packing) T h).card ≤ 3) ∧
  ∑ h ∈ SR object packing, (part (LinkVia object packing) (SR object packing) h).card
    ≤ 36858 * hubsR object packing ∧
  ∑ h ∈ SR object packing, (spart (LinkVia object packing) (SR object packing) h).card
    ≤ 6 * hubsR object packing ∧
  (∀ h h', h ∈ hubs object → h' ∈ hubs object → h ≠ h' →
    ¬ SLk (LinkVia object packing) h h' → (linkX object packing h h').card ≤ 3 * 6142)

theorem hubLinkStructure {packing : Finset (Finset object.Vertex)}
    (hmax : JointObject.PackingMaximal object packing) (base : MinimumDegreeAtLeast 3 object)
    (slack : SlackIndependent object) : HubLinkStructure object packing := by
  have hind := hubs_indep base slack
  exact ⟨fun ℓ m hℓ hm hlen h c hH hseg hhc hcross hR hcR =>
      chain_contra hmax ℓ m hℓ hm hlen h c hH hseg hhc hcross hR hcR,
    no_rainbow hmax hind,
    fun _ _ _ _ _ m1 m2 m3 m4 m5 n12 n13 n14 n15 n23 n24 n25 n34 n35 n45 s1 s2 s3 s4 =>
      no_rainbow hmax hind (strong_path_rainbow _ _ m1 m2 m3 m4 m5 n12 n13 n14 n15 n23 n24 n25
        n34 n35 n45 s1 s2 s3 s4),
    link_degenerate hmax base hind, strong_degenerate hmax hind, link_pairs hmax base hind,
    strong_pairs hmax hind, fun _ _ hh hh' hne hw => weak_capacity hmax base hh hh' hne hw⟩

/-- **The hub classes of the cubic vertices** (`t(x) = |N(x) ∩ H|`, `A_j = {t = j}`):
`|A₀| + |A₁| + |A₂| = |L|`, `|A₁| + 2|A₂| = 3|H| + σ`, `|A₂| ≤ C(|H|, 2)`,
`|A₂| + n = |A₀| + 4|H| + σ`, `|U| ≤ 3|A₀|`; at every hub
`d_h ≤ (|H| − 1) + |N(h) ∩ U| + |N(h) ∩ (A₁ ∖ U)|`, `Σ_H |N(h) ∩ U| = |U|`, and at most
`2d_c` vertices outside `N[c]` have a neighbour in `N(c)`. -/
abbrev HubClassCounts (object : Graph.FiniteObject.{u}) : Prop :=
  (Aset object.graph 0).card + (Aset object.graph 1).card + (Aset object.graph 2).card
      = (Hypostructure.Graph.JointSystem.Lset object.graph).card ∧
  (Aset object.graph 1).card + 2 * (Aset object.graph 2).card
      = 3 * (Hypostructure.Graph.JointSystem.Hset object.graph).card
        + Hypostructure.Graph.JointSystem.sigma object.graph ∧
  (Aset object.graph 2).card ≤ (Hypostructure.Graph.JointSystem.Hset object.graph).card.choose 2 ∧
  (Aset object.graph 2).card + Fintype.card object.Vertex
      = (Aset object.graph 0).card + 4 * (Hypostructure.Graph.JointSystem.Hset object.graph).card
        + Hypostructure.Graph.JointSystem.sigma object.graph ∧
  (Uset object.graph).card ≤ 3 * (Aset object.graph 0).card ∧
  (∀ h ∈ Hypostructure.Graph.JointSystem.Hset object.graph,
    object.graph.degree h
      ≤ ((Hypostructure.Graph.JointSystem.Hset object.graph).card - 1)
        + (object.graph.neighborFinset h ∩ Uset object.graph).card
        + (object.graph.neighborFinset h ∩ linkedSet object.graph).card) ∧
  ∑ h ∈ Hypostructure.Graph.JointSystem.Hset object.graph,
      (object.graph.neighborFinset h ∩ Uset object.graph).card = (Uset object.graph).card ∧
  (∀ c ∈ Hypostructure.Graph.JointSystem.Hset object.graph,
    (univ.filter (fun x => x ≠ c ∧ ¬ object.graph.Adj x c ∧
      ∃ y, object.graph.Adj x y ∧ object.graph.Adj y c)).card
      ≤ 2 * object.graph.degree c)

theorem hubClassCounts (base : MinimumDegreeAtLeast 3 object) (noProper : NoProperCubic object)
    (slack : SlackIndependent object)
    (avoid : ¬ HasCycleWithLength Core.DyadicLength.PowerOfTwoLength object) :
    HubClassCounts object := by
  have hmin := jmin base
  have hind := jind base slack
  have hC4 := jC4 avoid
  have hdeg := jdeg noProper
  obtain ⟨a1, a2⟩ := acount hmin hind hdeg
  refine ⟨a1, a2, a2_le hC4, exception_identity hmin hind hdeg, unlinked_card hmin hC4,
    fun h hh => ?_, by convert unlinked_hub_sum, fun c hc => ?_⟩
  · have := hub_link_count hmin hind hdeg hC4 (h := h) (mem_Hset_iff.1 hh)
    convert this
  · have := into_centre_le hmin hind (c := c) (mem_Hset_iff.1 hc)
    convert this

/-- **The slot relation**: `|A₁| ≤ 3|A₀| + |A₂| + 2(|H|² − |H|) + 2C(|H|, 2)`,
`4σ + 21|H| ≤ 3n + 6|H|²`, `4σ + 18|H| ≤ 3n + 6|A₂| + 3|H|²`, and at most two
matched-link and two link-link vertices per pair of hubs. -/
abbrev SlotRelation (object : Graph.FiniteObject.{u}) : Prop :=
  (Aset object.graph 1).card
      ≤ 3 * (Aset object.graph 0).card + (Aset object.graph 2).card
        + 2 * ((Hypostructure.Graph.JointSystem.Hset object.graph).card
            * (Hypostructure.Graph.JointSystem.Hset object.graph).card
            - (Hypostructure.Graph.JointSystem.Hset object.graph).card)
        + 2 * (Hypostructure.Graph.JointSystem.Hset object.graph).card.choose 2 ∧
  4 * Hypostructure.Graph.JointSystem.sigma object.graph
      + 21 * (Hypostructure.Graph.JointSystem.Hset object.graph).card
    ≤ 3 * Fintype.card object.Vertex
      + 6 * ((Hypostructure.Graph.JointSystem.Hset object.graph).card
        * (Hypostructure.Graph.JointSystem.Hset object.graph).card) ∧
  4 * Hypostructure.Graph.JointSystem.sigma object.graph
      + 18 * (Hypostructure.Graph.JointSystem.Hset object.graph).card
    ≤ 3 * Fintype.card object.Vertex + 6 * (Aset object.graph 2).card
      + 3 * ((Hypostructure.Graph.JointSystem.Hset object.graph).card
        * (Hypostructure.Graph.JointSystem.Hset object.graph).card) ∧
  (∀ h ∈ Hypostructure.Graph.JointSystem.Hset object.graph,
    ∀ c ∈ Hypostructure.Graph.JointSystem.Hset object.graph, h ≠ c →
      (univ.filter (MLat object.graph h c)).card ≤ 2) ∧
  (∀ a ∈ Hypostructure.Graph.JointSystem.Hset object.graph,
    ∀ b ∈ Hypostructure.Graph.JointSystem.Hset object.graph, a ≠ b →
      (univ.filter (LLat object.graph a b)).card ≤ 2)

theorem slotRelation (base : MinimumDegreeAtLeast 3 object) (noProper : NoProperCubic object)
    (slack : SlackIndependent object)
    (avoid : ¬ HasCycleWithLength Core.DyadicLength.PowerOfTwoLength object) :
    SlotRelation object := by
  have hmin := jmin base
  have hind := jind base slack
  have hC4 := jC4 avoid
  have hC8 := jC8 avoid
  have hdeg := jdeg noProper
  exact ⟨slot_bound hmin hind hdeg hC4 hC8, slot_relation hmin hind hdeg hC4 hC8,
    slot_exact hmin hind hdeg hC4 hC8,
    fun h hh c hc hne => ml_fibre hmin hind hC4 hC8 (mem_Hset_iff.1 hh) (mem_Hset_iff.1 hc) hne,
    fun a ha b hb hab => ll_fibre hmin hind hC8 (mem_Hset_iff.1 ha) (mem_Hset_iff.1 hb) hab⟩

/-- **Closed bag-link classes of the hubs of `R`**: every edge leaving the closure of a closed
class ends in `W`; disjoint closed classes have disjoint closures; with a window, a nonempty
closed class reaches `W` along an `R`–`W` edge; pairwise disjoint nonempty closed classes
number at most `e(R, W)`. -/
abbrev ClosedClasses (object : Graph.FiniteObject.{u})
    (packing : Finset (Finset object.Vertex)) : Prop :=
  (∀ T : Finset object.Vertex, Closed object packing T → ∀ x w, x ∈ closure object packing T →
    object.graph.Adj x w → w ∉ closure object packing T → w ∉ object.remainderSupport packing) ∧
  (∀ T T' : Finset object.Vertex, Closed object packing T → Closed object packing T' →
    Disjoint T T' → Disjoint (closure object packing T) (closure object packing T')) ∧
  (packing.Nonempty → ∀ T : Finset object.Vertex, Closed object packing T → T.Nonempty →
    ∃ x ∈ closure object packing T, ∃ w, object.graph.Adj x w ∧
      (x, w) ∈ object.windowRemainderIncidences packing) ∧
  (packing.Nonempty → ∀ 𝒯 : Finset (Finset object.Vertex),
    (∀ T ∈ 𝒯, Closed object packing T ∧ T.Nonempty) →
    (∀ T ∈ 𝒯, ∀ T' ∈ 𝒯, T ≠ T' → Disjoint T T') →
    𝒯.card ≤ (object.windowRemainderIncidences packing).card)

theorem closedClasses {packing : Finset (Finset object.Vertex)}
    (base : MinimumDegreeAtLeast 3 object) (noProper : NoProperCubic object)
    (slack : SlackIndependent object) (valid : object.IsWindowPacking 13 packing) :
    ClosedClasses object packing := by
  have hind := hubs_indep base slack
  exact ⟨fun T hT x w hx hxw hw => closure_out_edges hind hT hx hxw hw,
    fun T T' hT hT' hd => closure_disjoint hT hT' hd,
    fun hW T hT hne => closed_reaches_W base noProper hind valid hW hT hne,
    fun hW 𝒯 hcl hdisj => closed_classes_le base noProper hind valid hW 𝒯 hcl hdisj⟩

end Facts

/-! ## Two-hop links, the linear slot relation and the scale pressure -/

section Linear

variable {object : Graph.FiniteObject.{u}}

/-- **Two-hop links between the hubs of `R`**: no seven hubs of `R` joined consecutively by
common neighbours (the forbid path of length `6`), so the common-neighbour graph on `S_R` is
`25`-degenerate (`Σ ≤ 50 h_R`); at every centre `c`, no four hubs joined by two-hop links in
distinct bags, the two-hop graph at `c` has at most `6142` partners per bag, is
`12286`-degenerate, and `Σ_{a∈S} #partners_S ≤ 24572|S|` for `S ⊆ S_R`. -/
abbrev HubTwoHopLinks (object : Graph.FiniteObject.{u})
    (packing : Finset (Finset object.Vertex)) : Prop :=
  (∀ h b, ¬ FPath (Lk2 object packing) (F2 object) (SR object packing) 6 h b) ∧
  (∀ T ⊆ SR object packing, T.Nonempty → ∃ h ∈ T, (part (Lk2 object packing) T h).card ≤ 25) ∧
  ∑ h ∈ SR object packing, (part (Lk2 object packing) (SR object packing) h).card
    ≤ 50 * hubsR object packing ∧
  ∀ c : object.Vertex,
    (∀ a B, (univ.filter (fun b => LkJ object packing c a b B)).card ≤ 6142) ∧
    (∀ h B, ¬ FPath (LkJ object packing c) (fun B => {B}) (SR object packing) 3 h B) ∧
    (∀ T ⊆ SR object packing, T.Nonempty →
      ∃ h ∈ T, (part (LkJ object packing c) T h).card ≤ 12286) ∧
    (∀ S ⊆ SR object packing, ∑ a ∈ S, (part (LkJ object packing c) S a).card ≤ 24572 * S.card)

theorem hubTwoHopLinks {packing : Finset (Finset object.Vertex)}
    (hmax : JointObject.PackingMaximal object packing) (base : MinimumDegreeAtLeast 3 object)
    (slack : SlackIndependent object) : HubTwoHopLinks object packing := by
  have hind := hubs_indep base slack
  exact ⟨no_path2 hmax hind, degenerate2 hmax base hind, sum2 hmax base hind,
    fun c => ⟨capJ hmax base c, no_pathJ hmax hind c, degenerateJ hmax base hind c,
      fun S hS => sumJ hmax base hind c S hS⟩⟩

/-- **The slot classes are linear in `h_R`**: with the near-window set `B_W = W ∪ D₁ ∪ D₂`,
`|B_W| ≤ 13ν + 4e(R, W)`; `|A₂ ∖ B_W| ≤ Σ_{S_R} #Lk2-partners`, `|MLall ∖ B_W| ≤ 2P`,
`|LLall ∖ B_W| ≤ 2P + 49144P` (`P` the link-partner sum); and
`4σ + 15|H| ≤ 3n + K·h_R + 8|B_W|` and `4σ + 15|H| ≤ 3n + K·h_R + 584ν + 32σ_W`,
`K = 300 + 49148·36858 = 1811497284`. -/
abbrev SlotLinear (object : Graph.FiniteObject.{u})
    (packing : Finset (Finset object.Vertex)) : Prop :=
  (Bw object packing).card
      ≤ 13 * packing.card + 4 * (object.windowRemainderIncidences packing).card ∧
  ((Aset object.graph 2).filter (· ∉ Bw object packing)).card
      ≤ ∑ a ∈ SR object packing, (part (Lk2 object packing) (SR object packing) a).card ∧
  ((MLall object.graph).filter (· ∉ Bw object packing)).card ≤ 2 * Psum object packing ∧
  ((LLall object.graph).filter (· ∉ Bw object packing)).card
      ≤ 2 * Psum object packing + 49144 * Psum object packing ∧
  4 * Hypostructure.Graph.JointSystem.sigma object.graph
      + 15 * (Hypostructure.Graph.JointSystem.Hset object.graph).card
    ≤ 3 * Fintype.card object.Vertex + (300 + 49148 * 36858) * hubsR object packing
      + 8 * (Bw object packing).card ∧
  4 * Hypostructure.Graph.JointSystem.sigma object.graph
      + 15 * (Hypostructure.Graph.JointSystem.Hset object.graph).card
    ≤ 3 * Fintype.card object.Vertex + (300 + 49148 * 36858) * hubsR object packing
      + 584 * packing.card + 32 * object.ambientSurplus (FiniteObject.windowSupport packing) 3

theorem slotLinear {packing : Finset (Finset object.Vertex)}
    (hmax : JointObject.PackingMaximal object packing) (base : MinimumDegreeAtLeast 3 object)
    (noProper : NoProperCubic object) (slack : SlackIndependent object)
    (avoid : ¬ HasCycleWithLength Core.DyadicLength.PowerOfTwoLength object)
    (valid : object.IsWindowPacking 13 packing) : SlotLinear object packing := by
  obtain ⟨h1, h2, h3⟩ := slot_linear_at20a hmax base noProper slack avoid valid
  exact ⟨Bw_card base valid, a2_count hmax base noProper slack avoid valid,
    ml_count hmax base noProper slack avoid valid, ll_count hmax base noProper slack avoid valid,
    h1, by omega⟩

/-- **Scale pressure**: if `C·q < σ`, then
`C·q + 15|H| < 3(n − σ) + K·h_R + 584ν + 32σ_W`; and for `σ + s = n`,
`11·C·q + 165|H| + 27156|B| < 1785s + 11K·h_R + 21900|B|² + 352σ_W`. -/
abbrev ScalePressure (object : Graph.FiniteObject.{u})
    (packing : Finset (Finset object.Vertex)) (C q : ℕ) : Prop :=
  C * q + 15 * (Hypostructure.Graph.JointSystem.Hset object.graph).card
      < 3 * (Fintype.card object.Vertex - Hypostructure.Graph.JointSystem.sigma object.graph)
        + (300 + 49148 * 36858) * hubsR object packing + 584 * packing.card
        + 32 * object.ambientSurplus (FiniteObject.windowSupport packing) 3 ∧
  ∀ s, Hypostructure.Graph.JointSystem.sigma object.graph + s = Fintype.card object.Vertex →
    11 * ((C * q : ℕ) : ℤ) + 165 * (Hypostructure.Graph.JointSystem.Hset object.graph).card
        + 27156 * (Hypostructure.Graph.JointSystem.Bset object.graph).card
      < 1785 * (s : ℤ) + 11 * (300 + 49148 * 36858) * hubsR object packing
        + 21900 * ((Hypostructure.Graph.JointSystem.Bset object.graph).card
            * (Hypostructure.Graph.JointSystem.Bset object.graph).card : ℕ)
        + 352 * object.ambientSurplus (FiniteObject.windowSupport packing) 3

theorem scalePressure {packing : Finset (Finset object.Vertex)}
    (hmax : JointObject.PackingMaximal object packing) (base : MinimumDegreeAtLeast 3 object)
    (noProper : NoProperCubic object) (slack : SlackIndependent object)
    (avoid : ¬ HasCycleWithLength Core.DyadicLength.PowerOfTwoLength object)
    (valid : object.IsWindowPacking 13 packing) (C q : ℕ)
    (habove : C * q < Hypostructure.Graph.JointSystem.sigma object.graph) :
    ScalePressure object packing C q := by
  have h1 := (slotLinear hmax base noProper slack avoid valid).2.2.2.2.2
  have h3 : Hypostructure.Graph.JointSystem.sigma object.graph ≤ Fintype.card object.Vertex := by
    have := Hypostructure.Graph.JointSystem.big_hub_bound (jmin base) (jind base slack)
      (jdeg noProper)
    omega
  refine ⟨by omega, fun s hs => ?_⟩
  have fw := fewWindows base noProper slack avoid valid s hs
  have e := hubs_split (object := object) packing
  have hH := Hset_card_eq base
  push_cast
  omega

end Linear

end Hypostructure.Graph.HubLinkObject
