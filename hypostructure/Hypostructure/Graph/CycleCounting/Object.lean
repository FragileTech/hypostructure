import Hypostructure.Graph.CycleCounting.Cycles
import Hypostructure.Graph.CycleCounting.Meeting
import Hypostructure.Graph.CycleCounting.Components
import Hypostructure.Graph.CycleCounting.Arithmetic
import Hypostructure.Graph.BoundaryDemand
import Hypostructure.Graph.Contraction
import Hypostructure.Graph.DeletionCriticality
import Hypostructure.Core.DyadicLength

/-!
# Cycle counting at a finite object

The cycle-counting library read at any `FiniteObject`, with its own vertex
schedule and adjacency decision as the instances, and with the hypotheses a
minimal object supplies stated in their generic forms:

* the baseline `MinimumDegreeAtLeast 3`;
* no proper subgraph meets the baseline (`ProperSubgraph`);
* no bridge: every `EdgeContraction` has a return;
* no accepted cycle, with the accepted lengths exactly the dyadic ones `2^k`,
  `k ≥ 2` (`Core.DyadicLength.PowerOfTwoLength`);
* the vertices above the baseline pairwise nonadjacent.

Each property below is a statement about the object and its own vertices,
walks and cycles; nothing here names an application.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Hypostructure.Graph.CycleCounting

open Finset Classical

universe u

variable (object : FiniteObject.{u})

/-! ## The properties -/

/-- `G − h` is connected, seen from every neighbour `x` of `h`: the component
of `x` in `G − h` is everything but `h`. -/
noncomputable def DeletionConnected (h : object.Vertex) : Prop :=
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  ∀ x, object.graph.Adj h x → insert h (comp object.graph h x) = Finset.univ

/-- **Vertex-deletion shape.** For every vertex `h`: `G − h` is connected, or
`d_h` is even, `d_h = 2·#blocks(h)`, and the component of every neighbour `x`
of `h` in `G − h` holds exactly two neighbours of `h`. -/
noncomputable def VertexDeletionShape : Prop :=
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  ∀ h : object.Vertex, DeletionConnected object h ∨
    (Even (object.degree h) ∧ object.degree h = 2 * #(blocks object.graph h) ∧
      ∀ x, object.graph.Adj h x →
        #(object.graph.neighborFinset h ∩ comp object.graph h x) = 2)

/-- **Cycles through a vertex.** For every vertex `h`: if `G − h` is connected,
`G` has at least `C(d_h, 2)` cycles through `h`; otherwise exactly `d_h / 2`
pairs of edges at `h` are closed in `G − h` (`2·#pairs = d_h`) and `G` has at
least `d_h / 2` cycles through `h`. -/
noncomputable def CyclesThroughVertex : Prop :=
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  ∀ h : object.Vertex,
    (DeletionConnected object h ∧
      (object.degree h).choose 2 ≤ #(cyclesThrough object.graph (fun _ => True) h)) ∨
    (¬ DeletionConnected object h ∧
      2 * #(pairsThrough object.graph (fun _ => True) h) = object.degree h ∧
      object.degree h / 2 ≤ #(cyclesThrough object.graph (fun _ => True) h))

/-- The vertices off the baseline degree `δ`. -/
noncomputable def offBaseline (δ : ℕ) : Finset object.Vertex :=
  letI : FinEnum object.Vertex := object.vertices
  Finset.univ.filter fun v => object.degree v ≠ δ

/-- **Pair sums over the high vertices** `H = {d ≠ δ}` against the surplus
`σ = 2m − δn`: `σ = Σ_H (d_h − 3)`, `5σ ≤ Σ_H C(d_h, 2)`, the Cauchy–Schwarz
form `σ² + 5σ|H| + 6|H|² ≤ 2|H| Σ_H C(d_h, 2)`, the cap
`2 Σ_H C(d_h, 2) ≤ 16σ²`, and a heavy centre `σ ≤ |H|(d_h − 3)` (unless
`σ = 0`). -/
noncomputable def HighPairSum (δ : ℕ) : Prop :=
  object.degreeSurplus δ = ∑ h ∈ offBaseline object δ, (object.degree h - 3) ∧
  5 * object.degreeSurplus δ ≤ ∑ h ∈ offBaseline object δ, (object.degree h).choose 2 ∧
  object.degreeSurplus δ ^ 2 + 5 * object.degreeSurplus δ * #(offBaseline object δ) +
      6 * #(offBaseline object δ) ^ 2 ≤
    2 * #(offBaseline object δ) * ∑ h ∈ offBaseline object δ, (object.degree h).choose 2 ∧
  2 * ∑ h ∈ offBaseline object δ, (object.degree h).choose 2 ≤
    16 * object.degreeSurplus δ ^ 2 ∧
  (object.degreeSurplus δ = 0 ∨ ∃ h ∈ offBaseline object δ,
    object.degreeSurplus δ ≤ #(offBaseline object δ) * (object.degree h - 3))

/-- The per-vertex lower bound on the cycles through `h`: `C(d_h, 2)` when
`G − h` is connected, `d_h / 2` otherwise. -/
noncomputable def cycleLowerAt (h : object.Vertex) : ℕ :=
  if DeletionConnected object h then (object.degree h).choose 2 else object.degree h / 2

/-- **Double count of the cycles at the high vertices** `H = {d ≠ δ}`:
`2 Σ_{h∈H} #cycles(h) ≤ n · #cycles(G)`, `2 Σ_{h∈H} L_h ≤ n · #cycles(G)` with
`L_h` the per-vertex lower bound, and `#cycles(G) ≤ 2^m`. -/
noncomputable def CycleDoubleCount (δ : ℕ) : Prop :=
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  2 * ∑ h ∈ offBaseline object δ, #(cyclesThrough object.graph (fun _ => True) h) ≤
      object.vertexCount * #(allCycles (G := object.graph)) ∧
    2 * ∑ h ∈ offBaseline object δ, cycleLowerAt object h ≤
      object.vertexCount * #(allCycles (G := object.graph)) ∧
    #(allCycles (G := object.graph)) ≤ 2 ^ object.edgeCount

/-- **Star constraint.** Two paths `x → y`, `x → z` of `G − h` to distinct
neighbours `y, z` of `h`, meeting only at `x`, have `|P| + |Q| + 2 ≠ 2^k`
(`k ≥ 2`). -/
def StarConstraint : Prop :=
  ∀ ⦃h x y z : object.Vertex⦄, object.graph.Adj h y → object.graph.Adj h z → y ≠ z →
    ∀ (P : object.graph.Walk x y) (Q : object.graph.Walk x z), P.IsPath → Q.IsPath →
      h ∉ P.support → h ∉ Q.support → (∀ v ∈ P.support, v ∈ Q.support → v = x) →
      ∀ k, 2 ≤ k → P.length + Q.length + 2 ≠ 2 ^ k

/-- **Meeting constraint.** Two paths `x → y`, `x → z` of `G − h` to distinct
neighbours of `h` meet at a vertex `t` reached along them by `P₁`, `Q₁`, and
`|P| + |Q| + 2 ≠ 2^k + |P₁| + |Q₁|` for every `k ≥ 2`. -/
def MeetingConstraint : Prop :=
  ∀ ⦃h x y z : object.Vertex⦄, object.graph.Adj h y → object.graph.Adj h z → y ≠ z →
    ∀ (P : object.graph.Walk x y) (Q : object.graph.Walk x z), P.IsPath → Q.IsPath →
      h ∉ P.support → h ∉ Q.support →
      ∃ t, ∃ P₁ Q₁ : object.graph.Walk x t, P₁.length ≤ P.length ∧ Q₁.length ≤ Q.length ∧
        ∀ k, 2 ≤ k → P.length + Q.length + 2 ≠ 2 ^ k + P₁.length + Q₁.length

/-- **Neighbourhood pairs.** For every vertex `h`: `G[N(h)]` is a matching,
`N(h)` has at least `C(d_h, 2) − ⌊d_h/2⌋` nonadjacent pairs, and every
neighbour `x` has at least `d_h − 2` nonadjacent partners in `N(h)`. -/
noncomputable def NeighbourhoodPairs : Prop :=
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  ∀ h : object.Vertex,
    (∀ x ∈ object.graph.neighborFinset h,
      #((object.graph.neighborFinset h).filter (object.graph.Adj x)) ≤ 1) ∧
    (object.degree h).choose 2 - object.degree h / 2 ≤
      #(nonAdjPairs object.graph (object.graph.neighborFinset h)) ∧
    ∀ x ∈ object.graph.neighborFinset h, object.degree h - 2 ≤
      #(((object.graph.neighborFinset h).erase x).filter (fun y => ¬ object.graph.Adj x y))

/-- **Block paths at a cut vertex.** For every vertex `h` with `G − h`
disconnected and every neighbour `a` of `h`, the block of `a` is `{a, b}` with
`b ≠ a` a neighbour of `h`, and:
* every `a → b` path of `G − h` has `|r| + 2 ≠ 2^k` (`k ≥ 2`);
* every return `q : a → h` of `ha` is `a ⋯ b h` with an `a → b` path of `G − h`
  of length `|q| − 1`;
* every `a → b` path avoiding `ha`, `hb` avoids `h`, and has `|p| ≡ 3 (mod 4)`
  when `|p| + 1 = 2^j` (`j ≥ 2`);
* every path from `a` to a neighbour `a₂` outside the component of `a`, avoiding
  `ha`, `ha₂`, splits at `h` as `a ⋯ b₁ h b₂ ⋯ a₂` with `|r₁| + |r₂| + 2 = |p|`,
  and when `|p| + 1 = 2^j` (`j ≥ 2`), `|r₁| + |r₂| ≡ 1 (mod 4)` with opposite
  parities. -/
noncomputable def BlockPaths : Prop :=
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  ∀ h : object.Vertex, ¬ DeletionConnected object h →
    ∀ a, object.graph.Adj h a → ∃ b, b ≠ a ∧ object.graph.Adj h b ∧
      object.graph.neighborFinset h ∩ comp object.graph h a = {a, b} ∧
      (∀ r : object.graph.Walk a b, r.IsPath → h ∉ r.support →
        ∀ k, 2 ≤ k → r.length + 2 ≠ 2 ^ k) ∧
      (∀ q : object.graph.Walk a h, q.IsPath → s(h, a) ∉ q.edges →
        ∃ r : object.graph.Walk a b, r.IsPath ∧ h ∉ r.support ∧ r.length + 1 = q.length) ∧
      (∀ p : object.graph.Walk a b, p.IsPath → s(h, a) ∉ p.edges → s(h, b) ∉ p.edges →
        h ∉ p.support ∧ ∀ j, 2 ≤ j → p.length + 1 = 2 ^ j → p.length % 4 = 3) ∧
      (∀ a₂, object.graph.Adj h a₂ → a₂ ∉ comp object.graph h a →
        ∀ p : object.graph.Walk a a₂, p.IsPath → s(h, a) ∉ p.edges → s(h, a₂) ∉ p.edges →
          ∃ b₁ b₂, b₁ ≠ a ∧ b₂ ≠ a₂ ∧ object.graph.Adj h b₁ ∧ object.graph.Adj h b₂ ∧
            b₁ ∈ comp object.graph h a ∧ b₂ ∈ comp object.graph h a₂ ∧
            ∃ (r₁ : object.graph.Walk a b₁) (r₂ : object.graph.Walk a₂ b₂),
              r₁.IsPath ∧ r₂.IsPath ∧ h ∉ r₁.support ∧ h ∉ r₂.support ∧
              r₁.length + r₂.length + 2 = p.length ∧
              ∀ j, 2 ≤ j → p.length + 1 = 2 ^ j →
                (r₁.length + r₂.length) % 4 = 1 ∧ r₁.length % 2 ≠ r₂.length % 2)

/-! ## Converters from the generic hypotheses -/

section Converters

variable {object}

/-- No bridge, in path form: every edge `uv` has a `u → v` path avoiding it. -/
theorem path_of_bridgeless
    (bridgeless : ∀ contraction : EdgeContraction object, contraction.HasReturn)
    {u v : object.Vertex} (a : object.graph.Adj u v) :
    ∃ p : object.graph.Walk u v, p.IsPath ∧ s(u, v) ∉ p.edges := by
  obtain ⟨p⟩ := bridgeless ⟨u, v, a⟩
  refine ⟨p.1.mapLe (object.graph.deleteEdges_le _), p.2.mapLe _, ?_⟩
  rw [SimpleGraph.Walk.edges_mapLe_eq_edges]
  intro m
  have := p.1.edges_subset_edgeSet m
  change s(u, v) ∈ (object.graph.deleteEdges {s(u, v)}).edgeSet at this
  rw [SimpleGraph.edgeSet_deleteEdges] at this
  exact this.2 rfl

/-- The baseline, in degree form. -/
theorem degree_ge_of_baseline (baseline : MinimumDegreeAtLeast 3 object) :
    letI : FinEnum object.Vertex := object.vertices
    letI : DecidableRel object.graph.Adj := object.decideAdj
    ∀ v, 3 ≤ object.graph.degree v := by
  intro v
  exact le_trans baseline (object.minDegree_le_degree v)

/-- No proper baseline, in support form: every nonempty proper support has a
vertex with at most two neighbours inside it. -/
theorem low_of_noProper
    (noProper : ∀ sub : ProperSubgraph object, ¬ MinimumDegreeAtLeast 3 sub.value) :
    letI : FinEnum object.Vertex := object.vertices
    letI : DecidableRel object.graph.Adj := object.decideAdj
    ∀ S : Finset object.Vertex, S.Nonempty → S ≠ Finset.univ →
      ∃ v ∈ S, #(object.graph.neighborFinset v ∩ S) ≤ 2 := by
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  intro S nonempty proper
  have strict : S.card < object.vertexCount := by
    rw [← FiniteObject.card_vertexFinset]
    apply Finset.card_lt_card
    refine ⟨fun v _ => object.mem_vertexFinset v, fun hsub => proper ?_⟩
    ext v
    simp only [Finset.mem_univ, iff_true]
    exact hsub (object.mem_vertexFinset v)
  by_contra h
  push Not at h
  let sub := ProperSubgraph.ofInducedSupport object S strict
  obtain ⟨v0, hv0⟩ := nonempty
  letI : Nonempty sub.value.Vertex := ⟨⟨v0, hv0⟩⟩
  apply noProper sub
  apply sub.value.le_minDegree_of_forall_le_degree 3
  intro vertex
  change 3 ≤ (object.induce S).degree vertex
  rw [object.degree_induce_eq_internalDegree S vertex]
  have h3 : 3 ≤ #(object.graph.neighborFinset vertex.1 ∩ S) := h vertex.1 vertex.2
  unfold FiniteObject.internalDegree
  convert h3 using 2

/-- The accepted lengths, read as powers of two: a cycle of length `2^k`,
`k ≥ 2`, is accepted. -/
theorem no_dyadic_cycle {LengthOK : ℕ → Prop}
    (avoid : ¬ HasCycleWithLength LengthOK object)
    (lengthLaw : ∀ length, LengthOK length ↔ Core.DyadicLength.PowerOfTwoLength length)
    {v : object.Vertex} (c : object.graph.Walk v v) (cc : c.IsCycle) :
    ∀ k, 2 ≤ k → c.length ≠ 2 ^ k := by
  intro k hk e
  exact avoid ⟨⟨v, c, cc, (lengthLaw _).2
    (Core.DyadicLength.powerOfTwoLength_of_exists ⟨k, hk, e⟩)⟩⟩

end Converters

/-! ## The properties hold -/

section Holds

variable {object}

theorem vertexDeletionShape
    (baseline : MinimumDegreeAtLeast 3 object)
    (noProper : ∀ sub : ProperSubgraph object, ¬ MinimumDegreeAtLeast 3 sub.value)
    (bridgeless : ∀ contraction : EdgeContraction object, contraction.HasReturn) :
    VertexDeletionShape object := by
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  intro h
  by_cases conn : DeletionConnected object h
  · exact Or.inl conn
  right
  have conn' := conn
  unfold DeletionConnected at conn'
  push Not at conn'
  obtain ⟨x₀, a₀, dis⟩ := conn'
  have deg := degree_ge_of_baseline baseline
  have low := low_of_noProper noProper
  have br : ∀ u v, object.graph.Adj u v →
      ∃ p : object.graph.Walk u v, p.IsPath ∧ s(u, v) ∉ p.edges :=
    fun u v a => path_of_bridgeless bridgeless a
  refine ⟨degree_even deg low br a₀ dis, degree_eq_two_mul_blocks deg low br a₀ dis,
    fun x ax => block_card_two deg low br a₀ dis ax⟩

theorem cyclesThroughVertex
    (baseline : MinimumDegreeAtLeast 3 object)
    (noProper : ∀ sub : ProperSubgraph object, ¬ MinimumDegreeAtLeast 3 sub.value)
    (bridgeless : ∀ contraction : EdgeContraction object, contraction.HasReturn) :
    CyclesThroughVertex object := by
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  intro h
  have deg := degree_ge_of_baseline baseline
  have low := low_of_noProper noProper
  have br : ∀ u v, object.graph.Adj u v →
      ∃ p : object.graph.Walk u v, p.IsPath ∧ s(u, v) ∉ p.edges :=
    fun u v a => path_of_bridgeless bridgeless a
  by_cases conn : DeletionConnected object h
  · left
    refine ⟨conn, ?_⟩
    have pos : 0 < object.graph.degree h := by have := deg h; omega
    obtain ⟨x, hx⟩ := (object.graph.degree_pos_iff_exists_adj h).1 pos
    exact choose_le_cycles_of_connected hx (conn x hx)
  · right
    refine ⟨conn, ?_⟩
    have conn' := conn
    unfold DeletionConnected at conn'
    push Not at conn'
    obtain ⟨x₀, a₀, dis⟩ := conn'
    exact disconnected_cycles_lower deg low br a₀ dis

/-- Handshake at the baseline: `2m − δn = Σ_{d ≠ δ} (d − 3)` when `δ = 3`. -/
theorem degreeSurplus_eq_sum (baseline : MinimumDegreeAtLeast 3 object) :
    object.degreeSurplus 3 = ∑ h ∈ offBaseline object 3, (object.degree h - 3) := by
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  have deg := degree_ge_of_baseline baseline
  have hs : ∑ v, object.graph.degree v = 2 * object.graph.edgeFinset.card :=
    object.graph.sum_degrees_eq_twice_card_edges
  have e1 : ∑ v, (object.graph.degree v - 3) + 3 * Fintype.card object.Vertex =
      ∑ v, object.graph.degree v := by
    rw [← Finset.card_univ, mul_comm, ← smul_eq_mul, ← Finset.sum_const,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun v _ => by have := deg v; omega)
  have e2 : ∑ v, (object.graph.degree v - 3) =
      ∑ h ∈ offBaseline object 3, (object.degree h - 3) := by
    unfold offBaseline
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    change object.graph.degree v - 3 = if object.graph.degree v ≠ 3 then _ else 0
    split_ifs with hv
    · rfl
    · push Not at hv; omega
  have n : object.vertexCount = Fintype.card object.Vertex := by
    rw [← FiniteObject.card_vertexFinset]; rfl
  unfold FiniteObject.degreeSurplus
  rw [n, ← e2]
  change 2 * object.graph.edgeFinset.card - 3 * Fintype.card object.Vertex = _
  omega

theorem highPairSum (baseline : MinimumDegreeAtLeast 3 object) :
    HighPairSum object 3 := by
  have hσ := degreeSurplus_eq_sum baseline
  have d4 : ∀ h ∈ offBaseline object 3, 4 ≤ object.degree h := by
    intro h hh
    letI : FinEnum object.Vertex := object.vertices
    unfold offBaseline at hh
    rw [Finset.mem_filter] at hh
    have := le_trans baseline (object.minDegree_le_degree h)
    omega
  refine ⟨hσ, ?_, ?_, ?_, ?_⟩
  · rw [hσ]; exact five_sigma_le _ _ d4
  · rw [hσ]; exact cauchy_choose _ _ (fun h hh => by have := d4 h hh; omega)
  · rw [hσ]; exact choose_sum_le_sigma _ _ d4
  · by_cases hH : (offBaseline object 3).Nonempty
    · right
      obtain ⟨h, hh, le⟩ := exists_heavy _ hH (fun v => object.degree v)
      exact ⟨h, hh, hσ ▸ le⟩
    · left
      rw [hσ, Finset.not_nonempty_iff_eq_empty.1 hH, Finset.sum_empty]

theorem cycleDoubleCount
    (baseline : MinimumDegreeAtLeast 3 object)
    (noProper : ∀ sub : ProperSubgraph object, ¬ MinimumDegreeAtLeast 3 sub.value)
    (bridgeless : ∀ contraction : EdgeContraction object, contraction.HasReturn)
    (independent : ∀ left right : object.Vertex,
      3 < object.degree left → 3 < object.degree right → ¬ object.graph.Adj left right) :
    CycleDoubleCount object 3 := by
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  have deg := degree_ge_of_baseline baseline
  have gt : ∀ h ∈ offBaseline object 3, 3 < object.degree h := by
    intro h hh
    unfold offBaseline at hh
    rw [Finset.mem_filter] at hh
    have := deg h
    change 3 ≤ object.degree h at this
    omega
  have indep : ∀ a ∈ offBaseline object 3, ∀ b ∈ offBaseline object 3,
      ¬ object.graph.Adj a b := fun a ha b hb => independent a b (gt a ha) (gt b hb)
  have n : object.vertexCount = Fintype.card object.Vertex := by
    rw [← FiniteObject.card_vertexFinset]; rfl
  have glob := global_cycles_bound (G := object.graph) (offBaseline object 3) indep
  have cyc := cyclesThroughVertex baseline noProper bridgeless
  have lower : ∑ h ∈ offBaseline object 3, cycleLowerAt object h ≤
      ∑ h ∈ offBaseline object 3, #(cyclesThrough object.graph (fun _ => True) h) := by
    refine Finset.sum_le_sum (fun h _ => ?_)
    unfold cycleLowerAt
    rcases cyc h with ⟨conn, le⟩ | ⟨conn, -, le⟩
    · rw [if_pos conn]; exact le
    · rw [if_neg conn]; exact le
  refine ⟨?_, ?_, ?_⟩
  · rw [n]; exact glob
  · rw [n]; exact le_trans (Nat.mul_le_mul_left 2 lower) glob
  · exact card_allCycles_le

theorem starConstraint {LengthOK : ℕ → Prop}
    (avoid : ¬ HasCycleWithLength LengthOK object)
    (lengthLaw : ∀ length, LengthOK length ↔ Core.DyadicLength.PowerOfTwoLength length) :
    StarConstraint object := by
  letI : FinEnum object.Vertex := object.vertices
  intro h x y z ay az yz P Q pp qp hp hq disj k hk e
  obtain ⟨c, cc, cl⟩ := star_cycle ay az yz P Q pp qp hp hq disj
  exact no_dyadic_cycle avoid lengthLaw c cc k hk (cl.trans e)

theorem meetingConstraint {LengthOK : ℕ → Prop}
    (avoid : ¬ HasCycleWithLength LengthOK object)
    (lengthLaw : ∀ length, LengthOK length ↔ Core.DyadicLength.PowerOfTwoLength length) :
    MeetingConstraint object := by
  letI : FinEnum object.Vertex := object.vertices
  intro h x y z ay az yz P Q pp qp hp hq
  obtain ⟨t, P₁, Q₁, l1, l2, c, cc, cl⟩ := meet_cycle ay az yz P Q pp qp hp hq
  refine ⟨t, P₁, Q₁, l1, l2, fun k hk e => no_dyadic_cycle avoid lengthLaw c cc k hk ?_⟩
  omega

/-- No accepted quadrilateral: the four vertices `a b c d` with `a ≠ c`,
`b ≠ d` and the edges `ab, bc, cd, da` close an accepted cycle. -/
theorem no_quadrilateral {LengthOK : ℕ → Prop}
    (avoid : ¬ HasCycleWithLength LengthOK object) (four : LengthOK 4)
    {a b c d : object.Vertex}
    (ab : object.graph.Adj a b) (bc : object.graph.Adj b c)
    (cd : object.graph.Adj c d) (da : object.graph.Adj d a)
    (ac : a ≠ c) (bd : b ≠ d) : False := by
  have isCycle :
      (SimpleGraph.Walk.cons ab
        (SimpleGraph.Walk.cons bc
          (SimpleGraph.Walk.cons cd
            (SimpleGraph.Walk.cons da .nil)))).IsCycle := by
    rw [SimpleGraph.Walk.cons_isCycle_iff]
    refine ⟨?_, ?_⟩
    · rw [SimpleGraph.Walk.isPath_def]
      simp [ab.ne', bc.ne, cd.ne, da.ne, ac.symm, bd]
    · simp [ab.ne, ab.ne', bc.ne, da.ne', ac, bd]
  exact avoid ⟨⟨a, _, isCycle, by simpa using four⟩⟩

theorem neighbourhoodPairs {LengthOK : ℕ → Prop}
    (avoid : ¬ HasCycleWithLength LengthOK object) (four : LengthOK 4) :
    NeighbourhoodPairs object := by
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  intro h
  have matching : ∀ x ∈ object.graph.neighborFinset h, ∀ y ∈ object.graph.neighborFinset h,
      ∀ z ∈ object.graph.neighborFinset h,
        object.graph.Adj x y → object.graph.Adj x z → y = z := by
    intro x hx y hy z hz axy axz
    by_contra yz
    rw [SimpleGraph.mem_neighborFinset] at hx hy hz
    exact no_quadrilateral avoid four hy axy.symm axz hz.symm hx.ne yz
  have one : ∀ x ∈ object.graph.neighborFinset h,
      #((object.graph.neighborFinset h).filter (object.graph.Adj x)) ≤ 1 := by
    intro x hx
    rw [Finset.card_le_one]
    intro y hy z hz
    rw [Finset.mem_filter] at hy hz
    exact matching x hx y hy.1 z hz.1 hy.2 hz.2
  refine ⟨one, ?_, fun x hx => ?_⟩
  · have := card_nonAdjPairs (G := object.graph) (object.graph.neighborFinset h) matching
    rwa [SimpleGraph.card_neighborFinset_eq_degree] at this
  · have := partners_card (G := object.graph) (object.graph.neighborFinset h) hx (one x hx)
    rwa [SimpleGraph.card_neighborFinset_eq_degree] at this

theorem blockPaths {LengthOK : ℕ → Prop}
    (baseline : MinimumDegreeAtLeast 3 object)
    (noProper : ∀ sub : ProperSubgraph object, ¬ MinimumDegreeAtLeast 3 sub.value)
    (bridgeless : ∀ contraction : EdgeContraction object, contraction.HasReturn)
    (avoid : ¬ HasCycleWithLength LengthOK object)
    (lengthLaw : ∀ length, LengthOK length ↔ Core.DyadicLength.PowerOfTwoLength length) :
    BlockPaths object := by
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  intro h conn a aa
  have deg := degree_ge_of_baseline baseline
  have low := low_of_noProper noProper
  have br : ∀ u v, object.graph.Adj u v →
      ∃ p : object.graph.Walk u v, p.IsPath ∧ s(u, v) ∉ p.edges :=
    fun u v a => path_of_bridgeless bridgeless a
  have conn' := conn
  unfold DeletionConnected at conn'
  push Not at conn'
  obtain ⟨x₀, a₀, dis⟩ := conn'
  have c2 := block_card_two deg low br a₀ dis aa
  have am : a ∈ object.graph.neighborFinset h ∩ comp object.graph h a :=
    Finset.mem_inter.2 ⟨(SimpleGraph.mem_neighborFinset _ _ _).2 aa, self_mem_comp aa.ne⟩
  obtain ⟨b, hb⟩ : ∃ b, (object.graph.neighborFinset h ∩ comp object.graph h a).erase a = {b} :=
    Finset.card_eq_one.1 (by rw [Finset.card_erase_of_mem am, c2])
  have bm : b ∈ object.graph.neighborFinset h ∩ comp object.graph h a :=
    Finset.mem_of_mem_erase (hb ▸ Finset.mem_singleton_self b)
  have ba : b ≠ a := by
    have : b ∈ (object.graph.neighborFinset h ∩ comp object.graph h a).erase a :=
      hb ▸ Finset.mem_singleton_self b
    exact Finset.ne_of_mem_erase this
  have blk : object.graph.neighborFinset h ∩ comp object.graph h a = {a, b} := by
    rw [← Finset.insert_erase am, hb]
  have ab : object.graph.Adj h b := (SimpleGraph.mem_neighborFinset _ _ _).1 (Finset.mem_inter.1 bm).1
  refine ⟨b, ba, ab, blk, ?_, ?_, ?_, ?_⟩
  · intro r rp hr k hk e
    obtain ⟨c, cc, cl, -⟩ := pair_cycle ba.symm aa ab r rp hr
    exact no_dyadic_cycle avoid lengthLaw c cc k hk (cl.trans e)
  · intro q qp fresh
    exact return_ends_at_partner aa blk q qp fresh
  · intro p pp fa fb
    exact ⟨sameComp_avoids aa blk p pp fa fb, fun j hj e => sameComp_residue hj e⟩
  · intro a₂ a2 far p pp f1 f2
    obtain ⟨b₁, b₂, n1, n2, ab1, ab2, c1, c2', r₁, r₂, rp1, rp2, hr1, hr2, l⟩ :=
      cross_pair_split aa a2 far p pp f1 f2
    refine ⟨b₁, b₂, n1, n2, ab1, ab2, c1, c2', r₁, r₂, rp1, rp2, hr1, hr2, l, ?_⟩
    intro j hj e
    exact cross_residue hj (by omega)

end Holds

end Hypostructure.Graph.CycleCounting
