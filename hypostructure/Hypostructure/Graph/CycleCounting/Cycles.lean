import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Walk.Decomp
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

/-!
# Cycle sets and cycle counts at a vertex

Vocabulary-free counting of the cycles of a finite simple graph through a
fixed vertex `h`:

* `cyclesThrough G P h` (edge sets of the cycles through `h` with length in `P`)
  and `pairsThrough G P h` (the pairs of edges at `h` closed by a path of
  `G − h`), with `#pairsThrough ≤ #cyclesThrough` and the per-pair lower bound
  `C(d_h, 2) ≤ #cyclesThrough` when every two neighbours are joined in `G − h`;
* the cycle decomposition at `h` and the exact fibre count
  `#(cycles with h-edges {hx, hy}) = #(x → y paths of G − h)`;
* `allCycles G`, `#allCycles ≤ 2^m`, and the double count at an independent set
  `H`: `2 Σ_{h∈H} #cyclesThrough h ≤ n · #allCycles`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace Hypostructure.Graph.CycleCounting
open Finset Classical

variable {V : Type*} [Fintype V] (G : SimpleGraph V)

/-- Edge sets of the cycles of `G` through `h` whose length satisfies `P`. -/
noncomputable def cyclesThrough (P : ℕ → Prop) (h : V) : Finset (Finset (Sym2 V)) :=
  univ.filter (fun s => ∃ c : G.Walk h h, c.IsCycle ∧ c.edges.toFinset = s ∧ P c.length)

/-- The `h`-part of an edge set: its edges at `h`. -/
noncomputable def hPart (h : V) (s : Finset (Sym2 V)) : Finset (Sym2 V) := s.filter (fun e => h ∈ e)

/-- `{hx, hy}` for neighbours `x ≠ y` of `h` joined in `G − h` by a path of length `ℓ`
with `P (ℓ + 2)`. -/
noncomputable def pairsThrough (P : ℕ → Prop) (h : V) : Finset (Finset (Sym2 V)) :=
  univ.filter (fun T => ∃ x y, x ≠ y ∧ G.Adj h x ∧ G.Adj h y ∧
    (∃ p : G.Walk x y, p.IsPath ∧ h ∉ p.support ∧ P (p.length + 2)) ∧ T = {s(h, x), s(h, y)})

variable {G}

/-- The cycle `h x ⋯ y h` built from a path avoiding `h`. -/
theorem pair_cycle {h x y : V} (hxy : x ≠ y) (ax : G.Adj h x) (ay : G.Adj h y)
    (p : G.Walk x y) (pp : p.IsPath) (hp : h ∉ p.support) :
    ∃ c : G.Walk h h, c.IsCycle ∧ c.length = p.length + 2 ∧
      hPart h c.edges.toFinset = {s(h, x), s(h, y)} := by
  refine ⟨.cons ax (p.concat ay.symm), ?_, ?_, ?_⟩
  · rw [SimpleGraph.Walk.cons_isCycle_iff]
    refine ⟨(SimpleGraph.Walk.concat_isPath_iff _).2 ⟨pp, hp⟩, ?_⟩
    rw [SimpleGraph.Walk.edges_concat, List.concat_eq_append, List.mem_append, not_or]
    refine ⟨fun m => hp (p.fst_mem_support_of_mem_edges m), ?_⟩
    rw [List.mem_singleton]
    intro e
    rcases Sym2.eq_iff.1 e with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact ay.ne h1
    · exact hxy h2
  · simp [SimpleGraph.Walk.length_concat]
  · ext e
    simp only [hPart, mem_filter, List.mem_toFinset, SimpleGraph.Walk.edges_cons,
      SimpleGraph.Walk.edges_concat, List.concat_eq_append, List.mem_cons, List.mem_append,
      mem_insert, mem_singleton]
    constructor
    · rintro ⟨e1 | e2 | e3, he⟩
      · exact Or.inl e1
      · exact absurd (p.fst_mem_support_of_mem_edges (t := h) (u := (Sym2.Mem.other he)) (by rwa [Sym2.other_spec he])) hp
      · rcases e3 with e3 | e3
        · exact Or.inr (e3.trans (Sym2.eq_swap))
        · simp at e3
    · rintro (e1 | e2)
      · exact ⟨Or.inl e1, e1 ▸ Sym2.mem_mk_left _ _⟩
      · exact ⟨Or.inr (Or.inr (Or.inl (e2.trans Sym2.eq_swap))), e2 ▸ Sym2.mem_mk_left _ _⟩

/-- **Lower bound (any graph).** Distinct pairs at `h` give distinct cycles through `h`:
`#pairsThrough P h ≤ #cyclesThrough P h`. -/
theorem card_pairsThrough_le (P : ℕ → Prop) (h : V) :
    #(pairsThrough G P h) ≤ #(cyclesThrough G P h) := by
  apply card_le_card_of_surjOn (hPart h)
  intro T hT
  simp only [pairsThrough, coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hT
  obtain ⟨x, y, hxy, ax, ay, ⟨p, pp, hp, hP⟩, rfl⟩ := hT
  obtain ⟨c, cc, cl, cT⟩ := pair_cycle hxy ax ay p pp hp
  refine ⟨c.edges.toFinset, ?_, cT⟩
  simp only [cyclesThrough, coe_filter, mem_univ, true_and, Set.mem_setOf_eq]
  exact ⟨c, cc, rfl, cl ▸ hP⟩

/-- Every pair at `h` is a 2-subset of the edges at `h`. -/
theorem pairsThrough_subset [DecidableRel G.Adj] (P : ℕ → Prop) (h : V) :
    pairsThrough G P h ⊆ (G.incidenceFinset h).powersetCard 2 := by
  intro T hT
  simp only [pairsThrough, mem_filter, mem_univ, true_and] at hT
  obtain ⟨x, y, hxy, ax, ay, -, rfl⟩ := hT
  rw [mem_powersetCard]
  refine ⟨?_, ?_⟩
  · intro e he
    rw [mem_insert, mem_singleton] at he
    rw [SimpleGraph.mem_incidenceFinset]
    rcases he with rfl | rfl
    · exact ⟨ax, Sym2.mem_mk_left _ _⟩
    · exact ⟨ay, Sym2.mem_mk_left _ _⟩
  · apply card_pair
    intro e
    rcases Sym2.eq_iff.1 e with ⟨-, h2⟩ | ⟨h1, -⟩
    · exact hxy h2
    · exact ay.ne h1

/-- **Upper bound on what per-pair forcing can give**: `#pairsThrough P h ≤ C(d_h, 2)`. -/
theorem card_pairsThrough_le_choose [DecidableRel G.Adj] (P : ℕ → Prop) (h : V) :
    #(pairsThrough G P h) ≤ (G.degree h).choose 2 := by
  have := card_le_card (pairsThrough_subset (G := G) P h)
  rwa [card_powersetCard, SimpleGraph.card_incidenceFinset_eq_degree] at this

/-- If every two neighbours of `h` are joined in `G − h` by a path with `P (ℓ+2)`, then
`G` has at least `C(d_h, 2)` cycles through `h` with lengths in `P`. -/
theorem choose_le_cyclesThrough [DecidableRel G.Adj] (P : ℕ → Prop) (h : V)
    (conn : ∀ x y, x ≠ y → G.Adj h x → G.Adj h y →
      ∃ p : G.Walk x y, p.IsPath ∧ h ∉ p.support ∧ P (p.length + 2)) :
    (G.degree h).choose 2 ≤ #(cyclesThrough G P h) := by
  refine le_trans ?_ (card_pairsThrough_le P h)
  rw [← SimpleGraph.card_incidenceFinset_eq_degree, ← card_powersetCard]
  apply card_le_card
  intro T hT
  rw [mem_powersetCard, card_eq_two] at hT
  obtain ⟨sub, e₁, e₂, ne, rfl⟩ := hT
  have m₁ := sub (mem_insert_self _ _)
  have m₂ := sub (mem_insert_of_mem (mem_singleton_self _))
  rw [SimpleGraph.mem_incidenceFinset] at m₁ m₂
  obtain ⟨x, rfl⟩ := Sym2.mem_iff_exists.1 m₁.2
  obtain ⟨y, rfl⟩ := Sym2.mem_iff_exists.1 m₂.2
  have hxy : x ≠ y := by rintro rfl; exact ne rfl
  simp only [pairsThrough, mem_filter, mem_univ, true_and]
  exact ⟨x, y, hxy, m₁.1, m₂.1, conn x y hxy m₁.1 m₂.1, rfl⟩

/-- Monotonicity in the length predicate. -/
theorem pairsThrough_mono {P Q : ℕ → Prop} (hPQ : ∀ n, P n → Q n) (h : V) :
    pairsThrough G P h ⊆ pairsThrough G Q h := by
  intro T hT
  simp only [pairsThrough, mem_filter, mem_univ, true_and] at hT ⊢
  obtain ⟨x, y, hxy, ax, ay, ⟨p, pp, hp, hP⟩, rfl⟩ := hT
  exact ⟨x, y, hxy, ax, ay, ⟨p, pp, hp, hPQ _ hP⟩, rfl⟩


/-! ## Bridge from the forced paths, the star lemma, theta arithmetic, global bound -/

/-- A path of `G − E` is a path of `G` with the same support and length. -/
theorem deleteEdges_path_lift {E : Set (Sym2 V)} {x y : V}
    (p : (G.deleteEdges E).Walk x y) (pp : p.IsPath) :
    ∃ q : G.Walk x y, q.IsPath ∧ q.support = p.support ∧ q.length = p.length :=
  ⟨p.mapLe (G.deleteEdges_le E), pp.mapLe _, SimpleGraph.Walk.support_mapLe_eq_support _ _,
    SimpleGraph.Walk.length_map _ _⟩

/-- **Bridge from the same-vertex switch.** A forced path `p : x → y` of `G − {hx, hy}`
with `L (|p| + 1)` that avoids `h` (case (i) of `sameVertex_path_dichotomy`) puts the pair
`{hx, hy}` in `pairsThrough` for the shifted predicate `ℓ ↦ ∃ k, L k ∧ ℓ = k + 1`; with
`L = 2^·` this is the cycle length `2^j + 1`. -/
theorem avoid_pair_mem {L : ℕ → Prop} {h x y : V} (xy : x ≠ y) (ax : G.Adj h x)
    (ay : G.Adj h y) (p : (G.deleteEdges {s(h, x), s(h, y)}).Walk x y) (pp : p.IsPath)
    (hL : L (p.length + 1)) (avoid : h ∉ p.support) :
    ({s(h, x), s(h, y)} : Finset (Sym2 V)) ∈
      pairsThrough G (fun ℓ => ∃ k, L k ∧ ℓ = k + 1) h := by
  obtain ⟨q, qp, qs, ql⟩ := deleteEdges_path_lift p pp
  simp only [pairsThrough, mem_filter, mem_univ, true_and]
  exact ⟨x, y, xy, ax, ay, ⟨q, qp, qs ▸ avoid, _, hL, by omega⟩, rfl⟩

/-- Edge sets of all cycles of `G`. -/
noncomputable def allCycles : Finset (Finset (Sym2 V)) :=
  univ.filter (fun s => ∃ u, ∃ c : G.Walk u u, c.IsCycle ∧ c.edges.toFinset = s)

/-- **Trivial global upper bound**: `#cycles(G) ≤ 2^m`. -/
theorem card_allCycles_le [DecidableRel G.Adj] :
    #(allCycles (G := G)) ≤ 2 ^ #G.edgeFinset := by
  rw [← card_powerset]
  apply card_le_card
  intro s hs
  simp only [allCycles, mem_filter, mem_univ, true_and] at hs
  obtain ⟨u, c, -, rfl⟩ := hs
  rw [mem_powerset]
  intro e he
  rw [SimpleGraph.mem_edgeFinset]
  exact c.edges_subset_edgeSet (List.mem_toFinset.1 he)

/-- **Domination (any graph, any length predicate `P`).** The number of pairs at `h` that
per-pair forcing can certify is at most the number of pairs joined in `G − h`, which is at
most the number of cycles of `G` through `h` — a count every graph has from connectivity
alone.  So any valid upper bound `U ≥ #cycles through h` also dominates every per-pair
forced count: a raw count cannot contradict. -/
theorem forced_le_unconditional (P : ℕ → Prop) (h : V) :
    #(pairsThrough G P h) ≤ #(pairsThrough G (fun _ => True) h) ∧
      #(pairsThrough G (fun _ => True) h) ≤ #(cyclesThrough G (fun _ => True) h) :=
  ⟨card_le_card (pairsThrough_mono (fun _ _ => trivial) h), card_pairsThrough_le _ h⟩

end Hypostructure.Graph.CycleCounting

namespace Hypostructure.Graph.CycleCounting
open Finset Classical

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-! ## Decomposition of a cycle at `h` and the cycle/path bijection -/

theorem mem_hPart {h : V} {s : Finset (Sym2 V)} {e : Sym2 V} :
    e ∈ hPart h s ↔ e ∈ s ∧ h ∈ e := by simp [hPart]

/-- **Cycle decomposition at `h`.** Every cycle `c` at `h` is `h u ⋯ w h` with `u ≠ w`
neighbours of `h` and `r : u → w` a path avoiding `h`; its edge set is
`{hu, hw} ∪ E(r)` and `|c| = |r| + 2`. -/
theorem cycle_decomp {h : V} (c : G.Walk h h) (cc : c.IsCycle) :
    ∃ u w, u ≠ w ∧ G.Adj h u ∧ G.Adj h w ∧ ∃ r : G.Walk u w, r.IsPath ∧ h ∉ r.support ∧
      c.length = r.length + 2 ∧
      c.edges.toFinset = insert s(h, u) (insert s(h, w) r.edges.toFinset) := by
  cases c with
  | nil => exact absurd cc (SimpleGraph.Walk.IsCycle.not_of_nil)
  | @cons _ u _ ha rest =>
    rw [SimpleGraph.Walk.cons_isCycle_iff] at cc
    obtain ⟨rp, rfresh⟩ := cc
    have rrp : rest.reverse.IsPath := rp.reverse
    have hrev : rest = rest.reverse.reverse := (SimpleGraph.Walk.reverse_reverse rest).symm
    generalize hq : rest.reverse = q at rrp hrev
    cases q with
    | nil => exact absurd rfl ha.ne
    | @cons _ w _ hb r2 =>
      rw [SimpleGraph.Walk.cons_isPath_iff] at rrp
      obtain ⟨r2p, hr2⟩ := rrp
      subst hrev
      have uw : u ≠ w := by
        rintro rfl
        have : r2 = SimpleGraph.Walk.nil := by
          cases r2 with
          | nil => rfl
          | cons a p => exact absurd r2p (by
              intro hp; rw [SimpleGraph.Walk.isPath_def] at hp
              simp at hp)
        subst this
        exact rfresh (by simp [Sym2.eq_swap])
      refine ⟨u, w, uw, ha, hb, r2.reverse, r2p.reverse, ?_, ?_, ?_⟩
      · rw [SimpleGraph.Walk.support_reverse, List.mem_reverse]; exact hr2
      · simp
      · ext e
        simp only [SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_reverse, List.mem_toFinset,
          List.mem_cons, List.mem_reverse, List.mem_append, mem_insert,
          SimpleGraph.Walk.reverse_cons, SimpleGraph.Walk.edges_append,
          SimpleGraph.Walk.edges_nil, List.not_mem_nil, or_false]
        rw [Sym2.eq_swap (a := w)]
        tauto

/-- The edge set of the cycle built by `pair_cycle`. -/
theorem pair_cycle_edges {h x y : V} (hxy : x ≠ y) (ax : G.Adj h x) (ay : G.Adj h y)
    (p : G.Walk x y) (pp : p.IsPath) (hp : h ∉ p.support) :
    ∃ c : G.Walk h h, c.IsCycle ∧ c.length = p.length + 2 ∧
      c.edges.toFinset = insert s(h, x) (insert s(h, y) p.edges.toFinset) := by
  refine ⟨.cons ax (p.concat ay.symm), ?_, by simp [SimpleGraph.Walk.length_concat], ?_⟩
  · obtain ⟨c, cc, -, -⟩ := pair_cycle hxy ax ay p pp hp
    rw [SimpleGraph.Walk.cons_isCycle_iff]
    refine ⟨(SimpleGraph.Walk.concat_isPath_iff _).2 ⟨pp, hp⟩, ?_⟩
    rw [SimpleGraph.Walk.edges_concat, List.concat_eq_append, List.mem_append, not_or]
    refine ⟨fun m => hp (p.fst_mem_support_of_mem_edges m), ?_⟩
    rw [List.mem_singleton]
    intro e
    rcases Sym2.eq_iff.1 e with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact ay.ne h1
    · exact hxy h2
  · ext e
    simp only [SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_concat, List.concat_eq_append,
      List.mem_toFinset, List.mem_cons, List.mem_append, mem_insert, List.not_mem_nil, or_false]
    rw [Sym2.eq_swap (a := y)]
    tauto

/-- Edge sets of `x → y` paths of `G − h`. -/
noncomputable def pathSets (h x y : V) : Finset (Finset (Sym2 V)) :=
  univ.filter (fun e => ∃ p : G.Walk x y, p.IsPath ∧ h ∉ p.support ∧ p.edges.toFinset = e)

/-- Cycles through `h` whose edges at `h` are exactly `{hx, hy}`. -/
noncomputable def fibre (h x y : V) : Finset (Finset (Sym2 V)) :=
  (cyclesThrough G (fun _ => True) h).filter (fun s => hPart h s = {s(h, x), s(h, y)})

theorem not_mem_path_edges {h x y : V} {p : G.Walk x y} (hp : h ∉ p.support) {e : Sym2 V}
    (he : e ∈ p.edges) : h ∉ e := fun m =>
  hp (p.fst_mem_support_of_mem_edges (t := h) (u := Sym2.Mem.other m)
    (by rwa [Sym2.other_spec m]))

theorem hPart_insert_path {h x y u w : V} {p : G.Walk u w} (hp : h ∉ p.support) :
    hPart h (insert s(h, x) (insert s(h, y) p.edges.toFinset)) = {s(h, x), s(h, y)} := by
  ext e
  simp only [mem_hPart, mem_insert, mem_singleton, List.mem_toFinset]
  constructor
  · rintro ⟨e1 | e2 | e3, he⟩
    · exact Or.inl e1
    · exact Or.inr e2
    · exact absurd he (not_mem_path_edges hp e3)
  · rintro (rfl | rfl)
    · exact ⟨Or.inl rfl, Sym2.mem_mk_left _ _⟩
    · exact ⟨Or.inr (Or.inl rfl), Sym2.mem_mk_left _ _⟩

theorem sym2_pair_eq {h u w x y : V} (hu : h ≠ u) (hw : h ≠ w)
    (e : ({s(h, u), s(h, w)} : Finset (Sym2 V)) = {s(h, x), s(h, y)}) :
    (u = x ∨ u = y) ∧ (w = x ∨ w = y) := by
  have mu : s(h, u) ∈ ({s(h, x), s(h, y)} : Finset (Sym2 V)) := e ▸ mem_insert_self _ _
  have mw : s(h, w) ∈ ({s(h, x), s(h, y)} : Finset (Sym2 V)) :=
    e ▸ mem_insert_of_mem (mem_singleton_self _)
  simp only [mem_insert, mem_singleton, Sym2.eq_iff] at mu mw
  constructor
  · rcases mu with (⟨-, h1⟩ | ⟨-, h1⟩) | (⟨-, h1⟩ | ⟨-, h1⟩)
    · exact Or.inl h1
    · exact absurd h1.symm hu
    · exact Or.inr h1
    · exact absurd h1.symm hu
  · rcases mw with (⟨-, h1⟩ | ⟨-, h1⟩) | (⟨-, h1⟩ | ⟨-, h1⟩)
    · exact Or.inl h1
    · exact absurd h1.symm hw
    · exact Or.inr h1
    · exact absurd h1.symm hw

/-- **Bijection.** Cycles through `h` with `h`-edges `{hx, hy}` correspond exactly to the
`x → y` paths of `G − h` (as edge sets): `#fibre h x y = #pathSets h x y`. -/
theorem card_fibre_eq {h x y : V} (hxy : x ≠ y) (ax : G.Adj h x) (ay : G.Adj h y) :
    #(fibre (G := G) h x y) = #(pathSets (G := G) h x y) := by
  have img : fibre (G := G) h x y =
      (pathSets (G := G) h x y).image (fun e => insert s(h, x) (insert s(h, y) e)) := by
    ext s
    simp only [fibre, cyclesThrough, pathSets, mem_filter, mem_univ, true_and, mem_image,
      and_true]
    constructor
    · rintro ⟨⟨c, cc, rfl, -⟩, hs⟩
      obtain ⟨u, w, uw, au, aw, r, rp, hr, -, ce⟩ := cycle_decomp c cc
      rw [ce, hPart_insert_path hr] at hs
      obtain ⟨hu1, hw1⟩ := sym2_pair_eq au.ne aw.ne hs
      rcases hu1 with rfl | rfl
      · rcases hw1 with rfl | rfl
        · exact absurd rfl uw
        · exact ⟨r.edges.toFinset, ⟨r, rp, hr, rfl⟩, ce.symm⟩
      · rcases hw1 with rfl | rfl
        · refine ⟨r.reverse.edges.toFinset, ⟨r.reverse, rp.reverse, by simpa using hr, rfl⟩, ?_⟩
          rw [ce, insert_comm]
          congr 2
          ext e; simp [SimpleGraph.Walk.edges_reverse]
        · exact absurd rfl uw
    · rintro ⟨e, ⟨p, pp, hp, rfl⟩, rfl⟩
      obtain ⟨c, cc, -, ce⟩ := pair_cycle_edges hxy ax ay p pp hp
      exact ⟨⟨c, cc, ce⟩, hPart_insert_path hp⟩
  rw [img]
  apply card_image_of_injOn
  intro e he e' he' eq
  simp only [pathSets, coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at he he'
  obtain ⟨p, -, hp, rfl⟩ := he
  obtain ⟨p', -, hp', rfl⟩ := he'
  simp only at eq
  have side : ∀ {u w : V} {q : G.Walk u w}, h ∉ q.support → ∀ f ∈ q.edges.toFinset,
      f ≠ s(h, x) ∧ f ≠ s(h, y) := by
    intro u w q hq f hf
    have := not_mem_path_edges hq (List.mem_toFinset.1 hf)
    exact ⟨fun e => this (e ▸ Sym2.mem_mk_left _ _), fun e => this (e ▸ Sym2.mem_mk_left _ _)⟩
  ext f
  constructor
  · intro hf
    have : f ∈ insert s(h, x) (insert s(h, y) p'.edges.toFinset) := eq ▸ mem_insert_of_mem
      (mem_insert_of_mem hf)
    obtain ⟨n1, n2⟩ := side hp f hf
    simpa [n1, n2] using this
  · intro hf
    have : f ∈ insert s(h, x) (insert s(h, y) p.edges.toFinset) := eq.symm ▸ mem_insert_of_mem
      (mem_insert_of_mem hf)
    obtain ⟨n1, n2⟩ := side hp' f hf
    simpa [n1, n2] using this

end Hypostructure.Graph.CycleCounting

namespace Hypostructure.Graph.CycleCounting
open Finset Classical

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-! ## Global distinct-cycle bound by double counting -/

theorem cyclesThrough_sub_all {P : ℕ → Prop} {h : V} :
    cyclesThrough G P h ⊆ allCycles (G := G) := by
  intro s hs
  simp only [cyclesThrough, allCycles, mem_filter, mem_univ, true_and] at hs ⊢
  obtain ⟨c, cc, rfl, -⟩ := hs
  exact ⟨h, c, cc, rfl⟩

/-- A cycle through `h` has exactly two edges at `h`. -/
theorem hPart_card_two {P : ℕ → Prop} {h : V} {s : Finset (Sym2 V)}
    (hs : s ∈ cyclesThrough G P h) : #(hPart h s) = 2 := by
  simp only [cyclesThrough, mem_filter, mem_univ, true_and] at hs
  obtain ⟨c, cc, rfl, -⟩ := hs
  obtain ⟨u, w, uw, au, aw, r, -, hr, -, ce⟩ := cycle_decomp c cc
  rw [ce, hPart_insert_path hr]
  apply card_pair
  intro e
  exact uw (Sym2.congr_right.1 e)

/-- A cycle has at most `n` edges. -/
theorem card_le_of_mem_allCycles {s : Finset (Sym2 V)} (hs : s ∈ allCycles (G := G)) :
    #s ≤ Fintype.card V := by
  simp only [allCycles, mem_filter, mem_univ, true_and] at hs
  obtain ⟨u, c, cc, rfl⟩ := hs
  rw [List.toFinset_card_of_nodup cc.edges_nodup, SimpleGraph.Walk.length_edges]
  have tl := cc.support_nodup
  have : c.support.tail.length = c.length := by
    rw [List.length_tail, SimpleGraph.Walk.length_support]; rfl
  rw [← this]
  exact tl.length_le_card

/-- **`H` independent ⇒ `μ ≤ ⌊|C|/2⌋`**: a cycle meets at most `|C|/2` vertices of an
independent set `H`. -/
theorem two_mul_card_H_le (H : Finset V) (indep : ∀ a ∈ H, ∀ b ∈ H, ¬ G.Adj a b)
    {s : Finset (Sym2 V)} (hs : s ∈ allCycles (G := G)) :
    2 * #(H.filter (fun h => s ∈ cyclesThrough G (fun _ => True) h)) ≤ #s := by
  obtain ⟨F, hF⟩ : ∃ F, F = H.filter (fun h => s ∈ cyclesThrough G (fun _ => True) h) :=
    ⟨_, rfl⟩
  rw [← hF]
  have memF : ∀ {a}, a ∈ F → a ∈ H ∧ s ∈ cyclesThrough G (fun _ => True) a := fun m => by
    rw [hF] at m; exact mem_filter.1 m
  have sE : ∀ e ∈ s, e ∈ G.edgeSet := by
    simp only [allCycles, mem_filter, mem_univ, true_and] at hs
    obtain ⟨u, c, -, rfl⟩ := hs
    intro e he
    exact c.edges_subset_edgeSet (List.mem_toFinset.1 he)
  have disj : (F : Set V).PairwiseDisjoint (fun h => hPart h s) := by
    intro a ha b hb ab
    rw [Function.onFun, disjoint_left]
    intro e ea eb
    rw [mem_hPart] at ea eb
    have := (Sym2.mem_and_mem_iff ab).1 ⟨ea.2, eb.2⟩
    have adj := sE e ea.1
    rw [this, SimpleGraph.mem_edgeSet] at adj
    exact indep a (memF ha).1 b (memF hb).1 adj
  have card := card_biUnion (s := F) (t := fun h => hPart h s) (fun a ha b hb ab => disj ha hb ab)
  rw [sum_congr rfl (fun h hh => hPart_card_two (memF hh).2), sum_const,
    smul_eq_mul] at card
  have sub : F.biUnion (fun h => hPart h s) ⊆ s := by
    intro e he
    obtain ⟨h, -, he⟩ := mem_biUnion.1 he
    exact (mem_hPart.1 he).1
  have := card_le_card sub
  omega

/-- **Double counting.** If every cycle meets at most `μ` of the centres in `H`, then
`Σ_{h∈H} #(cycles through h) ≤ μ · #cycles(G)`. -/
theorem sum_cyclesThrough_le (H : Finset V) (μ : ℕ)
    (hμ : ∀ s ∈ allCycles (G := G), #(H.filter (fun h => s ∈ cyclesThrough G (fun _ => True) h)) ≤ μ) :
    ∑ h ∈ H, #(cyclesThrough G (fun _ => True) h) ≤ μ * #(allCycles (G := G)) := by
  calc ∑ h ∈ H, #(cyclesThrough G (fun _ => True) h)
      = ∑ h ∈ H, ∑ s ∈ allCycles (G := G), if s ∈ cyclesThrough G (fun _ => True) h then 1 else 0 := by
        refine sum_congr rfl (fun h _ => ?_)
        rw [← card_filter]
        congr 1
        ext s
        simp only [mem_filter]
        exact ⟨fun m => ⟨cyclesThrough_sub_all m, m⟩, fun m => m.2⟩
    _ = ∑ s ∈ allCycles (G := G), ∑ h ∈ H, if s ∈ cyclesThrough G (fun _ => True) h then 1 else 0 :=
        sum_comm
    _ = ∑ s ∈ allCycles (G := G), #(H.filter (fun h => s ∈ cyclesThrough G (fun _ => True) h)) := by
        refine sum_congr rfl (fun s _ => ?_)
        rw [card_filter]
    _ ≤ ∑ _s ∈ allCycles (G := G), μ := sum_le_sum hμ
    _ = μ * #(allCycles (G := G)) := by rw [sum_const, smul_eq_mul, mul_comm]

/-- **Global distinct-cycle bound at an independent `H`**:
`2 · Σ_{h∈H} #(cycles through h) ≤ n · #cycles(G)`, i.e. `#cycles ≥ Σ_h L_h / ⌊n/2⌋`. -/
theorem global_cycles_bound (H : Finset V) (indep : ∀ a ∈ H, ∀ b ∈ H, ¬ G.Adj a b) :
    2 * ∑ h ∈ H, #(cyclesThrough G (fun _ => True) h) ≤
      Fintype.card V * #(allCycles (G := G)) := by
  have := sum_cyclesThrough_le (G := G) H (Fintype.card V / 2) (fun s hs => by
    have a := two_mul_card_H_le H indep hs
    have b := card_le_of_mem_allCycles hs
    omega)
  have : 2 * (Fintype.card V / 2) ≤ Fintype.card V := Nat.mul_div_le _ _
  nlinarith

end Hypostructure.Graph.CycleCounting
