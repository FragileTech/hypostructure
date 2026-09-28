import Hypostructure.Graph.CycleCounting.Cycles

/-!
# The components of `G − h`

For a graph with minimum degree `≥ 3`, no proper subgraph of minimum degree
`≥ 3` and no bridge, every vertex `h` either leaves `G − h` connected or every
component of `G − h` meeting `N(h)` meets it in exactly two vertices, so
`d_h = 2 · #blocks` is even.  In the disconnected case every return of an edge
`ha` ends at the partner of `a`, a path between the two neighbours of a block
avoiding their `h`-edges avoids `h`, a path between different blocks splits at
`h`, and the dyadic residues of those lengths.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Hypostructure.Graph.CycleCounting
open Finset Classical

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

variable [DecidableEq V] [DecidableRel G.Adj]

variable (G) in
/-- The vertex set of the component of `x` in `G − h`. -/
noncomputable def comp (h x : V) : Finset V :=
  univ.filter (fun v => ∃ p : G.Walk x v, h ∉ p.support)

theorem self_mem_comp {h x : V} (hx : h ≠ x) : x ∈ comp G h x := by
  simp only [comp, mem_filter, mem_univ, true_and]
  exact ⟨.nil, by simpa using hx⟩

theorem ne_of_mem_comp {h x v : V} (hv : v ∈ comp G h x) : v ≠ h := by
  simp only [comp, mem_filter, mem_univ, true_and] at hv
  obtain ⟨p, hp⟩ := hv
  rintro rfl
  exact hp p.end_mem_support

theorem comp_closed {h x v w : V} (hv : v ∈ comp G h x) (a : G.Adj v w) (hw : w ≠ h) :
    w ∈ comp G h x := by
  simp only [comp, mem_filter, mem_univ, true_and] at hv ⊢
  obtain ⟨p, hp⟩ := hv
  refine ⟨p.concat a, ?_⟩
  rw [SimpleGraph.Walk.support_concat, List.mem_append, not_or]
  exact ⟨hp, by simpa using hw.symm⟩

/-- **Component lemma.**  With `δ ≥ 3`, no proper induced subgraph of minimum degree `≥ 3`
(`noProperBaseline`), and no bridge, for every neighbour `x` of `h`: either `G − h` is
connected (the component of `x` is everything but `h`), or the component of `x` in `G − h`
contains exactly two neighbours of `h`. -/
theorem component_two_or_connected
    (deg : ∀ v, 3 ≤ G.degree v)
    (noProper : ∀ S : Finset V, S.Nonempty → S ≠ univ →
      ∃ v ∈ S, #(G.neighborFinset v ∩ S) ≤ 2)
    (bridgeless : ∀ u v, G.Adj u v → ∃ p : G.Walk u v, p.IsPath ∧ s(u, v) ∉ p.edges)
    {h x : V} (ax : G.Adj h x) :
    insert h (comp G h x) = univ ∨ #(G.neighborFinset h ∩ comp G h x) = 2 := by
  -- at least two: the return of `hx`
  have two : 2 ≤ #(G.neighborFinset h ∩ comp G h x) := by
    obtain ⟨p, pp, pe⟩ := bridgeless h x ax
    cases p with
    | nil => exact absurd rfl ax.ne
    | @cons _ z _ a q =>
      rw [SimpleGraph.Walk.cons_isPath_iff] at pp
      have zx : z ≠ x := by
        rintro rfl
        exact pe (by simp)
      have zc : z ∈ comp G h x := by
        simp only [comp, mem_filter, mem_univ, true_and]
        exact ⟨q.reverse, by rw [SimpleGraph.Walk.support_reverse, List.mem_reverse]; exact pp.2⟩
      have sub : ({x, z} : Finset V) ⊆ G.neighborFinset h ∩ comp G h x := by
        intro w hw
        rw [mem_insert, mem_singleton] at hw
        rw [mem_inter, SimpleGraph.mem_neighborFinset]
        rcases hw with rfl | rfl
        · exact ⟨ax, self_mem_comp ax.ne⟩
        · exact ⟨a, zc⟩
      have := card_le_card sub
      rwa [card_pair zx.symm] at this
  by_cases full : insert h (comp G h x) = univ
  · exact Or.inl full
  right
  obtain ⟨v, vS, vle⟩ := noProper _ ⟨h, mem_insert_self _ _⟩ full
  rcases mem_insert.1 vS with rfl | vc
  · refine le_antisymm (le_trans (card_le_card ?_) vle) two
    exact inter_subset_inter_left (subset_insert _ _)
  · exfalso
    have sub : G.neighborFinset v ⊆ G.neighborFinset v ∩ insert h (comp G h x) := by
      intro w hw
      refine mem_inter.2 ⟨hw, ?_⟩
      by_cases wh : w = h
      · exact wh ▸ mem_insert_self _ _
      · exact mem_insert_of_mem (comp_closed vc ((SimpleGraph.mem_neighborFinset _ _ _).1 hw) wh)
    have := card_le_card sub
    rw [SimpleGraph.card_neighborFinset_eq_degree] at this
    have := deg v
    omega

/-- In the connected case every two neighbours of `h` are joined by a path avoiding `h`, so
`C(d_h, 2) ≤ #(cycles through h)`. -/
theorem choose_le_cycles_of_connected {h x : V} (ax : G.Adj h x)
    (full : insert h (comp G h x) = univ) :
    (G.degree h).choose 2 ≤ #(cyclesThrough G (fun _ => True) h) := by
  apply choose_le_cyclesThrough
  intro y z yz ay az
  have my : y ∈ comp G h x := by
    have := full ▸ mem_univ y
    rcases mem_insert.1 this with e | e
    · exact absurd e.symm ay.ne
    · exact e
  have mz : z ∈ comp G h x := by
    have := full ▸ mem_univ z
    rcases mem_insert.1 this with e | e
    · exact absurd e.symm az.ne
    · exact e
  simp only [comp, mem_filter, mem_univ, true_and] at my mz
  obtain ⟨p, hp⟩ := my
  obtain ⟨q, hq⟩ := mz
  let w := p.reverse.append q
  have hw : h ∉ w.support := by
    intro m
    rw [SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.support_reverse,
      List.mem_reverse] at m
    rcases m with m | m
    · exact hp m
    · exact hq m
  refine ⟨w.bypass, w.bypass_isPath, fun m => hw (w.support_bypass_subset_support m), trivial⟩



end Hypostructure.Graph.CycleCounting

namespace Hypostructure.Graph.CycleCounting
open Finset Classical

variable {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableEq V] [DecidableRel G.Adj]

/-! ## The disconnected arm: parity and the exact pair count -/

theorem walk_of_mem_comp {h x v : V} (hv : v ∈ comp G h x) :
    ∃ p : G.Walk x v, h ∉ p.support := by
  simpa [comp] using hv

theorem mem_comp_of_walk {h x v : V} (p : G.Walk x v) (hp : h ∉ p.support) :
    v ∈ comp G h x := by
  simp only [comp, mem_filter, mem_univ, true_and]; exact ⟨p, hp⟩

theorem comp_symm {h x y : V} (hy : y ∈ comp G h x) : x ∈ comp G h y := by
  obtain ⟨p, hp⟩ := walk_of_mem_comp hy
  exact mem_comp_of_walk p.reverse (by simpa using hp)

theorem comp_eq {h x y : V} (hy : y ∈ comp G h x) : comp G h y = comp G h x := by
  obtain ⟨p, hp⟩ := walk_of_mem_comp hy
  ext v
  constructor
  · intro hv
    obtain ⟨q, hq⟩ := walk_of_mem_comp hv
    refine mem_comp_of_walk (p.append q) ?_
    rw [SimpleGraph.Walk.mem_support_append_iff]; tauto
  · intro hv
    obtain ⟨q, hq⟩ := walk_of_mem_comp hv
    refine mem_comp_of_walk (p.reverse.append q) ?_
    rw [SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.support_reverse,
      List.mem_reverse]; tauto

/-- Disconnection of `G − h` seen from one neighbour holds from every neighbour. -/
theorem all_disconnected {h x₀ : V} (a₀ : G.Adj h x₀) (dis : insert h (comp G h x₀) ≠ univ)
    {x : V} (_ : G.Adj h x) : insert h (comp G h x) ≠ univ := by
  intro full
  have : x₀ ∈ comp G h x := by
    rcases mem_insert.1 (full ▸ mem_univ x₀) with e | e
    · exact absurd e.symm a₀.ne
    · exact e
  rw [comp_eq this] at dis
  exact dis full

/-- The blocks `N(h) ∩ K` of the components `K` of `G − h`. -/
noncomputable def blocks (G : SimpleGraph V) [DecidableRel G.Adj] (h : V) : Finset (Finset V) :=
  (G.neighborFinset h).image (fun x => G.neighborFinset h ∩ comp G h x)

section Disconnected

variable (deg : ∀ v, 3 ≤ G.degree v)
    (noProper : ∀ S : Finset V, S.Nonempty → S ≠ univ →
      ∃ v ∈ S, #(G.neighborFinset v ∩ S) ≤ 2)
    (bridgeless : ∀ u v, G.Adj u v → ∃ p : G.Walk u v, p.IsPath ∧ s(u, v) ∉ p.edges)
    {h x₀ : V} (a₀ : G.Adj h x₀) (dis : insert h (comp G h x₀) ≠ univ)
include deg noProper bridgeless a₀ dis

theorem block_card_two {x : V} (ax : G.Adj h x) :
    #(G.neighborFinset h ∩ comp G h x) = 2 :=
  (component_two_or_connected deg noProper bridgeless ax).resolve_left
    (all_disconnected a₀ dis ax)

/-- **Parity.** When `G − h` is disconnected, `d_h = 2 · #blocks`: `d_h` is even and `G − h`
has exactly `d_h / 2` components meeting `N(h)`, each meeting it in exactly two vertices. -/
theorem degree_eq_two_mul_blocks : G.degree h = 2 * #(blocks G h) := by
  have disj : ((blocks G h : Set (Finset V))).PairwiseDisjoint id := by
    intro B₁ h₁ B₂ h₂ ne
    rw [Function.onFun, id, id, disjoint_left]
    intro v v₁ v₂
    simp only [blocks, coe_image, Set.mem_image, mem_coe] at h₁ h₂
    obtain ⟨x₁, -, rfl⟩ := h₁
    obtain ⟨x₂, -, rfl⟩ := h₂
    rw [mem_inter] at v₁ v₂
    apply ne
    rw [← comp_eq v₁.2, ← comp_eq v₂.2]
  have card := card_biUnion (s := blocks G h) (t := id) (fun a ha b hb ab => disj ha hb ab)
  have two : ∀ B ∈ blocks G h, #(id B) = 2 := by
    intro B hB
    simp only [blocks, mem_image] at hB
    obtain ⟨x, hx, rfl⟩ := hB
    exact block_card_two deg noProper bridgeless a₀ dis ((SimpleGraph.mem_neighborFinset _ _ _).1 hx)
  rw [sum_congr rfl two, sum_const, smul_eq_mul] at card
  have eq : (blocks G h).biUnion id = G.neighborFinset h := by
    ext v
    simp only [mem_biUnion, blocks, mem_image, id]
    constructor
    · rintro ⟨B, ⟨x, -, rfl⟩, hv⟩; exact (mem_inter.1 hv).1
    · intro hv
      exact ⟨_, ⟨v, hv, rfl⟩, mem_inter.2 ⟨hv, self_mem_comp
        ((SimpleGraph.mem_neighborFinset _ _ _).1 hv).ne⟩⟩
  rw [eq, SimpleGraph.card_neighborFinset_eq_degree] at card
  omega

theorem degree_even : Even (G.degree h) :=
  ⟨#(blocks G h), by rw [degree_eq_two_mul_blocks deg noProper bridgeless a₀ dis]; ring⟩

/-- **Exact pair count in the disconnected arm**: `#pairsThrough True h = #blocks = d_h / 2`. -/
theorem card_pairsThrough_disconnected :
    #(pairsThrough G (fun _ => True) h) = #(blocks G h) := by
  have img : pairsThrough G (fun _ => True) h =
      (blocks G h).image (fun B => B.image (fun v => s(h, v))) := by
    ext T
    simp only [pairsThrough, mem_filter, mem_univ, true_and, mem_image, blocks]
    constructor
    · rintro ⟨x, y, xy, ax, ay, ⟨p, -, hp, -⟩, rfl⟩
      have yc : y ∈ comp G h x := mem_comp_of_walk p hp
      have sub : ({x, y} : Finset V) ⊆ G.neighborFinset h ∩ comp G h x := by
        intro v hv
        rw [mem_insert, mem_singleton] at hv
        rcases hv with rfl | rfl
        · exact mem_inter.2 ⟨(SimpleGraph.mem_neighborFinset _ _ _).2 ax, self_mem_comp ax.ne⟩
        · exact mem_inter.2 ⟨(SimpleGraph.mem_neighborFinset _ _ _).2 ay, yc⟩
      have eqB : G.neighborFinset h ∩ comp G h x = {x, y} :=
        (eq_of_subset_of_card_le sub (by
          rw [block_card_two deg noProper bridgeless a₀ dis ax, card_pair xy])).symm
      refine ⟨_, ⟨x, (SimpleGraph.mem_neighborFinset _ _ _).2 ax, rfl⟩, ?_⟩
      rw [eqB, image_insert, image_singleton]
      ext e; simp
    · rintro ⟨B, ⟨x, hx, rfl⟩, rfl⟩
      have ax := (SimpleGraph.mem_neighborFinset _ _ _).1 hx
      have c2 := block_card_two deg noProper bridgeless a₀ dis ax
      have xm : x ∈ G.neighborFinset h ∩ comp G h x := mem_inter.2 ⟨hx, self_mem_comp ax.ne⟩
      obtain ⟨y, hy⟩ : ∃ y, (G.neighborFinset h ∩ comp G h x).erase x = {y} :=
        card_eq_one.1 (by rw [card_erase_of_mem xm, c2])
      have ym : y ∈ G.neighborFinset h ∩ comp G h x := mem_of_mem_erase (hy ▸ mem_singleton_self y)
      have xy : x ≠ y := fun e => by
        have : y ∈ (G.neighborFinset h ∩ comp G h x).erase x := hy ▸ mem_singleton_self y
        exact (ne_of_mem_erase this) e.symm
      have eqB : G.neighborFinset h ∩ comp G h x = {x, y} := by
        rw [← insert_erase xm, hy]
      obtain ⟨w, hw⟩ := walk_of_mem_comp (mem_inter.1 ym).2
      refine ⟨x, y, xy, ax, (SimpleGraph.mem_neighborFinset _ _ _).1 (mem_inter.1 ym).1,
        ⟨w.bypass, w.bypass_isPath, fun m => hw (w.support_bypass_subset_support m), trivial⟩, ?_⟩
      rw [eqB, image_insert, image_singleton]
      ext e; simp
  rw [img]
  exact card_image_of_injective _ (image_injective (fun a b e => Sym2.congr_right.1 e))

/-- Lower bound in the disconnected arm: `d_h / 2 ≤ #(cycles through h)`, with
`2 · (pairs) = d_h` exactly. -/
theorem disconnected_cycles_lower :
    2 * #(pairsThrough G (fun _ => True) h) = G.degree h ∧
      G.degree h / 2 ≤ #(cyclesThrough G (fun _ => True) h) := by
  have e1 := card_pairsThrough_disconnected deg noProper bridgeless a₀ dis
  have e2 := degree_eq_two_mul_blocks deg noProper bridgeless a₀ dis
  have e3 := card_pairsThrough_le (G := G) (fun _ => True) h
  omega

end Disconnected

end Hypostructure.Graph.CycleCounting

namespace Hypostructure.Graph.CycleCounting
open Finset Classical

variable {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableEq V] [DecidableRel G.Adj]

/-! ## The disconnected arm: returns end at the partner; cross-pair length equations -/

/-- **A return of `ha` ends at a neighbour `b ≠ a` of `h` in the component of `a`**, and
`|q| = |r| + 1` for an `a → b` path `r` of `G − h`. -/
theorem return_ends_in_comp {h a : V} (aa : G.Adj h a) (q : G.Walk a h) (qp : q.IsPath)
    (fresh : s(h, a) ∉ q.edges) :
    ∃ b, b ≠ a ∧ G.Adj h b ∧ b ∈ comp G h a ∧ ∃ r : G.Walk a b, r.IsPath ∧ h ∉ r.support ∧
      r.length + 1 = q.length := by
  have qrp : q.reverse.IsPath := qp.reverse
  have hrev : q = q.reverse.reverse := (SimpleGraph.Walk.reverse_reverse q).symm
  generalize hw : q.reverse = w at qrp hrev
  cases w with
  | nil => exact absurd rfl aa.ne
  | @cons _ b _ hb r2 =>
    rw [SimpleGraph.Walk.cons_isPath_iff] at qrp
    obtain ⟨r2p, hr2⟩ := qrp
    subst hrev
    have ba : b ≠ a := by
      rintro rfl
      exact fresh (by simp)
    refine ⟨b, ba, hb, mem_comp_of_walk r2.reverse (by simpa using hr2), r2.reverse,
      r2p.reverse, by simpa using hr2, by simp⟩

/-- **Partner lemma (disconnected arm).** If the block of `a` is `{a, b}`, every return of
`ha` is `a ⋯ b h` with an `a → b` path of `G − h` of length `|q| − 1`. -/
theorem return_ends_at_partner {h a b : V} (aa : G.Adj h a)
    (blk : G.neighborFinset h ∩ comp G h a = {a, b}) (q : G.Walk a h) (qp : q.IsPath)
    (fresh : s(h, a) ∉ q.edges) :
    ∃ r : G.Walk a b, r.IsPath ∧ h ∉ r.support ∧ r.length + 1 = q.length := by
  obtain ⟨b', ba, hb', hc, r, rp, hr, rl⟩ := return_ends_in_comp aa q qp fresh
  have : b' ∈ ({a, b} : Finset V) :=
    blk ▸ mem_inter.2 ⟨(SimpleGraph.mem_neighborFinset _ _ _).2 hb', hc⟩
  rw [mem_insert, mem_singleton] at this
  rcases this with rfl | rfl
  · exact absurd rfl ba
  · exact ⟨r, rp, hr, rl⟩

/-- **Same-component switch path avoids `h`.** If the block of `a` is `{a, b}`, a path
`a → b` using neither `ha` nor `hb` never visits `h`. -/
theorem sameComp_avoids {h a b : V} (aa : G.Adj h a)
    (blk : G.neighborFinset h ∩ comp G h a = {a, b}) (p : G.Walk a b) (pp : p.IsPath)
    (fa : s(h, a) ∉ p.edges) (fb : s(h, b) ∉ p.edges) : h ∉ p.support := by
  intro hin
  let q := p.takeUntil h hin
  have qp : q.IsPath := pp.takeUntil hin
  have qe : ∀ e ∈ q.edges, e ∈ p.edges := fun e he => p.edges_takeUntil_subset_edges hin he
  obtain ⟨v, va, hv, vc, -⟩ := return_ends_in_comp aa q qp (fun m => fa (qe _ m))
  have : v ∈ ({a, b} : Finset V) :=
    blk ▸ mem_inter.2 ⟨(SimpleGraph.mem_neighborFinset _ _ _).2 hv, vc⟩
  rw [mem_insert, mem_singleton] at this
  rcases this with rfl | rfl
  · exact va rfl
  · -- the last edge of `q` is `vh = bh`
    have qrp : q.reverse.IsPath := qp.reverse
    have hrev : q = q.reverse.reverse := (SimpleGraph.Walk.reverse_reverse q).symm
    generalize hw : q.reverse = w at qrp hrev
    cases w with
    | nil => exact absurd rfl aa.ne
    | @cons _ c _ hc r2 =>
      have cm : c ∈ ({a, v} : Finset V) := by
        have hcomp : c ∈ comp G h a := mem_comp_of_walk r2.reverse (by
          rw [SimpleGraph.Walk.cons_isPath_iff] at qrp; simpa using qrp.2)
        exact blk ▸ mem_inter.2 ⟨(SimpleGraph.mem_neighborFinset _ _ _).2 hc, hcomp⟩
      have lastE : s(h, c) ∈ q.edges := by
        have : s(h, c) ∈ q.reverse.edges := by rw [hw]; simp
        simpa using this
      rw [mem_insert, mem_singleton] at cm
      rcases cm with rfl | rfl
      · exact fa (qe _ lastE)
      · exact fb (qe _ lastE)

/-- **Cross-pair split.** For `a₂` outside the component of `a₁` in `G − h`, a path
`a₁ → a₂` using neither `ha₁` nor `ha₂` passes through `h` and splits as
`a₁ ⋯ b₁ h b₂ ⋯ a₂` with `r₁ : a₁ → b₁`, `r₂ : a₂ → b₂` paths of `G − h` (`bᵢ ≠ aᵢ`
neighbours of `h` in the component of `aᵢ`) and `|r₁| + |r₂| + 2 = |p|`. -/
theorem cross_pair_split {h a₁ a₂ : V} (a1 : G.Adj h a₁) (a2 : G.Adj h a₂)
    (far : a₂ ∉ comp G h a₁) (p : G.Walk a₁ a₂) (pp : p.IsPath)
    (f1 : s(h, a₁) ∉ p.edges) (f2 : s(h, a₂) ∉ p.edges) :
    ∃ b₁ b₂, b₁ ≠ a₁ ∧ b₂ ≠ a₂ ∧ G.Adj h b₁ ∧ G.Adj h b₂ ∧ b₁ ∈ comp G h a₁ ∧
      b₂ ∈ comp G h a₂ ∧ ∃ (r₁ : G.Walk a₁ b₁) (r₂ : G.Walk a₂ b₂), r₁.IsPath ∧ r₂.IsPath ∧
      h ∉ r₁.support ∧ h ∉ r₂.support ∧ r₁.length + r₂.length + 2 = p.length := by
  have hin : h ∈ p.support := by
    by_contra hn
    exact far (mem_comp_of_walk p hn)
  let q₁ := p.takeUntil h hin
  let q₂ := (p.dropUntil h hin).reverse
  obtain ⟨b₁, n1, ab1, c1, r₁, rp1, hr1, l1⟩ := return_ends_in_comp a1 q₁ (pp.takeUntil hin)
    (fun m => f1 (p.edges_takeUntil_subset_edges hin m))
  obtain ⟨b₂, n2, ab2, c2, r₂, rp2, hr2, l2⟩ := return_ends_in_comp a2 q₂
    (pp.dropUntil hin).reverse
    (fun m => f2 (p.edges_dropUntil_subset_edges hin (by simpa [q₂] using m)))
  have lp := congrArg SimpleGraph.Walk.length (p.take_spec hin)
  rw [SimpleGraph.Walk.length_append] at lp
  have e1 : q₁.length = (p.takeUntil h hin).length := rfl
  have e2 : q₂.length = (p.dropUntil h hin).length := SimpleGraph.Walk.length_reverse _
  exact ⟨b₁, b₂, n1, n2, ab1, ab2, c1, c2, r₁, r₂, rp1, rp2, hr1, hr2, by omega⟩

/-! ### Residues -/

/-- Same-component forced path: `λ + 1 = 2^j`, `j ≥ 2` ⇒ `λ ≡ 3 (mod 4)`. -/
theorem sameComp_residue {l j : ℕ} (hj : 2 ≤ j) (e : l + 1 = 2 ^ j) : l % 4 = 3 := by
  obtain ⟨t, rfl⟩ : ∃ t, j = t + 2 := ⟨j - 2, by omega⟩
  rw [pow_add] at e; norm_num at e; omega

/-- Cross pair: `λ₁ + λ₂ + 2 + 1 = 2^j`, `j ≥ 2` ⇒ `λ₁ + λ₂ ≡ 1 (mod 4)`; opposite parities. -/
theorem cross_residue {l₁ l₂ j : ℕ} (hj : 2 ≤ j) (e : l₁ + l₂ + 2 + 1 = 2 ^ j) :
    (l₁ + l₂) % 4 = 1 ∧ l₁ % 2 ≠ l₂ % 2 := by
  obtain ⟨t, rfl⟩ : ∃ t, j = t + 2 := ⟨j - 2, by omega⟩
  rw [pow_add] at e; norm_num at e; omega

/-- **Triangle parity.** Three components cannot each use one fixed length in both of their
cross pairs: pairwise-odd sums of three numbers are impossible. -/
theorem triangle_parity {l₁ l₂ l₃ : ℕ} (h12 : l₁ % 2 ≠ l₂ % 2) (h13 : l₁ % 2 ≠ l₃ % 2)
    (h23 : l₂ % 2 ≠ l₃ % 2) : False := by omega

/-- **At most one single-parity component of each parity.** If every two components `i ≠ i'`
have lengths of opposite parity (`Λ i`, `Λ i'`), at most one component has only even lengths
and at most one only odd lengths; so at least `r − 2` of the `r = d_h/2` components carry
`a_i`–`b_i` paths of both parities. -/
theorem single_parity_le_one {ι : Type*} (I : Finset ι) (Λ : ι → Set ℕ) (par : ℕ)
    (cross : ∀ i ∈ I, ∀ i' ∈ I, i ≠ i' → ∃ l ∈ Λ i, ∃ l' ∈ Λ i', l % 2 ≠ l' % 2) :
    #(I.filter (fun i => ∀ l ∈ Λ i, l % 2 = par)) ≤ 1 := by
  rw [card_le_one]
  intro i hi i' hi'
  by_contra ne
  rw [mem_filter] at hi hi'
  obtain ⟨l, hl, l', hl', d⟩ := cross i hi.1 i' hi'.1 ne
  exact d ((hi.2 l hl).trans (hi'.2 l' hl').symm)

end Hypostructure.Graph.CycleCounting
