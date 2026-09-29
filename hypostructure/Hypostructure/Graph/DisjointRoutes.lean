import Mathlib.Combinatorics.SimpleGraph.Walk.Counting
import Hypostructure.Graph.PathChords
import Hypostructure.Graph.PathUncrossing
import Hypostructure.Graph.StubDeficit
import Hypostructure.Graph.Contraction

/-!
# The route number: internally disjoint routes between two terminals (B04)

For two vertices `u, v` of a finite graph, a *route family* is a finite set of
`u`–`v` paths that pairwise meet only at `u` and `v`.  The **route number**
`routeNumber u v` is the largest size of a route family.  It is a finite
maximum (`Finset.sup` over the powerset of the finite set of `u`–`v` paths), so
it is a canonical number of the given graph.

* `exists_routeFamily_card_eq`: the maximum is attained by a route family.
* `routeNumber_comm`: the route number is symmetric.
* **Upper bounds.**  `routeNumber_le_cut`: for every region `S` with `u ∈ S`,
  `v ∉ S`, the route number is at most the number of boundary darts
  `Σ_{x∈S} |N(x) \ S|`; on a `FiniteObject` this is `e(S, G − S)`
  (`FiniteObject.routeNumber_le_boundaryIncidence`).  At `S = {u}` this is the
  degree bound, and with symmetry `routeNumber u v ≤ min (deg u) (deg v)`.
  `card_le_cut_of_edgeDisjoint`: any family of pairwise edge-disjoint walks
  from inside `S` to outside `S` has at most `e(S, G − S)` members.
* **Lower bounds.**  `one_le_routeNumber`: reachable terminals have a route.
  `two_le_routeNumber_of_return`: an edge `uv` with a return `u ⇝ v` avoiding
  the edge has two internally disjoint routes (the edge and the return).  On a
  `FiniteObject` the ledger's `lem:bridgeless` statement
  (`∀ contraction : EdgeContraction object, contraction.HasReturn`) gives
  `2 ≤ routeNumber u v` for every edge `uv`.
* **Edge routes.**  `edgeRouteNumber u v`: the maximum number of pairwise
  edge-disjoint `u`–`v` paths, canonical in the same way.  It is at most the
  cut `e(S, G − S)` and the degree, at least `routeNumber u v`, and
  `two_le_edgeRouteNumber`: in a graph where every edge has a return
  (`lem:bridgeless`) any two distinct connected vertices have two edge-disjoint
  paths (propagation of two edge-disjoint paths along a walk, each step
  merging the edge's return by `PathUncrossing.exists_first_hit`).
  `edgeDisjoint_pair_cycle`: two edge-disjoint `a ⇝ b` paths close a cycle
  through `a` of length `|p₁| + |q₁|`, `p₁, q₁` their prefixes to the first
  vertex `z ≠ a` of `p` on `q`.
* **Coupling with the cycle spectrum.**  `route_pair_cycle`: two distinct
  routes of lengths `Lᵢ, Lⱼ` close a cycle of length `Lᵢ + Lⱼ`
  (`PathChords.ear_cycle`); under `avoids`, `¬ LengthOK (Lᵢ + Lⱼ)` for every
  pair of a maximum route family.
* **Stubs.**  `e(S, G − S) + 2·e(G[S]) = Σ_{v∈S} d(v)`, so
  `routeNumber u v + 2·e(G[S]) ≤ Σ_{v∈S} d(v) = δ|S| + σ(S)` for every region
  separating the terminals.
-/

namespace Hypostructure.Graph.DisjointRoutes

open SimpleGraph
open scoped BigOperators

universe u

variable {V : Type u} (G : SimpleGraph V)

/-! ## Route families -/

/-- A **route family** between `u` and `v`: a finite set of `u`–`v` paths
that pairwise meet only at the two terminals. -/
def IsRouteFamily {u v : V} (F : Finset (G.Walk u v)) : Prop :=
  (∀ p ∈ F, p.IsPath) ∧
    ∀ p ∈ F, ∀ q ∈ F, p ≠ q → ∀ x ∈ p.support, x ∈ q.support → x = u ∨ x = v

variable {G}

theorem isRouteFamily_empty {u v : V} : IsRouteFamily G (∅ : Finset (G.Walk u v)) :=
  ⟨by simp, by simp⟩

section Finite

variable [Fintype V]

variable (G) in
/-- The finite set of all `u`–`v` paths of `G`. -/
noncomputable def pathFinset (u v : V) : Finset (G.Walk u v) := by
  classical
  exact (G.finsetWalkLengthLT (Fintype.card V) u v).filter fun p => p.IsPath

theorem mem_pathFinset {u v : V} {p : G.Walk u v} :
    p ∈ pathFinset G u v ↔ p.IsPath := by
  classical
  unfold pathFinset
  rw [Finset.mem_filter, mem_finsetWalkLengthLT_iff]
  exact ⟨fun h => h.2, fun h => ⟨h.length_lt, h⟩⟩

variable (G) in
/-- **The route number** `routeNumber u v`: the maximum size of a family of
internally disjoint `u`–`v` paths of `G` (the Menger number, register
coordinate B04).  A finite maximum over the powerset of the finite set of
`u`–`v` paths. -/
noncomputable def routeNumber (u v : V) : Nat := by
  classical
  exact ((pathFinset G u v).powerset.filter fun F => IsRouteFamily G F).sup Finset.card

/-- Every route family has at most `routeNumber u v` routes. -/
theorem card_le_routeNumber {u v : V} {F : Finset (G.Walk u v)}
    (hF : IsRouteFamily G F) : F.card ≤ routeNumber G u v := by
  classical
  unfold routeNumber
  refine Finset.le_sup (f := Finset.card) ?_
  rw [Finset.mem_filter, Finset.mem_powerset]
  exact ⟨fun p hp => mem_pathFinset.2 (hF.1 p hp), hF⟩

/-- The route number is attained by a route family of `G`. -/
theorem exists_routeFamily_card_eq (u v : V) :
    ∃ F : Finset (G.Walk u v), IsRouteFamily G F ∧ F.card = routeNumber G u v := by
  classical
  have mem : (∅ : Finset (G.Walk u v)) ∈
      (pathFinset G u v).powerset.filter fun F => IsRouteFamily G F := by
    rw [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨Finset.empty_subset _, isRouteFamily_empty⟩
  obtain ⟨F, hF, eq⟩ := Finset.exists_mem_eq_sup _ ⟨_, mem⟩ Finset.card
  refine ⟨F, (Finset.mem_filter.1 hF).2, ?_⟩
  unfold routeNumber
  convert eq.symm

end Finite

/-! ## Walk facts used by the bounds -/

/-- A path whose second vertex is its end is the single edge. -/
theorem eq_of_snd_eq_end {u v : V} (p q : G.Walk u v) (hp : p.IsPath) (hq : q.IsPath)
    (hne : u ≠ v) (hps : p.snd = v) (hqs : q.snd = v) : p = q := by
  cases p with
  | nil => exact absurd rfl hne
  | cons h p' =>
    cases q with
    | nil => exact absurd rfl hne
    | cons h' q' =>
      rw [Walk.snd_cons] at hps hqs
      subst hps
      subst hqs
      have e1 := (Walk.cons_isPath_iff _ _).1 hp |>.1
      have e2 := (Walk.cons_isPath_iff _ _).1 hq |>.1
      rw [Walk.isPath_iff_nil, ← Walk.eq_nil_iff_nil] at e1 e2
      subst e1
      subst e2
      rfl

/-- A path of length one has its end as second vertex. -/
theorem snd_eq_end_of_length_one {u v : V} (p : G.Walk u v) (h1 : p.length = 1) :
    p.snd = v := by
  cases p with
  | nil => simp at h1
  | cons h p' =>
    rw [Walk.snd_cons]
    simp only [Walk.length_cons, Nat.add_eq_right] at h1
    exact Walk.eq_of_length_eq_zero h1

/-- A `u`–`v` path through the edge `uv` is that single edge: its second vertex
is `v`. -/
theorem snd_eq_end_of_mem_edges {u v : V} (p : G.Walk u v) (hp : p.IsPath)
    (he : s(u, v) ∈ p.edges) : p.snd = v := by
  cases p with
  | nil => simp at he
  | @cons _ w _ h p' =>
    rw [Walk.snd_cons]
    have hc := (Walk.cons_isPath_iff _ _).1 hp
    rw [Walk.edges_cons, List.mem_cons] at he
    rcases he with e | e
    · rcases Sym2.eq_iff.1 e with ⟨_, e2⟩ | ⟨e1, _⟩
      · exact e2.symm
      · exact absurd e1 h.ne
    · exact absurd (p'.fst_mem_support_of_mem_edges e) hc.2

/-- Distinct routes of a route family between distinct terminals do not share
an edge. -/
theorem edges_disjoint_of_routeFamily {u v : V} {F : Finset (G.Walk u v)}
    (hF : IsRouteFamily G F) (hne : u ≠ v) {p q : G.Walk u v} (hp : p ∈ F) (hq : q ∈ F)
    (pq : p ≠ q) {x y : V} (hxp : s(x, y) ∈ p.edges) (hxq : s(x, y) ∈ q.edges)
    (hxu : x = u) (hyv : y = v) : False := by
  subst hxu hyv
  exact pq (eq_of_snd_eq_end p q (hF.1 p hp) (hF.1 q hq) hne
    (snd_eq_end_of_mem_edges p (hF.1 p hp) hxp)
    (snd_eq_end_of_mem_edges q (hF.1 q hq) hxq))

/-- **A walk leaving a region crosses its boundary**: some edge of the walk
goes from inside `S` to outside `S`. -/
theorem exists_crossing (S : Set V) :
    ∀ {a b : V} (p : G.Walk a b), a ∈ S → b ∉ S →
      ∃ x y, x ∈ S ∧ y ∉ S ∧ G.Adj x y ∧ s(x, y) ∈ p.edges
  | _, _, .nil, ha, hb => absurd ha hb
  | _, _, .cons (v := w) h p, ha, hb => by
      by_cases hw : w ∈ S
      · obtain ⟨x, y, hx, hy, adj, mem⟩ := exists_crossing S p hw hb
        exact ⟨x, y, hx, hy, adj, by simp [Walk.edges_cons, mem]⟩
      · exact ⟨_, _, ha, hw, h, by simp [Walk.edges_cons]⟩

/-! ## Upper bounds -/

section Upper

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- **The cut bound.**  A route family between `u ∈ S` and `v ∉ S` has at most
as many routes as `S` has boundary darts `Σ_{x∈S} |N(x) \ S|`: each route
crosses the boundary, and two routes never cross through the same edge. -/
theorem card_le_cut {u v : V} {F : Finset (G.Walk u v)} (hF : IsRouteFamily G F)
    (S : Finset V) (hu : u ∈ S) (hv : v ∉ S) :
    F.card ≤ ∑ x ∈ S, (G.neighborFinset x \ S).card := by
  have hne : u ≠ v := fun h => hv (h ▸ hu)
  have cross : ∀ p : G.Walk u v, ∃ xy : (Σ _ : V, V),
      xy.1 ∈ S ∧ xy.2 ∉ S ∧ G.Adj xy.1 xy.2 ∧ s(xy.1, xy.2) ∈ p.edges := by
    intro p
    obtain ⟨x, y, hx, hy, adj, mem⟩ := exists_crossing (S : Set V) p hu hv
    exact ⟨⟨x, y⟩, hx, hy, adj, mem⟩
  choose f hf using cross
  rw [← Finset.card_sigma]
  refine Finset.card_le_card_of_injOn f ?_ ?_
  · intro p _
    obtain ⟨hx, hy, adj, _⟩ := hf p
    rw [Finset.coe_sigma]
    refine Set.mem_sigma_iff.2 ⟨hx, ?_⟩
    simp [adj, hy]
  · intro p hp q hq eq
    by_contra pq
    obtain ⟨hx, hy, _, mp⟩ := hf p
    obtain ⟨_, _, _, mq⟩ := hf q
    have eq' : f q = f p := eq.symm
    rw [eq'] at mq
    set x := (f p).1
    set y := (f p).2
    have xp := p.fst_mem_support_of_mem_edges mp
    have xq := q.fst_mem_support_of_mem_edges mq
    have yp := p.snd_mem_support_of_mem_edges mp
    have yq := q.snd_mem_support_of_mem_edges mq
    have hxuv := hF.2 p hp q hq pq x xp xq
    have hyuv := hF.2 p hp q hq pq y yp yq
    have hxu : x = u := by
      rcases hxuv with h | h
      · exact h
      · exact absurd (h ▸ hx) hv
    have hyv : y = v := by
      rcases hyuv with h | h
      · exact absurd (h ▸ hu) hy
      · exact h
    exact edges_disjoint_of_routeFamily hF hne hp hq pq mp mq hxu hyv

/-- **Edge-disjoint exits of a region.**  Any family of pairwise edge-disjoint
walks, each starting inside `S` and ending outside `S` (with arbitrary ends),
has at most `Σ_{x∈S} |N(x) \ S|` members. -/
theorem card_le_cut_of_edgeDisjoint {ι : Type*} [Fintype ι] (S : Finset V)
    (s t : ι → V) (P : ∀ i, G.Walk (s i) (t i)) (hs : ∀ i, s i ∈ S) (ht : ∀ i, t i ∉ S)
    (disj : ∀ i j, i ≠ j → ∀ e ∈ (P i).edges, e ∉ (P j).edges) :
    Fintype.card ι ≤ ∑ x ∈ S, (G.neighborFinset x \ S).card := by
  have cross : ∀ i, ∃ xy : (Σ _ : V, V),
      xy.1 ∈ S ∧ xy.2 ∉ S ∧ G.Adj xy.1 xy.2 ∧ s(xy.1, xy.2) ∈ (P i).edges := by
    intro i
    obtain ⟨x, y, hx, hy, adj, mem⟩ := exists_crossing (S : Set V) (P i) (hs i) (ht i)
    exact ⟨⟨x, y⟩, hx, hy, adj, mem⟩
  choose f hf using cross
  rw [← Finset.card_sigma, ← Finset.card_univ]
  refine Finset.card_le_card_of_injOn f ?_ ?_
  · intro i _
    obtain ⟨hx, hy, adj, _⟩ := hf i
    rw [Finset.coe_sigma]
    exact Set.mem_sigma_iff.2 ⟨hx, by simp [adj, hy]⟩
  · intro i _ j _ eq
    by_contra ij
    have mi := (hf i).2.2.2
    have mj := (hf j).2.2.2
    rw [← eq] at mj
    exact disj i j ij _ mi mj

/-- **The route number is at most the boundary of any separating region.** -/
theorem routeNumber_le_cut {u v : V} (S : Finset V) (hu : u ∈ S) (hv : v ∉ S) :
    routeNumber G u v ≤ ∑ x ∈ S, (G.neighborFinset x \ S).card := by
  obtain ⟨F, hF, eq⟩ := exists_routeFamily_card_eq (G := G) u v
  exact eq ▸ card_le_cut hF S hu hv

/-- **The degree bound at the first terminal.** -/
theorem routeNumber_le_degree_left {u v : V} (hne : u ≠ v) :
    routeNumber G u v ≤ G.degree u := by
  have h := routeNumber_le_cut (G := G) (u := u) (v := v) {u} (Finset.mem_singleton_self u)
    (by simpa [eq_comm] using hne)
  rw [Finset.sum_singleton] at h
  have : G.neighborFinset u \ {u} = G.neighborFinset u := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_singleton, SimpleGraph.mem_neighborFinset]
    exact ⟨fun h => h.1, fun h => ⟨h, h.ne'⟩⟩
  rw [this, SimpleGraph.card_neighborFinset_eq_degree] at h
  exact h

end Upper

section Symm

variable [Fintype V]

omit [Fintype V] in
/-- Reversing every route of a route family gives a route family. -/
theorem isRouteFamily_map_reverse {u v : V} {F : Finset (G.Walk u v)}
    (hF : IsRouteFamily G F) :
    IsRouteFamily G (F.map ⟨Walk.reverse, Walk.reverse_injective⟩) := by
  refine ⟨?_, ?_⟩
  · intro p hp
    obtain ⟨p', hp', rfl⟩ := Finset.mem_map.1 hp
    exact (hF.1 p' hp').reverse
  · intro p hp q hq pq x xp xq
    obtain ⟨p', hp', rfl⟩ := Finset.mem_map.1 hp
    obtain ⟨q', hq', rfl⟩ := Finset.mem_map.1 hq
    have pq' : p' ≠ q' := fun h => pq (by rw [h])
    simp only [Function.Embedding.coeFn_mk, Walk.support_reverse, List.mem_reverse] at xp xq
    exact (hF.2 p' hp' q' hq' pq' x xp xq).symm

/-- **The route number is symmetric.** -/
theorem routeNumber_comm (u v : V) : routeNumber G u v = routeNumber G v u := by
  have key : ∀ a b : V, routeNumber G a b ≤ routeNumber G b a := by
    intro a b
    obtain ⟨F, hF, eq⟩ := exists_routeFamily_card_eq (G := G) a b
    rw [← eq, ← Finset.card_map ⟨Walk.reverse, Walk.reverse_injective⟩]
    exact card_le_routeNumber (isRouteFamily_map_reverse hF)
  exact le_antisymm (key u v) (key v u)

end Symm

section UpperBoth

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- **The degree bound**: `routeNumber u v ≤ min (deg u) (deg v)`. -/
theorem routeNumber_le_min_degree {u v : V} (hne : u ≠ v) :
    routeNumber G u v ≤ min (G.degree u) (G.degree v) := by
  refine le_min (routeNumber_le_degree_left hne) ?_
  rw [routeNumber_comm]
  exact routeNumber_le_degree_left (Ne.symm hne)

end UpperBoth

/-! ## Lower bounds -/

section Lower

variable [Fintype V]

omit [Fintype V] in
/-- A single path is a route family. -/
theorem isRouteFamily_singleton {u v : V} {p : G.Walk u v} (hp : p.IsPath) :
    IsRouteFamily G ({p} : Finset (G.Walk u v)) := by
  refine ⟨by simpa using hp, ?_⟩
  intro a ha b hb ab
  rw [Finset.mem_singleton] at ha hb
  exact absurd (ha.trans hb.symm) ab

/-- **Reachable terminals have a route.** -/
theorem one_le_routeNumber {u v : V} (reach : G.Reachable u v) : 1 ≤ routeNumber G u v := by
  classical
  obtain ⟨p⟩ := reach
  have := card_le_routeNumber (isRouteFamily_singleton (G := G) p.bypass_isPath)
  simpa using this

/-- **An edge with a return has two internally disjoint routes**: the edge
itself and the return `u ⇝ v` of `G − uv`. -/
theorem two_le_routeNumber_of_return {u v : V} (adj : G.Adj u v)
    (ret : (G.deleteEdges {s(u, v)}).Path u v) : 2 ≤ routeNumber G u v := by
  classical
  let e : G.Walk u v := Walk.cons adj Walk.nil
  let r : G.Walk u v := ret.1.mapLe (G.deleteEdges_le _)
  have he : e.IsPath := by simp [e, adj.ne]
  have hr : r.IsPath := (Walk.mapLe_isPath _).2 ret.2
  have ne : e ≠ r := by
    intro h
    have mem : s(u, v) ∈ r.edges := by rw [← h]; simp [e]
    rw [Walk.edges_mapLe_eq_edges] at mem
    have := ret.1.edges_subset_edgeSet mem
    rw [SimpleGraph.edgeSet_deleteEdges] at this
    exact this.2 rfl
  have fam : IsRouteFamily G ({e, r} : Finset (G.Walk u v)) := by
    refine ⟨?_, ?_⟩
    · intro p hp
      rcases Finset.mem_insert.1 hp with rfl | hp
      · exact he
      · rw [Finset.mem_singleton] at hp; subst hp; exact hr
    · intro p hp q hq pq x xp xq
      rcases Finset.mem_insert.1 hp with rfl | hp
      · simpa [e] using xp
      · rw [Finset.mem_singleton] at hp
        subst hp
        rcases Finset.mem_insert.1 hq with rfl | hq
        · simpa [e] using xq
        · rw [Finset.mem_singleton] at hq
          exact absurd hq.symm pq
  have := card_le_routeNumber fam
  rwa [Finset.card_pair ne] at this

end Lower

/-! ## Coupling with the cycle spectrum -/

/-- **Two routes close a cycle**: two distinct routes of a route family between
distinct terminals, of lengths `Lᵢ, Lⱼ`, close a cycle of length `Lᵢ + Lⱼ`. -/
theorem route_pair_cycle {u v : V} {F : Finset (G.Walk u v)} (hF : IsRouteFamily G F)
    (hne : u ≠ v) {p q : G.Walk u v} (hp : p ∈ F) (hq : q ∈ F) (pq : p ≠ q) :
    ∃ c : G.Walk u u, c.IsCycle ∧ c.length = p.length + q.length := by
  have pp := hF.1 p hp
  have qp := hF.1 q hq
  have len : ∀ w : G.Walk u v, 1 ≤ w.length := by
    intro w
    by_contra h
    exact hne (Walk.eq_of_length_eq_zero (p := w) (by omega))
  obtain ⟨c, hc, hl⟩ := PathChords.ear_cycle p q.reverse pp qp.reverse
    (fun y yp yq => by
      rw [Walk.support_reverse, List.mem_reverse] at yq
      exact hF.2 p hp q hq pq y yp yq)
    (len p) (by rw [Walk.length_reverse]; exact len q)
    (by
      rintro ⟨h1, h2⟩
      rw [Walk.length_reverse] at h2
      exact pq (eq_of_snd_eq_end p q pp qp hne (snd_eq_end_of_length_one p h1)
        (snd_eq_end_of_length_one q h2)))
  exact ⟨c, hc, by rw [hl, Walk.length_reverse]⟩

/-- **Under `avoids`, no two routes have an accepted length sum.** -/
theorem route_pair_not_lengthOK {LengthOK : Nat → Prop}
    (avoids : ¬ ∃ (c : V) (cy : G.Walk c c), cy.IsCycle ∧ LengthOK cy.length)
    {u v : V} {F : Finset (G.Walk u v)} (hF : IsRouteFamily G F)
    (hne : u ≠ v) {p q : G.Walk u v} (hp : p ∈ F) (hq : q ∈ F) (pq : p ≠ q) :
    ¬ LengthOK (p.length + q.length) := by
  intro ok
  obtain ⟨c, hc, hl⟩ := route_pair_cycle hF hne hp hq pq
  exact avoids ⟨u, c, hc, hl ▸ ok⟩

/-- **A maximum route family with the cycle-spectrum coupling**: there are
`routeNumber u v` internally disjoint routes, and every two of them have a
length sum that is not accepted. -/
theorem exists_max_routeFamily_avoiding [Fintype V] {LengthOK : Nat → Prop}
    (avoids : ¬ ∃ (c : V) (cy : G.Walk c c), cy.IsCycle ∧ LengthOK cy.length)
    {u v : V} (hne : u ≠ v) :
    ∃ F : Finset (G.Walk u v), IsRouteFamily G F ∧ F.card = routeNumber G u v ∧
      ∀ p ∈ F, ∀ q ∈ F, p ≠ q → ¬ LengthOK (p.length + q.length) := by
  obtain ⟨F, hF, eq⟩ := exists_routeFamily_card_eq (G := G) u v
  exact ⟨F, hF, eq, fun p hp q hq pq =>
    route_pair_not_lengthOK avoids hF hne hp hq pq⟩

/-- **An edge and its return**: under `avoids`, a return `u ⇝ v` of `G − uv`
has `¬ LengthOK (1 + |return|)`. -/
theorem return_not_lengthOK {LengthOK : Nat → Prop}
    (avoids : ¬ ∃ (c : V) (cy : G.Walk c c), cy.IsCycle ∧ LengthOK cy.length)
    {u v : V} (adj : G.Adj u v) (ret : (G.deleteEdges {s(u, v)}).Path u v) :
    ¬ LengthOK (1 + ret.1.length) := by
  classical
  let e : G.Walk u v := Walk.cons adj Walk.nil
  let r : G.Walk u v := ret.1.mapLe (G.deleteEdges_le _)
  have he : e.IsPath := by simp [e, adj.ne]
  have hr : r.IsPath := (Walk.mapLe_isPath _).2 ret.2
  have ne : e ≠ r := by
    intro h
    have mem : s(u, v) ∈ r.edges := by rw [← h]; simp [e]
    rw [Walk.edges_mapLe_eq_edges] at mem
    have := ret.1.edges_subset_edgeSet mem
    rw [SimpleGraph.edgeSet_deleteEdges] at this
    exact this.2 rfl
  have fam : IsRouteFamily G ({e, r} : Finset (G.Walk u v)) := by
    refine ⟨?_, ?_⟩
    · intro p hp
      rcases Finset.mem_insert.1 hp with rfl | hp
      · exact he
      · rw [Finset.mem_singleton] at hp; subst hp; exact hr
    · intro p hp q hq pq x xp xq
      rcases Finset.mem_insert.1 hp with rfl | hp
      · simpa [e] using xp
      · rw [Finset.mem_singleton] at hp
        subst hp
        rcases Finset.mem_insert.1 hq with rfl | hq
        · simpa [e] using xq
        · rw [Finset.mem_singleton] at hq
          exact absurd hq.symm pq
  have h := route_pair_not_lengthOK avoids fam adj.ne (Finset.mem_insert_self e {r})
    (Finset.mem_insert_of_mem (Finset.mem_singleton_self r)) ne
  have hl : r.length = ret.1.length := Walk.length_map _ _
  have he1 : e.length = 1 := rfl
  rw [he1, hl] at h
  exact h

/-! ## Edge-disjoint routes -/

variable (G) in
/-- An **edge-route family** between `u` and `v`: a finite set of `u`–`v`
paths, two distinct members of which share no edge. -/
def IsEdgeRouteFamily {u v : V} (F : Finset (G.Walk u v)) : Prop :=
  (∀ p ∈ F, p.IsPath) ∧ ∀ p ∈ F, ∀ q ∈ F, p ≠ q → ∀ e ∈ p.edges, e ∉ q.edges

theorem isEdgeRouteFamily_empty {u v : V} :
    IsEdgeRouteFamily G (∅ : Finset (G.Walk u v)) :=
  ⟨by simp, by simp⟩

section EdgeFinite

variable [Fintype V]

variable (G) in
/-- **The edge-route number** `edgeRouteNumber u v`: the maximum size of a
family of pairwise edge-disjoint `u`–`v` paths of `G`.  A finite maximum over
the powerset of the finite set of `u`–`v` paths. -/
noncomputable def edgeRouteNumber (u v : V) : Nat := by
  classical
  exact ((pathFinset G u v).powerset.filter fun F => IsEdgeRouteFamily G F).sup Finset.card

/-- Every edge-route family has at most `edgeRouteNumber u v` routes. -/
theorem card_le_edgeRouteNumber {u v : V} {F : Finset (G.Walk u v)}
    (hF : IsEdgeRouteFamily G F) : F.card ≤ edgeRouteNumber G u v := by
  classical
  unfold edgeRouteNumber
  refine Finset.le_sup (f := Finset.card) ?_
  rw [Finset.mem_filter, Finset.mem_powerset]
  exact ⟨fun p hp => mem_pathFinset.2 (hF.1 p hp), hF⟩

/-- The edge-route number is attained by an edge-route family of `G`. -/
theorem exists_edgeRouteFamily_card_eq (u v : V) :
    ∃ F : Finset (G.Walk u v), IsEdgeRouteFamily G F ∧ F.card = edgeRouteNumber G u v := by
  classical
  have mem : (∅ : Finset (G.Walk u v)) ∈
      (pathFinset G u v).powerset.filter fun F => IsEdgeRouteFamily G F := by
    rw [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨Finset.empty_subset _, isEdgeRouteFamily_empty⟩
  obtain ⟨F, hF, eq⟩ := Finset.exists_mem_eq_sup _ ⟨_, mem⟩ Finset.card
  refine ⟨F, (Finset.mem_filter.1 hF).2, ?_⟩
  unfold edgeRouteNumber
  convert eq.symm

end EdgeFinite

/-- A route family between distinct terminals is an edge-route family. -/
theorem isEdgeRouteFamily_of_isRouteFamily {u v : V} {F : Finset (G.Walk u v)}
    (hF : IsRouteFamily G F) (hne : u ≠ v) : IsEdgeRouteFamily G F := by
  refine ⟨hF.1, ?_⟩
  intro p hp q hq pq e ep eq
  induction e using Sym2.ind with
  | _ x y =>
    have adj : G.Adj x y := p.adj_of_mem_edges ep
    have hx := hF.2 p hp q hq pq x (p.fst_mem_support_of_mem_edges ep)
      (q.fst_mem_support_of_mem_edges eq)
    have hy := hF.2 p hp q hq pq y (p.snd_mem_support_of_mem_edges ep)
      (q.snd_mem_support_of_mem_edges eq)
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact adj.ne rfl
    · exact edges_disjoint_of_routeFamily hF hne hp hq pq ep eq rfl rfl
    · rw [Sym2.eq_swap] at ep eq
      exact edges_disjoint_of_routeFamily hF hne hp hq pq ep eq rfl rfl
    · exact adj.ne rfl

/-- The route number is at most the edge-route number. -/
theorem routeNumber_le_edgeRouteNumber [Fintype V] {u v : V} (hne : u ≠ v) :
    routeNumber G u v ≤ edgeRouteNumber G u v := by
  obtain ⟨F, hF, eq⟩ := exists_routeFamily_card_eq (G := G) u v
  exact eq ▸ card_le_edgeRouteNumber (isEdgeRouteFamily_of_isRouteFamily hF hne)

section EdgeUpper

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- **The cut bound for edge routes**: for every region `S` with `u ∈ S`,
`v ∉ S`, `edgeRouteNumber u v ≤ Σ_{x∈S} |N(x) \ S|`. -/
theorem edgeRouteNumber_le_cut {u v : V} (S : Finset V) (hu : u ∈ S) (hv : v ∉ S) :
    edgeRouteNumber G u v ≤ ∑ x ∈ S, (G.neighborFinset x \ S).card := by
  obtain ⟨F, hF, eq⟩ := exists_edgeRouteFamily_card_eq (G := G) u v
  rw [← eq, ← Fintype.card_coe]
  exact card_le_cut_of_edgeDisjoint S (fun _ : F => u) (fun _ => v) (fun i => i.1)
    (fun _ => hu) (fun _ => hv)
    (fun i j ij => hF.2 i.1 i.2 j.1 j.2 (fun h => ij (Subtype.ext h)))

/-- **The degree bound for edge routes.** -/
theorem edgeRouteNumber_le_degree_left {u v : V} (hne : u ≠ v) :
    edgeRouteNumber G u v ≤ G.degree u := by
  have h := edgeRouteNumber_le_cut (G := G) (u := u) (v := v) {u}
    (Finset.mem_singleton_self u) (by simpa [eq_comm] using hne)
  rw [Finset.sum_singleton] at h
  have : G.neighborFinset u \ {u} = G.neighborFinset u := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_singleton, SimpleGraph.mem_neighborFinset]
    exact ⟨fun h => h.1, fun h => ⟨h, h.ne'⟩⟩
  rw [this, SimpleGraph.card_neighborFinset_eq_degree] at h
  exact h

end EdgeUpper

/-! ### Two edge-disjoint routes in a bridgeless connected graph -/

variable (G) in
/-- `x` is reached from `a` by two edge-disjoint paths. -/
def TwoEdgeReach (a x : V) : Prop :=
  ∃ p q : G.Walk a x, p.IsPath ∧ q.IsPath ∧ ∀ e ∈ p.edges, e ∉ q.edges

theorem twoEdgeReach_of_walks [DecidableEq V] {a y : V} (A B : G.Walk a y)
    (disj : ∀ e ∈ A.edges, e ∉ B.edges) : TwoEdgeReach G a y :=
  ⟨A.bypass, B.bypass, A.bypass_isPath, B.bypass_isPath,
    fun e hA hB => disj e (A.edges_bypass_subset_edges hA) (B.edges_bypass_subset_edges hB)⟩

/-- A proper prefix `p₁ : a ⇝ y` of a path `a ⇝ x` does not visit `x`. -/
theorem end_notMem_prefix {a x y : V} {p : G.Walk a x} (hp : p.IsPath) (p₁ : G.Walk a y)
    (p₂ : G.Walk y x) (split : p = p₁.append p₂) (hyx : y ≠ x) : x ∉ p₁.support := by
  intro xs
  subst split
  rw [Walk.isPath_def, Walk.support_append] at hp
  exact (List.nodup_append.1 hp).2.2 x xs x (p₂.end_mem_tail_support_of_ne hyx) rfl

/-- The core step: from two edge-disjoint `a ⇝ x` walks `p, q`, a prefix
`p₁ : a ⇝ z` of `p` and a connector `r : z ⇝ y` sharing no edge with `q`,
with `xy` on neither `p₁` nor `r`, the walks `q + xy` and `p₁ + r` are
edge-disjoint `a ⇝ y` walks. -/
theorem twoEdgeReach_core [DecidableEq V] {a x y z : V} (adj : G.Adj x y)
    (p q : G.Walk a x) (disj : ∀ e ∈ p.edges, e ∉ q.edges) (p₁ : G.Walk a z)
    (p₂ : G.Walk z x) (split : p = p₁.append p₂) (r : G.Walk z y)
    (rq : ∀ e ∈ r.edges, e ∉ q.edges)
    (ep : s(x, y) ∉ p₁.edges) (er : s(x, y) ∉ r.edges) :
    TwoEdgeReach G a y := by
  refine twoEdgeReach_of_walks (q.append (Walk.cons adj Walk.nil)) (p₁.append r) ?_
  intro e hA hB
  rw [Walk.edges_append, List.mem_append] at hA hB
  have p₁p : ∀ f ∈ p₁.edges, f ∈ p.edges := fun f hf => by
    rw [split, Walk.edges_append]; exact List.mem_append_left _ hf
  rcases hA with hA | hA
  · rcases hB with hB | hB
    · exact disj e (p₁p e hB) hA
    · exact rq e hB hA
  · simp only [Walk.edges_cons, Walk.edges_nil, List.mem_singleton] at hA
    subst hA
    rcases hB with hB | hB
    · exact ep hB
    · exact er hB

/-- The core step with the roles of `p` and `q` exchanged. -/
theorem twoEdgeReach_core' [DecidableEq V] {a x y z : V} (adj : G.Adj x y)
    (p q : G.Walk a x) (disj : ∀ e ∈ p.edges, e ∉ q.edges) (q₁ : G.Walk a z)
    (q₂ : G.Walk z x) (split : q = q₁.append q₂) (r : G.Walk z y)
    (rp : ∀ e ∈ r.edges, e ∉ p.edges) (eq : s(x, y) ∉ q₁.edges) (er : s(x, y) ∉ r.edges) :
    TwoEdgeReach G a y :=
  twoEdgeReach_core adj q p (fun e hq hp => disj e hp hq) q₁ q₂ split r rp eq er

/-- **The propagation step**: two edge-disjoint paths to `x`, an edge `xy`
and a return of `xy` give two edge-disjoint paths to `y`. -/
theorem twoEdgeReach_step [DecidableEq V] {a x y : V} (hx : TwoEdgeReach G a x)
    (adj : G.Adj x y) (ret : (G.deleteEdges {s(x, y)}).Path x y) : TwoEdgeReach G a y := by
  obtain ⟨p, q, hp, hq, disj⟩ := hx
  have disj' : ∀ e ∈ q.edges, e ∉ p.edges := fun e hq hp => disj e hp hq
  have hyx : y ≠ x := adj.ne.symm
  by_cases yp : y ∈ p.support
  · obtain ⟨z, p₁, p₂, split, hz, _⟩ :=
      PathUncrossing.exists_first_hit ({y} : Set V) p ⟨y, yp, rfl⟩
    rw [Set.mem_singleton_iff] at hz
    subst hz
    have ep : s(x, z) ∉ p₁.edges := fun h =>
      end_notMem_prefix hp p₁ p₂ split hyx (p₁.fst_mem_support_of_mem_edges h)
    by_cases eq : s(x, z) ∈ q.edges
    · -- the edge lies on `q`: cut `q` at `z` instead
      have zq : z ∈ q.support := q.snd_mem_support_of_mem_edges eq
      obtain ⟨z', q₁, q₂, splitq, hz', _⟩ :=
        PathUncrossing.exists_first_hit ({z} : Set V) q ⟨z, zq, rfl⟩
      rw [Set.mem_singleton_iff] at hz'
      subst hz'
      have eq₁ : s(x, z') ∉ q₁.edges := fun h =>
        end_notMem_prefix hq q₁ q₂ splitq hyx (q₁.fst_mem_support_of_mem_edges h)
      exact twoEdgeReach_core' adj p q disj q₁ q₂ splitq Walk.nil (by simp) eq₁ (by simp)
    · exact twoEdgeReach_core adj p q disj p₁ p₂ split Walk.nil (by simp) ep (by simp)
  by_cases yq : y ∈ q.support
  · obtain ⟨z, q₁, q₂, split, hz, _⟩ :=
      PathUncrossing.exists_first_hit ({y} : Set V) q ⟨y, yq, rfl⟩
    rw [Set.mem_singleton_iff] at hz
    subst hz
    have eq₁ : s(x, z) ∉ q₁.edges := fun h =>
      end_notMem_prefix hq q₁ q₂ split hyx (q₁.fst_mem_support_of_mem_edges h)
    exact twoEdgeReach_core' adj p q disj q₁ q₂ split Walk.nil (by simp) eq₁ (by simp)
  -- `y` is off both paths: follow the return from `y` to its first vertex on them
  have ep : s(x, y) ∉ p.edges := fun h => yp (p.snd_mem_support_of_mem_edges h)
  have eq : s(x, y) ∉ q.edges := fun h => yq (q.snd_mem_support_of_mem_edges h)
  let r : G.Walk y x := (ret.1.mapLe (G.deleteEdges_le _)).reverse
  have er : ∀ f ∈ r.edges, f ≠ s(x, y) := by
    intro f hf h
    subst h
    simp only [r, Walk.edges_reverse, List.mem_reverse, Walk.edges_mapLe_eq_edges] at hf
    have := ret.1.edges_subset_edgeSet hf
    rw [SimpleGraph.edgeSet_deleteEdges] at this
    exact this.2 rfl
  let S : Set V := {v | v ∈ p.support ∨ v ∈ q.support}
  obtain ⟨z, r₁, r₂, splitr, hz, first⟩ :=
    PathUncrossing.exists_first_hit S r ⟨x, r.end_mem_support, Or.inl p.end_mem_support⟩
  have r₁r : ∀ f ∈ r₁.edges, f ∈ r.edges := fun f hf => by
    rw [splitr, Walk.edges_append]; exact List.mem_append_left _ hf
  have off : ∀ f ∈ r₁.edges, (∀ c ∈ f, c ∈ S) → False := by
    intro f hf hS
    induction f using Sym2.ind with
    | _ c d =>
      have cz := first c (r₁.fst_mem_support_of_mem_edges hf) (hS c (Sym2.mem_mk_left c d))
      have dz := first d (r₁.snd_mem_support_of_mem_edges hf) (hS d (Sym2.mem_mk_right c d))
      exact (r₁.adj_of_mem_edges hf).ne (cz.trans dz.symm)
  have rp : ∀ e ∈ r₁.reverse.edges, e ∉ p.edges := by
    intro e he hp'
    rw [Walk.edges_reverse, List.mem_reverse] at he
    exact off e he fun c hc => Or.inl (p.mem_support_of_mem_edges hp' hc)
  have rq : ∀ e ∈ r₁.reverse.edges, e ∉ q.edges := by
    intro e he hq'
    rw [Walk.edges_reverse, List.mem_reverse] at he
    exact off e he fun c hc => Or.inr (q.mem_support_of_mem_edges hq' hc)
  have err : s(x, y) ∉ r₁.reverse.edges := by
    intro h
    rw [Walk.edges_reverse, List.mem_reverse] at h
    exact er _ (r₁r _ h) rfl
  rcases hz with zp | zq
  · obtain ⟨z', p₁, p₂, split, hz', _⟩ :=
      PathUncrossing.exists_first_hit ({z} : Set V) p ⟨z, zp, rfl⟩
    rw [Set.mem_singleton_iff] at hz'
    subst hz'
    have ep₁ : s(x, y) ∉ p₁.edges := fun h => ep (by
      rw [split, Walk.edges_append]; exact List.mem_append_left _ h)
    exact twoEdgeReach_core adj p q disj p₁ p₂ split r₁.reverse rq ep₁ err
  · obtain ⟨z', q₁, q₂, split, hz', _⟩ :=
      PathUncrossing.exists_first_hit ({z} : Set V) q ⟨z, zq, rfl⟩
    rw [Set.mem_singleton_iff] at hz'
    subst hz'
    have eq₁ : s(x, y) ∉ q₁.edges := fun h => eq (by
      rw [split, Walk.edges_append]; exact List.mem_append_left _ h)
    exact twoEdgeReach_core' adj p q disj q₁ q₂ split r₁.reverse rp eq₁ err

/-- **Bridgeless graphs are 2-edge-connected along walks**: if every edge has
a return, two edge-disjoint paths from `a` extend along any walk. -/
theorem twoEdgeReach_of_walk [DecidableEq V]
    (returns : ∀ x y, G.Adj x y → Nonempty ((G.deleteEdges {s(x, y)}).Path x y))
    {a : V} : ∀ {x b : V} (_ : G.Walk x b), TwoEdgeReach G a x → TwoEdgeReach G a b
  | _, _, .nil, h => h
  | _, _, .cons adj w, h => by
      obtain ⟨ret⟩ := returns _ _ adj
      exact twoEdgeReach_of_walk returns w (twoEdgeReach_step h adj ret)

/-- **Two edge-disjoint routes in a bridgeless connected graph**: between any
two distinct vertices there are two distinct edge-disjoint paths. -/
theorem exists_two_edgeDisjoint_paths
    (returns : ∀ x y, G.Adj x y → Nonempty ((G.deleteEdges {s(x, y)}).Path x y))
    {a b : V} (reach : G.Reachable a b) (hne : a ≠ b) :
    ∃ p q : G.Walk a b, p.IsPath ∧ q.IsPath ∧ p ≠ q ∧ ∀ e ∈ p.edges, e ∉ q.edges := by
  classical
  obtain ⟨w⟩ := reach
  obtain ⟨p, q, hp, hq, disj⟩ := twoEdgeReach_of_walk returns w
    ⟨Walk.nil, Walk.nil, by simp, by simp, by simp⟩
  refine ⟨p, q, hp, hq, ?_, disj⟩
  rintro rfl
  cases p with
  | nil => exact hne rfl
  | @cons _ v _ h p' =>
    exact disj s(a, v) (by rw [Walk.edges_cons]; exact List.mem_cons_self)
      (by rw [Walk.edges_cons]; exact List.mem_cons_self)

/-- **`2 ≤ edgeRouteNumber a b`** for distinct vertices of a bridgeless
connected graph. -/
theorem two_le_edgeRouteNumber [Fintype V]
    (returns : ∀ x y, G.Adj x y → Nonempty ((G.deleteEdges {s(x, y)}).Path x y))
    {a b : V} (reach : G.Reachable a b) (hne : a ≠ b) : 2 ≤ edgeRouteNumber G a b := by
  classical
  obtain ⟨p, q, hp, hq, pq, disj⟩ := exists_two_edgeDisjoint_paths returns reach hne
  have fam : IsEdgeRouteFamily G ({p, q} : Finset (G.Walk a b)) := by
    refine ⟨?_, ?_⟩
    · intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with h | h <;> rw [h]
      · exact hp
      · exact hq
    · intro w hw w' hw' ww'
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw hw'
      rcases hw with rfl | rfl <;> rcases hw' with rfl | rfl
      all_goals first
        | exact absurd rfl ww'
        | exact disj
        | exact fun e h1 h2 => disj e h2 h1
  have := card_le_edgeRouteNumber fam
  rwa [Finset.card_pair pq] at this

/-! ### Coupling of two edge-disjoint routes with the cycle spectrum -/

/-- **Two edge-disjoint routes close a cycle through `a`**: for edge-disjoint
paths `p, q : a ⇝ b` with `a ≠ b`, follow `p` to its first vertex `z ≠ a` on
`q`.  The prefixes `p₁ : a ⇝ z` of `p` and `q₁ : a ⇝ z` of `q` close a cycle
through `a` of length `|p₁| + |q₁|`. -/
theorem edgeDisjoint_pair_cycle {a b : V} (p q : G.Walk a b) (hp : p.IsPath) (hq : q.IsPath)
    (disj : ∀ e ∈ p.edges, e ∉ q.edges) (hne : a ≠ b) :
    ∃ (z : V) (p₁ : G.Walk a z) (p₂ : G.Walk z b) (q₁ : G.Walk a z) (q₂ : G.Walk z b),
      p = p₁.append p₂ ∧ q = q₁.append q₂ ∧ z ≠ a ∧
      ∃ c : G.Walk a a, c.IsCycle ∧ c.length = p₁.length + q₁.length := by
  let S : Set V := {v | v ∈ q.support ∧ v ≠ a}
  obtain ⟨z, p₁, p₂, splitp, ⟨zq, za⟩, first⟩ := PathUncrossing.exists_first_hit S p
    ⟨b, p.end_mem_support, q.end_mem_support, hne.symm⟩
  obtain ⟨z', q₁, q₂, splitq, hz', _⟩ :=
    PathUncrossing.exists_first_hit ({z} : Set V) q ⟨z, zq, rfl⟩
  rw [Set.mem_singleton_iff] at hz'
  subst hz'
  refine ⟨z', p₁, p₂, q₁, q₂, splitp, splitq, za, ?_⟩
  have hp₁ : p₁.IsPath := (splitp ▸ hp).of_append_left
  have hq₁ : q₁.IsPath := (splitq ▸ hq).of_append_left
  have len : ∀ w : G.Walk a z', 1 ≤ w.length := by
    intro w
    by_contra h
    exact za (Walk.eq_of_length_eq_zero (p := w) (by omega)).symm
  have first_edge : ∀ w : G.Walk a z', w.length = 1 → s(a, z') ∈ w.edges := by
    intro w h1
    cases w with
    | nil => simp at h1
    | cons h w' =>
      simp only [Walk.length_cons, Nat.add_eq_right] at h1
      have := Walk.eq_of_length_eq_zero h1
      subst this
      simp
  obtain ⟨c, hc, hl⟩ := PathChords.ear_cycle p₁ q₁.reverse hp₁ hq₁.reverse
    (fun y yp yq => by
      rw [Walk.support_reverse, List.mem_reverse] at yq
      by_cases ya : y = a
      · exact Or.inl ya
      · have yqq : y ∈ q.support := by
          rw [splitq, Walk.support_append]; exact List.mem_append_left _ yq
        exact Or.inr (first y yp ⟨yqq, ya⟩))
    (len p₁) (by rw [Walk.length_reverse]; exact len q₁)
    (by
      rintro ⟨h1, h2⟩
      rw [Walk.length_reverse] at h2
      have ep := first_edge p₁ h1
      have eq := first_edge q₁ h2
      refine disj s(a, z') ?_ ?_
      · rw [splitp, Walk.edges_append]; exact List.mem_append_left _ ep
      · rw [splitq, Walk.edges_append]; exact List.mem_append_left _ eq)
  exact ⟨c, hc, by rw [hl, Walk.length_reverse]⟩

/-- **Under `avoids`**: the cycle through `a` of two edge-disjoint routes has
a rejected length `|p₁| + |q₁|`. -/
theorem edgeDisjoint_pair_not_lengthOK {LengthOK : Nat → Prop}
    (avoids : ¬ ∃ (c : V) (cy : G.Walk c c), cy.IsCycle ∧ LengthOK cy.length)
    {a b : V} (p q : G.Walk a b) (hp : p.IsPath) (hq : q.IsPath)
    (disj : ∀ e ∈ p.edges, e ∉ q.edges) (hne : a ≠ b) :
    ∃ (z : V) (p₁ : G.Walk a z) (p₂ : G.Walk z b) (q₁ : G.Walk a z) (q₂ : G.Walk z b),
      p = p₁.append p₂ ∧ q = q₁.append q₂ ∧ z ≠ a ∧
      ¬ LengthOK (p₁.length + q₁.length) := by
  obtain ⟨z, p₁, p₂, q₁, q₂, sp, sq, za, c, hc, hl⟩ :=
    edgeDisjoint_pair_cycle p q hp hq disj hne
  exact ⟨z, p₁, p₂, q₁, q₂, sp, sq, za, fun ok => avoids ⟨a, c, hc, hl ▸ ok⟩⟩

end Hypostructure.Graph.DisjointRoutes

/-! ## The route number of a finite object -/

namespace Hypostructure.Graph.FiniteObject

open Hypostructure.Graph.DisjointRoutes
open scoped BigOperators

universe u

variable (object : FiniteObject.{u})

/-- **`routeNumber u v`** of a finite object: the maximum number of internally
disjoint `u`–`v` paths of its graph. -/
noncomputable def routeNumber (a b : object.Vertex) : Nat := by
  letI : FinEnum object.Vertex := object.vertices
  exact DisjointRoutes.routeNumber object.graph a b

/-- The boundary incidence `e(S, G − S)` counts the boundary darts
`Σ_{x∈S} |N(x) \ S|`. -/
theorem boundaryIncidence_eq_sum_sdiff (support : Finset object.Vertex) :
    letI : FinEnum object.Vertex := object.vertices
    letI : DecidableRel object.graph.Adj := object.decideAdj
    object.boundaryIncidence support =
      ∑ x ∈ support, (object.graph.neighborFinset x \ support).card := by
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  classical
  unfold boundaryIncidence internalDegree degree
  refine Finset.sum_congr rfl fun x _ => ?_
  have h := Finset.card_sdiff_add_card_inter (object.graph.neighborFinset x) support
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  omega

/-- **The cut bound on G**: for every region `S` containing `u` and not `v`,
`routeNumber u v ≤ e(S, G − S)`. -/
theorem routeNumber_le_boundaryIncidence {a b : object.Vertex}
    (support : Finset object.Vertex) (ha : a ∈ support) (hb : b ∉ support) :
    object.routeNumber a b ≤ object.boundaryIncidence support := by
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  rw [object.boundaryIncidence_eq_sum_sdiff support]
  exact DisjointRoutes.routeNumber_le_cut support ha hb

/-- **Edge-disjoint exits of a region of G**: a family of pairwise
edge-disjoint walks from inside `S` to outside `S` has at most `e(S, G − S)`
members. -/
theorem card_le_boundaryIncidence_of_edgeDisjoint {ι : Type*} [Fintype ι]
    (support : Finset object.Vertex) (s t : ι → object.Vertex)
    (P : ∀ i, object.graph.Walk (s i) (t i)) (hs : ∀ i, s i ∈ support)
    (ht : ∀ i, t i ∉ support)
    (disj : ∀ i j, i ≠ j → ∀ e ∈ (P i).edges, e ∉ (P j).edges) :
    Fintype.card ι ≤ object.boundaryIncidence support := by
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  rw [object.boundaryIncidence_eq_sum_sdiff support]
  exact DisjointRoutes.card_le_cut_of_edgeDisjoint support s t P hs ht disj

/-- **The degree bound on G**: `routeNumber u v ≤ min (d(u)) (d(v))`. -/
theorem routeNumber_le_min_degree {a b : object.Vertex} (hne : a ≠ b) :
    object.routeNumber a b ≤ min (object.degree a) (object.degree b) := by
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  exact DisjointRoutes.routeNumber_le_min_degree hne

/-- The route number of G is symmetric. -/
theorem routeNumber_comm (a b : object.Vertex) :
    object.routeNumber a b = object.routeNumber b a := by
  letI : FinEnum object.Vertex := object.vertices
  exact DisjointRoutes.routeNumber_comm a b

/-- **Connectivity (node `[8]`) gives a route between any two vertices.** -/
theorem one_le_routeNumber (connected : object.graph.Connected) (a b : object.Vertex) :
    1 ≤ object.routeNumber a b := by
  letI : FinEnum object.Vertex := object.vertices
  exact DisjointRoutes.one_le_routeNumber (connected.preconnected a b)

/-- **`lem:bridgeless` gives two internally disjoint routes along every
edge**: the edge and its return `R_e(G)`. -/
theorem two_le_routeNumber_of_bridgeless
    (bridgeless : ∀ contraction : EdgeContraction object, contraction.HasReturn)
    {a b : object.Vertex} (adj : object.graph.Adj a b) :
    2 ≤ object.routeNumber a b := by
  letI : FinEnum object.Vertex := object.vertices
  obtain ⟨ret⟩ := bridgeless ⟨a, b, adj⟩
  exact DisjointRoutes.two_le_routeNumber_of_return adj ret

/-- **The route number on an edge of G**: `2 ≤ routeNumber u v ≤ min(d(u), d(v))`. -/
theorem routeNumber_edge_bounds
    (bridgeless : ∀ contraction : EdgeContraction object, contraction.HasReturn)
    {a b : object.Vertex} (adj : object.graph.Adj a b) :
    2 ≤ object.routeNumber a b ∧
      object.routeNumber a b ≤ min (object.degree a) (object.degree b) :=
  ⟨object.two_le_routeNumber_of_bridgeless bridgeless adj,
    object.routeNumber_le_min_degree adj.ne⟩

/-- **The route number with the cycle-spectrum coupling on G**: a maximum
route family of `routeNumber u v` internally disjoint `u`–`v` paths, every two
of whose length sums is rejected by `LengthOK`. -/
theorem exists_max_routeFamily_avoiding {LengthOK : Nat → Prop}
    (avoids : ¬ ∃ (c : object.Vertex) (cy : object.graph.Walk c c),
      cy.IsCycle ∧ LengthOK cy.length)
    {a b : object.Vertex} (hne : a ≠ b) :
    ∃ F : Finset (object.graph.Walk a b), IsRouteFamily object.graph F ∧
      F.card = object.routeNumber a b ∧
      ∀ p ∈ F, ∀ q ∈ F, p ≠ q → ¬ LengthOK (p.length + q.length) := by
  letI : FinEnum object.Vertex := object.vertices
  exact DisjointRoutes.exists_max_routeFamily_avoiding avoids hne

/-! ## Edge-disjoint routes of a finite object -/

/-- **`edgeRouteNumber u v`** of a finite object: the maximum number of
pairwise edge-disjoint `u`–`v` paths of its graph. -/
noncomputable def edgeRouteNumber (a b : object.Vertex) : Nat := by
  letI : FinEnum object.Vertex := object.vertices
  exact DisjointRoutes.edgeRouteNumber object.graph a b

/-- `lem:bridgeless` in its published form supplies a return for every edge. -/
theorem returns_of_bridgeless
    (bridgeless : ∀ contraction : EdgeContraction object, contraction.HasReturn) :
    ∀ x y, object.graph.Adj x y →
      Nonempty ((object.graph.deleteEdges {s(x, y)}).Path x y) :=
  fun x y adj => bridgeless ⟨x, y, adj⟩

/-- **Two edge-disjoint routes between any two vertices of G**: from
`lem:bridgeless` and connectivity (node `[8]`), `2 ≤ edgeRouteNumber a b`
for every `a ≠ b`. -/
theorem two_le_edgeRouteNumber
    (bridgeless : ∀ contraction : EdgeContraction object, contraction.HasReturn)
    (connected : object.graph.Connected) {a b : object.Vertex} (hne : a ≠ b) :
    2 ≤ object.edgeRouteNumber a b := by
  letI : FinEnum object.Vertex := object.vertices
  exact DisjointRoutes.two_le_edgeRouteNumber (object.returns_of_bridgeless bridgeless)
    (connected.preconnected a b) hne

/-- **The cut bound for edge routes on G**: `edgeRouteNumber a b ≤ e(S, G − S)`
for every region `S` containing `a` and not `b`. -/
theorem edgeRouteNumber_le_boundaryIncidence {a b : object.Vertex}
    (support : Finset object.Vertex) (ha : a ∈ support) (hb : b ∉ support) :
    object.edgeRouteNumber a b ≤ object.boundaryIncidence support := by
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  rw [object.boundaryIncidence_eq_sum_sdiff support]
  exact DisjointRoutes.edgeRouteNumber_le_cut support ha hb

/-- **The degree bound for edge routes on G.** -/
theorem edgeRouteNumber_le_degree {a b : object.Vertex} (hne : a ≠ b) :
    object.edgeRouteNumber a b ≤ object.degree a := by
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  exact DisjointRoutes.edgeRouteNumber_le_degree_left hne

/-- Internally disjoint routes are edge-disjoint:
`routeNumber a b ≤ edgeRouteNumber a b`. -/
theorem routeNumber_le_edgeRouteNumber {a b : object.Vertex} (hne : a ≠ b) :
    object.routeNumber a b ≤ object.edgeRouteNumber a b := by
  letI : FinEnum object.Vertex := object.vertices
  exact DisjointRoutes.routeNumber_le_edgeRouteNumber hne

/-- **Two edge-disjoint routes of G and their cycle through `a`**: under
`lem:bridgeless`, connectivity and `avoids`, any `a ≠ b` have two distinct
edge-disjoint paths `p, q : a ⇝ b`; following `p` to its first vertex
`z ≠ a` on `q`, the prefixes `p₁, q₁ : a ⇝ z` close a cycle through `a`, so
`¬ LengthOK (|p₁| + |q₁|)`. -/
theorem exists_edgeDisjoint_pair_avoiding {LengthOK : Nat → Prop}
    (bridgeless : ∀ contraction : EdgeContraction object, contraction.HasReturn)
    (connected : object.graph.Connected)
    (avoids : ¬ ∃ (c : object.Vertex) (cy : object.graph.Walk c c),
      cy.IsCycle ∧ LengthOK cy.length)
    {a b : object.Vertex} (hne : a ≠ b) :
    ∃ p q : object.graph.Walk a b, p.IsPath ∧ q.IsPath ∧ p ≠ q ∧
      (∀ e ∈ p.edges, e ∉ q.edges) ∧
      ∃ (z : object.Vertex) (p₁ : object.graph.Walk a z) (p₂ : object.graph.Walk z b)
        (q₁ : object.graph.Walk a z) (q₂ : object.graph.Walk z b),
        p = p₁.append p₂ ∧ q = q₁.append q₂ ∧ z ≠ a ∧
        ¬ LengthOK (p₁.length + q₁.length) := by
  obtain ⟨p, q, hp, hq, pq, disj⟩ := DisjointRoutes.exists_two_edgeDisjoint_paths
    (object.returns_of_bridgeless bridgeless) (connected.preconnected a b) hne
  exact ⟨p, q, hp, hq, pq, disj,
    DisjointRoutes.edgeDisjoint_pair_not_lengthOK avoids p q hp hq disj hne⟩

/-! ## Stubs at a region -/

/-- **Stub count at a region**: `e(S, G − S) + 2·e(G[S]) = Σ_{v∈S} d(v)`. -/
theorem boundaryIncidence_add_two_mul_internalEdgeCount (support : Finset object.Vertex) :
    object.boundaryIncidence support + 2 * object.internalEdgeCount support =
      ∑ x ∈ support, object.degree x := by
  have bd := object.boundaryIncidence_eq_sub support
  have hand := object.sum_internalDegree_eq_two_mul_internalEdgeCount support
  have le : ∑ x ∈ support, object.internalDegree support x ≤
      ∑ x ∈ support, object.degree x :=
    Finset.sum_le_sum fun x _ => object.internalDegree_le_degree support x
  omega

/-- **Stub lower bound on the boundary** at baseline `δ`:
`δ·|S| ≤ e(S, G − S) + 2·e(G[S])`, with equality defect exactly `σ(S)`. -/
theorem threshold_mul_card_le_boundary_add (support : Finset object.Vertex) (threshold : Nat)
    (baseline : ∀ x : object.Vertex, threshold ≤ object.degree x) :
    threshold * support.card ≤
      object.boundaryIncidence support + 2 * object.internalEdgeCount support := by
  have := object.two_mul_internalEdgeCount_add_boundaryIncidence support threshold baseline
  omega

/-- **Routes against stubs**: for a region `S` separating the terminals,
`routeNumber u v + 2·e(G[S]) ≤ Σ_{v∈S} d(v) = δ|S| + σ(S)`. -/
theorem routeNumber_add_two_mul_internalEdgeCount_le {a b : object.Vertex}
    (support : Finset object.Vertex) (ha : a ∈ support) (hb : b ∉ support)
    (threshold : Nat) (baseline : ∀ x : object.Vertex, threshold ≤ object.degree x) :
    object.routeNumber a b + 2 * object.internalEdgeCount support ≤
      threshold * support.card + object.ambientSurplus support threshold := by
  have r := object.routeNumber_le_boundaryIncidence support ha hb
  have := object.two_mul_internalEdgeCount_add_boundaryIncidence support threshold baseline
  omega

end Hypostructure.Graph.FiniteObject
