import Mathlib.Combinatorics.SimpleGraph.Walk.Counting
import Hypostructure.Graph.PathChords
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
