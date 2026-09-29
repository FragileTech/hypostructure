import Hypostructure.Graph.SpliceLift

/-!
# Splice lifting with routes

`SpliceLift.cycle_lift` and `multiSplice_cycle_lift` recorded only the length of the lifted cycle.
Here the lifted cycle's *route* is recorded: which edges of the original cycle survive, which
shortcut paths lie on it, and that the interior of an unused shortcut is untouched.
-/

namespace Hypostructure.Graph.SpliceLift

open SimpleGraph

set_option linter.unusedSectionVars false
universe u
variable {V : Type*} [DecidableEq V]

/-- `exists_cycle_snd` with the edges of the remainder: `c`'s edges are `s(a,b)` and the edges
of `rest`. -/
theorem exists_cycle_snd_edges {G : SimpleGraph V} {x a b : V} (c : G.Walk x x)
    (hc : c.IsCycle) (hab : s(a, b) ∈ c.edges) :
    ∃ (_ : G.Adj a b) (rest : G.Walk b a), rest.IsPath ∧ s(a, b) ∉ rest.edges ∧
      rest.length + 1 = c.length ∧ ∀ e, e ∈ c.edges ↔ e = s(a, b) ∨ e ∈ rest.edges := by
  have ha : a ∈ c.support := c.fst_mem_support_of_mem_edges hab
  have hrot : (c.rotate a ha).IsCycle := hc.rotate ha
  have hedges : s(a, b) ∈ (c.rotate a ha).edges :=
    ((Walk.rotate_edges c a ha).mem_iff).2 hab
  have hlen : (c.rotate a ha).length = c.length := by simp
  have hmem : ∀ e, e ∈ c.edges ↔ e ∈ (c.rotate a ha).edges :=
    fun e => ((Walk.rotate_edges c a ha).mem_iff).symm
  generalize c.rotate a ha = d at hrot hedges hlen hmem
  clear hc hab ha
  cases d with
  | nil => exact absurd hrot (by simp)
  | cons h rest =>
    rename_i y
    have hcyc := hrot
    rw [Walk.cons_isCycle_iff] at hcyc
    have hedges0 := hedges
    rw [Walk.edges_cons, List.mem_cons] at hedges
    rcases hedges with e | e
    · have : y = b := by
        rcases Sym2.eq_iff.1 e.symm with ⟨_, hy⟩ | ⟨_, hb⟩
        · exact hy
        · exact absurd hb.symm (G.ne_of_adj h)
      subst this
      refine ⟨h, rest, hcyc.1, hcyc.2, by simpa [Walk.length_cons] using hlen, ?_⟩
      intro e'
      rw [hmem e', Walk.edges_cons, List.mem_cons]
    · have hrev : (Walk.cons h rest).reverse.IsCycle := hrot.reverse
      have hp : rest.reverse.IsPath := hcyc.1.reverse
      have he' : s(a, b) ∈ rest.reverse.edges := by simpa using e
      obtain ⟨h', q', hq⟩ := path_first_step rest.reverse hp he'
      have hform : (Walk.cons h rest).reverse =
          Walk.cons h' (q'.append (Walk.cons h.symm Walk.nil)) := by
        rw [Walk.reverse_cons, hq, Walk.cons_append]
      have hrev' := hrev
      rw [hform, Walk.cons_isCycle_iff] at hrev'
      refine ⟨h', q'.append (Walk.cons h.symm Walk.nil), hrev'.1, hrev'.2, ?_, ?_⟩
      · have : (Walk.cons h' (q'.append (Walk.cons h.symm Walk.nil))).length =
            (Walk.cons h rest).length := by
          rw [← hform]; simp
        calc (q'.append (Walk.cons h.symm Walk.nil)).length + 1
            = (Walk.cons h' (q'.append (Walk.cons h.symm Walk.nil))).length :=
              (Walk.length_cons _ _).symm
          _ = (Walk.cons h rest).length := this
          _ = c.length := hlen
      · intro e'
        rw [hmem e']
        have h1 : e' ∈ (Walk.cons h rest).edges ↔
            e' ∈ (Walk.cons h rest).reverse.edges := by
          rw [Walk.edges_reverse, List.mem_reverse]
        rw [h1, hform, Walk.edges_cons, List.mem_cons]

/-- **The splice lifting lemma with routes.** -/
theorem cycle_lift_route {G G' : SimpleGraph V} {a b : V} (p : G.Walk a b) (hp : p.IsPath)
    (hlen : 2 ≤ p.length)
    (hG' : ∀ x y, G'.Adj x y → G.Adj x y ∨ s(x, y) = s(a, b))
    (hiso : ∀ v ∈ p.support, v ≠ a → v ≠ b → ∀ y, ¬ G'.Adj v y)
    {x : V} (c : G'.Walk x x) (hc : c.IsCycle) :
    ∃ (y : V) (d : G.Walk y y), d.IsCycle ∧
      (∀ e ∈ d.edges, e ∈ c.edges ∨ (s(a, b) ∈ c.edges ∧ e ∈ p.edges)) ∧
      (∀ e ∈ c.edges, e ≠ s(a, b) → e ∈ d.edges) ∧
      (s(a, b) ∈ c.edges →
        (∀ e ∈ p.edges, e ∈ d.edges) ∧ d.length + 1 = c.length + p.length) ∧
      (s(a, b) ∉ c.edges → d.length = c.length) := by
  by_cases hab : s(a, b) ∈ c.edges
  · obtain ⟨hadj, rest, hrest, hn, hl, hcedges⟩ := exists_cycle_snd_edges c hc hab
    have restG : ∀ e ∈ rest.edges, e ∈ G.edgeSet := by
      intro e he
      induction e using Sym2.ind with
      | h u v =>
        have := rest.adj_of_mem_edges he
        rcases hG' u v this with h | h
        · exact h
        · rw [h] at he; exact absurd he hn
    let rest' : G.Walk b a := rest.transfer G restG
    have hrest' : rest'.IsPath := hrest.transfer restG
    cases p with
    | nil => simp at hlen
    | cons h1 p' =>
      rename_i a1
      have hpp : p'.IsPath ∧ a ∉ p'.support := by simpa [Walk.cons_isPath_iff] using hp
      have hptrail : s(a, a1) ∉ p'.edges := by
        intro h
        exact hpp.2 (p'.fst_mem_support_of_mem_edges h)
      have hp'len : 1 ≤ p'.length := by simp at hlen; omega
      have ha1b : a1 ≠ b := by
        rintro rfl
        have := Walk.isPath_iff_nil.1 hpp.1
        have := Walk.length_eq_zero_iff.2 this
        omega
      have hpath : (p'.append rest').IsPath := by
        rw [Walk.isPath_def, Walk.support_append]
        refine List.nodup_append.2 ⟨hpp.1.support_nodup, ?_, ?_⟩
        · have : rest'.support.Nodup := hrest'.support_nodup
          exact this.sublist (List.tail_sublist _)
        · intro v hv1 w hv2 hvw
          subst hvw
          have hv1' : v ∈ (Walk.cons h1 p').support := List.mem_cons_of_mem _ hv1
          have vne : v ≠ a := fun e => hpp.2 (e ▸ hv1)
          by_cases vb : v = b
          · subst vb
            have hs : rest'.support = v :: rest'.support.tail := by
              cases rest' <;> simp
            have : rest'.support.Nodup := hrest'.support_nodup
            rw [hs] at this
            exact (List.nodup_cons.1 this).1 hv2
          · have hmem : v ∈ rest.support := by
              have : rest'.support = rest.support := by simp [rest']
              rw [← this]; exact List.mem_of_mem_tail hv2
            rcases (Walk.mem_support_iff_exists_mem_edges).1 hmem with hvb | ⟨e, he, hve⟩
            · exact vne hvb
            · induction e using Sym2.ind with
              | h u w =>
                have hadj' := rest.adj_of_mem_edges he
                rcases Sym2.mem_iff.1 hve with rfl | rfl
                · exact hiso v hv1' vne vb _ hadj'
                · exact hiso v hv1' vne vb _ hadj'.symm
      have hedge : s(a, a1) ∉ (p'.append rest').edges := by
        rw [Walk.edges_append, List.mem_append]
        rintro (h | h)
        · exact hptrail h
        · have hr : s(a, a1) ∈ rest.edges := by
            have : rest'.edges = rest.edges := by simp [rest']
            rwa [this] at h
          have := rest.adj_of_mem_edges hr
          exact hiso a1 (List.mem_cons_of_mem _ (p'.start_mem_support)) (G.ne_of_adj h1).symm
            ha1b _ this.symm
      have hre : rest'.edges = rest.edges := by simp [rest']
      refine ⟨a, Walk.cons h1 (p'.append rest'), ?_, ?_, ?_, ?_, fun h => absurd hab h⟩
      · rw [Walk.cons_isCycle_iff]; exact ⟨hpath, hedge⟩
      · intro e he
        rw [Walk.edges_cons, Walk.edges_append, List.mem_cons, List.mem_append] at he
        rcases he with h | h | h
        · exact Or.inr ⟨hab, by rw [Walk.edges_cons, List.mem_cons]; exact Or.inl h⟩
        · exact Or.inr ⟨hab, by rw [Walk.edges_cons, List.mem_cons]; exact Or.inr h⟩
        · rw [hre] at h
          exact Or.inl ((hcedges e).2 (Or.inr h))
      · intro e he hne
        rcases (hcedges e).1 he with h | h
        · exact absurd h hne
        · rw [Walk.edges_cons, Walk.edges_append, List.mem_cons, List.mem_append, hre]
          exact Or.inr (Or.inr h)
      · intro _
        refine ⟨?_, ?_⟩
        · intro e he
          rw [Walk.edges_cons, List.mem_cons] at he
          rw [Walk.edges_cons, Walk.edges_append, List.mem_cons, List.mem_append]
          rcases he with h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
        · simp [Walk.length_append, rest', ← hl]; omega
  · have restG : ∀ e ∈ c.edges, e ∈ G.edgeSet := by
      intro e he
      induction e using Sym2.ind with
      | h u v =>
        have := c.adj_of_mem_edges he
        rcases hG' u v this with h | h
        · exact h
        · rw [h] at he; exact absurd he hab
    refine ⟨x, c.transfer G restG, hc.transfer restG, ?_, ?_, fun h => absurd h hab, ?_⟩
    · intro e he
      exact Or.inl (by simpa using he)
    · intro e he _
      simpa using he
    · intro _; simp


/-- `cycle_lift_route` for `splice G a b D`. -/
theorem splice_cycle_route {G : SimpleGraph V} {a b : V} (p : G.Walk a b) (hp : p.IsPath)
    (hlen : 2 ≤ p.length) (D : Set V) (hD : ∀ v, v ∈ D ↔ v ∈ interior p) {x : V}
    (c : (splice G a b D).Walk x x) (hc : c.IsCycle) :
    ∃ (y : V) (d : G.Walk y y), d.IsCycle ∧
      (∀ e ∈ d.edges, e ∈ c.edges ∨ (s(a, b) ∈ c.edges ∧ e ∈ p.edges)) ∧
      (∀ e ∈ c.edges, e ≠ s(a, b) → e ∈ d.edges) ∧
      (s(a, b) ∈ c.edges →
        (∀ e ∈ p.edges, e ∈ d.edges) ∧ d.length + 1 = c.length + p.length) ∧
      (s(a, b) ∉ c.edges → d.length = c.length) := by
  have : D = interior p := Set.ext hD
  subst this
  refine cycle_lift_route p hp hlen ?_ ?_ c hc
  · intro x y h
    rcases h with ⟨h, _, _⟩ | ⟨h, _⟩
    · exact Or.inl h
    · exact Or.inr h
  · intro v hv hva hvb y h
    rcases h with ⟨_, hx, _⟩ | ⟨h, _⟩
    · exact hx ⟨hv, hva, hvb⟩
    · rcases Sym2.eq_iff.1 h with ⟨e, _⟩ | ⟨e, _⟩
      · exact hva e
      · exact hvb e

/-- Route compatibility of a shortcut family: compatible, no shortcut edge coincides with
another's or lies on any path of the family. -/
def RouteCompatible {G : SimpleGraph V} (L : List (Shortcut G)) : Prop :=
  Compatible L ∧ (∀ s ∈ L, s(s.a, s.b) ∉ s.p.edges) ∧
    L.Pairwise fun s t => s(s.a, s.b) ≠ s(t.a, t.b) ∧ s(t.a, t.b) ∉ s.p.edges ∧
      s(s.a, s.b) ∉ t.p.edges

open Classical in
/-- **Lifting through several shortcuts, with routes.**  The lifted cycle `d` keeps every edge of
`c` that is not a shortcut edge, contains the whole path of every shortcut whose edge `c`
uses, has no other new edges, and its length is `c.length` plus the shifts of the used
shortcuts. -/
theorem multiSplice_cycle_route {G : SimpleGraph V} :
    ∀ (L : List (Shortcut G)), RouteCompatible L → ∀ {x : V}
      (c : (multiSplice G L).Walk x x), c.IsCycle →
      ∃ (y : V) (d : G.Walk y y), d.IsCycle ∧
        (∀ e ∈ d.edges, e ∈ c.edges ∨ ∃ s ∈ L, s(s.a, s.b) ∈ c.edges ∧ e ∈ s.p.edges) ∧
        (∀ e ∈ c.edges, (∀ s ∈ L, e ≠ s(s.a, s.b)) → e ∈ d.edges) ∧
        (∀ s ∈ L, s(s.a, s.b) ∈ c.edges → ∀ e ∈ s.p.edges, e ∈ d.edges) ∧
        d.length = c.length +
          (((L.filter fun s => decide (s(s.a, s.b) ∈ c.edges)).map Shortcut.shift).sum)
  | [], _, x, c, hc => ⟨x, c, hc, fun e he => Or.inl he, fun e he _ => he,
      fun s hs => by simp at hs, by simp; rfl⟩
  | s :: L, hrc, x, c, hc => by
    obtain ⟨hcomp, hself, hpair⟩ := hrc
    have hpair' := List.pairwise_cons.1 hpair
    have hcomp' := List.pairwise_cons.1 hcomp
    have hsupp : ∀ v ∈ s.p.support, v ∉ delSet L :=
      not_mem_delSet_of_support s L (fun t ht => (hcomp'.1 t ht).2)
    have hedges : ∀ e ∈ s.p.edges, e ∈ (multiSplice G L).edgeSet := by
      intro e he
      induction e using Sym2.ind with
      | h u v =>
        have hadj := s.p.adj_of_mem_edges he
        exact adj_multiSplice L hadj (hsupp u (s.p.fst_mem_support_of_mem_edges he))
          (hsupp v (s.p.snd_mem_support_of_mem_edges he))
    let p' : (multiSplice G L).Walk s.a s.b := s.p.transfer _ hedges
    have hp' : p'.IsPath := s.isPath.transfer hedges
    have hlen' : 2 ≤ p'.length := by simpa [p'] using s.two_le
    have hlp : p'.length = s.p.length := by simp [p']
    have hep : p'.edges = s.p.edges := by simp [p']
    obtain ⟨y1, d1, hd1, r1, r2, r3, r4⟩ := splice_cycle_route p' hp' hlen' (interior s.p)
        (by intro v; simp [interior, p']) c hc
    obtain ⟨y, d, hd, q1, q2, q3, q4⟩ :=
      multiSplice_cycle_route L ⟨hcomp'.2, fun t ht => hself t (List.mem_cons_of_mem _ ht),
        hpair'.2⟩ d1 hd1
    rw [hep] at r1 r3
    refine ⟨y, d, hd, ?_, ?_, ?_, ?_⟩
    · intro e he
      rcases q1 e he with h | ⟨t, ht, hu, h⟩
      · rcases r1 e h with h' | ⟨h1, h2⟩
        · exact Or.inl h'
        · exact Or.inr ⟨s, List.mem_cons_self, h1, h2⟩
      · have hu' : s(t.a, t.b) ∈ c.edges := by
          rcases r1 _ hu with h' | ⟨_, h'⟩
          · exact h'
          · exact absurd h' (hpair'.1 t ht).2.1
        exact Or.inr ⟨t, List.mem_cons_of_mem _ ht, hu', h⟩
    · intro e he hne
      have hne1 : e ≠ s(s.a, s.b) := hne s List.mem_cons_self
      exact q2 e (r2 e he hne1) (fun t ht => hne t (List.mem_cons_of_mem _ ht))
    · intro t ht hin e he
      rcases List.mem_cons.1 ht with rfl | ht'
      · exact q2 e ((r3 hin).1 e he) (fun t' ht' heq =>
          (hpair'.1 t' ht').2.1 (heq ▸ he))
      · have hne : s(t.a, t.b) ≠ s(s.a, s.b) := fun h => (hpair'.1 t ht').1 h.symm
        exact q3 t ht' (r2 _ hin hne) e he
    · have hfilter : L.filter (fun t => decide (s(t.a, t.b) ∈ d1.edges)) =
          L.filter (fun t => decide (s(t.a, t.b) ∈ c.edges)) := by
        apply List.filter_congr
        intro t ht
        rw [decide_eq_decide]
        constructor
        · intro h
          rcases r1 _ h with h' | ⟨_, h'⟩
          · exact h'
          · exact absurd h' (hpair'.1 t ht).2.1
        · intro h
          exact r2 _ h (fun h' => (hpair'.1 t ht).1 h'.symm)
      have hdl : d.length = d1.length +
          (((L.filter fun t => decide (s(t.a, t.b) ∈ c.edges)).map Shortcut.shift).sum) := by
        rw [q4, hfilter]
      by_cases hin : s(s.a, s.b) ∈ c.edges
      · have hl : d1.length + 1 = c.length + s.p.length := by
          rw [← hlp]; exact (r3 hin).2
        have := s.two_le
        rw [List.filter_cons_of_pos (by simpa using hin)]
        simp only [List.map_cons, List.sum_cons, Shortcut.shift]
        omega
      · have hl : d1.length = c.length := r4 hin
        rw [List.filter_cons_of_neg (by simpa using hin)]
        omega

open Classical in
/-- `d` is a lift of `c` through the shortcuts `L`, with its route. -/
def RouteLift {G : SimpleGraph V} (L : List (Shortcut G)) {x y : V}
    (c : (multiSplice G L).Walk x x) (d : G.Walk y y) : Prop :=
  (∀ e ∈ d.edges, e ∈ c.edges ∨ ∃ s ∈ L, s(s.a, s.b) ∈ c.edges ∧ e ∈ s.p.edges) ∧
  (∀ e ∈ c.edges, (∀ s ∈ L, e ≠ s(s.a, s.b)) → e ∈ d.edges) ∧
  (∀ s ∈ L, s(s.a, s.b) ∈ c.edges → ∀ e ∈ s.p.edges, e ∈ d.edges) ∧
  d.length = c.length +
    (((L.filter fun s => decide (s(s.a, s.b) ∈ c.edges)).map Shortcut.shift).sum)

open Classical in
theorem multiSplice_route_lift {G : SimpleGraph V} (L : List (Shortcut G))
    (hL : RouteCompatible L) {x : V} (c : (multiSplice G L).Walk x x) (hc : c.IsCycle) :
    ∃ (y : V) (d : G.Walk y y), d.IsCycle ∧ RouteLift L c d := by
  obtain ⟨y, d, hd, r1, r2, r3, r4⟩ := multiSplice_cycle_route L hL c hc
  exact ⟨y, d, hd, r1, r2, r3, r4⟩

open Classical in
open Hypostructure.Graph in
/-- **Excision with routes.**  `G` minimal target-avoiding; `L` route-compatible; the multiply
excised object keeps the baseline.  Then it has an accepted cycle `c`, which lifts to a
non-accepted cycle `d` of `G` with its route. -/
theorem multi_excision_route (G : FiniteObject.{u}) (L : List (Shortcut G.graph))
    (hL : RouteCompatible L) (v : G.Vertex) (hv : v ∈ delSet L)
    (LengthOK : Nat → Prop) (avoids : ¬ HasCycleWithLength LengthOK G)
    (Baseline : FiniteObject.{u} → Prop)
    (minimal : ∀ X : FiniteObject.{u}, Baseline X → X.LexicographicallySmaller G →
      HasCycleWithLength LengthOK X)
    (hb : Baseline (multiSpliceObject G L)) :
    ∃ (x : G.Vertex) (c : (multiSplice G.graph L).Walk x x), c.IsCycle ∧ LengthOK c.length ∧
      ∃ (y : G.Vertex) (d : G.graph.Walk y y), d.IsCycle ∧ ¬ LengthOK d.length ∧
        RouteLift L c d := by
  have small : (multiSpliceObject G L).LexicographicallySmaller G :=
    FiniteObject.lexicographicallySmaller_of_vertexCount_lt
      (vertexCount_multiSpliceObject_lt G L v hv)
  obtain ⟨x, c, hc, hok⟩ := cycle_of_multiSpliceObject G L LengthOK (minimal _ hb small)
  obtain ⟨y, d, hd, hr⟩ := multiSplice_route_lift L hL c hc
  exact ⟨x, c, hc, hok, y, d, hd, fun hok' => avoids ⟨⟨y, d, hd, hok'⟩⟩, hr⟩

end Hypostructure.Graph.SpliceLift
