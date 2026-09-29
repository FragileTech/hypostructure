import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
import Mathlib.Combinatorics.SimpleGraph.Paths
import Hypostructure.Graph.Induced
import Hypostructure.Graph.Target
import Hypostructure.Graph.Progress
import Hypostructure.Graph.DeletionCriticality

/-!
# Splice lifting

Let `G'` be obtained from `G` by deleting the interior `I` of a path `p : a ⇝ b` of `G`
and adding the edge `s(a, b)`.  Every cycle of `G'` is a cycle of `G` of the same length,
or uses the new edge and lifts to a cycle of `G` of length `L + |p| - 1`.  Vocabulary-free.
-/

namespace Hypostructure.Graph.SpliceLift

open SimpleGraph

set_option linter.unusedSectionVars false
universe u
variable {V : Type*} [DecidableEq V]

/-- The direct case: a cycle whose first step is `a → b`. -/
theorem direct_case {G : SimpleGraph V} {a b : V} (hadj : G.Adj a b) (rest : G.Walk b a)
    (hcyc : (Walk.cons hadj rest).IsCycle) :
    ∃ (rest' : G.Walk b a), rest'.IsPath ∧ s(a, b) ∉ rest'.edges ∧
      rest'.length + 1 = (Walk.cons hadj rest).length := by
  rw [Walk.cons_isCycle_iff] at hcyc
  exact ⟨rest, hcyc.1, hcyc.2, by simp⟩

/-- A path starting at `a` whose edges contain `s(a,b)` starts with the step `a → b`. -/
theorem path_first_step {G : SimpleGraph V} {a b y : V} (q : G.Walk a y) (hq : q.IsPath)
    (hab : s(a, b) ∈ q.edges) :
    ∃ (h' : G.Adj a b) (q' : G.Walk b y), q = Walk.cons h' q' := by
  cases q with
  | nil => simp at hab
  | cons h' q' =>
    rename_i z
    rw [Walk.cons_isPath_iff] at hq
    rw [Walk.edges_cons, List.mem_cons] at hab
    rcases hab with e | e
    · have : z = b := by
        rcases Sym2.eq_iff.1 e.symm with ⟨_, hy⟩ | ⟨_, hb⟩
        · exact hy
        · exact absurd hb.symm (G.ne_of_adj h')
      subst this
      exact ⟨h', q', rfl⟩
    · exact absurd (q'.fst_mem_support_of_mem_edges e) hq.2

/-- A cycle through a vertex `a` and an edge `s(a,b)`: rotated and possibly reversed,
it starts with the step `a → b`. -/
theorem exists_cycle_snd {G : SimpleGraph V} {x a b : V} (c : G.Walk x x) (hc : c.IsCycle)
    (hab : s(a, b) ∈ c.edges) :
    ∃ (_ : G.Adj a b) (rest : G.Walk b a), rest.IsPath ∧ s(a, b) ∉ rest.edges ∧
      rest.length + 1 = c.length := by
  have ha : a ∈ c.support := c.fst_mem_support_of_mem_edges hab
  have hrot : (c.rotate a ha).IsCycle := hc.rotate ha
  have hedges : s(a, b) ∈ (c.rotate a ha).edges :=
    ((Walk.rotate_edges c a ha).mem_iff).2 hab
  have hlen : (c.rotate a ha).length = c.length := by simp
  generalize c.rotate a ha = d at hrot hedges hlen
  clear hc hab ha
  cases d with
  | nil => exact absurd hrot (by simp)
  | cons h rest =>
    rename_i y
    have hcyc := hrot
    rw [Walk.cons_isCycle_iff] at hcyc
    rw [Walk.edges_cons, List.mem_cons] at hedges
    rcases hedges with e | e
    · have : y = b := by
        rcases Sym2.eq_iff.1 e.symm with ⟨_, hy⟩ | ⟨_, hb⟩
        · exact hy
        · exact absurd hb.symm (G.ne_of_adj h)
      subst this
      exact ⟨h, rest, hcyc.1, hcyc.2, by simpa [Walk.length_cons] using hlen⟩
    · have hrev : (Walk.cons h rest).reverse.IsCycle := hrot.reverse
      have hp : rest.reverse.IsPath := hcyc.1.reverse
      have he' : s(a, b) ∈ rest.reverse.edges := by simpa using e
      obtain ⟨h', q', hq⟩ := path_first_step rest.reverse hp he'
      have hform : (Walk.cons h rest).reverse =
          Walk.cons h' (q'.append (Walk.cons h.symm Walk.nil)) := by
        rw [Walk.reverse_cons, hq, Walk.cons_append]
      rw [hform] at hrev
      obtain ⟨r2, hr2, hn2, hl2⟩ := direct_case h' _ hrev
      refine ⟨h', r2, hr2, hn2, ?_⟩
      have : (Walk.cons h' (q'.append (Walk.cons h.symm Walk.nil))).length =
          (Walk.cons h rest).length := by
        rw [← hform]; simp
      rw [hl2, this]; simpa [Walk.length_cons] using hlen

/-- **The splice lifting lemma.**  `G'` has the edges of `G` and possibly `s(a,b)`, and every
interior vertex of the path `p : a ⇝ b` of `G` (length at least `2`) is isolated in `G'`.
Every cycle of `G'` is a cycle of `G` of the same length, or lifts to a cycle of `G` of
length `L + |p| - 1` (the new edge replaced by `p`). -/
theorem cycle_lift {G G' : SimpleGraph V} {a b : V} (p : G.Walk a b) (hp : p.IsPath)
    (hlen : 2 ≤ p.length)
    (hG' : ∀ x y, G'.Adj x y → G.Adj x y ∨ s(x, y) = s(a, b))
    (hiso : ∀ v ∈ p.support, v ≠ a → v ≠ b → ∀ y, ¬ G'.Adj v y)
    {x : V} (c : G'.Walk x x) (hc : c.IsCycle) :
    (∃ (y : V) (d : G.Walk y y), d.IsCycle ∧ d.length = c.length) ∨
    (∃ (y : V) (d : G.Walk y y), d.IsCycle ∧ d.length + 1 = c.length + p.length) := by
  by_cases hab : s(a, b) ∈ c.edges
  · right
    obtain ⟨hadj, rest, hrest, hn, hl⟩ := exists_cycle_snd c hc hab
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
      refine ⟨a, Walk.cons h1 (p'.append rest'), ?_, ?_⟩
      · rw [Walk.cons_isCycle_iff]; exact ⟨hpath, hedge⟩
      · simp [Walk.length_append, rest', ← hl]; omega
  · left
    have restG : ∀ e ∈ c.edges, e ∈ G.edgeSet := by
      intro e he
      induction e using Sym2.ind with
      | h u v =>
        have := c.adj_of_mem_edges he
        rcases hG' u v this with h | h
        · exact h
        · rw [h] at he; exact absurd he hab
    exact ⟨x, c.transfer G restG, hc.transfer restG, by simp⟩

/-! ## The spliced graph -/

/-- `G` with the vertices of `D` deleted (left isolated) and the edge `s(a,b)` added. -/
def splice (G : SimpleGraph V) (a b : V) (D : Set V) : SimpleGraph V where
  Adj x y := (G.Adj x y ∧ x ∉ D ∧ y ∉ D) ∨ (s(x, y) = s(a, b) ∧ x ≠ y)
  symm := ⟨by
    intro x y h
    rcases h with ⟨h, hx, hy⟩ | ⟨h, hne⟩
    · exact Or.inl ⟨h.symm, hy, hx⟩
    · exact Or.inr ⟨by rw [Sym2.eq_swap]; exact h, hne.symm⟩⟩
  loopless := ⟨fun x h => by
    rcases h with ⟨h, _, _⟩ | ⟨_, hne⟩
    · exact G.loopless.irrefl x h
    · exact hne rfl⟩

/-- The interior of a walk: its support without the two ends. -/
def interior {G : SimpleGraph V} {a b : V} (p : G.Walk a b) : Set V :=
  {v | v ∈ p.support ∧ v ≠ a ∧ v ≠ b}

/-- **Cycles of the spliced graph lift.**  Deleting the interior of a path `p : a ⇝ b` of `G`
(length at least `2`) and adding `s(a,b)`: every cycle of the result is a cycle of `G` of the
same length, or lifts to a cycle of `G` of length `L + (|p| - 1)`. -/
theorem splice_cycle_lift {G : SimpleGraph V} {a b : V} (p : G.Walk a b) (hp : p.IsPath)
    (hlen : 2 ≤ p.length) {x : V} (c : (splice G a b (interior p)).Walk x x) (hc : c.IsCycle) :
    (∃ (y : V) (d : G.Walk y y), d.IsCycle ∧ d.length = c.length) ∨
    (∃ (y : V) (d : G.Walk y y), d.IsCycle ∧ d.length + 1 = c.length + p.length) := by
  refine cycle_lift p hp hlen ?_ ?_ c hc
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

theorem splice_cycle_lift' {G : SimpleGraph V} {a b : V} (p : G.Walk a b) (hp : p.IsPath)
    (hlen : 2 ≤ p.length) (D : Set V) (hD : ∀ v, v ∈ D ↔ v ∈ interior p) {x : V}
    (c : (splice G a b D).Walk x x) (hc : c.IsCycle) :
    (∃ (y : V) (d : G.Walk y y), d.IsCycle ∧ d.length = c.length) ∨
    (∃ (y : V) (d : G.Walk y y), d.IsCycle ∧ d.length + 1 = c.length + p.length) := by
  have : D = interior p := Set.ext hD
  subst this
  exact splice_cycle_lift p hp hlen c hc

/-- **F08 at graph level: what a target cycle of the excision costs.**  If the spliced graph
has a cycle whose length satisfies `LengthOK`, then `G` has an accepted cycle, or `G` has a
cycle of length `L + q` with `LengthOK L`, where `q = |p| - 1` is the number of deleted
vertices: the shift of the excised segment. -/
theorem splice_target {G : SimpleGraph V} {a b : V} (p : G.Walk a b) (hp : p.IsPath)
    (hlen : 2 ≤ p.length) (LengthOK : Nat → Prop)
    (h : ∃ (x : V) (c : (splice G a b (interior p)).Walk x x),
      c.IsCycle ∧ LengthOK c.length) :
    (∃ (y : V) (d : G.Walk y y), d.IsCycle ∧ LengthOK d.length) ∨
    (∃ (L : Nat) (y : V) (d : G.Walk y y), LengthOK L ∧ d.IsCycle ∧
      d.length = L + (p.length - 1)) := by
  obtain ⟨x, c, hc, hok⟩ := h
  rcases splice_cycle_lift p hp hlen c hc with ⟨y, d, hd, hl⟩ | ⟨y, d, hd, hl⟩
  · exact Or.inl ⟨y, d, hd, hl ▸ hok⟩
  · exact Or.inr ⟨c.length, y, d, hok, hd, by omega⟩

/-! ## Several shortcuts at once (the multi-boundary splice) -/

/-- A shortcut of `G`: a path of length at least `2` to be replaced by one edge. -/
structure Shortcut (G : SimpleGraph V) where
  a : V
  b : V
  p : G.Walk a b
  isPath : p.IsPath
  two_le : 2 ≤ p.length

/-- The shift of a shortcut: the number of vertices its interior deletes. -/
def Shortcut.shift {G : SimpleGraph V} (s : Shortcut G) : Nat := s.p.length - 1

/-- `G` with the interiors of the given shortcut paths deleted and each shortcut edge added. -/
def multiSplice (G : SimpleGraph V) : List (Shortcut G) → SimpleGraph V
  | [] => G
  | s :: L => splice (multiSplice G L) s.a s.b (interior s.p)

/-- The vertices deleted by the shortcut paths. -/
def delSet {G : SimpleGraph V} : List (Shortcut G) → Set V
  | [] => ∅
  | s :: L => interior s.p ∪ delSet L

/-- The shortcut paths are pairwise compatible: the interior of each avoids the support of
the others. -/
def Compatible {G : SimpleGraph V} (L : List (Shortcut G)) : Prop :=
  L.Pairwise fun s t => Disjoint (interior s.p) {v | v ∈ t.p.support} ∧
    Disjoint (interior t.p) {v | v ∈ s.p.support}

theorem adj_multiSplice {G : SimpleGraph V} (L : List (Shortcut G)) {x y : V}
    (h : G.Adj x y) (hx : x ∉ delSet L) (hy : y ∉ delSet L) : (multiSplice G L).Adj x y := by
  induction L with
  | nil => exact h
  | cons s L ih =>
    simp only [delSet, Set.mem_union, not_or] at hx hy
    exact Or.inl ⟨ih hx.2 hy.2, hx.1, hy.1⟩

theorem not_mem_delSet_of_support {G : SimpleGraph V} (s : Shortcut G) :
    ∀ (L : List (Shortcut G)),
      (∀ t ∈ L, Disjoint (interior t.p) {v | v ∈ s.p.support}) →
      ∀ v ∈ s.p.support, v ∉ delSet L
  | [], _, v, _ => by simp [delSet]
  | t :: L, h, v, hv => by
    simp only [delSet, Set.mem_union, not_or]
    refine ⟨fun hvt => ?_, not_mem_delSet_of_support s L (fun u hu => h u (List.mem_cons_of_mem _ hu)) v hv⟩
    exact Set.disjoint_left.1 (h t (List.mem_cons_self)) hvt hv

/-- **Lifting through several shortcuts.**  Every cycle of the multiply spliced graph lifts to
a cycle of `G` whose length is the cycle's length plus the shifts of some of the shortcuts
(those whose new edge the cycle uses). -/
theorem multiSplice_cycle_lift {G : SimpleGraph V} :
    ∀ (L : List (Shortcut G)), Compatible L → ∀ {x : V} (c : (multiSplice G L).Walk x x),
      c.IsCycle →
      ∃ (S : List (Shortcut G)) (y : V) (d : G.Walk y y), S.Sublist L ∧ d.IsCycle ∧
        d.length = c.length + (S.map Shortcut.shift).sum
  | [], _, x, c, hc => ⟨[], x, c, List.Sublist.slnil, hc, by simp; rfl⟩
  | s :: L, hcomp, x, c, hc => by
    have hpair := List.pairwise_cons.1 hcomp
    have hsupp : ∀ v ∈ s.p.support, v ∉ delSet L :=
      not_mem_delSet_of_support s L (fun t ht => (hpair.1 t ht).2)
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
    rcases splice_cycle_lift' p' hp' hlen' (interior s.p)
        (by intro v; simp [interior, p']) c hc with ⟨y, d, hd, hl⟩ | ⟨y, d, hd, hl⟩
    · obtain ⟨S, y', d', hS, hd', hl'⟩ := multiSplice_cycle_lift L hpair.2 d hd
      have hl2 : d.length = c.length := hl
      exact ⟨S, y', d', hS.cons s, hd', by rw [hl', hl2]⟩
    · obtain ⟨S, y', d', hS, hd', hl'⟩ := multiSplice_cycle_lift L hpair.2 d hd
      refine ⟨s :: S, y', d', hS.cons_cons s, hd', ?_⟩
      have := s.two_le
      have hl2 : d.length + 1 = c.length + s.p.length := by rw [← hlp]; exact hl
      simp only [List.map_cons, List.sum_cons, Shortcut.shift]
      omega

/-! ## The excised object -/

open Hypostructure.Graph in
/-- **The excised object.**  `G` with the vertices of `D` deleted and the edge `s(a,b)`
added, as a finite object on the vertices outside `D` (the induced restriction of the packed
spliced graph). -/
noncomputable def spliceObject (G : FiniteObject.{u}) (a b : G.Vertex)
    (D : Finset G.Vertex) : FiniteObject.{u} := by
  classical
  exact (FiniteObject.of (splice G.graph a b (D : Set G.Vertex)) G.vertices
      (fun _ _ => Classical.propDecidable _)).induce (G.vertexFinset.filter (fun v => v ∉ D))

open Hypostructure.Graph in
theorem vertexCount_spliceObject_lt (G : FiniteObject.{u}) (a b : G.Vertex)
    (D : Finset G.Vertex) (hD : D.Nonempty) :
    (spliceObject G a b D).vertexCount < G.vertexCount := by
  classical
  unfold spliceObject
  rw [FiniteObject.vertexCount_induce, ← FiniteObject.card_vertexFinset]
  obtain ⟨d, hd⟩ := hD
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.2 ⟨Finset.filter_subset _ _, ?_⟩
  intro h
  have hdm : d ∈ G.vertexFinset := by simp [FiniteObject.vertexFinset]
  have := (Finset.ext_iff.1 h d).2 hdm
  exact (Finset.mem_filter.1 this).2 hd

open Hypostructure.Graph in
theorem cycle_of_spliceObject (G : FiniteObject.{u}) (a b : G.Vertex)
    (D : Finset G.Vertex) (LengthOK : Nat → Prop)
    (h : HasCycleWithLength LengthOK (spliceObject G a b D)) :
    ∃ (x : G.Vertex) (c : (splice G.graph a b (D : Set G.Vertex)).Walk x x),
      c.IsCycle ∧ LengthOK c.length := by
  classical
  unfold spliceObject at h
  obtain ⟨cert⟩ := hasCycleWithLength_of_hom
    (right := FiniteObject.of (splice G.graph a b (D : Set G.Vertex)) G.vertices
      (fun _ _ => Classical.propDecidable _))
    (FiniteObject.induceEmbedding _ _).toHom (FiniteObject.induceEmbedding _ _).injective h
  exact ⟨cert.vertex, cert.walk, cert.isCycle, cert.length_ok⟩

open Hypostructure.Graph in
/-- **F08 (exact form): what the excision of a path of `G` costs.**  Let `p : a ⇝ b` be a path
of `G` (length at least `2`) and `D` its interior.  If `G` has no accepted cycle and the
excised object `spliceObject G a b D` has one, then `G` has a cycle of length `L + q` with
`LengthOK L` and `q = |p| - 1` (the number of deleted vertices plus zero for the new edge:
the length shift of the excised segment). -/
theorem excision_shift_hit (G : FiniteObject.{u}) {a b : G.Vertex}
    (p : G.graph.Walk a b) (hp : p.IsPath) (hlen : 2 ≤ p.length)
    (D : Finset G.Vertex) (hD : ∀ v, v ∈ D ↔ v ∈ interior p)
    (LengthOK : Nat → Prop) (avoids : ¬ HasCycleWithLength LengthOK G)
    (h : HasCycleWithLength LengthOK (spliceObject G a b D)) :
    ∃ (L : Nat) (y : G.Vertex) (d : G.graph.Walk y y),
      LengthOK L ∧ d.IsCycle ∧ d.length = L + (p.length - 1) := by
  classical
  have hset : (D : Set G.Vertex) = interior p := by ext v; simpa using hD v
  obtain ⟨x, c, hc, hok⟩ : ∃ (x : G.Vertex)
      (c : (splice G.graph a b (interior p)).Walk x x), c.IsCycle ∧ LengthOK c.length := by
    rw [← hset]; exact cycle_of_spliceObject G a b D LengthOK h
  rcases splice_target p hp hlen LengthOK ⟨x, c, hc, hok⟩ with ⟨y, d, hd, hk⟩ | hit
  · exact absurd ⟨⟨y, d, hd, hk⟩⟩ avoids
  · exact hit

open Hypostructure.Graph in
/-- **F08 (the excision dichotomy at G).**  `G` is a minimal target-avoiding object for
`Baseline`.  For any path `p : a ⇝ b` of `G` of length at least `2` with interior `D`,
either the excised object fails the baseline, or `G` has a cycle of length `L + q` where
`L` is accepted, `L + q` is *not* accepted, and `q = |p| - 1` is the shift of the
excised segment. -/
theorem excision_dichotomy (G : FiniteObject.{u}) {a b : G.Vertex}
    (p : G.graph.Walk a b) (hp : p.IsPath) (hlen : 2 ≤ p.length)
    (D : Finset G.Vertex) (hD : ∀ v, v ∈ D ↔ v ∈ interior p)
    (LengthOK : Nat → Prop) (avoids : ¬ HasCycleWithLength LengthOK G)
    (Baseline : FiniteObject.{u} → Prop)
    (minimal : ∀ X : FiniteObject.{u}, Baseline X → X.LexicographicallySmaller G →
      HasCycleWithLength LengthOK X) :
    ¬ Baseline (spliceObject G a b D) ∨
    ∃ (L : Nat) (y : G.Vertex) (d : G.graph.Walk y y),
      LengthOK L ∧ ¬ LengthOK (L + (p.length - 1)) ∧ d.IsCycle ∧
        d.length = L + (p.length - 1) := by
  classical
  by_cases hb : Baseline (spliceObject G a b D)
  · right
    have hne : D.Nonempty := by
      have hv : (p.getVert 1) ∈ interior p := by
        refine ⟨p.getVert_mem_support 1, ?_, ?_⟩
        · exact fun h => by
            have := hp.getVert_injOn (by simp; omega) (by simp) (h.trans p.getVert_zero.symm)
            omega
        · exact fun h => by
            have := hp.getVert_injOn (by simp; omega) (by simp) (h.trans p.getVert_length.symm)
            omega
      exact ⟨_, (hD _).2 hv⟩
    have small : (spliceObject G a b D).LexicographicallySmaller G :=
      FiniteObject.lexicographicallySmaller_of_vertexCount_lt
        (vertexCount_spliceObject_lt G a b D hne)
    obtain ⟨L, y, d, hL, hd, hl⟩ :=
      excision_shift_hit G p hp hlen D hD LengthOK avoids (minimal _ hb small)
    refine ⟨L, y, d, hL, fun hok => avoids ⟨⟨y, d, hd, hl ▸ hok⟩⟩, hd, hl⟩
  · exact Or.inl hb

open Classical in
open Hypostructure.Graph in
/-- A kept vertex other than `a`, `b` with no neighbour in `D` keeps its degree. -/
theorem degree_spliceObject_of_no_deleted_neighbour (G : FiniteObject.{u}) (a b : G.Vertex)
    (D : Finset G.Vertex) (v : G.Vertex) (hv : v ∈ G.vertexFinset.filter (fun v => v ∉ D))
    (va : v ≠ a) (vb : v ≠ b) (hno : ∀ w ∈ D, ¬ G.graph.Adj v w) :
    (spliceObject G a b D).degree ⟨v, hv⟩ = G.degree v := by
  classical
  unfold spliceObject
  rw [FiniteObject.degree_eq_ncard_neighborSet, FiniteObject.degree_eq_ncard_neighborSet]
  have hvD : v ∉ D := (Finset.mem_filter.1 hv).2
  have : ((FiniteObject.of (splice G.graph a b (D : Set G.Vertex)) G.vertices
      (fun _ _ => Classical.propDecidable _)).induce
      (G.vertexFinset.filter (fun v => v ∉ D))).graph.neighborSet ⟨v, hv⟩ =
      (fun w : {x // x ∈ G.vertexFinset.filter (fun v => v ∉ D)} => w.1) ⁻¹'
        (G.graph.neighborSet v) := by
    ext w
    simp only [SimpleGraph.mem_neighborSet, Set.mem_preimage]
    change (splice G.graph a b (D : Set G.Vertex)).Adj v w.1 ↔ G.graph.Adj v w.1
    constructor
    · rintro (⟨h, _, _⟩ | ⟨h, _⟩)
      · exact h
      · rcases Sym2.eq_iff.1 h with ⟨e, _⟩ | ⟨e, _⟩
        · exact absurd e va
        · exact absurd e vb
    · intro h
      have hw : w.1 ∉ D := (Finset.mem_filter.1 w.2).2
      exact Or.inl ⟨h, hvD, hw⟩
  rw [this]
  have hsub : G.graph.neighborSet v ⊆ Set.range (fun w : {x // x ∈
      G.vertexFinset.filter (fun v => v ∉ D)} => w.1) := by
    intro w hw
    refine ⟨⟨w, Finset.mem_filter.2 ⟨by simp [FiniteObject.vertexFinset], fun hwD => hno w hwD hw⟩⟩, rfl⟩
  exact Set.ncard_preimage_of_injective_subset_range Subtype.val_injective hsub

open Classical in
open Hypostructure.Graph in
/-- **The canonical deficient vertex of an excision.**  If `G` has minimum degree at least `t`
and the excised object does not, some kept vertex is `a`, `b`, or a neighbour of a deleted
vertex. -/
theorem excision_deficient (G : FiniteObject.{u}) {a b : G.Vertex}
    (D : Finset G.Vertex) (ha : a ∉ D) (t : Nat) (hG : MinimumDegreeAtLeast t G)
    (h : ¬ MinimumDegreeAtLeast t (spliceObject G a b D)) :
    ∃ v ∈ G.vertexFinset.filter (fun v => v ∉ D),
      v = a ∨ v = b ∨ ∃ w ∈ D, G.graph.Adj v w := by
  classical
  by_contra hcon
  push Not at hcon
  apply h
  have hmemA : a ∈ G.vertexFinset.filter (fun v => v ∉ D) :=
    Finset.mem_filter.2 ⟨by simp [FiniteObject.vertexFinset], ha⟩
  haveI : Nonempty (spliceObject G a b D).Vertex := ⟨⟨a, hmemA⟩⟩
  apply FiniteObject.le_minDegree_of_forall_le_degree
  intro ⟨v, hv⟩
  obtain ⟨va, vb, hno⟩ := hcon v hv
  rw [degree_spliceObject_of_no_deleted_neighbour G a b D v hv va vb hno]
  exact hG.trans (FiniteObject.minDegree_le_degree G v)

open Classical in
open Hypostructure.Graph in
/-- A kept vertex other than `a`, `b` with a neighbour in `D` strictly loses degree. -/
theorem degree_spliceObject_lt (G : FiniteObject.{u}) (a b : G.Vertex)
    (D : Finset G.Vertex) (w : G.Vertex) (hw : w ∈ G.vertexFinset.filter (fun v => v ∉ D))
    (wa : w ≠ a) (wb : w ≠ b) (hD : ∃ x ∈ D, G.graph.Adj w x) :
    (spliceObject G a b D).degree ⟨w, hw⟩ < G.degree w := by
  unfold spliceObject
  rw [FiniteObject.degree_eq_ncard_neighborSet, FiniteObject.degree_eq_ncard_neighborSet]
  have hwD : w ∉ D := (Finset.mem_filter.1 hw).2
  have hset : ((FiniteObject.of (splice G.graph a b (D : Set G.Vertex)) G.vertices
      (fun _ _ => Classical.propDecidable _)).induce
      (G.vertexFinset.filter (fun v => v ∉ D))).graph.neighborSet ⟨w, hw⟩ =
      (fun x : {x // x ∈ G.vertexFinset.filter (fun v => v ∉ D)} => x.1) ⁻¹'
        (G.graph.neighborSet w \ (D : Set G.Vertex)) := by
    ext x
    simp only [SimpleGraph.mem_neighborSet, Set.mem_preimage, Set.mem_diff]
    change (splice G.graph a b (D : Set G.Vertex)).Adj w x.1 ↔
      G.graph.Adj w x.1 ∧ x.1 ∉ (D : Set G.Vertex)
    constructor
    · rintro (⟨h, _, hx⟩ | ⟨h, _⟩)
      · exact ⟨h, hx⟩
      · rcases Sym2.eq_iff.1 h with ⟨e, _⟩ | ⟨e, _⟩
        · exact absurd e wa
        · exact absurd e wb
    · rintro ⟨h, hx⟩
      exact Or.inl ⟨h, hwD, hx⟩
  rw [hset]
  have hsub : G.graph.neighborSet w \ (D : Set G.Vertex) ⊆ Set.range
      (fun x : {x // x ∈ G.vertexFinset.filter (fun v => v ∉ D)} => x.1) := by
    intro x hx
    exact ⟨⟨x, Finset.mem_filter.2 ⟨by simp [FiniteObject.vertexFinset], hx.2⟩⟩, rfl⟩
  refine lt_of_eq_of_lt
    (Set.ncard_preimage_of_injective_subset_range Subtype.val_injective hsub) ?_
  obtain ⟨x, hxD, hx⟩ := hD
  apply Set.ncard_lt_ncard
  · refine ⟨Set.diff_subset, fun h => ?_⟩
    have := h hx
    exact this.2 hxD
  · letI : FinEnum G.Vertex := G.vertices
    exact Set.toFinite _

open Classical in
open Hypostructure.Graph in
/-- **The degree side of the excision, exactly.**  If a kept vertex `w ∉ {a, b}` of degree at
most `t` in `G` has a neighbour in the deleted set `D`, the excised object misses the
baseline `t`. -/
theorem not_baseline_of_external (G : FiniteObject.{u}) (a b : G.Vertex)
    (D : Finset G.Vertex) (t : Nat) (w : G.Vertex)
    (hw : w ∈ G.vertexFinset.filter (fun v => v ∉ D))
    (wa : w ≠ a) (wb : w ≠ b) (hD : ∃ x ∈ D, G.graph.Adj w x) (deg : G.degree w ≤ t) :
    ¬ MinimumDegreeAtLeast t (spliceObject G a b D) := by
  intro h
  have h1 := degree_spliceObject_lt G a b D w hw wa wb hD
  have h2 := FiniteObject.minDegree_le_degree (spliceObject G a b D) ⟨w, hw⟩
  unfold MinimumDegreeAtLeast at h
  omega

open Classical in
open Hypostructure.Graph in
/-- **The multiply excised object**: `G` with the interiors of the shortcut paths deleted and
the shortcut edges added. -/
noncomputable def multiSpliceObject (G : FiniteObject.{u}) (L : List (Shortcut G.graph)) :
    FiniteObject.{u} :=
  (FiniteObject.of (multiSplice G.graph L) G.vertices
      (fun _ _ => Classical.propDecidable _)).induce
    (G.vertexFinset.filter (fun v => v ∉ delSet L))

open Classical in
open Hypostructure.Graph in
theorem vertexCount_multiSpliceObject_lt (G : FiniteObject.{u}) (L : List (Shortcut G.graph))
    (v : G.Vertex) (hv : v ∈ delSet L) :
    (multiSpliceObject G L).vertexCount < G.vertexCount := by
  unfold multiSpliceObject
  rw [FiniteObject.vertexCount_induce, ← FiniteObject.card_vertexFinset]
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.2 ⟨Finset.filter_subset _ _, ?_⟩
  intro h
  have hdm : v ∈ G.vertexFinset := by simp [FiniteObject.vertexFinset]
  have := (Finset.ext_iff.1 h v).2 hdm
  exact (Finset.mem_filter.1 this).2 hv

open Classical in
open Hypostructure.Graph in
theorem cycle_of_multiSpliceObject (G : FiniteObject.{u}) (L : List (Shortcut G.graph))
    (LengthOK : Nat → Prop) (h : HasCycleWithLength LengthOK (multiSpliceObject G L)) :
    ∃ (x : G.Vertex) (c : (multiSplice G.graph L).Walk x x), c.IsCycle ∧ LengthOK c.length := by
  unfold multiSpliceObject at h
  obtain ⟨cert⟩ := hasCycleWithLength_of_hom
    (right := FiniteObject.of (multiSplice G.graph L) G.vertices
      (fun _ _ => Classical.propDecidable _))
    (FiniteObject.induceEmbedding _ _).toHom (FiniteObject.induceEmbedding _ _).injective h
  exact ⟨cert.vertex, cert.walk, cert.isCycle, cert.length_ok⟩

open Classical in
open Hypostructure.Graph in
/-- **F08 for a family of shortcuts (multi-boundary excision).**  `G` is a minimal
target-avoiding object for `Baseline`; `L` is a compatible family of shortcut paths with a
nonempty deleted set.  Either the multiply excised object misses the baseline, or `G` has a
cycle whose length is an accepted length plus the shifts of a subfamily of `L`, and is not
accepted. -/
theorem multi_excision_dichotomy (G : FiniteObject.{u}) (L : List (Shortcut G.graph))
    (hL : Compatible L) (v : G.Vertex) (hv : v ∈ delSet L)
    (LengthOK : Nat → Prop) (avoids : ¬ HasCycleWithLength LengthOK G)
    (Baseline : FiniteObject.{u} → Prop)
    (minimal : ∀ X : FiniteObject.{u}, Baseline X → X.LexicographicallySmaller G →
      HasCycleWithLength LengthOK X) :
    ¬ Baseline (multiSpliceObject G L) ∨
    ∃ (S : List (Shortcut G.graph)) (Lk : Nat) (y : G.Vertex) (d : G.graph.Walk y y),
      S.Sublist L ∧ LengthOK Lk ∧ ¬ LengthOK (Lk + (S.map Shortcut.shift).sum) ∧
        d.IsCycle ∧ d.length = Lk + (S.map Shortcut.shift).sum := by
  by_cases hb : Baseline (multiSpliceObject G L)
  · right
    have small : (multiSpliceObject G L).LexicographicallySmaller G :=
      FiniteObject.lexicographicallySmaller_of_vertexCount_lt
        (vertexCount_multiSpliceObject_lt G L v hv)
    obtain ⟨x, c, hc, hok⟩ := cycle_of_multiSpliceObject G L LengthOK (minimal _ hb small)
    obtain ⟨S, y, d, hS, hd, hl⟩ := multiSplice_cycle_lift L hL c hc
    refine ⟨S, c.length, y, d, hS, hok, fun hok' => avoids ⟨⟨y, d, hd, hl ▸ hok'⟩⟩, hd, hl⟩
  · exact Or.inl hb

end Hypostructure.Graph.SpliceLift
