import Hypostructure.Graph.Target

/-!
# Chords of a path (`[144a]`, G audit S144a)

Vocabulary-free.  A path `w = p₁ ++ p₂ ++ p₃` of a graph, with a chord `uv`
between the ends of the middle segment `p₂ : u ⇝ v` of length `≥ 2`:

* `chord_cycle`: `p₂` and the chord close a cycle of length `|p₂| + 1`;
* `chord_shortcut`: `p₁`, the chord and `p₃` form a path `a ⇝ b` of length
  `|p₁| + 1 + |p₃|`, shorter than `w`;
* `stub_of_degree_three`: an interior vertex of degree `3` of a path has exactly
  one neighbour off the path's two edges at it.
-/

namespace Hypostructure.Graph.PathChords

open Hypostructure
open Hypostructure.Graph

universe u v

section Generic

variable {V : Type u} {H : SimpleGraph V}

/-- **A chord of a path closes a cycle of the length of its span plus one.** -/
theorem chord_cycle {a b u w : V} {p1 : H.Walk a u} {p2 : H.Walk u w} {p3 : H.Walk w b}
    (hp : (p1.append (p2.append p3)).IsPath) (adj : H.Adj u w) (long : 2 ≤ p2.length) :
    ∃ (c : H.Walk w w), c.IsCycle ∧ c.length = p2.length + 1 := by
  have hp23 : (p2.append p3).IsPath := hp.of_append_right
  have hp2 : p2.IsPath := hp23.of_append_left
  refine ⟨SimpleGraph.Walk.cons adj.symm p2, ?_, by simp⟩
  rw [SimpleGraph.Walk.cons_isCycle_iff]
  refine ⟨hp2, fun mem => ?_⟩
  have hsnd := hp2.eq_snd_of_mem_edges (w := w) (by rwa [Sym2.eq_swap] at mem)
  -- `p2` is a path from `u` to `w` whose second vertex is `w`: it has length 1
  cases p2 with
  | nil => simp at long
  | cons h q =>
    simp only [SimpleGraph.Walk.snd_cons] at hsnd
    subst hsnd
    have hq : q.IsPath := (SimpleGraph.Walk.cons_isPath_iff _ _).1 hp2 |>.1
    rw [SimpleGraph.Walk.isPath_iff_eq_nil] at hq
    subst hq
    simp at long

/-- **A chord of a path is a shortcut**: the walk `p₁ ++ chord ++ p₃` is a path
from the start to the end of `w`, of length `|p₁| + 1 + |p₃|`. -/
theorem chord_shortcut {a b u w : V} {p1 : H.Walk a u} {p2 : H.Walk u w} {p3 : H.Walk w b}
    (hp : (p1.append (p2.append p3)).IsPath) (adj : H.Adj u w) (long : 1 ≤ p2.length) :
    ∃ q : H.Walk a b, q.IsPath ∧ q.length = p1.length + 1 + p3.length ∧
      ∀ y, y ∈ q.support → y ∈ (p1.append (p2.append p3)).support := by
  refine ⟨p1.append (SimpleGraph.Walk.cons adj p3), ?_, by simp; omega, ?_⟩
  swap
  · intro y hy
    simp only [SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.support_cons,
      List.mem_cons] at hy ⊢
    rcases hy with h | h | h
    · exact Or.inl h
    · subst h; exact Or.inl p1.end_mem_support
    · exact Or.inr (Or.inr h)
  rw [SimpleGraph.Walk.isPath_def] at hp ⊢
  have hsup : (p1.append (p2.append p3)).support =
      p1.support ++ (p2.support.tail ++ p3.support.tail) := by
    simp [SimpleGraph.Walk.support_append]
  rw [hsup] at hp
  have hq : (p1.append (SimpleGraph.Walk.cons adj p3)).support = p1.support ++ p3.support := by
    simp [SimpleGraph.Walk.support_append]
  rw [hq]
  refine List.Nodup.sublist ?_ hp
  refine List.Sublist.append (List.Sublist.refl _) ?_
  have hv : w ∈ p2.support.tail := by
    cases p2 with
    | nil => simp at long
    | cons h q => simp [SimpleGraph.Walk.support_cons]
  have hcons : p3.support = w :: p3.support.tail := (SimpleGraph.Walk.cons_tail_support p3).symm
  conv_lhs => rw [hcons]
  exact List.Sublist.append (List.singleton_sublist.2 hv) (List.Sublist.refl _)

end Generic


/-! ## Chord predicates on a walk -/

section Predicates

variable {V : Type u} {H : SimpleGraph V}

/-- **`w` has no chord**: every decomposition `w = p₁ ++ p₂ ++ p₃` with `p₂ : u ⇝ v`
and `uv` an edge has `|p₂| ≤ 1` (`w` is an induced path). -/
def ChordFree {a b : V} (w : H.Walk a b) : Prop :=
  ∀ (u v : V) (p1 : H.Walk a u) (p2 : H.Walk u v) (p3 : H.Walk v b),
    w = p1.append (p2.append p3) → H.Adj u v → p2.length ≤ 1

/-- **Every chord of `w` has a span whose cycle length is not accepted**: every
decomposition with `uv` an edge and `|p₂| ≥ 2` has `|p₂| + 1` not accepted. -/
def ChordCycles (LengthOK : Nat → Prop) {a b : V} (w : H.Walk a b) : Prop :=
  ∀ (u v : V) (p1 : H.Walk a u) (p2 : H.Walk u v) (p3 : H.Walk v b),
    w = p1.append (p2.append p3) → H.Adj u v → 2 ≤ p2.length →
      ¬ LengthOK (p2.length + 1)

/-- A path of a shortest-path selection has no chord. -/
theorem chordFree_of_shortest {a b : V} (w : H.Walk a b) (hp : w.IsPath)
    (shortest : ∀ q : H.Walk a b, q.IsPath → w.length ≤ q.length) : ChordFree w := by
  intro u v p1 p2 p3 heq adj
  by_contra long
  have hp' : (p1.append (p2.append p3)).IsPath := heq ▸ hp
  obtain ⟨q, hq, hlen, -⟩ := chord_shortcut hp' adj (by omega)
  have := shortest q hq
  rw [heq] at this
  simp only [SimpleGraph.Walk.length_append] at this
  omega

/-- **On a graph with no accepted cycle, every chord of a path has an unaccepted
span.** -/
theorem chordCycles_of_avoids {LengthOK : Nat → Prop} {a b : V} (w : H.Walk a b)
    (hp : w.IsPath) (avoids : ¬ ∃ (c : V) (cy : H.Walk c c), cy.IsCycle ∧ LengthOK cy.length) :
    ChordCycles LengthOK w := by
  intro u v p1 p2 p3 heq adj long ok
  have hp' : (p1.append (p2.append p3)).IsPath := heq ▸ hp
  obtain ⟨c, hc, hlen⟩ := chord_cycle hp' adj long
  exact avoids ⟨v, c, hc, hlen ▸ ok⟩

end Predicates


/-! ## The stub of an interior cubic vertex -/

section Stub

variable {object : FiniteObject.{u}}

/-- **Every interior vertex of degree `3` of `w` has exactly one neighbour off the
path's two edges at it** (its stub): every decomposition with `m` between `l` and
`r`, `deg m = 3`, has a neighbour `s ∉ {l, r}` and no other. -/
def StubStructure {a b : object.Vertex} (w : object.graph.Walk a b) : Prop :=
  ∀ (l m r : object.Vertex) (p1 : object.graph.Walk a l) (h1 : object.graph.Adj l m)
    (h2 : object.graph.Adj m r) (p3 : object.graph.Walk r b),
    w = p1.append (SimpleGraph.Walk.cons h1 (SimpleGraph.Walk.cons h2 p3)) →
    object.degree m = 3 →
    ∃ s, object.graph.Adj m s ∧ s ≠ l ∧ s ≠ r ∧
      ∀ t, object.graph.Adj m t → t = l ∨ t = r ∨ t = s

theorem stub_of_path {a b : object.Vertex} (w : object.graph.Walk a b) (hp : w.IsPath) :
    StubStructure w := by
  intro l m r p1 h1 h2 p3 heq deg
  have hp' : (p1.append (SimpleGraph.Walk.cons h1 (SimpleGraph.Walk.cons h2 p3))).IsPath :=
    heq ▸ hp
  have hsuffix := hp'.of_append_right
  have lm : l ≠ m := h1.ne
  have mr : m ≠ r := h2.ne
  have lr : l ≠ r := by
    intro e
    subst e
    rw [SimpleGraph.Walk.cons_isPath_iff] at hsuffix
    have := hsuffix.1
    rw [SimpleGraph.Walk.cons_isPath_iff] at this
    exact hsuffix.2 (by simp [SimpleGraph.Walk.support_cons])
  rw [FiniteObject.degree_eq_ncard_neighborSet] at deg
  have lmem : l ∈ object.graph.neighborSet m := h1.symm
  have rmem : r ∈ object.graph.neighborSet m := h2
  haveI : Finite object.Vertex := by letI := object.vertices; infer_instance
  have fin : (object.graph.neighborSet m).Finite := Set.toFinite _
  -- a neighbour off `{l, r}`
  obtain ⟨s, hs, sl, sr⟩ : ∃ s, object.graph.Adj m s ∧ s ≠ l ∧ s ≠ r := by
    by_contra none
    push Not at none
    have sub : object.graph.neighborSet m ⊆ {l, r} := by
      intro t ht
      by_cases tl : t = l
      · simp [tl]
      · simp [none t ht tl]
    have := Set.ncard_le_ncard sub (Set.toFinite _)
    have h2' : ({l, r} : Set object.Vertex).ncard ≤ 2 := by
      have := Set.ncard_insert_le l ({r} : Set object.Vertex)
      simpa using this
    omega
  refine ⟨s, hs, sl, sr, fun t ht => ?_⟩
  by_contra none
  push Not at none
  obtain ⟨tl, tr, ts⟩ := none
  have sub : ({l, r, s, t} : Set object.Vertex) ⊆ object.graph.neighborSet m := by
    intro q hq
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact lmem
    · exact rmem
    · exact hs
    · exact ht
  have card4 : ({l, r, s, t} : Set object.Vertex).ncard = 4 := by
    rw [Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem, Set.ncard_pair]
    · exact fun h => ts h.symm
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨fun h => sr h.symm, fun h => tr h.symm⟩
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨lr, fun h => sl h.symm, fun h => tl h.symm⟩
  have := Set.ncard_le_ncard sub fin
  omega

/-- **Two paths through one cubic vertex share an edge there**: if `m` has degree
`3` and lies inside two paths, entered from `l`, `l'` and left towards `r`, `r'`,
then `{l, r} ∩ {l', r'} ≠ ∅` (three neighbours cannot hold four distinct ones). -/
def ShareEdge {a b a' b' : object.Vertex} (w : object.graph.Walk a b)
    (w' : object.graph.Walk a' b') : Prop :=
  ∀ (l m r l' r' : object.Vertex) (p1 : object.graph.Walk a l) (h1 : object.graph.Adj l m)
    (h2 : object.graph.Adj m r) (p3 : object.graph.Walk r b)
    (p1' : object.graph.Walk a' l') (h1' : object.graph.Adj l' m) (h2' : object.graph.Adj m r')
    (p3' : object.graph.Walk r' b'),
    w = p1.append (SimpleGraph.Walk.cons h1 (SimpleGraph.Walk.cons h2 p3)) →
    w' = p1'.append (SimpleGraph.Walk.cons h1' (SimpleGraph.Walk.cons h2' p3')) →
    object.degree m = 3 → (l = l' ∨ l = r' ∨ r = l' ∨ r = r')

theorem lr_ne_of_path {a b : object.Vertex} {l m r : object.Vertex}
    {p1 : object.graph.Walk a l} {h1 : object.graph.Adj l m} {h2 : object.graph.Adj m r}
    {p3 : object.graph.Walk r b}
    (hp : (p1.append (SimpleGraph.Walk.cons h1 (SimpleGraph.Walk.cons h2 p3))).IsPath) :
    l ≠ r := by
  have hsuffix := hp.of_append_right
  intro e
  subst e
  rw [SimpleGraph.Walk.cons_isPath_iff] at hsuffix
  have := hsuffix.1
  rw [SimpleGraph.Walk.cons_isPath_iff] at this
  exact hsuffix.2 (by simp [SimpleGraph.Walk.support_cons])

theorem shareEdge_of_paths {a b a' b' : object.Vertex} (w : object.graph.Walk a b)
    (w' : object.graph.Walk a' b') (hp : w.IsPath) (hp' : w'.IsPath) : ShareEdge w w' := by
  intro l m r l' r' p1 h1 h2 p3 p1' h1' h2' p3' heq heq' deg
  have hw : (p1.append (SimpleGraph.Walk.cons h1 (SimpleGraph.Walk.cons h2 p3))).IsPath :=
    heq ▸ hp
  have hw' : (p1'.append (SimpleGraph.Walk.cons h1' (SimpleGraph.Walk.cons h2' p3'))).IsPath :=
    heq' ▸ hp'
  have lr : l ≠ r := lr_ne_of_path hw
  have lr' : l' ≠ r' := lr_ne_of_path hw'
  by_contra none
  push Not at none
  obtain ⟨n1, n2, n3, n4⟩ := none
  haveI : Finite object.Vertex := by letI := object.vertices; infer_instance
  rw [FiniteObject.degree_eq_ncard_neighborSet] at deg
  have sub : ({l, r, l', r'} : Set object.Vertex) ⊆ object.graph.neighborSet m := by
    intro q hq
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact h1.symm
    · exact h2
    · exact h1'.symm
    · exact h2'
  have card4 : ({l, r, l', r'} : Set object.Vertex).ncard = 4 := by
    rw [Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem, Set.ncard_pair]
    · exact lr'
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨n3, n4⟩
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨lr, n1, n2⟩
  have := Set.ncard_le_ncard sub (Set.toFinite _)
  omega

end Stub


/-! ## Two internally disjoint paths close a cycle -/

section Ear

variable {V : Type u} {H : SimpleGraph V}

/-- **Ear lemma.**  Two paths `p : u ⇝ v` and `q : v ⇝ u` that meet only at their
ends, not both single edges, close a cycle of length `|p| + |q|`. -/
theorem ear_cycle {u v : V} (p : H.Walk u v) (q : H.Walk v u) (hp : p.IsPath) (hq : q.IsPath)
    (disj : ∀ y, y ∈ p.support → y ∈ q.support → y = u ∨ y = v)
    (hp1 : 1 ≤ p.length) (hq1 : 1 ≤ q.length) (nd : ¬ (p.length = 1 ∧ q.length = 1)) :
    ∃ c : H.Walk u u, c.IsCycle ∧ c.length = p.length + q.length := by
  cases p with
  | nil => simp at hp1
  | @cons _ x _ h p' =>
    have hcons := (SimpleGraph.Walk.cons_isPath_iff h p').1 hp
    have hp' : p'.IsPath := hcons.1
    have uNot : u ∉ p'.support := hcons.2
    have hqsup : q.support.Nodup := (SimpleGraph.Walk.isPath_def q).1 hq
    refine ⟨SimpleGraph.Walk.cons h (p'.append q), ?_, by simp; omega⟩
    rw [SimpleGraph.Walk.cons_isCycle_iff]
    have vNotTail : v ∉ q.support.tail := by
      have := hqsup
      rw [← SimpleGraph.Walk.cons_tail_support q] at this
      exact (List.nodup_cons.1 this).1
    have hpath : (p'.append q).IsPath := by
      rw [SimpleGraph.Walk.isPath_def, SimpleGraph.Walk.support_append]
      refine List.nodup_append.2 ⟨(SimpleGraph.Walk.isPath_def _).1 hp',
        hqsup.sublist (List.tail_sublist _), ?_⟩
      intro y hy1 z hz heq
      subst heq
      have hyq : y ∈ q.support := List.mem_of_mem_tail hz
      have hyp : y ∈ (SimpleGraph.Walk.cons h p').support := by
        simp [SimpleGraph.Walk.support_cons, hy1]
      rcases disj y hyp hyq with rfl | rfl
      · exact uNot hy1
      · exact vNotTail hz
    refine ⟨hpath, fun mem => ?_⟩
    rw [SimpleGraph.Walk.edges_append, List.mem_append] at mem
    rcases mem with m | m
    · exact uNot (SimpleGraph.Walk.fst_mem_support_of_mem_edges _ m)
    · have xq : x ∈ q.support := SimpleGraph.Walk.snd_mem_support_of_mem_edges _ m
      have xp : x ∈ (SimpleGraph.Walk.cons h p').support := by
        simp [SimpleGraph.Walk.support_cons]
      rcases disj x xp xq with hx | hx
      · exact h.ne hx.symm
      · subst hx
        -- `x = v`: `p'` is a path `v ⇝ v`, so `p` has length one; `q` starts with the edge to `u`
        have hp'nil : p'.length = 0 := by
          have := SimpleGraph.Walk.isPath_iff_eq_nil.1 hp'
          rw [this]; rfl
        have hsnd := hq.eq_snd_of_mem_edges (w := u) (by rwa [Sym2.eq_swap] at m)
        have hq1' : q.length = 1 := by
          cases q with
          | nil => simp at hq1
          | cons h2 q2 =>
            simp only [SimpleGraph.Walk.snd_cons] at hsnd
            subst hsnd
            have := ((SimpleGraph.Walk.cons_isPath_iff h2 q2).1 hq).1
            rw [SimpleGraph.Walk.isPath_iff_eq_nil] at this
            subst this
            rfl
        exact nd ⟨by simp [hp'nil], hq1'⟩

end Ear


/-! ## Hubs, closing vertices and rungs -/

section Connectors

variable {V : Type u} {H : SimpleGraph V}

theorem mem_decomp_support {a b u v : V} {p1 : H.Walk a u} {p2 : H.Walk u v} {p3 : H.Walk v b}
    {y : V} (hy : y ∈ p2.support) : y ∈ (p1.append (p2.append p3)).support := by
  simp only [SimpleGraph.Walk.mem_support_append_iff]
  exact Or.inr (Or.inl hy)

theorem ne_of_path_length {u v : V} {p : H.Walk u v} (hp : p.IsPath) (h1 : 1 ≤ p.length) :
    u ≠ v := by
  rintro rfl
  have := SimpleGraph.Walk.isPath_iff_eq_nil.1 hp
  subst this
  simp at h1

/-- **Hub cycles**: a vertex `h` off the path, adjacent to both ends of a segment
`p₂` (`|p₂| ≥ 1`), closes a cycle of length `|p₂| + 2`; such a length is not accepted. -/
def HubCycles (LengthOK : Nat → Prop) {a b : V} (w : H.Walk a b) : Prop :=
  ∀ (u v : V) (p1 : H.Walk a u) (p2 : H.Walk u v) (p3 : H.Walk v b) (h : V),
    w = p1.append (p2.append p3) → 1 ≤ p2.length → h ∉ w.support →
    H.Adj u h → H.Adj h v → ¬ LengthOK (p2.length + 2)

theorem hubCycles_of_avoids {LengthOK : Nat → Prop} {a b : V} (w : H.Walk a b)
    (hp : w.IsPath)
    (avoids : ¬ ∃ (c : V) (cy : H.Walk c c), cy.IsCycle ∧ LengthOK cy.length) :
    HubCycles LengthOK w := by
  intro u v p1 p2 p3 h heq long hnot huh hhv ok
  have hp' : (p1.append (p2.append p3)).IsPath := heq ▸ hp
  have hp2 : p2.IsPath := hp'.of_append_right.of_append_left
  have huv : u ≠ v := ne_of_path_length hp2 long
  have hvh : v ≠ h := hhv.ne.symm
  have hhu : h ≠ u := huh.ne.symm
  let q : H.Walk v u := SimpleGraph.Walk.cons hhv.symm (SimpleGraph.Walk.cons huh.symm .nil)
  have hq : q.IsPath := by
    rw [SimpleGraph.Walk.isPath_def]
    simp [q, SimpleGraph.Walk.support_cons, hvh, hhu, huv.symm]
  have disj : ∀ y, y ∈ p2.support → y ∈ q.support → y = u ∨ y = v := by
    intro y hy1 hy2
    simp only [q, SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hy2
    rcases hy2 with rfl | rfl | rfl
    · exact Or.inr rfl
    · exact absurd (heq ▸ mem_decomp_support (p1 := p1) (p3 := p3) hy1) hnot
    · exact Or.inl rfl
  obtain ⟨c, hc, hlen⟩ := ear_cycle p2 q hp2 hq disj long (by simp [q]) (by simp [q])
  exact avoids ⟨u, c, hc, by rw [hlen]; simpa [q] using ok⟩


/-- **A closing vertex** `x` off the path, adjacent to both ends: the whole path
closes a cycle of length `|w| + 2`, and every chord's shortcut path closes one of
length `|p₁| + |p₃| + 3`; neither length is accepted. -/
def ClosedCycles (LengthOK : Nat → Prop) {a b : V} (w : H.Walk a b) : Prop :=
  ∀ x : V, x ∉ w.support → H.Adj x a → H.Adj x b →
    (1 ≤ w.length → ¬ LengthOK (w.length + 2)) ∧
    ∀ (u v : V) (p1 : H.Walk a u) (p2 : H.Walk u v) (p3 : H.Walk v b),
      w = p1.append (p2.append p3) → H.Adj u v → 2 ≤ p2.length →
        ¬ LengthOK (p1.length + p3.length + 3)

theorem closedCycles_of_avoids {LengthOK : Nat → Prop} {a b : V} (w : H.Walk a b)
    (hp : w.IsPath)
    (avoids : ¬ ∃ (c : V) (cy : H.Walk c c), cy.IsCycle ∧ LengthOK cy.length) :
    ClosedCycles LengthOK w := by
  intro x hx hxa hxb
  have close : ∀ (q : H.Walk a b), q.IsPath → 1 ≤ q.length →
      (∀ y, y ∈ q.support → y ∈ w.support) → ¬ LengthOK (q.length + 2) := by
    intro q hq hq1 hsub ok
    have hab : a ≠ b := ne_of_path_length hq hq1
    let r : H.Walk b a := SimpleGraph.Walk.cons hxb.symm (SimpleGraph.Walk.cons hxa .nil)
    have hr : r.IsPath := by
      rw [SimpleGraph.Walk.isPath_def]
      simp [r, SimpleGraph.Walk.support_cons, hxb.ne.symm, hxa.ne, hab.symm]
    have disj : ∀ y, y ∈ q.support → y ∈ r.support → y = a ∨ y = b := by
      intro y hy1 hy2
      simp only [r, SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.mem_cons,
        List.not_mem_nil, or_false] at hy2
      rcases hy2 with rfl | rfl | rfl
      · exact Or.inr rfl
      · exact absurd (hsub _ hy1) hx
      · exact Or.inl rfl
    obtain ⟨c, hc, hlen⟩ := ear_cycle q r hq hr disj hq1 (by simp [r]) (by simp [r])
    exact avoids ⟨a, c, hc, by rw [hlen]; simpa [r] using ok⟩
  refine ⟨fun h1 => close w hp h1 (fun y hy => hy), ?_⟩
  intro u v p1 p2 p3 heq adj long
  have hp' : (p1.append (p2.append p3)).IsPath := heq ▸ hp
  obtain ⟨q, hq, hlen, hsub⟩ := chord_shortcut hp' adj (by omega)
  intro ok
  refine close q hq (by omega) (fun y hy => heq ▸ hsub y hy) ?_
  rw [hlen]
  have : p1.length + 1 + p3.length + 2 = p1.length + p3.length + 3 := by omega
  rw [this]; exact ok

/-- **Rung cycles**: two disjoint segments `p₂ : u ⇝ v` of `w₁` and `q₂ : c ⇝ d` of
`w₂` joined by two edges (`v c`, `d u`, or the crossed pair `v d`, `c u`) close a
cycle of length `|p₂| + |q₂| + 2`; that length is not accepted. -/
def RungCycles (LengthOK : Nat → Prop) {a₁ b₁ a₂ b₂ : V} (w₁ : H.Walk a₁ b₁)
    (w₂ : H.Walk a₂ b₂) : Prop :=
  ∀ (u v c d : V) (p1 : H.Walk a₁ u) (p2 : H.Walk u v) (p3 : H.Walk v b₁)
    (q1 : H.Walk a₂ c) (q2 : H.Walk c d) (q3 : H.Walk d b₂),
    w₁ = p1.append (p2.append p3) → w₂ = q1.append (q2.append q3) →
    1 ≤ p2.length → 1 ≤ q2.length →
    (∀ y, y ∈ p2.support → y ∈ q2.support → False) →
    ((H.Adj v c ∧ H.Adj d u) ∨ (H.Adj v d ∧ H.Adj c u)) →
    ¬ LengthOK (p2.length + q2.length + 2)

theorem rungCycles_of_avoids {LengthOK : Nat → Prop} {a₁ b₁ a₂ b₂ : V} (w₁ : H.Walk a₁ b₁)
    (w₂ : H.Walk a₂ b₂) (hp₁ : w₁.IsPath) (hp₂ : w₂.IsPath)
    (avoids : ¬ ∃ (c : V) (cy : H.Walk c c), cy.IsCycle ∧ LengthOK cy.length) :
    RungCycles LengthOK w₁ w₂ := by
  intro u v c d p1 p2 p3 q1 q2 q3 heq1 heq2 long1 long2 disjSeg rung ok
  have hp1' : (p1.append (p2.append p3)).IsPath := heq1 ▸ hp₁
  have hp2' : (q1.append (q2.append q3)).IsPath := heq2 ▸ hp₂
  have hp2 : p2.IsPath := hp1'.of_append_right.of_append_left
  have hq2 : q2.IsPath := hp2'.of_append_right.of_append_left
  have huv : u ≠ v := ne_of_path_length hp2 long1
  have hcd : c ≠ d := ne_of_path_length hq2 long2
  -- the closing path `v ⇝ u` through the second segment, in either orientation
  have build : ∀ (c' d' : V) (s : H.Walk c' d'), s.IsPath → s.length = q2.length →
      (∀ y, y ∈ s.support → y ∈ q2.support) → (∀ y, y ∈ q2.support → y ∈ s.support) →
      H.Adj v c' → H.Adj d' u → False := by
    intro c' d' s hs hslen hs1 hs2 h1 h2
    have cd' : c' ≠ d' := ne_of_path_length hs (by omega)
    let r : H.Walk v u := SimpleGraph.Walk.cons h1 (s.append (SimpleGraph.Walk.cons h2 .nil))
    have hvs : v ∉ s.support := fun hv => disjSeg v p2.end_mem_support (hs1 v hv)
    have hus : u ∉ s.support := fun hu => disjSeg u p2.start_mem_support (hs1 u hu)
    have hr : r.IsPath := by
      rw [SimpleGraph.Walk.isPath_def]
      simp only [r, SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_append,
        SimpleGraph.Walk.support_nil, List.tail_cons, List.nodup_cons, List.mem_append,
        List.mem_singleton, not_or]
      refine ⟨⟨hvs, fun hvu => huv hvu.symm⟩, ?_⟩
      refine List.nodup_append.2 ⟨(SimpleGraph.Walk.isPath_def _).1 hs, by simp, ?_⟩
      intro y hy z hz hyz
      simp only [List.mem_singleton] at hz
      subst hz; subst hyz
      exact hus hy
    have disj : ∀ y, y ∈ p2.support → y ∈ r.support → y = u ∨ y = v := by
      intro y hy1 hy2
      simp only [r, SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_append,
        SimpleGraph.Walk.support_nil, List.tail_cons, List.mem_cons, List.mem_append,
        List.not_mem_nil, or_false] at hy2
      rcases hy2 with h | h | h
      · exact Or.inr h
      · exact absurd (hs1 y h) (fun hq => disjSeg y hy1 hq)
      · exact Or.inl h
    obtain ⟨cy, hc, hlen⟩ := ear_cycle p2 r hp2 hr disj long1 (by simp [r])
      (by simp [r])
    apply avoids
    refine ⟨u, cy, hc, ?_⟩
    rw [hlen]
    have : p2.length + r.length = p2.length + q2.length + 2 := by simp [r, hslen]; omega
    rw [this]; exact ok
  rcases rung with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact build c d q2 hq2 rfl (fun y hy => hy) (fun y hy => hy) h1 h2
  · refine build d c q2.reverse hq2.reverse (by simp) ?_ ?_ h1 h2
    · intro y hy; simpa using hy
    · intro y hy; simpa using hy

end Connectors

end Hypostructure.Graph.PathChords
