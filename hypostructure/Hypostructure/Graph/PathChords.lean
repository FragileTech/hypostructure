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
    ∃ q : H.Walk a b, q.IsPath ∧ q.length = p1.length + 1 + p3.length := by
  refine ⟨p1.append (SimpleGraph.Walk.cons adj p3), ?_, by simp; omega⟩
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
  obtain ⟨q, hq, hlen⟩ := chord_shortcut hp' adj (by omega)
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

end Stub

end Hypostructure.Graph.PathChords
