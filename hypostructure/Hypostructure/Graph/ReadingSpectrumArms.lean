import Hypostructure.Graph.GluedReadingMaps

/-!
# Outside returns of a support

A vertex of degree exactly the baseline in a support `Z` of G with an outside
neighbour has an outside return to another vertex of `Z` (on a connected
bridgeless G with no proper baseline subgraph).  Statements about G's own
walks; no boundaried context other than `G − Z` is read.
-/

namespace Hypostructure.Graph.ReadingSpectrumArms

open Hypostructure
open Hypostructure.Graph
open Hypostructure.Graph.Strategy.InterfaceReplacement

universe u

section OutsideReturn

open Classical

/-- **A cubic vertex of a support has an outside return to another vertex of
the support** (vocabulary-free; `single_boundary_shape` applied to
`S = W ∪ {a}`, `W` the outside component of `y`).  With `δ ≥ 3`, no proper
baseline, no bridge and `G` connected: if `a ∈ Z` is cubic with an outside
neighbour `y`, and `Z ∖ {a} ≠ ∅`, then the outside component of `y` has a
neighbour `b' ∈ Z ∖ {a}`. -/
theorem cubic_outside_return {G : FiniteObject.{u}}
    (baseline : MinimumDegreeAtLeast 3 G)
    (noProper : ∀ sub : ProperSubgraph G, ¬ MinimumDegreeAtLeast 3 sub.value)
    (bridgeless : ∀ contraction : EdgeContraction G, contraction.HasReturn)
    (connected : G.graph.Connected)
    {Z : Finset G.Vertex} {a y z : G.Vertex} (aZ : a ∈ Z) (cubic : G.degree a = 3)
    (ay : G.graph.Adj a y) (yZ : y ∉ Z) (zZ : z ∈ Z) (za : z ≠ a) :
    ∃ v b', v ∉ Z ∧ G.graph.Adj v b' ∧ b' ∈ Z ∧ b' ≠ a ∧
      ∃ p : G.graph.Walk y v, ∀ x ∈ p.support, x ∉ Z := by
  letI : FinEnum G.Vertex := G.vertices
  let W : Finset G.Vertex := Finset.univ.filter fun v => ∃ p : G.graph.Walk y v, ∀ x ∈ p.support, x ∉ Z
  have yW : y ∈ W := by
    simp only [W, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨.nil, by simpa using yZ⟩
  have Wout : ∀ v ∈ W, v ∉ Z := by
    intro v hv
    simp only [W, Finset.mem_filter, Finset.mem_univ, true_and] at hv
    obtain ⟨p, hp⟩ := hv
    exact hp v p.end_mem_support
  by_contra none
  push Not at none
  -- every `Z`-neighbour of `W` is `a`
  have onlyA : ∀ v ∈ W, ∀ x, G.graph.Adj v x → x ∈ Z → x = a := by
    intro v hv x adj xZ
    by_contra xa
    have hv' := hv
    simp only [W, Finset.mem_filter, Finset.mem_univ, true_and] at hv'
    obtain ⟨p, hp⟩ := hv'
    obtain ⟨u, hu, uZ⟩ := none v x (Wout v hv) adj xZ xa p
    exact hp u hu uZ
  have closed : ∀ v ∈ W, ∀ x, G.graph.Adj v x → x ∉ Z → x ∈ W := by
    intro v hv x adj xZ
    simp only [W, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    obtain ⟨p, hp⟩ := hv
    refine ⟨p.concat adj, ?_⟩
    intro u hu
    rw [SimpleGraph.Walk.support_concat, List.mem_append,
      List.mem_singleton] at hu
    rcases hu with hu | rfl
    · exact hp u hu
    · exact xZ
  let S : Finset G.Vertex := insert a W
  have nbrS : ∀ v ∈ W, ∀ x, G.graph.Adj v x → x ∈ S := by
    intro v hv x adj
    by_cases xZ : x ∈ Z
    · rw [onlyA v hv x adj xZ]; exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (closed v hv x adj xZ)
  have zS : z ∉ S := by
    intro h
    rcases Finset.mem_insert.1 h with e | h
    · exact za e
    · exact Wout z h zZ
  have single : SupportAtom.cutBoundary G S = {a} := by
    ext v
    simp only [SupportAtom.mem_cutBoundary_iff, Finset.mem_singleton]
    constructor
    · rintro ⟨vS, x, adj, xS⟩
      rcases Finset.mem_insert.1 vS with e | vW
      · exact e
      · exact absurd (nbrS v vW x adj) xS
    · rintro rfl
      refine ⟨Finset.mem_insert_self _ _, ?_⟩
      obtain ⟨p⟩ := connected.preconnected y z
      obtain ⟨d, -, dIn, dOut⟩ := p.exists_boundary_dart (S : Set G.Vertex)
        (Finset.mem_insert_of_mem yW) zS
      rcases Finset.mem_insert.1 dIn with e | dW
      · exact ⟨d.snd, e ▸ d.adj, dOut⟩
      · exact absurd (nbrS _ dW _ d.adj) dOut
  obtain ⟨inn, out⟩ := GluedReadings.single_boundary_shape G baseline noProper bridgeless S a
    single (Finset.mem_insert_of_mem yW) (fun e => yZ (e ▸ aZ)) ⟨z, zS⟩
  have split := GluedReadings.degree_eq_inside_add_outside G S a
  omega

/-- The walk `a — y ⋯ v — b'` with outside interior bypasses to a path of
length `≥ 2` with outside interior. -/
theorem outside_path_of_walk {G : FiniteObject.{u}} {Z : Finset G.Vertex}
    {a y v b' : G.Vertex} (aZ : a ∈ Z) (bZ : b' ∈ Z) (ab : a ≠ b')
    (ay : G.graph.Adj a y) (p : G.graph.Walk y v) (hp : ∀ x ∈ p.support, x ∉ Z)
    (vb : G.graph.Adj v b') :
    ∃ τ : G.graph.Walk a b', τ.IsPath ∧ (∀ x ∈ τ.support, x ∉ Z ∨ x = a ∨ x = b') ∧
      2 ≤ τ.length := by
  let W : G.graph.Walk a b' := .cons ay (p.concat vb)
  have Wsupp : ∀ x ∈ W.support, x ∉ Z ∨ x = a ∨ x = b' := by
    intro x hx
    simp only [W, SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_concat,
      List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | hx | rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inl (hp x hx)
    · exact Or.inr (Or.inr rfl)
  refine ⟨W.bypass, W.bypass_isPath, fun x hx => Wsupp x (W.support_bypass_subset_support hx), ?_⟩
  by_contra lt
  have pos : 1 ≤ W.bypass.length := by
    rcases h : W.bypass with _ | ⟨_, _⟩
    · exact absurd rfl ab
    · simp
  have one : W.bypass.length = 1 := by omega
  have mem : s(a, b') ∈ W.bypass.edges := by
    rcases h : W.bypass with _ | ⟨h1, r⟩
    · exact absurd rfl ab
    · rw [h] at one
      cases r with
      | nil => simp
      | cons _ _ => simp at one
  have memW := W.edges_bypass_subset_edges mem
  simp only [W, SimpleGraph.Walk.edges_cons, List.mem_cons] at memW
  rcases memW with e | e
  · rcases Sym2.eq_iff.1 e with ⟨-, h⟩ | ⟨h, -⟩
    · exact hp y p.start_mem_support (h ▸ bZ)
    · exact hp y p.start_mem_support (h ▸ aZ)
  · have := (p.concat vb).fst_mem_support_of_mem_edges e
    rw [SimpleGraph.Walk.support_concat, List.mem_append, List.mem_singleton] at this
    rcases this with h | h
    · exact hp a h aZ
    · exact ab h

end OutsideReturn

end Hypostructure.Graph.ReadingSpectrumArms
