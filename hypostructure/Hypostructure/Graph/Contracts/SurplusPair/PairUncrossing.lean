import Hypostructure.Graph.Contracts.SurplusPair.PairCoverage
import Hypostructure.Graph.PathUncrossing

/-!
# Contract lemmas: the uncrossing of the two connector routes of `[179]`

`lem:pair-system-realizability` uncrosses the response supports of the minimal
obstruction at their first and last common vertex.  At G the two oriented routes of
the obstruction's connector -- `forward : left.2 → right.1` and
`backward : right.2 → left.1` -- are paths of G, and the demand edges close them.
`Graph.PathUncrossing.exists_uncrossing` reroutes them at the first and last common
vertex, giving a path `left.2 → left.1` and a path `right.2 → right.1`, each of which
closes with its demand edge into a cycle of G with the exact length bookkeeping of the
rerouting.  If the routes are disjoint, the two routes and the two demand edges are
one cycle of length `|forward| + |backward| + 2`.  G has no accepted cycle, so these
lengths are not accepted.
-/

namespace Hypostructure.Graph.Contracts.SurplusPair

open Hypostructure
open Hypostructure.Graph.Strategy.Spine
open SimpleGraph

universe u

variable {data : Parameters} {object : Graph.FiniteObject.{u}}

/-- A path of length at least two closed by an edge is a cycle, one edge longer. -/
theorem cons_isCycle_of_path {V : Type*} {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) (hp : p.IsPath) (h2 : 2 ≤ p.length) (h : G.Adj v u) :
    (Walk.cons h p).IsCycle := by
  rw [Walk.cons_isCycle_iff]
  refine ⟨hp, fun hmem => ?_⟩
  cases p with
  | nil => simp at h2
  | @cons _ w _ h1 p' =>
      rw [Walk.isPath_def, Walk.support_cons, List.nodup_cons] at hp
      rw [Walk.edges_cons, List.mem_cons] at hmem
      rcases hmem with heq | hmem'
      · have hvw : v = w := by
          rcases Sym2.eq_iff.mp heq with ⟨hv, hu⟩ | ⟨hv, hu⟩
          · exact absurd hu (G.ne_of_adj h1)
          · exact hv
        subst hvw
        have : p'.length = 0 := by
          have hp' : p'.IsPath := by rw [Walk.isPath_def]; exact hp.2
          have := Walk.isPath_iff_eq_nil.mp hp'
          rw [this]; rfl
        simp at h2
        omega
      · exact hp.1 (Walk.snd_mem_support_of_mem_edges _ hmem')

/-- **A path closed by its demand edge is not an accepted cycle.**  A path
`u → v` of G with `2 ≤ length` and `v ~ u` closes into a cycle of length
`length + 1`; G has none accepted. -/
theorem not_accepted_of_path
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object) {u v : object.Vertex}
    (p : object.graph.Walk u v) (hp : p.IsPath) (h2 : 2 ≤ p.length)
    (h : object.graph.Adj v u) : ¬ data.LengthOK (p.length + 1) := by
  intro ok
  exact avoids ⟨{ vertex := v
                  walk := Walk.cons h p
                  isCycle := cons_isCycle_of_path p hp h2 h
                  length_ok := by simpa using ok }⟩

/-- A path between distinct vertices has positive length. -/
theorem length_pos_of_adj {V : Type*} {G : SimpleGraph V} {u v : V} (p : G.Walk u v)
    (h : G.Adj v u) : 0 < p.length := by
  rcases Nat.eq_zero_or_pos p.length with h0 | h0
  · exact absurd (Walk.eq_of_length_eq_zero h0) (G.ne_of_adj h).symm
  · exact h0

/-- **A closed-off path has length one or a non-accepted length.** -/
theorem length_one_or_not_accepted
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object) {u v : object.Vertex}
    (p : object.graph.Walk u v) (hp : p.IsPath) (h : object.graph.Adj v u) :
    p.length = 1 ∨ ¬ data.LengthOK (p.length + 1) := by
  have pos := length_pos_of_adj p h
  by_cases one : p.length = 1
  · exact Or.inl one
  · exact Or.inr (not_accepted_of_path avoids p hp (by omega) h)

/-- **The crossing case.**  If the forward and backward connector routes of a return
system share a vertex, their uncrossing at the first and last common vertex gives two
paths `left.2 → left.1` and `right.2 → right.1` of lengths `l₁ ≤ |forward| + |backward|`
and `l₂ ≤ |forward| + |backward|` that close with the demand edges: each has length one
or a non-accepted `l + 1`. -/
theorem crossing_lengths_not_accepted
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (returns : PairDemandReturns data object)
    (routes : PairDemandReturns.ConnectorRoutes returns)
    (hit : ∃ v ∈ routes.forward.support, v ∈ routes.backward.support) :
    ∃ l₁ l₂ : ℕ, l₁ ≤ routes.forward.length + routes.backward.length ∧
      l₂ ≤ routes.forward.length + routes.backward.length ∧
      (l₁ = 1 ∨ ¬ data.LengthOK (l₁ + 1)) ∧ (l₂ = 1 ∨ ¬ data.LengthOK (l₂ + 1)) := by
  obtain ⟨x, y, P₁, P₂, P₃, P₄, Q₁, Q₂, Q₃, Q₄, hPx, hPy, hQx, hQy, -, -, -, -, hW₁, hW₂⟩ :=
    PathUncrossing.exists_uncrossing routes.forward routes.backward routes.forward_isPath
      routes.backward_isPath hit
  have lenP₁ : P₁.length ≤ routes.forward.length := by
    rw [hPx, Walk.length_append]; omega
  have lenQ₂ : Q₂.length ≤ routes.backward.length := by
    rw [hQx, Walk.length_append]; omega
  have lenQ₃ : Q₃.length ≤ routes.backward.length := by
    rw [hQy, Walk.length_append]; omega
  have lenP₄ : P₄.length ≤ routes.forward.length := by
    rw [hPy, Walk.length_append]; omega
  refine ⟨(P₁.append Q₂).length, (Q₃.append P₄).length, ?_, ?_,
    length_one_or_not_accepted avoids _ hW₁ returns.leftDemand_adj,
    length_one_or_not_accepted avoids _ hW₂ returns.rightDemand_adj⟩
  · rw [Walk.length_append]; omega
  · rw [Walk.length_append]; omega

/-- **The disjoint case.**  If the two connector routes are vertex-disjoint, they
close with the two demand edges into a cycle of length `|forward| + |backward| + 2`;
the rerouted path has length one or a non-accepted `l + 1`. -/
theorem disjoint_closing_not_accepted
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (returns : PairDemandReturns data object)
    (routes : PairDemandReturns.ConnectorRoutes returns)
    (disjoint : ∀ v ∈ routes.forward.support, v ∉ routes.backward.support) :
    routes.forward.length + routes.backward.length + 1 = 1 ∨
      ¬ data.LengthOK (routes.forward.length + routes.backward.length + 2) := by
  have hR : object.graph.Adj returns.rightDemand.1 returns.rightDemand.2 :=
    returns.rightDemand_adj
  let closing : object.graph.Walk returns.rightDemand.1 returns.leftDemand.1 :=
    Walk.cons hR routes.backward
  have closingPath : closing.IsPath := by
    rw [Walk.cons_isPath_iff]
    exact ⟨routes.backward_isPath, fun mem => disjoint _ (by simp) mem⟩
  have whole : (routes.forward.append closing).IsPath :=
    PathUncrossing.isPath_append_of_inter routes.forward_isPath closingPath
      (fun z hz hz' => by
        rcases List.mem_cons.mp (by simpa [closing] using hz') with rfl | hb
        · rfl
        · exact absurd hb (disjoint _ hz))
  have len : (routes.forward.append closing).length =
      routes.forward.length + routes.backward.length + 1 := by
    simp [closing, Walk.length_append]; ring
  have := length_one_or_not_accepted avoids _ whole returns.leftDemand_adj
  rw [len] at this
  exact this

/-- Node `[179]`: the uncrossing of G's canonical connector routes. -/
theorem pairUncrossing_of_demandReturns
    (returns : PairDemandReturnsStatement data object)
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object) :
    PairUncrossingStatement data object := by
  obtain ⟨returns, selected⟩ := returns
  exact ⟨returns, selected,
    fun disjoint => disjoint_closing_not_accepted avoids returns _ disjoint,
    fun hit => crossing_lengths_not_accepted avoids returns _ hit⟩

end Hypostructure.Graph.Contracts.SurplusPair
