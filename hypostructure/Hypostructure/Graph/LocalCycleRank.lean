import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Hypostructure.Graph.WindowRemainder

/-!
# Local cycle rank of a region

`lem:cycle-rank` (ledger key `cycleRankConstraint`) gives the global bound
`2β(G) ≥ n + 2`.  The residuals carry regions `S ⊆ V(G)`: the remainder `R`
and its pieces (route 8), `U` (pair Type B), `Z` (`[144a]`), `Y` (Type B
sublinear), `R0` (`[54]`), the entry piece `X` (route-8 quotient) and the
overlap support (pair conditional).  This module supplies the local form of
the cycle rank on such a region, for any finite simple graph:

* `β(G[S]) = e(S) − |S| + c(S)` (`regionCycleRank`), with `c(S)` the number
  of connected components of `G[S]`;
* the handshake on a region, `Σ_{v∈S} deg v = 2 e(S) + |∂S|`
  (`sum_degree_region`);
* near-cubic form: with every vertex of `S` of degree `≥ 3` and
  `σ_S = Σ_{v∈S} (deg v − 3)`, the exact identity
  `2 β(G[S]) = |S| + σ_S − |∂S| + 2 c(S)` (`two_mul_regionCycleRank`);
* additivity over `V = S ⊔ Sᶜ`:
  `β(G) = β(G[S]) + β(G[Sᶜ]) + |∂S| − c(S) − c(Sᶜ) + c(G)`
  (`cycleRank_eq_add`), specialised to windows `W` and remainder `R`;
* thin pieces: if every component of `G[S]` sends at least two edges out,
  `2 c(S) ≤ |∂S|`, hence `2 β(G[S]) ≤ |S| + σ_S` (`two_mul_regionCycleRank_le_of_thin`);
* the cross rank `β(G) − β(G[S]) − β(G[Sᶜ]) = |∂S| − c(S) − c(Sᶜ) + c(G)`
  (`crossRank_eq`): the part of the cycle rank of `G` not carried inside
  either side, i.e. the rank that every cycle basis of `G` must spend on
  cycles using an edge of `∂S`.

Cycle ranks are integers; nothing here uses truncated subtraction.
-/

namespace Hypostructure.Graph

open Finset

universe u

namespace LocalCycleRank

variable {V : Type u} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

/-- `e(S)`: the number of edges of the induced subgraph `G[S]`. -/
noncomputable def regionEdgeCount (S : Finset V) : ℕ :=
  #(G.induce (S : Set V)).edgeFinset

/-- `c(S)`: the number of connected components of `G[S]`. -/
noncomputable def regionComponents (S : Finset V) : ℕ :=
  Nat.card (G.induce (S : Set V)).ConnectedComponent

/-- `β(G[S]) = e(S) − |S| + c(S)`. -/
noncomputable def regionCycleRank (S : Finset V) : ℤ :=
  (regionEdgeCount G S : ℤ) - #S + regionComponents G S

/-- `β(G) = e(G) − |V| + c(G)`. -/
noncomputable def cycleRank : ℤ :=
  (#G.edgeFinset : ℤ) - Fintype.card V + Nat.card G.ConnectedComponent

/-- `∂S`, oriented outwards: the darts leaving `S`.  Each edge of the edge
boundary is the underlying edge of exactly one of them
(`card_boundaryEdges`). -/
noncomputable def boundaryDarts (S : Finset V) : Finset G.Dart :=
  univ.filter fun dart => dart.fst ∈ S ∧ dart.snd ∉ S

/-- `∂S` as a set of edges of `G`. -/
noncomputable def boundaryEdges (S : Finset V) : Finset (Sym2 V) :=
  (boundaryDarts G S).image SimpleGraph.Dart.edge

/-- `σ_S = Σ_{v∈S} (deg v − 3)`: the near-cubic excess of the region. -/
noncomputable def regionExcess (S : Finset V) : ℕ :=
  ∑ v ∈ S, (G.degree v - 3)

/-- The cross rank `β(G) − β(G[S]) − β(G[Sᶜ])`. -/
noncomputable def crossRank (S : Finset V) : ℤ :=
  cycleRank G - regionCycleRank G S - regionCycleRank G Sᶜ

theorem mem_boundaryDarts {S : Finset V} {dart : G.Dart} :
    dart ∈ boundaryDarts G S ↔ dart.fst ∈ S ∧ dart.snd ∉ S := by
  simp [boundaryDarts]

theorem card_boundaryEdges (S : Finset V) :
    #(boundaryEdges G S) = #(boundaryDarts G S) := by
  unfold boundaryEdges
  apply card_image_of_injOn
  intro left leftMem right rightMem same
  simp only [mem_coe, mem_boundaryDarts] at leftMem rightMem
  rcases (SimpleGraph.dart_edge_eq_iff left right).mp same with h | h
  · exact h
  · exfalso
    have : left.fst = right.snd := by rw [h]; rfl
    exact rightMem.2 (this ▸ leftMem.1)

/-- A dart leaving `S` is a dart entering `Sᶜ` reversed: `|∂S| = |∂Sᶜ|`. -/
theorem card_boundaryDarts_compl (S : Finset V) :
    #(boundaryDarts G Sᶜ) = #(boundaryDarts G S) := by
  apply card_nbij' SimpleGraph.Dart.symm SimpleGraph.Dart.symm
  · intro dart member
    simp only [mem_coe, mem_boundaryDarts, mem_compl, not_not] at member ⊢
    exact ⟨member.2, member.1⟩
  · intro dart member
    simp only [mem_coe, mem_boundaryDarts, mem_compl, not_not] at member ⊢
    exact ⟨member.2, member.1⟩
  · intro dart _
    exact SimpleGraph.Dart.symm_symm dart
  · intro dart _
    exact SimpleGraph.Dart.symm_symm dart

/-- The darts leaving `S` at a vertex `v ∈ S` are its neighbours outside `S`. -/
theorem card_boundaryDarts_eq_sum (S : Finset V) :
    #(boundaryDarts G S) = ∑ v ∈ S, #((G.neighborFinset v).filter (· ∉ S)) := by
  rw [card_eq_sum_card_fiberwise (f := fun dart : G.Dart => dart.fst) (t := S)
    (fun dart member => ((mem_boundaryDarts G).mp member).1)]
  apply sum_congr rfl
  intro v vMem
  refine card_bij (fun dart _ => dart.snd) ?_ ?_ ?_
  · intro dart member
    simp only [mem_filter, mem_boundaryDarts] at member
    simp only [mem_filter, SimpleGraph.mem_neighborFinset]
    refine ⟨?_, member.1.2⟩
    rw [← member.2]
    exact dart.adj
  · intro left leftMem right rightMem same
    simp only [mem_filter, mem_boundaryDarts] at leftMem rightMem
    exact SimpleGraph.Dart.ext left right (Prod.ext (leftMem.2.trans rightMem.2.symm) same)
  · intro w member
    simp only [mem_filter, SimpleGraph.mem_neighborFinset] at member
    refine ⟨⟨(v, w), member.1⟩, ?_, rfl⟩
    simp [mem_boundaryDarts, vMem, member.2]

/-- The degree of `v ∈ S` splits into its degree in `G[S]` and its number of
neighbours outside `S`. -/
theorem degree_eq_induce_add (S : Finset V) (v : (S : Set V)) :
    G.degree v = (G.induce (S : Set V)).degree v +
      #((G.neighborFinset v).filter (· ∉ S)) := by
  have split := card_filter_add_card_filter_not
    (s := G.neighborFinset v) (p := (· ∈ S))
  have inside : (G.induce (S : Set V)).degree v =
      #((G.neighborFinset v).filter (· ∈ S)) := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree,
      ← card_map (Function.Embedding.subtype (· ∈ (S : Set V)))]
    congr 1
    ext w
    simp [SimpleGraph.mem_neighborFinset]
  rw [inside, ← SimpleGraph.card_neighborFinset_eq_degree, ← split]

/-- **Handshake on a region**: `Σ_{v∈S} deg v = 2 e(S) + |∂S|`. -/
theorem sum_degree_region (S : Finset V) :
    ∑ v ∈ S, G.degree v = 2 * regionEdgeCount G S + #(boundaryDarts G S) := by
  rw [card_boundaryDarts_eq_sum, regionEdgeCount,
    ← SimpleGraph.sum_degrees_eq_twice_card_edges]
  have membership : ∀ v, v ∈ S ↔ v ∈ (S : Set V) := fun v => by simp
  rw [sum_subtype S membership, sum_subtype S membership
    (fun v => #((G.neighborFinset v).filter (· ∉ S))), ← sum_add_distrib]
  exact sum_congr rfl fun v _ => degree_eq_induce_add G S v

omit [DecidableEq V] in
/-- `Σ_{v∈S} deg v = 3|S| + σ_S` when every vertex of `S` has degree `≥ 3`. -/
theorem sum_degree_eq_three_mul_add_excess (S : Finset V)
    (degreeThree : ∀ v ∈ S, 3 ≤ G.degree v) :
    ∑ v ∈ S, G.degree v = 3 * #S + regionExcess G S := by
  unfold regionExcess
  rw [mul_comm, ← smul_eq_mul, ← sum_const, ← sum_add_distrib]
  exact sum_congr rfl fun v member => (Nat.add_sub_of_le (degreeThree v member)).symm

/-- **Near-cubic local cycle rank**: with every vertex of `S` of degree at
least three, `2 β(G[S]) = |S| + σ_S − |∂S| + 2 c(S)`. -/
theorem two_mul_regionCycleRank (S : Finset V)
    (degreeThree : ∀ v ∈ S, 3 ≤ G.degree v) :
    2 * regionCycleRank G S =
      (#S : ℤ) + regionExcess G S - #(boundaryDarts G S) +
        2 * regionComponents G S := by
  have handshake := sum_degree_region G S
  rw [sum_degree_eq_three_mul_add_excess G S degreeThree] at handshake
  unfold regionCycleRank
  have cast : ((3 * #S + regionExcess G S : ℕ) : ℤ) =
      ((2 * regionEdgeCount G S + #(boundaryDarts G S) : ℕ) : ℤ) := by
    rw [handshake]
  push_cast at cast
  linarith

/-- **Cycles carried by a region**: the local rank in terms of the boundary.
A region with `|∂S| < |S| + σ_S` carries at least
`(|S| + σ_S − |∂S|)/2 + c(S)` independent cycles of `G[S]`; this is the
same identity read as a lower bound. -/
theorem regionCycleRank_ge (S : Finset V)
    (degreeThree : ∀ v ∈ S, 3 ≤ G.degree v) :
    (#S : ℤ) + regionExcess G S - #(boundaryDarts G S) +
        2 * regionComponents G S ≤ 2 * regionCycleRank G S :=
  (two_mul_regionCycleRank G S degreeThree).ge

/-- Parity of the boundary: `|∂S| ≡ |S| + σ_S (mod 2)`. -/
theorem boundary_parity (S : Finset V)
    (degreeThree : ∀ v ∈ S, 3 ≤ G.degree v) :
    (#(boundaryDarts G S) : ℤ) ≡ #S + regionExcess G S [ZMOD 2] := by
  have h := two_mul_regionCycleRank G S degreeThree
  exact Int.modEq_iff_dvd.mpr
    ⟨regionCycleRank G S - regionComponents G S, by linarith⟩

omit [DecidableEq V] [DecidableRel G.Adj] in
/-- A nonempty region has at least one component. -/
theorem one_le_regionComponents {S : Finset V} (nonempty : S.Nonempty) :
    1 ≤ regionComponents G S := by
  obtain ⟨v, member⟩ := nonempty
  haveI : Nonempty (G.induce (S : Set V)).ConnectedComponent :=
    ⟨(G.induce (S : Set V)).connectedComponentMk ⟨v, by simpa using member⟩⟩
  exact Nat.one_le_iff_ne_zero.mpr (Nat.card_ne_zero.mpr ⟨inferInstance, inferInstance⟩)

/-- **Edge additivity over `V = S ⊔ Sᶜ`**: `e(G) = e(S) + e(Sᶜ) + |∂S|`. -/
theorem card_edgeFinset_eq_add (S : Finset V) :
    #G.edgeFinset = regionEdgeCount G S + regionEdgeCount G Sᶜ +
      #(boundaryDarts G S) := by
  have total := G.sum_degrees_eq_twice_card_edges
  rw [← sum_add_sum_compl S, sum_degree_region, sum_degree_region,
    card_boundaryDarts_compl] at total
  omega

/-- **Additivity of the cycle rank over `V = S ⊔ Sᶜ`**:
`β(G) = β(G[S]) + β(G[Sᶜ]) + |∂S| − c(S) − c(Sᶜ) + c(G)`. -/
theorem cycleRank_eq_add (S : Finset V) :
    cycleRank G = regionCycleRank G S + regionCycleRank G Sᶜ +
      #(boundaryDarts G S) - regionComponents G S - regionComponents G Sᶜ +
        Nat.card G.ConnectedComponent := by
  have edges := card_edgeFinset_eq_add G S
  have vertices : #S + #Sᶜ = Fintype.card V := card_add_card_compl S
  unfold cycleRank regionCycleRank
  have edgesZ : (#G.edgeFinset : ℤ) = regionEdgeCount G S +
      regionEdgeCount G Sᶜ + #(boundaryDarts G S) := by exact_mod_cast edges
  have verticesZ : (#S : ℤ) + #Sᶜ = Fintype.card V := by exact_mod_cast vertices
  linarith

/-- **Cross rank**: `β(G) − β(G[S]) − β(G[Sᶜ]) = |∂S| − c(S) − c(Sᶜ) + c(G)`.
Cycles lying in `G[S]` or in `G[Sᶜ]` span a subspace of the cycle space of `G`
of dimension `β(G[S]) + β(G[Sᶜ])`, so this is the number of independent
cycles of `G` that a cycle basis must spend on cycles using an edge of `∂S`. -/
theorem crossRank_eq (S : Finset V) :
    crossRank G S = #(boundaryDarts G S) - regionComponents G S -
      regionComponents G Sᶜ + Nat.card G.ConnectedComponent := by
  unfold crossRank
  rw [cycleRank_eq_add G S]
  ring

/-- For connected `G` the cross rank is `|∂S| − c(S) − c(Sᶜ) + 1`. -/
theorem crossRank_eq_of_connected (S : Finset V) (connected : G.Connected) :
    crossRank G S = #(boundaryDarts G S) - regionComponents G S -
      regionComponents G Sᶜ + 1 := by
  rw [crossRank_eq]
  haveI := connected.preconnected.subsingleton_connectedComponent
  haveI : Nonempty G.ConnectedComponent :=
    ⟨G.connectedComponentMk connected.nonempty.some⟩
  have : Nat.card G.ConnectedComponent = 1 := Nat.card_unique
  rw [this]
  push_cast
  ring

/-! ### Thin pieces -/

/-- The darts of `∂S` whose tail lies in the component `K` of `G[S]`. -/
noncomputable def componentBoundaryDarts (S : Finset V)
    (K : (G.induce (S : Set V)).ConnectedComponent) : Finset G.Dart := by
  classical
  exact (boundaryDarts G S).filter fun dart =>
    ∃ inside : dart.fst ∈ (S : Set V),
      (G.induce (S : Set V)).connectedComponentMk ⟨dart.fst, inside⟩ = K

/-- **Thin regions**: if every component of `G[S]` sends at least two edges
out of `S` (the thin-remainder shape of route 8), then `2 c(S) ≤ |∂S|`. -/
theorem two_mul_regionComponents_le_of_thin (S : Finset V)
    (thin : ∀ K, 2 ≤ #(componentBoundaryDarts G S K)) :
    2 * regionComponents G S ≤ #(boundaryDarts G S) := by
  classical
  letI : Fintype (G.induce (S : Set V)).ConnectedComponent := Fintype.ofFinite _
  have disjoint : ((univ : Finset (G.induce (S : Set V)).ConnectedComponent) : Set _).PairwiseDisjoint
      (componentBoundaryDarts G S) := by
    intro K _ L _ distinct
    refine disjoint_left.mpr ?_
    intro dart inK inL
    simp only [componentBoundaryDarts, mem_filter] at inK inL
    obtain ⟨_, ⟨insideK, hK⟩⟩ := inK
    obtain ⟨_, ⟨insideL, hL⟩⟩ := inL
    exact distinct (hK.symm.trans hL)
  have covered : (univ.biUnion (componentBoundaryDarts G S)) ⊆ boundaryDarts G S := by
    intro dart member
    obtain ⟨K, _, inK⟩ := mem_biUnion.mp member
    simp only [componentBoundaryDarts, mem_filter] at inK
    exact inK.1
  calc 2 * regionComponents G S
      = ∑ _K : (G.induce (S : Set V)).ConnectedComponent, 2 := by
        rw [sum_const, card_univ, smul_eq_mul, regionComponents,
          Nat.card_eq_fintype_card, mul_comm]
    _ ≤ ∑ K, #(componentBoundaryDarts G S K) := sum_le_sum fun K _ => thin K
    _ = #(univ.biUnion (componentBoundaryDarts G S)) := (card_biUnion disjoint).symm
    _ ≤ #(boundaryDarts G S) := card_le_card covered

/-- **Cycle rank of a thin near-cubic region**: `2 β(G[S]) ≤ |S| + σ_S`. -/
theorem two_mul_regionCycleRank_le_of_thin (S : Finset V)
    (degreeThree : ∀ v ∈ S, 3 ≤ G.degree v)
    (thin : ∀ K, 2 ≤ #(componentBoundaryDarts G S K)) :
    2 * regionCycleRank G S ≤ (#S : ℤ) + regionExcess G S := by
  have h := two_mul_regionCycleRank G S degreeThree
  have c : ((2 * regionComponents G S : ℕ) : ℤ) ≤ #(boundaryDarts G S) :=
    by exact_mod_cast two_mul_regionComponents_le_of_thin G S thin
  push_cast at c
  linarith

/-- For a thin region, the cross rank is at least `|∂S|/2 − c(Sᶜ) + c(G)`:
`2 · crossRank ≥ |∂S| − 2 c(Sᶜ) + 2 c(G)`. -/
theorem two_mul_crossRank_ge_of_thin (S : Finset V)
    (thin : ∀ K, 2 ≤ #(componentBoundaryDarts G S K)) :
    (#(boundaryDarts G S) : ℤ) - 2 * regionComponents G Sᶜ +
        2 * Nat.card G.ConnectedComponent ≤ 2 * crossRank G S := by
  rw [crossRank_eq]
  have c : ((2 * regionComponents G S : ℕ) : ℤ) ≤ #(boundaryDarts G S) :=
    by exact_mod_cast two_mul_regionComponents_le_of_thin G S thin
  push_cast at c
  linarith

/-- **The ledger bound `2β(G) ≥ n + 2` read on a partition.**  With `G`
connected and the ledger's `n + 2 ≤ 2 (e + 1 − n)`:
`n + 2 ≤ 2 (β(G[S]) + β(G[Sᶜ]) + |∂S| − c(S) − c(Sᶜ) + 1)`. -/
theorem vertexCount_add_two_le_of_partition (S : Finset V)
    (connected : G.Connected)
    (ledger : Fintype.card V + 2 ≤ 2 * (#G.edgeFinset + 1 - Fintype.card V)) :
    (Fintype.card V : ℤ) + 2 ≤
      2 * (regionCycleRank G S + regionCycleRank G Sᶜ + #(boundaryDarts G S) -
        regionComponents G S - regionComponents G Sᶜ + 1) := by
  have split := cycleRank_eq_add G S
  haveI := connected.preconnected.subsingleton_connectedComponent
  haveI : Nonempty G.ConnectedComponent :=
    ⟨G.connectedComponentMk connected.nonempty.some⟩
  have one : Nat.card G.ConnectedComponent = 1 := Nat.card_unique
  rw [one] at split
  have le : Fintype.card V ≤ #G.edgeFinset + 1 := by omega
  have ledgerZ : (Fintype.card V : ℤ) + 2 ≤
      2 * ((#G.edgeFinset : ℤ) + 1 - Fintype.card V) := by
    have := ledger
    zify [le] at this
    exact this
  unfold cycleRank at split
  push_cast at split
  linarith

end LocalCycleRank

/-! ### The same quantities on a `FiniteObject`

Every quantity is the `LocalCycleRank` one at the object's own finite data
(`vertices`, `decideAdj`), so `object.degree`, `object.edgeCount` and
`object.vertexCount` appear literally. -/

namespace FiniteObject

variable (object : FiniteObject.{u})

/-- `e(S)` for a region of the object. -/
noncomputable def regionEdgeCount (S : Finset object.Vertex) : ℕ := by
  letI := object.vertices; letI := object.decideAdj
  exact LocalCycleRank.regionEdgeCount object.graph S

/-- `c(S)` for a region of the object. -/
noncomputable def regionComponents (S : Finset object.Vertex) : ℕ :=
  Nat.card (object.graph.induce (S : Set object.Vertex)).ConnectedComponent

/-- `β(G[S])` for a region of the object. -/
noncomputable def regionCycleRank (S : Finset object.Vertex) : ℤ := by
  letI := object.vertices; letI := object.decideAdj
  exact LocalCycleRank.regionCycleRank object.graph S

/-- `∂S` (outward darts) for a region of the object. -/
noncomputable def boundaryDarts (S : Finset object.Vertex) :
    Finset object.graph.Dart := by
  letI := object.vertices; letI := object.decideAdj
  exact LocalCycleRank.boundaryDarts object.graph S

/-- `|∂S|`. -/
noncomputable def boundaryCount (S : Finset object.Vertex) : ℕ :=
  #(object.boundaryDarts S)

/-- `σ_S = Σ_{v∈S} (deg v − 3)`. -/
noncomputable def regionExcess (S : Finset object.Vertex) : ℕ :=
  ∑ v ∈ S, (object.degree v - 3)

/-- `β(G) = e − n + c(G)`. -/
noncomputable def cycleRankInt : ℤ :=
  (object.edgeCount : ℤ) - object.vertexCount +
    Nat.card object.graph.ConnectedComponent

/-- The complement region `V ∖ S`, at the object's own decidable equality. -/
noncomputable def regionCompl (S : Finset object.Vertex) : Finset object.Vertex := by
  letI := object.vertices
  exact Sᶜ

/-- `crossRank S = β(G) − β(G[S]) − β(G[V∖S])`. -/
noncomputable def crossRank (S : Finset object.Vertex) : ℤ :=
  object.cycleRankInt - object.regionCycleRank S -
    object.regionCycleRank (object.regionCompl S)

/-- The darts of `∂S` whose tail lies in the component `K` of `G[S]`. -/
noncomputable def componentBoundaryDarts (S : Finset object.Vertex)
    (K : (object.graph.induce (S : Set object.Vertex)).ConnectedComponent) :
    Finset object.graph.Dart := by
  letI := object.vertices; letI := object.decideAdj
  exact LocalCycleRank.componentBoundaryDarts object.graph S K

theorem vertexCount_eq_card :
    letI := object.vertices
    object.vertexCount = Fintype.card object.Vertex := by
  letI := object.vertices
  exact FinEnum.card_eq_fintypeCard

theorem cycleRankInt_eq :
    letI := object.vertices; letI := object.decideAdj
    object.cycleRankInt = LocalCycleRank.cycleRank object.graph := by
  letI := object.vertices; letI := object.decideAdj
  unfold cycleRankInt LocalCycleRank.cycleRank
  rw [vertexCount_eq_card]
  rfl

/-- A baseline `≥ 3` gives every region the degree hypothesis. -/
theorem degreeThree_of_baseline {threshold : ℕ}
    (baseline : MinimumDegreeAtLeast threshold object) (three : 3 ≤ threshold)
    (S : Finset object.Vertex) : ∀ v ∈ S, 3 ≤ object.degree v :=
  fun v _ => three.trans (baseline.trans (object.minDegree_le_degree v))

/-- **Handshake on a region of the object**:
`Σ_{v∈S} deg v = 2 e(S) + |∂S|`. -/
theorem sum_degree_region (S : Finset object.Vertex) :
    ∑ v ∈ S, object.degree v =
      2 * object.regionEdgeCount S + object.boundaryCount S := by
  letI := object.vertices; letI := object.decideAdj
  exact LocalCycleRank.sum_degree_region object.graph S

/-- **Near-cubic local cycle rank on a region of the object**:
`2 β(G[S]) = |S| + σ_S − |∂S| + 2 c(S)`. -/
theorem two_mul_regionCycleRank (S : Finset object.Vertex)
    (degreeThree : ∀ v ∈ S, 3 ≤ object.degree v) :
    2 * object.regionCycleRank S =
      (#S : ℤ) + object.regionExcess S - object.boundaryCount S +
        2 * object.regionComponents S := by
  letI := object.vertices; letI := object.decideAdj
  exact LocalCycleRank.two_mul_regionCycleRank object.graph S degreeThree

/-- Parity of the boundary of a near-cubic region:
`|∂S| ≡ |S| + σ_S (mod 2)`. -/
theorem boundary_parity (S : Finset object.Vertex)
    (degreeThree : ∀ v ∈ S, 3 ≤ object.degree v) :
    (object.boundaryCount S : ℤ) ≡ #S + object.regionExcess S [ZMOD 2] := by
  letI := object.vertices; letI := object.decideAdj
  exact LocalCycleRank.boundary_parity object.graph S degreeThree

/-- **Additivity over `V = S ⊔ (V ∖ S)`**. -/
theorem cycleRankInt_eq_add (S : Finset object.Vertex) :
    object.cycleRankInt = object.regionCycleRank S +
      object.regionCycleRank (object.regionCompl S) + object.boundaryCount S -
      object.regionComponents S - object.regionComponents (object.regionCompl S) +
      Nat.card object.graph.ConnectedComponent := by
  letI := object.vertices; letI := object.decideAdj
  rw [cycleRankInt_eq]
  exact LocalCycleRank.cycleRank_eq_add object.graph S

/-- **Cross rank of a region of the object**:
`β(G) − β(G[S]) − β(G[V∖S]) = |∂S| − c(S) − c(V∖S) + c(G)`. -/
theorem crossRank_eq (S : Finset object.Vertex) :
    object.crossRank S = object.boundaryCount S - object.regionComponents S -
      object.regionComponents (object.regionCompl S) +
      Nat.card object.graph.ConnectedComponent := by
  unfold crossRank
  rw [cycleRankInt_eq_add]
  ring

/-- **Thin regions of the object**: every component of `G[S]` with at least
two boundary edges gives `2 c(S) ≤ |∂S|`. -/
theorem two_mul_regionComponents_le_of_thin (S : Finset object.Vertex)
    (thin : ∀ K, 2 ≤ #(object.componentBoundaryDarts S K)) :
    2 * object.regionComponents S ≤ object.boundaryCount S := by
  letI := object.vertices; letI := object.decideAdj
  exact LocalCycleRank.two_mul_regionComponents_le_of_thin object.graph S thin

/-- **Cycle rank of a thin near-cubic region of the object**:
`2 β(G[S]) ≤ |S| + σ_S`. -/
theorem two_mul_regionCycleRank_le_of_thin (S : Finset object.Vertex)
    (degreeThree : ∀ v ∈ S, 3 ≤ object.degree v)
    (thin : ∀ K, 2 ≤ #(object.componentBoundaryDarts S K)) :
    2 * object.regionCycleRank S ≤ (#S : ℤ) + object.regionExcess S := by
  letI := object.vertices; letI := object.decideAdj
  exact LocalCycleRank.two_mul_regionCycleRank_le_of_thin object.graph S
    degreeThree thin

/-- **The ledger's `2β(G) ≥ n + 2` on a partition of the object.**  From
`cycleRankConstraint` in the literal form the ledger publishes
(`n + 2 ≤ 2 (e + 1 − n)`) and connectivity (node `[8]`):
`n + 2 ≤ 2 (β(G[S]) + β(G[V∖S]) + |∂S| − c(S) − c(V∖S) + 1)`. -/
theorem vertexCount_add_two_le_of_partition (S : Finset object.Vertex)
    (connected : object.graph.Connected)
    (ledger : object.vertexCount + 2 ≤
      2 * (object.edgeCount + 1 - object.vertexCount)) :
    (object.vertexCount : ℤ) + 2 ≤
      2 * (object.regionCycleRank S + object.regionCycleRank (object.regionCompl S) +
        object.boundaryCount S - object.regionComponents S -
        object.regionComponents (object.regionCompl S) + 1) := by
  letI := object.vertices; letI := object.decideAdj
  rw [vertexCount_eq_card] at ledger ⊢
  exact LocalCycleRank.vertexCount_add_two_le_of_partition object.graph S
    connected ledger

/-! ### Windows `W` and remainder `R` -/

theorem remainderSupport_eq_regionCompl (packing : Finset (Finset object.Vertex)) :
    object.remainderSupport packing = object.regionCompl (windowSupport packing) := by
  letI := object.vertices
  ext v
  simp [remainderSupport, regionCompl]

/-- **Additivity over `V = W ⊔ R`**:
`β(G) = β(G[W]) + β(G[R]) + |∂W| − c(W) − c(R) + c(G)`. -/
theorem cycleRankInt_eq_window_add_remainder
    (packing : Finset (Finset object.Vertex)) :
    object.cycleRankInt = object.regionCycleRank (windowSupport packing) +
      object.regionCycleRank (object.remainderSupport packing) +
      object.boundaryCount (windowSupport packing) -
      object.regionComponents (windowSupport packing) -
      object.regionComponents (object.remainderSupport packing) +
      Nat.card object.graph.ConnectedComponent := by
  rw [remainderSupport_eq_regionCompl]
  exact object.cycleRankInt_eq_add _

/-- `|∂W| = |∂R|`: the window boundary and the remainder boundary are the same
edges. -/
theorem boundaryCount_remainder_eq_window
    (packing : Finset (Finset object.Vertex)) :
    object.boundaryCount (object.remainderSupport packing) =
      object.boundaryCount (windowSupport packing) := by
  rw [remainderSupport_eq_regionCompl]
  letI := object.vertices; letI := object.decideAdj
  exact LocalCycleRank.card_boundaryDarts_compl object.graph _

/-- **The ledger bound on `W ⊔ R`**: with `G` connected,
`n + 2 ≤ 2 (β(G[W]) + β(G[R]) + |∂R| − c(W) − c(R) + 1)`. -/
theorem vertexCount_add_two_le_window_remainder
    (packing : Finset (Finset object.Vertex))
    (connected : object.graph.Connected)
    (ledger : object.vertexCount + 2 ≤
      2 * (object.edgeCount + 1 - object.vertexCount)) :
    (object.vertexCount : ℤ) + 2 ≤
      2 * (object.regionCycleRank (windowSupport packing) +
        object.regionCycleRank (object.remainderSupport packing) +
        object.boundaryCount (object.remainderSupport packing) -
        object.regionComponents (windowSupport packing) -
        object.regionComponents (object.remainderSupport packing) + 1) := by
  rw [boundaryCount_remainder_eq_window, remainderSupport_eq_regionCompl]
  exact object.vertexCount_add_two_le_of_partition _ connected ledger

end FiniteObject

end Hypostructure.Graph
