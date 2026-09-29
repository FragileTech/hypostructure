import Hypostructure.Graph.InterfaceReplacement
import Hypostructure.Graph.Target
import Hypostructure.Graph.Induced
import Hypostructure.Graph.DeletionCriticality

/-!
# G's actual surroundings, and the swap of a piece inside G

Vocabulary-free constructions that keep every statement about a finite object
`G` inside `G`:

* `actualGlue G Z X`: the edge restriction `X` of G's own piece at `Z`, glued
  into G's own surroundings `G − Z` (`SupportAtom.outside G Z`).  It is a
  subgraph of `G` (`actualGlue_hom`), so it never carries a target cycle `G`
  avoids (`not_target_actualGlue`).
* `swap G Z X`: the subgraph of `G` that keeps `G − Z`, keeps the edges of
  `G[Z]` inside `X`, and deletes the interior vertices of `Z` outside `X`
  (`swapVertices`, `SwapKeeps`).  It is a subgraph of `G` with an explicit
  injective homomorphism (`swapHom`), it has no target cycle when `G` has none
  (`not_target_swap`), and it is a proper subgraph as soon as it deletes a
  vertex or an edge (`swapProperSubgraph`).
* `swapDeficit G k Z X`: the first vertex, in `G`'s fixed vertex order, whose
  degree in the swap is below `k`.  When no proper subgraph of `G` has minimum
  degree `k`, a proper nonempty swap has one (`swapDeficit_isSome_of_noProper`):
  this vertex is the reason the swap is not a smaller counterexample.

No abstract boundaried context appears here: the only outside is `G − Z`.
-/

namespace Hypostructure.Graph.ActualContext

open Hypostructure
open Hypostructure.Graph
open Hypostructure.Graph.Strategy.InterfaceReplacement

universe u

section ActualGlue

variable (object : FiniteObject.{u})

/-- **G's piece `X` at `Z`, glued into G's own surroundings `G − Z`.** -/
noncomputable def actualGlue (Z X : Finset object.Vertex) : FiniteObject.{u} :=
  glue (SupportAtom.retainedPiece object Z X) (SupportAtom.outside object Z)

/-- The actual gluing is a subgraph of `G`, by an explicit injective
homomorphism. -/
theorem actualGlue_hom (Z X : Finset object.Vertex) :
    ∃ hom : (actualGlue object Z X).graph →g object.graph,
      Function.Injective hom := by
  classical
  have le : glueGraph (SupportAtom.retainedPiece object Z X)
      (SupportAtom.outside object Z) ≤
      glueGraph (SupportAtom.piece object Z) (SupportAtom.outside object Z) := by
    apply glueGraph_mono (piece := SupportAtom.piece object Z)
      (SupportAtom.outside object Z)
    intro left right adjacent
    exact adjacent.1
  let iso := (SupportAtom.decomposition object Z).reconstructionIso
  refine ⟨iso.toHom.comp (SimpleGraph.Hom.ofLE le), ?_⟩
  intro left right equal
  exact iso.injective equal

/-- **The actual gluing never closes a target cycle that `G` avoids.** -/
theorem not_target_actualGlue {L : Nat → Prop} {object : FiniteObject.{u}}
    (avoids : ¬ HasCycleWithLength L object) (Z X : Finset object.Vertex) :
    ¬ HasCycleWithLength L (actualGlue object Z X) := by
  intro cycle
  obtain ⟨hom, injective⟩ := actualGlue_hom object Z X
  exact avoids (hasCycleWithLength_of_hom hom injective cycle)

/-- **Two readings of G always agree in G's own surroundings `G − Z`**: on a
target-avoiding `G`, both actual gluings are target-free, so their target
responses in `G − Z` coincide.  This is the G-form of context equivalence:
the only context of G at `∂Z` is `G − Z`. -/
theorem actualGlue_agree {L : Nat → Prop} {object : FiniteObject.{u}}
    (avoids : ¬ HasCycleWithLength L object) (Z X Y : Finset object.Vertex) :
    HasCycleWithLength L (actualGlue object Z X) ↔
      HasCycleWithLength L (actualGlue object Z Y) :=
  iff_of_false (not_target_actualGlue avoids Z X) (not_target_actualGlue avoids Z Y)

end ActualGlue

section Swap

variable (object : FiniteObject.{u})

/-- The vertices the swap keeps: everything outside `Z`, the cut boundary
`∂Z`, and the vertices of `X`. -/
noncomputable def swapVertices (Z X : Finset object.Vertex) : Finset object.Vertex := by
  classical
  exact object.vertexFinset.filter fun v =>
    v ∉ Z ∨ v ∈ SupportAtom.cutBoundary object Z ∨ v ∈ X

theorem mem_swapVertices {Z X : Finset object.Vertex} {v : object.Vertex} :
    v ∈ swapVertices object Z X ↔
      v ∉ Z ∨ v ∈ SupportAtom.cutBoundary object Z ∨ v ∈ X := by
  classical
  unfold swapVertices
  simp only [Finset.mem_filter, FiniteObject.mem_vertexFinset, true_and]

/-- The edges of `G` the swap keeps: every edge with an end outside `Z` (the
edges of `G − Z` and the cut edges), every edge of `∂Z`, and the edges of
`G[Z]` inside `X`. -/
def SwapKeeps (Z X : Finset object.Vertex) (u v : object.Vertex) : Prop :=
  u ∉ Z ∨ v ∉ Z ∨
    (u ∈ SupportAtom.cutBoundary object Z ∧ v ∈ SupportAtom.cutBoundary object Z) ∨
    (u ∈ X ∧ v ∈ X)

theorem swapKeeps_symm {Z X : Finset object.Vertex} {u v : object.Vertex}
    (keeps : SwapKeeps object Z X u v) : SwapKeeps object Z X v u := by
  rcases keeps with h | h | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact Or.inr (Or.inl h)
  · exact Or.inl h
  · exact Or.inr (Or.inr (Or.inl ⟨h₂, h₁⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨h₂, h₁⟩))

/-- The kept edges of `G`, on `G`'s own vertex type. -/
def swapGraph (Z X : Finset object.Vertex) : SimpleGraph object.Vertex where
  Adj u v := object.graph.Adj u v ∧ SwapKeeps object Z X u v
  symm := ⟨fun _ _ ⟨h, k⟩ => ⟨h.symm, swapKeeps_symm object k⟩⟩
  loopless := ⟨fun _ ⟨h, _⟩ => object.graph.irrefl h⟩

/-- **The swap of G's piece at `Z` to the reading `X`, inside G**: the kept
edges on the kept vertices. -/
noncomputable def swap (Z X : Finset object.Vertex) : FiniteObject.{u} where
  Vertex := {v : object.Vertex // v ∈ swapVertices object Z X}
  graph := (swapGraph object Z X).induce (swapVertices object Z X : Set object.Vertex)
  vertices := (object.induce (swapVertices object Z X)).vertices
  decideAdj := Classical.decRel _

theorem swap_adj_iff {Z X : Finset object.Vertex} (a b : (swap object Z X).Vertex) :
    (swap object Z X).graph.Adj a b ↔
      object.graph.Adj a.1 b.1 ∧ SwapKeeps object Z X a.1 b.1 :=
  Iff.rfl

@[simp]
theorem vertexCount_swap (Z X : Finset object.Vertex) :
    (swap object Z X).vertexCount = (swapVertices object Z X).card :=
  object.vertexCount_induce (swapVertices object Z X)

/-- The explicit embedding of the swap into `G`: the inclusion of vertices. -/
def swapHom (Z X : Finset object.Vertex) : (swap object Z X).graph →g object.graph where
  toFun := Subtype.val
  map_rel' := fun h => h.1

theorem swapHom_apply (Z X : Finset object.Vertex) (v : (swap object Z X).Vertex) :
    swapHom object Z X v = v.1 :=
  rfl

theorem swapHom_injective (Z X : Finset object.Vertex) :
    Function.Injective (swapHom object Z X) :=
  Subtype.val_injective

/-- **The swap is a subgraph of `G`**, by the explicit injective `swapHom`. -/
theorem swap_le (Z X : Finset object.Vertex) :
    ∃ hom : (swap object Z X).graph →g object.graph, Function.Injective hom :=
  ⟨swapHom object Z X, swapHom_injective object Z X⟩

/-- **The swap never closes a target cycle that `G` avoids.** -/
theorem not_target_swap {L : Nat → Prop} {object : FiniteObject.{u}}
    (avoids : ¬ HasCycleWithLength L object) (Z X : Finset object.Vertex) :
    ¬ HasCycleWithLength L (swap object Z X) := fun cycle =>
  avoids (hasCycleWithLength_of_hom (swapHom object Z X) (swapHom_injective object Z X)
    cycle)

theorem swap_vertexCount_le (Z X : Finset object.Vertex) :
    (swap object Z X).vertexCount ≤ object.vertexCount := by
  rw [vertexCount_swap, ← object.card_vertexFinset]
  exact Finset.card_le_card fun v _ => object.mem_vertexFinset v

/-- **Deleting an interior vertex of `Z` outside `X` makes the swap smaller.** -/
theorem swap_card_lt {Z X : Finset object.Vertex}
    (deleted : ∃ v ∈ Z, v ∉ SupportAtom.cutBoundary object Z ∧ v ∉ X) :
    (swap object Z X).vertexCount < object.vertexCount := by
  rw [vertexCount_swap, ← object.card_vertexFinset]
  obtain ⟨v, inZ, notBoundary, notX⟩ := deleted
  apply Finset.card_lt_card
  refine ⟨fun w _ => object.mem_vertexFinset w, fun sub => ?_⟩
  rcases (mem_swapVertices object).1 (sub (object.mem_vertexFinset v)) with h | h | h
  · exact h inZ
  · exact notBoundary h
  · exact notX h

/-- **Dropping an edge of `G` leaves the swap with fewer edges.** -/
theorem swap_edgeCount_lt {Z X : Finset object.Vertex}
    (dropped : ∃ u v, object.graph.Adj u v ∧ ¬ SwapKeeps object Z X u v) :
    (swap object Z X).edgeCount < object.edgeCount := by
  classical
  letI : FinEnum object.Vertex := object.vertices
  obtain ⟨u, v, adj, drop⟩ := dropped
  have finj : Function.Injective (Sym2.map (swapHom object Z X)) :=
    Sym2.map.injective (swapHom_injective object Z X)
  have sub : Sym2.map (swapHom object Z X) '' (swap object Z X).graph.edgeSet ⊆
      object.graph.edgeSet := by
    rintro _ ⟨e, he, rfl⟩
    induction e using Sym2.ind with
    | h a b =>
        rw [Sym2.map_mk, SimpleGraph.mem_edgeSet]
        exact ((SimpleGraph.mem_edgeSet _).1 he).1
  have strict : Sym2.map (swapHom object Z X) '' (swap object Z X).graph.edgeSet ⊂
      object.graph.edgeSet := by
    refine (Set.ssubset_iff_of_subset sub).2 ⟨s(u, v), (SimpleGraph.mem_edgeSet _).2 adj, ?_⟩
    rintro ⟨e, he, image⟩
    induction e using Sym2.ind with
    | h a b =>
        rw [Sym2.map_mk] at image
        have keeps : SwapKeeps object Z X a.1 b.1 := ((SimpleGraph.mem_edgeSet _).1 he).2
        change s(a.1, b.1) = s(u, v) at image
        rcases Sym2.eq_iff.1 image with ⟨ha, hb⟩ | ⟨ha, hb⟩
        · rw [ha, hb] at keeps
          exact drop keeps
        · rw [ha, hb] at keeps
          exact drop (swapKeeps_symm object keeps)
  rw [FiniteObject.edgeCount_eq_ncard_edgeSet, FiniteObject.edgeCount_eq_ncard_edgeSet]
  calc (swap object Z X).graph.edgeSet.ncard
      = (Sym2.map (swapHom object Z X) '' (swap object Z X).graph.edgeSet).ncard :=
        (Set.ncard_image_of_injective _ finj).symm
    _ < object.graph.edgeSet.ncard := Set.ncard_lt_ncard strict (Set.toFinite _)

/-- The swap is proper when it deletes an interior vertex of `Z` outside `X`
or drops an edge of `G`. -/
abbrev SwapProper (Z X : Finset object.Vertex) : Prop :=
  (∃ v ∈ Z, v ∉ SupportAtom.cutBoundary object Z ∧ v ∉ X) ∨
    ∃ u v, object.graph.Adj u v ∧ ¬ SwapKeeps object Z X u v

/-- **A proper swap is a proper subgraph of `G`.** -/
noncomputable def swapProperSubgraph {Z X : Finset object.Vertex}
    (proper : SwapProper object Z X) : ProperSubgraph object where
  value := swap object Z X
  vertexEmbedding := ⟨Subtype.val, Subtype.val_injective⟩
  included := by
    rintro _ _ ⟨_different, left, right, adjacent, rfl, rfl⟩
    exact adjacent.1
  decreases := by
    rcases Nat.lt_or_ge (swap object Z X).vertexCount object.vertexCount with lt | ge
    · exact FiniteObject.lexicographicallySmaller_of_vertexCount_lt lt
    · have eq : (swap object Z X).vertexCount = object.vertexCount :=
        le_antisymm (swap_vertexCount_le object Z X) ge
      rcases proper with deleted | dropped
      · exact absurd (swap_card_lt object deleted) (by omega)
      · exact FiniteObject.lexicographicallySmaller_of_vertexCount_eq_edgeCount_lt eq
          (swap_edgeCount_lt object dropped)

/-- **A proper swap of a minimal target-avoiding `G` fails the baseline**: it is a
proper subgraph of `G` (hence lexicographically smaller and target-free), so if
it kept the baseline, minimality would give it a target cycle. -/
theorem not_baseline_swap_of_minimal {L : Nat → Prop}
    {Baseline : FiniteObject.{u} → Prop} {object : FiniteObject.{u}}
    (avoids : ¬ HasCycleWithLength L object)
    (minimal : ∀ H : FiniteObject.{u}, H.LexicographicallySmaller object →
      Baseline H → HasCycleWithLength L H)
    {Z X : Finset object.Vertex} (proper : SwapProper object Z X) :
    ¬ Baseline (swap object Z X) := fun baseline =>
  not_target_swap avoids Z X
    (minimal _ (swapProperSubgraph object proper).decreases baseline)

/-- The degree of a kept vertex in the swap: its kept `G`-neighbours. -/
theorem swap_degree_eq {Z X : Finset object.Vertex} (v : (swap object Z X).Vertex) :
    (swap object Z X).degree v =
      {w | object.graph.Adj v.1 w ∧ SwapKeeps object Z X v.1 w ∧
        w ∈ swapVertices object Z X}.ncard := by
  have inj : Function.Injective
      (Subtype.val : (swap object Z X).Vertex → object.Vertex) := Subtype.val_injective
  rw [FiniteObject.degree_eq_ncard_neighborSet,
    ← Set.ncard_image_of_injective ((swap object Z X).graph.neighborSet v) inj]
  congr 1
  ext w
  constructor
  · rintro ⟨w', hw', rfl⟩
    exact ⟨hw'.1, hw'.2, w'.2⟩
  · rintro ⟨hadj, hkeeps, hw⟩
    exact ⟨⟨w, hw⟩, ⟨hadj, hkeeps⟩, rfl⟩

/-- A vertex of `G` is swap-deficient at threshold `k` when the swap keeps it
with degree below `k`. -/
def SwapDeficient (threshold : Nat) (Z X : Finset object.Vertex) (v : object.Vertex) :
    Prop :=
  ∃ h : v ∈ swapVertices object Z X, (swap object Z X).degree ⟨v, h⟩ < threshold

/-- **The canonical degree deficit of the swap**: the first vertex, in `G`'s
fixed vertex order `orderedVertices`, that the swap keeps with degree below
`threshold`; `none` when there is none. -/
noncomputable def swapDeficit (threshold : Nat) (Z X : Finset object.Vertex) :
    Option object.Vertex := by
  classical
  exact object.orderedVertices.find? fun v => decide (SwapDeficient object threshold Z X v)

/-- **`swapDeficit` is exactly the first swap-deficient vertex in `G`'s
order.** -/
theorem swapDeficit_spec {threshold : Nat} {Z X : Finset object.Vertex}
    {v : object.Vertex} :
    swapDeficit object threshold Z X = some v ↔
      SwapDeficient object threshold Z X v ∧
        ∃ before after, object.orderedVertices = before ++ v :: after ∧
          ∀ a ∈ before, ¬ SwapDeficient object threshold Z X a := by
  classical
  unfold swapDeficit
  rw [List.find?_eq_some_iff_append]
  simp only [decide_eq_true_eq, Bool.not_eq_eq_eq_not, Bool.not_true,
    decide_eq_false_iff_not]

theorem swapDeficit_deficient {threshold : Nat} {Z X : Finset object.Vertex}
    {v : object.Vertex} (selected : swapDeficit object threshold Z X = some v) :
    SwapDeficient object threshold Z X v :=
  ((swapDeficit_spec object).1 selected).1

theorem swapDeficit_isSome_iff {threshold : Nat} {Z X : Finset object.Vertex} :
    (swapDeficit object threshold Z X).isSome ↔
      ∃ v, SwapDeficient object threshold Z X v := by
  classical
  unfold swapDeficit
  rw [List.find?_isSome]
  simp only [decide_eq_true_eq, FiniteObject.mem_orderedVertices, true_and]

/-- **A swap that fails the baseline on a nonempty kept set has its canonical
degree deficit.** -/
theorem swapDeficit_isSome_of_not_baseline {threshold : Nat} {Z X : Finset object.Vertex}
    (notBaseline : ¬ MinimumDegreeAtLeast threshold (swap object Z X))
    (nonempty : (swapVertices object Z X).Nonempty) :
    (swapDeficit object threshold Z X).isSome := by
  rw [swapDeficit_isSome_iff]
  by_contra none
  apply notBaseline
  obtain ⟨v, hv⟩ := nonempty
  haveI : Nonempty (swap object Z X).Vertex := ⟨⟨v, hv⟩⟩
  change threshold ≤ (swap object Z X).minDegree
  apply FiniteObject.le_minDegree_of_forall_le_degree
  intro w
  by_contra low
  exact none ⟨w.1, w.2, Nat.lt_of_not_le low⟩

/-- A canonical degree deficit is a failure of the baseline. -/
theorem not_baseline_of_swapDeficit_isSome {threshold : Nat} {Z X : Finset object.Vertex}
    (selected : (swapDeficit object threshold Z X).isSome) :
    ¬ MinimumDegreeAtLeast threshold (swap object Z X) := by
  rw [swapDeficit_isSome_iff] at selected
  obtain ⟨v, hv, low⟩ := selected
  intro base
  have := (swap object Z X).minDegree_le_degree ⟨v, hv⟩
  unfold MinimumDegreeAtLeast at base
  omega

/-- On a nonempty kept set, the canonical degree deficit exists exactly when the
swap fails the baseline. -/
theorem swapDeficit_isSome_iff_not_baseline {threshold : Nat} {Z X : Finset object.Vertex}
    (nonempty : (swapVertices object Z X).Nonempty) :
    (swapDeficit object threshold Z X).isSome ↔
      ¬ MinimumDegreeAtLeast threshold (swap object Z X) :=
  ⟨not_baseline_of_swapDeficit_isSome object,
    fun notBaseline => swapDeficit_isSome_of_not_baseline object notBaseline nonempty⟩

/-- **Why a proper swap is not a smaller counterexample**: when no proper
subgraph of `G` has minimum degree `threshold`, every proper swap with a kept
vertex has its canonical degree-deficient vertex. -/
theorem swapDeficit_isSome_of_noProper {threshold : Nat} {Z X : Finset object.Vertex}
    (noProper : ∀ subgraph : ProperSubgraph object,
      ¬ MinimumDegreeAtLeast threshold subgraph.value)
    (proper : SwapProper object Z X)
    (nonempty : (swapVertices object Z X).Nonempty) :
    (swapDeficit object threshold Z X).isSome :=
  swapDeficit_isSome_of_not_baseline object (noProper (swapProperSubgraph object proper))
    nonempty

/-- A kept vertex all of whose `G`-edges the swap keeps has its `G`-degree. -/
theorem swap_degree_eq_degree {Z X : Finset object.Vertex} (v : (swap object Z X).Vertex)
    (keeps : ∀ u, object.graph.Adj v.1 u →
      SwapKeeps object Z X v.1 u ∧ u ∈ swapVertices object Z X) :
    (swap object Z X).degree v = object.degree v.1 := by
  rw [swap_degree_eq object v, FiniteObject.degree_eq_ncard_neighborSet]
  congr 1
  ext u
  constructor
  · rintro ⟨adj, -, -⟩
    exact adj
  · intro adj
    exact ⟨adj, keeps u adj⟩

/-- **A swap that keeps every vertex and every edge of `G` has `G`'s
baseline.** -/
theorem baseline_swap_of_keepsAll {k : Nat} {Z X : Finset object.Vertex}
    (base : MinimumDegreeAtLeast k object) [inhabited : Nonempty object.Vertex]
    (all : ∀ v, v ∈ swapVertices object Z X)
    (keeps : ∀ u v, object.graph.Adj u v → SwapKeeps object Z X u v) :
    MinimumDegreeAtLeast k (swap object Z X) := by
  obtain ⟨v₀⟩ := inhabited
  haveI : Nonempty (swap object Z X).Vertex := ⟨⟨v₀, all v₀⟩⟩
  change k ≤ (swap object Z X).minDegree
  apply FiniteObject.le_minDegree_of_forall_le_degree
  intro v
  rw [swap_degree_eq_degree object v (fun u adj => ⟨keeps _ _ adj, all u⟩)]
  exact le_trans base (object.minDegree_le_degree v.1)

/-- **A whole reading swaps back to `G`**: when `Z ⊆ X` the swap keeps every
vertex and every edge, so it has `G`'s baseline. -/
theorem baseline_swap_of_subset {k : Nat} {Z X : Finset object.Vertex}
    (base : MinimumDegreeAtLeast k object) [Nonempty object.Vertex] (sub : Z ⊆ X) :
    MinimumDegreeAtLeast k (swap object Z X) := by
  apply baseline_swap_of_keepsAll object base
  · intro v
    refine (mem_swapVertices object).2 ?_
    by_cases hv : v ∈ Z
    · exact Or.inr (Or.inr (sub hv))
    · exact Or.inl hv
  · intro u v _
    by_cases hu : u ∈ Z
    · by_cases hv : v ∈ Z
      · exact Or.inr (Or.inr (Or.inr ⟨sub hu, sub hv⟩))
      · exact Or.inr (Or.inl hv)
    · exact Or.inl hu

/-- **An all-boundary support swaps back to `G`**: when every vertex of `Z`
lies on `∂Z` the swap keeps every vertex and every edge. -/
theorem baseline_swap_of_allBoundary {k : Nat} {Z X : Finset object.Vertex}
    (base : MinimumDegreeAtLeast k object) [Nonempty object.Vertex]
    (allBoundary : ∀ v ∈ Z, v ∈ SupportAtom.cutBoundary object Z) :
    MinimumDegreeAtLeast k (swap object Z X) := by
  apply baseline_swap_of_keepsAll object base
  · intro v
    refine (mem_swapVertices object).2 ?_
    by_cases hv : v ∈ Z
    · exact Or.inr (Or.inl (allBoundary v hv))
    · exact Or.inl hv
  · intro u v _
    by_cases hu : u ∈ Z
    · by_cases hv : v ∈ Z
      · exact Or.inr (Or.inr (Or.inl ⟨allBoundary u hu, allBoundary v hv⟩))
      · exact Or.inr (Or.inl hv)
    · exact Or.inl hu

/-- **Where a swap deficit sits**: a kept vertex whose swap-degree is below a
lower bound of its `G`-degree lies in `Z` and loses a `G`-edge `vu` with
`u ∈ Z` (an edge of `G[Z]` the swap drops, or an edge to a deleted interior
vertex). -/
theorem exists_dropped_of_deficient {k : Nat} {Z X : Finset object.Vertex}
    (base : ∀ v, k ≤ object.degree v) {v : object.Vertex}
    (hv : v ∈ swapVertices object Z X)
    (low : (swap object Z X).degree ⟨v, hv⟩ < k) :
    v ∈ Z ∧ ∃ u, u ∈ Z ∧ object.graph.Adj v u ∧
      ¬ (SwapKeeps object Z X v u ∧ u ∈ swapVertices object Z X) := by
  have dropped : ∃ u, object.graph.Adj v u ∧
      ¬ (SwapKeeps object Z X v u ∧ u ∈ swapVertices object Z X) := by
    by_contra none
    have keeps : ∀ u, object.graph.Adj v u →
        SwapKeeps object Z X v u ∧ u ∈ swapVertices object Z X :=
      fun u adj => Classical.byContradiction fun h => none ⟨u, adj, h⟩
    have same := swap_degree_eq_degree object ⟨v, hv⟩ keeps
    have lower := base v
    have : (swap object Z X).degree ⟨v, hv⟩ = object.degree v := same
    omega
  obtain ⟨u, adj, notKept⟩ := dropped
  have uZ : u ∈ Z := by
    by_contra uZ
    exact notKept ⟨Or.inr (Or.inl uZ), (mem_swapVertices object).2 (Or.inl uZ)⟩
  have vZ : v ∈ Z := by
    by_contra vZ
    refine notKept ⟨Or.inl vZ, (mem_swapVertices object).2 (Or.inr (Or.inl ?_))⟩
    exact (SupportAtom.mem_cutBoundary_iff object Z u).2 ⟨uZ, v, adj.symm, vZ⟩
  exact ⟨vZ, u, uZ, adj, notKept⟩

/-- **A swap failing the baseline needs two vertices in `Z`**: on a graph with
positive minimum degree, a one-vertex `Z` swaps back to `G`. -/
theorem one_lt_card_of_not_baseline_swap {k : Nat} {Z X : Finset object.Vertex}
    (base : MinimumDegreeAtLeast k object) (pos : 0 < k) [Nonempty object.Vertex]
    (Zne : Z.Nonempty) (notBaseline : ¬ MinimumDegreeAtLeast k (swap object Z X)) :
    1 < Z.card := by
  by_contra small
  obtain ⟨z, hz⟩ := Zne
  have single : ∀ v ∈ Z, v = z := fun v hv =>
    Finset.card_le_one.1 (by omega) v hv z hz
  apply notBaseline
  apply baseline_swap_of_keepsAll object base
  · intro v
    refine (mem_swapVertices object).2 ?_
    by_cases hv : v ∈ Z
    · refine Or.inr (Or.inl ((SupportAtom.mem_cutBoundary_iff object Z v).2 ⟨hv, ?_⟩))
      have deg : k ≤ object.degree v := le_trans base (object.minDegree_le_degree v)
      rw [FiniteObject.degree_eq_ncard_neighborSet] at deg
      obtain ⟨u, hu⟩ := Set.nonempty_of_ncard_ne_zero
        (show (object.graph.neighborSet v).ncard ≠ 0 by omega)
      have adj : object.graph.Adj v u := hu
      refine ⟨u, adj, fun uZ => ?_⟩
      exact adj.ne ((single v hv).trans (single u uZ).symm)
    · exact Or.inl hv
  · intro u v adj
    by_cases hu : u ∈ Z
    · by_cases hv : v ∈ Z
      · exact absurd ((single u hu).trans (single v hv).symm) adj.ne
      · exact Or.inr (Or.inl hv)
    · exact Or.inl hu

end Swap

end Hypostructure.Graph.ActualContext
