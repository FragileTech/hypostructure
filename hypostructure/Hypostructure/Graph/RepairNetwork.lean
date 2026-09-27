import Hypostructure.Graph.OneThreeRepair

/-!
# Delayed compensation components as `1`--`3` repair networks

`def:repair-network-terms` (tex 9280): after deleting the original coordinate
supports of a dependence from its support `Z`, each remaining connected
component, attached to the deleted part (and to the rest of the graph) only
through boundary leaves, is a *delayed compensation component*.

This module builds that component literally from a finite graph and a region
(`region = Z \ D`): the connected component `K` of the induced graph on the
region, together with one pendant boundary leaf for every edge that leaves
`K`.  Every edge of the ambient graph at a vertex of `K` is kept, either as an
edge of `K` or as a leaf edge, so the component's internal degrees are the
ambient degrees.  `lem:smearing-support-repair`'s identity
`s = p − 2 + 2β − σ` is then the one-three handshake of
`Graph.OneThreeRepair.Component` at this network.

The module is proof-agnostic: it imports no strategy, row or vocabulary
module.
-/

namespace Hypostructure.Graph.RepairNetwork

open Hypostructure.Graph

universe u

variable {object : FiniteObject.{u}} (region : Finset object.Vertex)

/-- The induced graph on the region. -/
abbrev regionGraph : SimpleGraph region :=
  object.graph.induce (region : Set object.Vertex)

/-- A connected component of the induced graph on the region: one delayed
compensation component. -/
abbrev RegionComponent := (regionGraph region).ConnectedComponent

/-- The vertices of the component. -/
abbrev Inside (component : RegionComponent region) := component.supp

/-- The boundary leaves of the component: one per edge leaving it, i.e. per
dart whose tail lies in the component and whose head lies outside the region
(a neighbour inside the region lies in the same component). -/
def Leaf (component : RegionComponent region) : Type u :=
  { dart : object.graph.Dart //
    ∃ tail : dart.fst ∈ region,
      (regionGraph region).connectedComponentMk ⟨dart.fst, tail⟩ = component ∧
        dart.snd ∉ region }

/-- The vertex set of the repair network. -/
abbrev NetworkVertex (component : RegionComponent region) : Type u :=
  Inside region component ⊕ Leaf region component

variable {region}

/-- The component vertex a leaf hangs from. -/
def Leaf.foot {component : RegionComponent region} (leaf : Leaf region component) :
    Inside region component :=
  ⟨⟨leaf.1.fst, leaf.2.1⟩,
    (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).2 leaf.2.2.1⟩

/-- Adjacency of the repair network. -/
def networkAdj {component : RegionComponent region} :
    NetworkVertex region component → NetworkVertex region component → Prop
  | .inl left, .inl right => object.graph.Adj left.1.1 right.1.1
  | .inl inside, .inr leaf => leaf.1.fst = inside.1.1
  | .inr leaf, .inl inside => leaf.1.fst = inside.1.1
  | .inr _, .inr _ => False

variable (region)

/-- The graph of the repair network. -/
def networkGraph (component : RegionComponent region) :
    SimpleGraph (NetworkVertex region component) where
  Adj := networkAdj
  symm := ⟨by
    intro left right adjacent
    rcases left with left | left <;> rcases right with right | right <;>
      simp only [networkAdj] at adjacent ⊢
    · exact adjacent.symm
    · exact adjacent
    · exact adjacent⟩
  loopless := ⟨by
    intro vertex adjacent
    rcases vertex with vertex | vertex <;> simp only [networkAdj] at adjacent
    exact object.graph.irrefl adjacent⟩

instance finiteLeaf (component : RegionComponent region) :
    Finite (Leaf region component) := by
  letI : Fintype object.Vertex := @FinEnum.instFintype _ object.vertices
  refine Finite.of_injective (fun leaf : Leaf region component => leaf.1.toProd)
    ?_
  intro first second equal
  exact Subtype.ext (SimpleGraph.Dart.toProd_injective equal)

instance finiteNetworkVertex (component : RegionComponent region) :
    Finite (NetworkVertex region component) := by
  letI : Fintype object.Vertex := @FinEnum.instFintype _ object.vertices
  infer_instance

/-- **The delayed compensation component as a finite graph**: the component
`K` with one pendant boundary leaf per edge leaving it. -/
noncomputable def network (component : RegionComponent region) :
    FiniteObject.{u} where
  Vertex := NetworkVertex region component
  graph := networkGraph region component
  vertices := by
    classical
    letI : Fintype (NetworkVertex region component) := Fintype.ofFinite _
    exact ⟨Fintype.card _, Fintype.equivFin _⟩
  decideAdj := Classical.decRel _

/-- The boundary leaves of the network (`p` of them). -/
noncomputable def leaves (component : RegionComponent region) :
    Finset (network region component).Vertex :=
  (network region component).vertexFinset.filter fun vertex => vertex.isRight

/-- `s`: the internal vertices of the network. -/
noncomputable def internalVertices (component : RegionComponent region) :
    Finset (network region component).Vertex := by
  classical
  exact (network region component).vertexFinset \ leaves region component

/-- `σ_Z`: the recorded surplus of the internal vertices above degree three. -/
noncomputable def surplus (component : RegionComponent region) : Nat :=
  ∑ vertex ∈ internalVertices region component,
    ((network region component).degree vertex - 3)

/-- `β_Z`: the cycle rank of the network. -/
noncomputable def cycleRank (component : RegionComponent region) : Nat :=
  (network region component).edgeCount + 1 -
    (network region component).vertexCount

/-- **`lem:smearing-support-repair`'s identity** `s = p − 2 + 2β − σ` at one
delayed compensation component. -/
def RepairIdentity (component : RegionComponent region) : Prop :=
  ((internalVertices region component).card : Int) =
    (leaves region component).card - 2 + 2 * cycleRank region component -
      surplus region component

variable {region}

theorem regionGraph_adj {left right : region} :
    (regionGraph region).Adj left right ↔ object.graph.Adj left.1 right.1 := by
  simp [regionGraph]

/-- The ambient endpoint a network neighbour of a component vertex stands for:
the vertex itself, or the head of the leaf's dart. -/
def ambientNeighbor {component : RegionComponent region} :
    NetworkVertex region component → object.Vertex
  | .inl inside => inside.1.1
  | .inr leaf => leaf.1.snd

/-- The neighbours of a component vertex in the network correspond exactly to
its neighbours in the ambient graph, so its degree is its ambient degree. -/
theorem degree_inl {component : RegionComponent region}
    (inside : Inside region component) :
    (network region component).degree (.inl inside) =
      object.degree inside.1.1 := by
  classical
  rw [FiniteObject.degree_eq_ncard_neighborSet,
    FiniteObject.degree_eq_ncard_neighborSet]
  change ((networkGraph region component).neighborSet (.inl inside)).ncard = _
  refine Set.ncard_congr (fun vertex _ => ambientNeighbor vertex) ?_ ?_ ?_
  · rintro (neighbor | leaf) adjacent
    · exact adjacent
    · have tail : leaf.1.fst = inside.1.1 := adjacent
      change object.graph.Adj inside.1.1 leaf.1.snd
      rw [← tail]
      exact leaf.1.adj
  · rintro (first | first) (second | second) firstAdj secondAdj equal
    · congr 1
      exact Subtype.ext (Subtype.ext equal)
    · have same : first.1.1 = second.1.snd := equal
      exact absurd (same ▸ first.1.2) second.2.2.2
    · have same : first.1.snd = second.1.1 := equal
      exact absurd (same.symm ▸ second.1.2) first.2.2.2
    · have firstTail : first.1.fst = inside.1.1 := firstAdj
      have secondTail : second.1.fst = inside.1.1 := secondAdj
      congr 1
      apply Subtype.ext
      apply SimpleGraph.Dart.toProd_injective
      exact Prod.ext (firstTail.trans secondTail.symm) equal
  · intro vertex adjacent
    by_cases inRegion : vertex ∈ region
    · refine ⟨.inl ⟨⟨vertex, inRegion⟩, ?_⟩, adjacent, rfl⟩
      exact component.mem_supp_of_adj_mem_supp inside.2
        (regionGraph_adj.2 adjacent)
    · refine ⟨.inr ⟨⟨(inside.1.1, vertex), adjacent⟩, inside.1.2, ?_, inRegion⟩,
        rfl, rfl⟩
      exact (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).1 inside.2

theorem degree_inr {component : RegionComponent region}
    (leaf : Leaf region component) :
    (network region component).degree (.inr leaf) = 1 := by
  rw [FiniteObject.degree_eq_ncard_neighborSet, Set.ncard_eq_one]
  refine ⟨.inl leaf.foot, ?_⟩
  ext neighbor
  rcases neighbor with inside | other
  · simp only [SimpleGraph.mem_neighborSet, Set.mem_singleton_iff]
    change leaf.1.fst = inside.1.1 ↔ _
    constructor
    · intro tail
      congr 1
      apply Subtype.ext
      apply Subtype.ext
      exact tail.symm
    · intro equal
      cases equal
      rfl
  · simp only [SimpleGraph.mem_neighborSet, Set.mem_singleton_iff]
    change False ↔ _
    simp

theorem mem_leaves {component : RegionComponent region}
    (vertex : (network region component).Vertex) :
    vertex ∈ leaves region component ↔ vertex.isRight := by
  simp [leaves]

variable (region)

/-- **The delayed compensation component is a `1`--`3` repair network**
(`lem:smearing-support-repair`): every leaf has degree one, every internal
vertex keeps its ambient degree (so at least three at the baseline), the leaves
inject into the edges, and the network is connected. -/
noncomputable def component (component : RegionComponent region)
    (degreeThree : ∀ vertex ∈ region, 3 ≤ object.degree vertex) :
    OneThreeRepair.Component.{u} where
  object := network region component
  boundary := leaves region component
  boundaryDegree := by
    rintro (inside | leaf) member
    · simp [mem_leaves] at member
    · exact degree_inr leaf
  internalDegreeThree := by
    rintro (inside | leaf) notLeaf
    · rw [degree_inl]
      exact degreeThree _ inside.1.2
    · simp [mem_leaves] at notLeaf
  boundaryCard_le_edgeCount := by
    classical
    rw [FiniteObject.edgeCount_eq_ncard_edgeSet, ← Set.ncard_coe_finset]
    haveI : Finite (network region component).Vertex :=
      finiteNetworkVertex region component
    letI : Fintype (network region component).Vertex := Fintype.ofFinite _
    refine Set.ncard_le_ncard_of_injOn
      (fun vertex : (network region component).Vertex =>
        match vertex with
        | .inl inside => s(Sum.inl inside, Sum.inl inside)
        | .inr leaf => s(Sum.inl leaf.foot, Sum.inr leaf)) ?_ ?_
      (Set.toFinite _)
    · rintro (inside | leaf) member
      · simp [mem_leaves] at member
      · change (networkGraph region component).Adj (.inl leaf.foot) (.inr leaf)
        change leaf.1.fst = leaf.foot.1.1
        rfl
    · rintro (first | first) firstMember (second | second) secondMember equal
      · simp [mem_leaves] at firstMember
      · simp [mem_leaves] at firstMember
      · simp [mem_leaves] at secondMember
      · simp only [Sym2.eq_iff] at equal
        rcases equal with ⟨-, same⟩ | ⟨impossible, -⟩
        · exact same
        · cases impossible
  connected := by
    have nonempty := (component.connected_toSimpleGraph).nonempty
    obtain ⟨base⟩ := nonempty
    have insideReach : ∀ first second : Inside region component,
        (networkGraph region component).Reachable (.inl first) (.inl second) := by
      intro first second
      let hom : component.toSimpleGraph →g networkGraph region component :=
        { toFun := fun vertex => .inl vertex
          map_rel' := fun {first second} adjacent => by
            change object.graph.Adj first.1.1 second.1.1
            exact regionGraph_adj.1 adjacent }
      exact ((component.connected_toSimpleGraph).preconnected first second).map hom
    have reach : ∀ vertex : NetworkVertex region component,
        (networkGraph region component).Reachable (.inl base) vertex := by
      rintro (inside | leaf)
      · exact insideReach base inside
      · refine (insideReach base leaf.foot).trans ?_
        refine SimpleGraph.Adj.reachable ?_
        change leaf.1.fst = leaf.foot.1.1
        rfl
    exact { preconnected := fun first second =>
              (reach first).symm.trans (reach second)
            nonempty := ⟨.inl base⟩ }

/-- **`lem:smearing-support-repair`** at a delayed compensation component:
`s = p − 2 + 2β − σ`, the one-three handshake of the network. -/
theorem repairIdentity (component' : RegionComponent region)
    (degreeThree : ∀ vertex ∈ region, 3 ≤ object.degree vertex) :
    RepairIdentity region component' := by
  have identity := (component region component' degreeThree).identity
  exact identity

end Hypostructure.Graph.RepairNetwork
