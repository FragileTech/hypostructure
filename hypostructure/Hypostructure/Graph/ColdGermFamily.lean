import Hypostructure.Graph.ColdFirstFailure
import Hypostructure.Graph.SubcubicReach
import Hypostructure.Graph.CanonicalRealization
import Hypostructure.Graph.PrimitiveCarrier
import Hypostructure.Graph.WindowStubStructure

/-!
# The (F5) cold bounded germs of the selected half-edges

`def:cold-corridor-first-failure` and `def:cold-bounded-germ`, constructed:

* the outside component `K` of a boundary stub's foot in `G − X_cold`;
* the first-failure exchange support of a corridor — the whole terminal
  corridor, or the bounded prefix inside which a cold corridor state repeats
  (`Q_cold + 1` initial segments) — as a connected proper support;
* the geometric support on which the ledger-retained cold bounded configuration
  is read.

The construction below produces the paper's `BoundedGerm` only from an actual
corridor presentation.  Its record is `Corridor.recordAt` at the terminal or
first repeated state, and its second representative is the framework's
canonical realization of that retained cut state.  The resulting
`FirstFailureGermWitness` is the semantic payload registered by
`K .coldCorridorState`; no default record or self-representative is used.
-/

namespace Hypostructure.Graph.ColdCorridor

open Hypostructure

universe u

/-- Oriented incidences whose first endpoint lies in `region` are bounded by
the exact degree mass of that region. -/
theorem card_incidences_filter_fst_le_sum_degree (object : FiniteObject.{u})
    [DecidableEq object.Vertex] (region : Finset object.Vertex) :
    (object.incidences.filter fun pair : object.Vertex × object.Vertex =>
      pair.1 ∈ region).card ≤
      ∑ vertex ∈ region, object.degree vertex := by
  classical
  letI : Fintype object.Vertex := @FinEnum.instFintype _ object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  rw [Finset.card_eq_sum_card_fiberwise
    (f := Prod.fst) (t := region) (by
      intro pair member
      exact (Finset.mem_filter.1 member).2)]
  calc
    ∑ vertex ∈ region,
          ((object.incidences.filter fun pair : object.Vertex × object.Vertex =>
              pair.1 ∈ region).filter
            fun pair => pair.1 = vertex).card
        ≤ ∑ vertex ∈ region, object.degree vertex := by
          refine Finset.sum_le_sum fun vertex vertexMem => ?_
          let fibre := (object.incidences.filter
              fun pair : object.Vertex × object.Vertex => pair.1 ∈ region).filter
            fun pair => pair.1 = vertex
          exact Finset.card_le_card_of_injOn Prod.snd
            (by
              intro pair pairMem
              change pair ∈ fibre at pairMem
              simp only [fibre, Finset.mem_filter] at pairMem
              have incidence := (object.mem_incidences_iff pair).1
                pairMem.1.1
              exact (SimpleGraph.mem_neighborFinset object.graph vertex pair.2).2
                (pairMem.2 ▸ incidence))
            (by
              intro left leftMem right rightMem same
              change left ∈ fibre at leftMem
              change right ∈ fibre at rightMem
              simp only [fibre, Finset.mem_filter] at leftMem rightMem
              apply Prod.ext
              · exact leftMem.2.trans rightMem.2.symm
              · exact same)

/-- The number of oriented graph incidences whose first endpoint lies in a
bounded-degree region is at most `threshold` times the size of that region. -/
theorem card_incidences_filter_fst_le (object : FiniteObject.{u})
    [DecidableEq object.Vertex] (region : Finset object.Vertex) (threshold : Nat)
    (bounded : ∀ vertex ∈ region, object.degree vertex ≤ threshold) :
    (object.incidences.filter fun pair : object.Vertex × object.Vertex =>
      pair.1 ∈ region).card ≤
      threshold * region.card := by
  calc
    (object.incidences.filter fun pair : object.Vertex × object.Vertex =>
        pair.1 ∈ region).card
        ≤ ∑ vertex ∈ region, object.degree vertex :=
          card_incidences_filter_fst_le_sum_degree object region
    _ ≤ ∑ _vertex ∈ region, threshold :=
      Finset.sum_le_sum fun vertex vertexMem => bounded vertex vertexMem
    _ = threshold * region.card := by
      simp [Nat.mul_comm]

variable {object : FiniteObject.{u}}

/-- A graph whose registered minimum-degree threshold is at least three has
more than two vertices.  The threshold is supplied by the problem
presentation; this lemma does not specialize its caller to a literal cubic
baseline. -/
theorem two_lt_vertexCount_of_minDegree {threshold : Nat}
    (three_le : 3 ≤ threshold)
    (baseline : Graph.MinimumDegreeAtLeast threshold object) :
    2 < object.vertexCount := by
  classical
  by_cases nonempty : Nonempty object.Vertex
  · obtain ⟨vertex⟩ := nonempty
    have := object.minDegree_le_degree vertex
    have := object.degree_lt_vertexCount vertex
    change threshold ≤ object.minDegree at baseline
    omega
  · exfalso
    rw [not_nonempty_iff] at nonempty
    change threshold ≤ object.minDegree at baseline
    have zero : object.minDegree = 0 := by
      letI : FinEnum object.Vertex := object.vertices
      letI : DecidableRel object.graph.Adj := object.decideAdj
      change object.graph.minDegree = 0
      simp [SimpleGraph.minDegree, Finset.univ_eq_empty]
    omega

/-! ## The outside component of a foot -/

/-- The vertex support of the outside graph `G − X_cold`. -/
noncomputable def outsideSupport (object : FiniteObject.{u})
    (windows : Finset object.Vertex) : Finset object.Vertex := by
  classical
  letI : FinEnum object.Vertex := object.vertices
  exact Finset.univ \ windows

theorem mem_outsideSupport (object : FiniteObject.{u})
    (windows : Finset object.Vertex) (vertex : object.Vertex) :
    vertex ∈ outsideSupport object windows ↔ vertex ∉ windows := by
  classical
  letI : FinEnum object.Vertex := object.vertices
  simp [outsideSupport]

/-- The outside graph `G − X_cold`. -/
noncomputable abbrev outsideGraph (object : FiniteObject.{u})
    (windows : Finset object.Vertex) : FiniteObject.{u} :=
  object.induce (outsideSupport object windows)

/-- **The connected component `K` of the outside graph containing a foot.** -/
noncomputable def outsideComponentOf (object : FiniteObject.{u})
    (windows : Finset object.Vertex) (foot : object.Vertex)
    (footOutside : foot ∉ windows) : Finset object.Vertex := by
  classical
  letI : FinEnum object.Vertex := object.vertices
  exact Finset.univ.filter fun vertex =>
    ∃ outside : vertex ∈ outsideSupport object windows,
      (outsideGraph object windows).graph.Reachable
        ⟨foot, (mem_outsideSupport object windows foot).2 footOutside⟩
        ⟨vertex, outside⟩

/-- A walk of one induced graph whose vertices all lie in a second support is a
reachability certificate in the second induced graph. -/
theorem reachable_induce_of_walk {first second : Finset object.Vertex}
    {left right : (object.induce first).Vertex}
    (walk : (object.induce first).graph.Walk left right)
    (inside : ∀ vertex ∈ walk.support, vertex.1 ∈ second) :
    (object.induce second).graph.Reachable
      ⟨left.1, inside left (SimpleGraph.Walk.start_mem_support walk)⟩
      ⟨right.1, inside right (SimpleGraph.Walk.end_mem_support walk)⟩ := by
  induction walk with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons a b c adjacent tail ih =>
      have adjacent' : (object.induce second).graph.Adj
          ⟨a.1, inside a (by simp)⟩ ⟨b.1, inside b (by simp)⟩ := by
        change object.graph.Adj a.1 b.1
        exact adjacent
      exact (SimpleGraph.Adj.reachable adjacent').trans
        (ih fun vertex member => inside vertex (by simp [member]))

theorem outsideComponentOf_isOutsideComponent (object : FiniteObject.{u})
    (windows : Finset object.Vertex) (foot : object.Vertex)
    (footOutside : foot ∉ windows) :
    IsOutsideComponent object windows
      (outsideComponentOf object windows foot footOutside) := by
  classical
  letI : FinEnum object.Vertex := object.vertices
  refine ⟨?_, ?_, ?_⟩
  · rw [Finset.disjoint_left]
    intro vertex member windowMem
    simp only [outsideComponentOf, Finset.mem_filter, Finset.mem_univ, true_and] at member
    obtain ⟨outside, _⟩ := member
    exact (mem_outsideSupport object windows vertex).1 outside windowMem
  · intro a aMem b adjacent bOutside
    simp only [outsideComponentOf, Finset.mem_filter, Finset.mem_univ, true_and] at aMem ⊢
    obtain ⟨aOutside, reach⟩ := aMem
    refine ⟨(mem_outsideSupport object windows b).2 bOutside, ?_⟩
    refine reach.trans (SimpleGraph.Adj.reachable ?_)
    change object.graph.Adj a b
    exact adjacent
  · intro left right
    have leftMem := left.2
    have rightMem := right.2
    simp only [outsideComponentOf, Finset.mem_filter, Finset.mem_univ, true_and] at leftMem rightMem
    obtain ⟨leftOutside, leftReach⟩ := leftMem
    obtain ⟨rightOutside, rightReach⟩ := rightMem
    obtain ⟨walk⟩ := leftReach.symm.trans rightReach
    have inside : ∀ vertex ∈ walk.support,
        vertex.1 ∈ outsideComponentOf object windows foot footOutside := by
      intro vertex member
      simp only [outsideComponentOf, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨vertex.2, ?_⟩
      exact leftReach.trans ⟨walk.takeUntil vertex member⟩
    have := reachable_induce_of_walk walk inside
    exact this

/-! ## The first-failure exchange support of a corridor -/

variable {windows component : Finset object.Vertex}

namespace Corridor

/-- **The exchange support of a corridor prefix**: the vertices of the first
`n + 1` initial segments, as vertices of the object. -/
noncomputable def prefixSupport (corridor : Corridor object windows component)
    (n : Nat) : Finset object.Vertex := by
  classical
  exact ((corridor.inside.1.take n).support.map (fun vertex => vertex.1)).toFinset

theorem mem_prefixSupport (corridor : Corridor object windows component) (n : Nat)
    (vertex : object.Vertex) :
    vertex ∈ corridor.prefixSupport n ↔
      ∃ inner ∈ (corridor.inside.1.take n).support, inner.1 = vertex := by
  classical
  simp [prefixSupport]

theorem prefixSupport_subset_component (corridor : Corridor object windows component)
    (n : Nat) : corridor.prefixSupport n ⊆ component := by
  intro vertex member
  obtain ⟨inner, _, rfl⟩ := (corridor.mem_prefixSupport n vertex).1 member
  exact inner.2

/-- The exchange support has at most `n + 1` vertices. -/
theorem prefixSupport_card_le (corridor : Corridor object windows component)
    (n : Nat) : (corridor.prefixSupport n).card ≤ n + 1 := by
  classical
  refine le_trans (List.toFinset_card_le _) ?_
  rw [List.length_map, SimpleGraph.Walk.length_support, SimpleGraph.Walk.take_length]
  omega

/-- The exchange support is connected: any two of its vertices are joined by a
path of the object that stays inside it, through the prefix's own start. -/
theorem prefixSupport_connectedOn (corridor : Corridor object windows component)
    (n : Nat) :
    Graph.SupportComponents.Connected.ConnectedOn object (corridor.prefixSupport n) := by
  classical
  let walk := corridor.inside.1.take n
  let embedding := object.induceEmbedding component
  refine ⟨⟨(corridor.inside.1.getVert 0).1, ?_⟩, ?_⟩
  · exact (corridor.mem_prefixSupport n _).2 ⟨_, by
      simpa [walk] using SimpleGraph.Walk.start_mem_support walk, rfl⟩
  · intro left right leftMem rightMem
    obtain ⟨leftInner, leftSupport, leftEq⟩ := (corridor.mem_prefixSupport n left).1 leftMem
    obtain ⟨rightInner, rightSupport, rightEq⟩ :=
      (corridor.mem_prefixSupport n right).1 rightMem
    -- left ← start → right, inside the prefix walk.
    let toLeft := walk.takeUntil leftInner leftSupport
    let toRight := walk.takeUntil rightInner rightSupport
    let joined := toLeft.reverse.append toRight
    let mapped := joined.map embedding.toHom
    have mappedSupport : ∀ vertex ∈ mapped.support, vertex ∈ corridor.prefixSupport n := by
      intro vertex member
      simp only [mapped, SimpleGraph.Walk.support_map, List.mem_map] at member
      obtain ⟨inner, innerMem, rfl⟩ := member
      refine (corridor.mem_prefixSupport n _).2 ⟨inner, ?_, rfl⟩
      simp only [joined, SimpleGraph.Walk.support_append, SimpleGraph.Walk.support_reverse,
        List.mem_append, List.mem_reverse] at innerMem
      rcases innerMem with member | member
      · exact walk.support_takeUntil_subset_support leftSupport member
      · exact walk.support_takeUntil_subset_support rightSupport (List.mem_of_mem_tail member)
    have leftEq' : embedding leftInner = left := leftEq
    have rightEq' : embedding rightInner = right := rightEq
    refine ⟨((mapped.copy leftEq' rightEq').toPath).1, ((mapped.copy leftEq' rightEq').toPath).2,
      ?_⟩
    intro vertex member
    have := SimpleGraph.Walk.support_toPath_subset_support _ member
    rw [SimpleGraph.Walk.support_copy] at this
    exact mappedSupport vertex this

/-- The exchange support is proper: the entry stub's window endpoint lies
outside it. -/
theorem prefixSupport_proper (corridor : Corridor object windows component)
    (outside : IsOutsideComponent object windows component) (n : Nat) :
    ∃ vertex, vertex ∉ corridor.prefixSupport n := by
  refine ⟨corridor.entryStub.2, fun member => ?_⟩
  have inComponent := corridor.prefixSupport_subset_component n member
  have isStub := (mem_boundaryStubs_iff object windows component _).1
    (List.get_mem _ corridor.entry)
  exact Finset.disjoint_left.mp outside.1 inComponent isStub.2.1

theorem prefixSupport_subset_inside
    (corridor : Corridor object windows component) (n : Nat) :
    ∀ vertex ∈ corridor.prefixSupport n,
      vertex ∈ corridor.inside.1.support.map (fun inner => inner.1) := by
  classical
  intro vertex member
  obtain ⟨inner, innerMem, rfl⟩ :=
    (corridor.mem_prefixSupport n vertex).1 member
  simp only [List.mem_map]
  exact ⟨inner, (corridor.inside.1.isSubwalk_take n).support_subset innerMem, rfl⟩

/-- The support between two retained corridor states.  This is the literal
`drop left; take (right-left)` interval used in the repeat subcase (F5). -/
noncomputable def intervalSupport (corridor : Corridor object windows component)
    (left right : corridor.Segment) : Finset object.Vertex := by
  classical
  exact ((((corridor.inside.1.drop left.1).take (right.1 - left.1)).support.map
    (fun vertex => vertex.1)).toFinset)

theorem mem_intervalSupport (corridor : Corridor object windows component)
    (left right : corridor.Segment) (vertex : object.Vertex) :
    vertex ∈ corridor.intervalSupport left right ↔
      ∃ inner ∈ ((corridor.inside.1.drop left.1).take
        (right.1 - left.1)).support, inner.1 = vertex := by
  classical
  simp [intervalSupport]

theorem intervalSupport_subset_component
    (corridor : Corridor object windows component)
    (left right : corridor.Segment) :
    corridor.intervalSupport left right ⊆ component := by
  intro vertex member
  obtain ⟨inner, _, rfl⟩ :=
    (corridor.mem_intervalSupport left right vertex).1 member
  exact inner.2

theorem intervalSupport_card_le (corridor : Corridor object windows component)
    (left right : corridor.Segment) :
    (corridor.intervalSupport left right).card ≤ right.1 - left.1 + 1 := by
  classical
  refine le_trans (List.toFinset_card_le _) ?_
  rw [List.length_map, SimpleGraph.Walk.length_support,
    SimpleGraph.Walk.take_length, SimpleGraph.Walk.drop_length]
  omega

theorem intervalSupport_connectedOn
    (corridor : Corridor object windows component)
    (left right : corridor.Segment) :
    Graph.SupportComponents.Connected.ConnectedOn object
      (corridor.intervalSupport left right) := by
  classical
  let walk := (corridor.inside.1.drop left.1).take (right.1 - left.1)
  let embedding := object.induceEmbedding component
  let start := corridor.inside.1.getVert left.1
  refine ⟨⟨start.1, ?_⟩, ?_⟩
  · exact (corridor.mem_intervalSupport left right _).2
      ⟨start, SimpleGraph.Walk.start_mem_support walk, rfl⟩
  · intro a b aMem bMem
    obtain ⟨aInner, aSupport, aEq⟩ :=
      (corridor.mem_intervalSupport left right a).1 aMem
    obtain ⟨bInner, bSupport, bEq⟩ :=
      (corridor.mem_intervalSupport left right b).1 bMem
    let toA := walk.takeUntil aInner aSupport
    let toB := walk.takeUntil bInner bSupport
    let joined := toA.reverse.append toB
    let mapped := joined.map embedding.toHom
    have mappedSupport : ∀ vertex ∈ mapped.support,
        vertex ∈ corridor.intervalSupport left right := by
      intro vertex member
      simp only [mapped, SimpleGraph.Walk.support_map, List.mem_map] at member
      obtain ⟨inner, innerMem, rfl⟩ := member
      refine (corridor.mem_intervalSupport left right _).2 ⟨inner, ?_, rfl⟩
      simp only [joined, SimpleGraph.Walk.support_append,
        SimpleGraph.Walk.support_reverse, List.mem_append, List.mem_reverse] at innerMem
      rcases innerMem with member | member
      · exact walk.support_takeUntil_subset_support aSupport member
      · exact walk.support_takeUntil_subset_support bSupport
          (List.mem_of_mem_tail member)
    have aEq' : embedding aInner = a := aEq
    have bEq' : embedding bInner = b := bEq
    refine ⟨((mapped.copy aEq' bEq').toPath).1,
      ((mapped.copy aEq' bEq').toPath).2, ?_⟩
    intro vertex member
    have subset := SimpleGraph.Walk.support_toPath_subset_support _ member
    rw [SimpleGraph.Walk.support_copy] at subset
    exact mappedSupport vertex subset

theorem intervalSupport_proper (corridor : Corridor object windows component)
    (outside : IsOutsideComponent object windows component)
    (left right : corridor.Segment) :
    ∃ vertex, vertex ∉ corridor.intervalSupport left right := by
  refine ⟨corridor.entryStub.2, fun member => ?_⟩
  have inComponent := corridor.intervalSupport_subset_component left right member
  have isStub := (mem_boundaryStubs_iff object windows component _).1
    (List.get_mem _ corridor.entry)
  exact Finset.disjoint_left.mp outside.1 inComponent isStub.2.1

theorem intervalSupport_subset_inside
    (corridor : Corridor object windows component)
    (left right : corridor.Segment) :
    ∀ vertex ∈ corridor.intervalSupport left right,
      vertex ∈ corridor.inside.1.support.map (fun inner => inner.1) := by
  classical
  intro vertex member
  obtain ⟨inner, innerMem, rfl⟩ :=
    (corridor.mem_intervalSupport left right vertex).1 member
  simp only [List.mem_map]
  refine ⟨inner, ?_, rfl⟩
  have taken : inner ∈ (corridor.inside.1.drop left.1).support :=
    ((corridor.inside.1.drop left.1).isSubwalk_take
      (right.1 - left.1)).support_subset innerMem
  exact (corridor.inside.1.isSubwalk_drop left.1).support_subset taken

/-- Initial corridor supports grow monotonically with the prefix length.  This
is the initial-segment monotonicity used by the subcubic-ball count in
`lem:cold-germ-extraction`. -/
theorem prefixSupport_mono (corridor : Corridor object windows component)
    {left right : Nat} (bounded : left ≤ right) :
    corridor.prefixSupport left ⊆ corridor.prefixSupport right := by
  classical
  intro vertex member
  obtain ⟨inner, innerMem, rfl⟩ :=
    (corridor.mem_prefixSupport left vertex).1 member
  refine (corridor.mem_prefixSupport right _).2 ⟨inner, ?_, rfl⟩
  exact (corridor.inside.1.take_isSubwalk_take bounded).support_subset innerMem

/-- A repeated-state exchange interval lies in the initial prefix ending at
the repeated right state. -/
theorem intervalSupport_subset_prefixSupport
    (corridor : Corridor object windows component)
    (left right : corridor.Segment) (leftLe : left.1 ≤ right.1) :
    corridor.intervalSupport left right ⊆ corridor.prefixSupport right.1 := by
  classical
  intro vertex member
  obtain ⟨inner, innerMem, rfl⟩ :=
    (corridor.mem_intervalSupport left right vertex).1 member
  refine (corridor.mem_prefixSupport right.1 _).2 ⟨inner, ?_, rfl⟩
  have sum : left.1 + (right.1 - left.1) = right.1 := Nat.add_sub_of_le leftLe
  have decomposed := corridor.inside.1.take_add_eq left.1 (right.1 - left.1)
  have intervalSub :
      ((corridor.inside.1.drop left.1).take
          (right.1 - left.1)).IsSubwalk
        ((corridor.inside.1.take left.1).append
          ((corridor.inside.1.drop left.1).take (right.1 - left.1))) :=
    SimpleGraph.Walk.isSubwalk_of_append_right rfl
  have inAppend := intervalSub.support_subset innerMem
  have supportEq : (corridor.inside.1.take right.1).support =
      ((corridor.inside.1.take left.1).append
        ((corridor.inside.1.drop left.1).take (right.1 - left.1))).support := by
    have supportEq0 := congrArg SimpleGraph.Walk.support decomposed
    simp only [SimpleGraph.Walk.support_copy] at supportEq0
    calc
      (corridor.inside.1.take right.1).support =
          (corridor.inside.1.take
            (left.1 + (right.1 - left.1))).support := by rw [sum]
      _ = _ := supportEq0
  rwa [supportEq]

end Corridor

namespace Corridor

/-- The foot of a corridor lies in every prefix support. -/
theorem foot_mem_prefixSupport (corridor : Corridor object windows component)
    (n : Nat) : corridor.entryStub.1 ∈ corridor.prefixSupport n := by
  classical
  refine (corridor.mem_prefixSupport n _).2 ⟨_, SimpleGraph.Walk.start_mem_support _, ?_⟩
  simp [stubFoot, Corridor.entryStub]

end Corridor

namespace Corridor

/-- The table record read at one actual corridor segment.  Every field is a
projection of the declared presentation; the only additional entry is the
false target bit of the selected counterexample branch. -/
noncomputable def recordAt {S : DeclaredSignature}
    (corridor : Corridor object windows component)
    (presentation : Presentation.{u} S object)
    (index : corridor.Segment → presentation.Segment)
    (segment : corridor.Segment) : Record S :=
  { boundaryDegrees := presentation.boundaryDegrees (index segment)
    stubs := presentation.halfEdges (index segment)
    offsets := presentation.offsets (index segment)
    state := presentation.state (index segment)
    truth := false }

/-- The literal (F5) witness carried by one selected cold half-edge.  This is
the mathematical payload of node `[153]`; it is a predicate on the actual
corridor, presentation, and germ, not a transport structure.  In the repeated
arm it retains not only equality of the two finite states, but the induced
equality of every supported generated reading (including (D8)) and the full
table record at both endpoints.  Thus no declared coordinate proved equal by
the first repeat is forgotten when the germ is published. -/
noncomputable def FirstFailureGermWitness {S : DeclaredSignature}
    {Baseline Target : FiniteObject.{u} → Prop}
    (baselineInvariant : FiniteObject.IsomorphismInvariant Baseline)
    (targetInvariant : FiniteObject.IsomorphismInvariant Target)
    (corridor : Corridor object windows component)
    (presentation : Presentation.{u} S object)
    (index : corridor.Segment → presentation.Segment)
    (germ : BoundedGerm S Baseline Target object) : Prop :=
  germ.support.card ≤ exchangeBound S ∧
    (∀ vertex ∈ germ.support,
      vertex ∈ corridor.inside.1.support.map (fun inner => inner.1)) ∧
    ((corridor.TerminalCorridor S ∧
        germ.support = corridor.prefixSupport corridor.statesRead ∧
        let terminal : corridor.Segment :=
          ⟨corridor.inside.1.length, Nat.lt_succ_self _⟩
        germ.record = corridor.recordAt presentation index terminal) ∨
      ∃ left right : corridor.Segment,
        right.1 ≤ stateBound S ∧ left.1 < right.1 ∧
          presentation.state (index left) = presentation.state (index right) ∧
          (∀ coordinate : Generated S,
            presentation.support (index left) coordinate ⊆
                ↑(presentation.activeInterface (index left)) →
              presentation.reading (index left) coordinate =
                presentation.reading (index right) coordinate) ∧
          (∀ earlierLeft earlierRight : corridor.Segment,
            earlierLeft.1 < earlierRight.1 → earlierRight.1 < right.1 →
              presentation.state (index earlierLeft) ≠
                presentation.state (index earlierRight)) ∧
          germ.support = corridor.intervalSupport left right ∧
          germ.record = corridor.recordAt presentation index left ∧
          germ.record = corridor.recordAt presentation index right)

/-- The support of an (F5) germ lies in the first `Q_cold` corridor steps.
This is the precise bounded-prefix fact used by the manuscript before applying
the subcubic ball estimate. -/
theorem FirstFailureGermWitness.support_subset_statePrefix
    {S : DeclaredSignature} {Baseline Target : FiniteObject.{u} → Prop}
    (baselineInvariant : FiniteObject.IsomorphismInvariant Baseline)
    (targetInvariant : FiniteObject.IsomorphismInvariant Target)
    (corridor : Corridor object windows component)
    (presentation : Presentation.{u} S object)
    (index : corridor.Segment → presentation.Segment)
    (germ : BoundedGerm S Baseline Target object)
    (witness : corridor.FirstFailureGermWitness baselineInvariant targetInvariant
      presentation index germ) :
    germ.support ⊆ corridor.prefixSupport (stateBound S) := by
  rcases witness.2.2 with terminal | repeated
  · obtain ⟨terminalBound, supportEq, _record⟩ := terminal
    rw [supportEq]
    exact corridor.prefixSupport_mono terminalBound
  · obtain ⟨left, right, rightBound, before, _same, _readings, _first, supportEq,
    _leftRecord, _rightRecord⟩ := repeated
    rw [supportEq]
    exact (corridor.intervalSupport_subset_prefixSupport left right
      (Nat.le_of_lt before)).trans (corridor.prefixSupport_mono rightBound)

/-- The exact trace endpoint at which (F5) fires.  In the terminal case it is
`statesRead`; in the repeated case it is the first repeated right endpoint.
Keeping this endpoint prevents the multiplicity argument from inspecting
corridor vertices that occur only after the paper's first failure. -/
theorem FirstFailureGermWitness.exists_traceEnd
    {S : DeclaredSignature} {Baseline Target : FiniteObject.{u} → Prop}
    (baselineInvariant : FiniteObject.IsomorphismInvariant Baseline)
    (targetInvariant : FiniteObject.IsomorphismInvariant Target)
    (corridor : Corridor object windows component)
    (presentation : Presentation.{u} S object)
    (index : corridor.Segment → presentation.Segment)
    (germ : BoundedGerm S Baseline Target object)
    (witness : corridor.FirstFailureGermWitness baselineInvariant targetInvariant
      presentation index germ) :
    ∃ traceEnd : Nat, traceEnd ≤ stateBound S ∧
      germ.support ⊆ corridor.prefixSupport traceEnd := by
  rcases witness.2.2 with terminal | repeated
  · obtain ⟨terminalBound, supportEq, _record⟩ := terminal
    refine ⟨corridor.statesRead, terminalBound, ?_⟩
    rw [supportEq]
  · obtain ⟨left, right, rightBound, before, _same, _readings, _first, supportEq,
    _leftRecord, _rightRecord⟩ := repeated
    refine ⟨right.1, rightBound, ?_⟩
    rw [supportEq]
    exact corridor.intervalSupport_subset_prefixSupport left right
      (Nat.le_of_lt before)

set_option maxHeartbeats 800000 in
/-- If the trace up to the actual first-failure endpoint is subcubic, every
vertex of its germ is within the manuscript's `M_cold + 2` ball of the
originating window endpoint.  This is the geometric input to the multiplicity
estimate; the origin is the corridor's actual entry stub. -/
lemma FirstFailureGermWitness.source_mem_subcubicReach_of_trace
    {S : DeclaredSignature} {Baseline Target : FiniteObject.{u} → Prop}
    (corridor : Corridor object windows component)
    (germ : BoundedGerm S Baseline Target object)
    (traceEnd : Nat) (traceEndBound : traceEnd ≤ stateBound S)
    (supportInTrace : germ.support ⊆ corridor.prefixSupport traceEnd)
    (threshold : Nat)
    (prefixSubcubic : ∀ vertex ∈ corridor.prefixSupport traceEnd,
      object.degree vertex ≤ threshold)
    (sourceSubcubic : object.degree corridor.entryStub.2 ≤ threshold)
    {vertex : object.Vertex} (vertexMem : vertex ∈ germ.support) :
    corridor.entryStub.2 ∈
      @Graph.SubcubicReach.reach object.Vertex
        (@FinEnum.instFintype _ object.vertices) object.graph
        (object.vertexFinset.filter
          fun current => object.degree current ≤ threshold)
        vertex (exchangeBound S + 2) vertex := by
  classical
  letI : FinEnum object.Vertex := object.vertices
  letI : Fintype object.Vertex := @FinEnum.instFintype _ object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  have inPrefix : vertex ∈ corridor.prefixSupport traceEnd :=
    supportInTrace vertexMem
  obtain ⟨inner, innerMem, innerEq⟩ :=
    (corridor.mem_prefixSupport traceEnd vertex).1 inPrefix
  let short := corridor.inside.1.take traceEnd
  let toInner := short.takeUntil inner innerMem
  let embedding := object.induceEmbedding component
  let backwards := toInner.reverse.map embedding.toHom
  have startEq : embedding inner = vertex := by
    exact innerEq
  have endEq : embedding
      (Graph.ColdCorridor.stubFoot object windows component corridor.entry) =
        corridor.entryStub.1 := by
    rfl
  let toFoot : object.graph.Walk vertex corridor.entryStub.1 :=
    backwards.copy startEq endEq
  have entryFacts := (mem_boundaryStubs_iff object windows component _).1
    (List.get_mem _ corridor.entry)
  let joined : object.graph.Walk vertex corridor.entryStub.2 :=
    toFoot.concat entryFacts.2.2
  let path := joined.toPath
  refine (Graph.SubcubicReach.mem_reach object.graph).2 ⟨path.1, path.2, ?_, ?_, ?_⟩
  · calc
      path.1.length ≤ joined.length := joined.length_bypass_le_length
      _ = toFoot.length + 1 := SimpleGraph.Walk.length_concat _ _
      _ = toInner.length + 1 := by
        simp [toFoot, backwards]
      _ ≤ short.length + 1 :=
        Nat.add_le_add_right (short.length_takeUntil_le_length innerMem) 1
      _ ≤ traceEnd + 1 := by
        simp [short, SimpleGraph.Walk.take_length]
      _ ≤ stateBound S + 1 := Nat.add_le_add_right traceEndBound 1
      _ ≤ exchangeBound S + 2 := by
        unfold exchangeBound interfaceBudget
        omega
  · intro current currentMem
    have currentJoined : current ∈ joined.support :=
      SimpleGraph.Walk.support_toPath_subset_support joined
        (List.mem_of_mem_dropLast currentMem)
    rw [SimpleGraph.Walk.support_concat] at currentJoined
    simp only [List.mem_append, List.mem_singleton] at currentJoined
    refine Finset.mem_filter.2 ⟨object.mem_vertexFinset _, ?_⟩
    rcases currentJoined with currentFoot | currentSource
    · have currentBackwards : current ∈ backwards.support := by
        simpa [toFoot, SimpleGraph.Walk.support_copy] using currentFoot
      simp only [backwards, SimpleGraph.Walk.support_map, List.mem_map] at currentBackwards
      obtain ⟨inside, insideMem, rfl⟩ := currentBackwards
      have insideToInner : inside ∈ toInner.support := by
        simpa [toInner, SimpleGraph.Walk.support_reverse] using insideMem
      have insideShort : inside ∈ short.support :=
        short.support_takeUntil_subset_support innerMem insideToInner
      apply prefixSubcubic inside.1
      exact (corridor.mem_prefixSupport traceEnd _).2
        ⟨inside, by simpa [short] using insideShort, rfl⟩
    · simpa [currentSource] using sourceSubcubic
  · intro nonnil same
    have adjacent := path.1.adj_getVert_succ
      (i := 0) (by simpa [SimpleGraph.Walk.not_nil_iff_lt_length] using nonnil)
    exact adjacent.ne (by simpa [SimpleGraph.Walk.getVert_zero, same])

end Corridor

/-! ## The selected branch-excess half-edges and their germs

`def:cold-skeleton-excess`: *"keep one incident half-edge for every edge of `G`
leaving `P` … the first two stubs of `P` are called the transit stubs; the
remaining `s(P)−2` stubs are the selected branch-excess half-edges of `P`."*
Node `[168]` applies the manuscript's endpoint repair by selecting from the
eleven interior single-stub incidences and absorbing two corridor ends. -/

section Family

variable (object : FiniteObject.{u})

/-- The external stubs `(w, u)` of a window, in the object's own enumeration
order (the manuscript's "lexicographic" order). -/
noncomputable def externalStubList (window : Finset object.Vertex) :
    List (object.Vertex × object.Vertex) := by
  classical
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  exact (FinEnum.toList (object.Vertex × object.Vertex)).filter fun stub =>
    decide (stub.1 ∈ window ∧ stub.2 ∉ window ∧ object.graph.Adj stub.1 stub.2)

theorem mem_externalStubList (window : Finset object.Vertex)
    (stub : object.Vertex × object.Vertex) :
    stub ∈ externalStubList object window ↔
      stub.1 ∈ window ∧ stub.2 ∉ window ∧ object.graph.Adj stub.1 stub.2 := by
  classical
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  simp only [externalStubList, List.mem_filter, decide_eq_true_eq]
  exact ⟨fun member => member.2, fun isStub => ⟨FinEnum.mem_toList _, isStub⟩⟩

theorem externalStubList_nodup (window : Finset object.Vertex) :
    (externalStubList object window).Nodup := by
  classical
  letI : FinEnum object.Vertex := object.vertices
  exact List.Nodup.filter _ FinEnum.nodup_toList

/-- The external stubs whose window endpoint is an interior vertex of the
ambient-cubic path.  At the registered cubic baseline this is exactly the
sublist whose endpoint has one external neighbour. -/
noncomputable def interiorStubList (window : Finset object.Vertex) :
    List (object.Vertex × object.Vertex) := by
  classical
  exact (externalStubList object window).filter fun stub =>
    decide ((object.externalNeighbours window stub.1).card = 1)

theorem interiorStubList_nodup (window : Finset object.Vertex) :
    (interiorStubList object window).Nodup := by
  classical
  exact (externalStubList_nodup object window).filter _

/-- Counting the interior-stub list fibrewise gives the sum of the external
degrees of its one-stub window endpoints. -/
theorem interiorStubList_length_eq_sum (window : Finset object.Vertex) :
    (interiorStubList object window).length =
      ∑ vertex ∈ window.filter (fun vertex =>
        (object.externalNeighbours window vertex).card = 1),
        (object.externalNeighbours window vertex).card := by
  classical
  let stubsAt : object.Vertex → Finset (object.Vertex × object.Vertex) :=
    fun vertex => (object.externalNeighbours window vertex).image fun outside =>
      (vertex, outside)
  have listFinset : (interiorStubList object window).toFinset =
      (window.filter fun vertex =>
        (object.externalNeighbours window vertex).card = 1).biUnion stubsAt := by
    ext stub
    simp only [interiorStubList, List.mem_toFinset, List.mem_filter,
      decide_eq_true_eq, Finset.mem_biUnion, Finset.mem_filter]
    constructor
    · intro member
      have external := (mem_externalStubList object window stub).1 member.1
      refine ⟨stub.1, ⟨external.1, member.2⟩, ?_⟩
      refine Finset.mem_image.2 ⟨stub.2, ?_, rfl⟩
      simp only [FiniteObject.externalNeighbours, Finset.mem_filter,
        SimpleGraph.mem_neighborFinset]
      exact ⟨external.2.2, external.2.1⟩
    · rintro ⟨vertex, ⟨vertexMem, one⟩, stubMem⟩
      obtain ⟨outside, outsideMem, rfl⟩ := Finset.mem_image.1 stubMem
      simp only [FiniteObject.externalNeighbours, Finset.mem_filter,
        SimpleGraph.mem_neighborFinset] at outsideMem
      refine ⟨(mem_externalStubList object window _).2 ?_, one⟩
      exact ⟨vertexMem, outsideMem.2, outsideMem.1⟩
  rw [← List.toFinset_card_of_nodup (interiorStubList_nodup object window),
    listFinset, Finset.card_biUnion]
  · refine Finset.sum_congr rfl fun vertex _ => ?_
    exact Finset.card_image_of_injective _ fun left right same =>
      congrArg Prod.snd same
  · intro left _ right _ different
    change Disjoint (stubsAt left) (stubsAt right)
    rw [Finset.disjoint_left]
    intro stub leftMem rightMem
    obtain ⟨leftOutside, _, leftEq⟩ := Finset.mem_image.1 leftMem
    obtain ⟨rightOutside, _, rightEq⟩ := Finset.mem_image.1 rightMem
    apply different
    exact congrArg Prod.fst (leftEq.trans rightEq.symm)

/-- **The selected branch-excess half-edges of a window**: its interior stubs
with the two absorbed corridor ends dropped.  Thus an ambient-cubic window of
order `r` contributes the manuscript's `(r - 2) - 2` selected incidences. -/
noncomputable def selectedStubs (window : Finset object.Vertex) :
    Finset (object.Vertex × object.Vertex) := by
  classical
  exact ((interiorStubList object window).drop 2).toFinset

theorem card_selectedStubs (window : Finset object.Vertex) :
    (selectedStubs object window).card = (interiorStubList object window).length - 2 := by
  classical
  simp only [selectedStubs]
  rw [List.toFinset_card_of_nodup ((interiorStubList_nodup object window).sublist
    (List.drop_sublist _ _))]
  simp

/-- Membership in the selected family retains the defining one-stub interior
incidence. -/
theorem mem_selectedStubs_isInterior {window : Finset object.Vertex}
    {stub : object.Vertex × object.Vertex} (member : stub ∈ selectedStubs object window) :
    (object.externalNeighbours window stub.1).card = 1 := by
  classical
  simp only [selectedStubs, List.mem_toFinset] at member
  have interior := List.mem_of_mem_drop member
  simp only [interiorStubList, List.mem_filter, decide_eq_true_eq] at interior
  exact interior.2

theorem mem_selectedStubs_isStub {window : Finset object.Vertex}
    {stub : object.Vertex × object.Vertex} (member : stub ∈ selectedStubs object window) :
    stub.1 ∈ window ∧ stub.2 ∉ window ∧ object.graph.Adj stub.1 stub.2 := by
  classical
  simp only [selectedStubs, List.mem_toFinset] at member
  have interior := List.mem_of_mem_drop member
  simp only [interiorStubList, List.mem_filter] at interior
  exact (mem_externalStubList object window stub).1 interior.1

/-- All selected half-edges of a family of windows. -/
noncomputable def allSelectedStubs (family : Finset (Finset object.Vertex)) :
    Finset (object.Vertex × object.Vertex) := by
  classical
  exact family.biUnion (selectedStubs object)

theorem card_allSelectedStubs (family : Finset (Finset object.Vertex))
    (disjoint : ∀ left ∈ family, ∀ right ∈ family, left ≠ right → Disjoint left right) :
    (allSelectedStubs object family).card =
      ∑ window ∈ family, ((interiorStubList object window).length - 2) := by
  classical
  simp only [allSelectedStubs]
  rw [Finset.card_biUnion]
  · exact Finset.sum_congr rfl fun window _ => card_selectedStubs object window
  · intro left leftMem right rightMem different
    show Disjoint (selectedStubs object left) (selectedStubs object right)
    rw [Finset.disjoint_left]
    intro stub leftStub rightStub
    have := (mem_selectedStubs_isStub object leftStub).1
    have := (mem_selectedStubs_isStub object rightStub).1
    exact Finset.disjoint_left.mp (disjoint left leftMem right rightMem different) ‹_› ‹_›

end Family

/-! ## Selected half-edges in the cold-window union -/

section Germ

variable (object : FiniteObject.{u})

/-- The foot of an outside stub lies in its own outside component. -/
theorem foot_mem_outsideComponentOf (windows : Finset object.Vertex)
    (foot : object.Vertex) (footOutside : foot ∉ windows) :
    foot ∈ outsideComponentOf object windows foot footOutside := by
  classical
  letI : FinEnum object.Vertex := object.vertices
  simp only [outsideComponentOf, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨(mem_outsideSupport object windows foot).2 footOutside, SimpleGraph.Reachable.refl _⟩

/-- `X_cold`: the union of a family of windows. -/
noncomputable def windowsOf (family : Finset (Finset object.Vertex)) : Finset object.Vertex := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  exact family.biUnion id

theorem mem_windowsOf (family : Finset (Finset object.Vertex)) (vertex : object.Vertex) :
    vertex ∈ windowsOf object family ↔ ∃ window ∈ family, vertex ∈ window := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  simp [windowsOf]

/-- A selected half-edge of a family: its window endpoint lies in the family's
union and it is an edge. -/
theorem selected_facts (family : Finset (Finset object.Vertex))
    (stub : {stub // stub ∈ allSelectedStubs object family}) :
    stub.1.1 ∈ windowsOf object family ∧ object.graph.Adj stub.1.1 stub.1.2 := by
  classical
  obtain ⟨window, windowMem, stubMem⟩ := Finset.mem_biUnion.1 stub.2
  have isStub := mem_selectedStubs_isStub object stubMem
  exact ⟨(mem_windowsOf object family _).2 ⟨window, windowMem, isStub.1⟩, isStub.2.2⟩

/-! ## `lem:cold-window-stub-excess`: an ambient-cubic window has `δ·order − 2(order−1)` stubs -/

section StubCount

variable (object : FiniteObject.{u})

open scoped Classical in
/-- The ordered adjacent pairs of the path graph on `n` vertices number
`2(n−1)`. -/
theorem card_pathGraph_adjPairs (n : Nat) :
    ((Finset.univ : Finset (Fin n × Fin n)).filter
      fun pair : Fin n × Fin n => (SimpleGraph.pathGraph n).Adj pair.1 pair.2).card =
      2 * (n - 1) := by
  classical
  cases n with
  | zero => simp
  | succ m =>
      let forward : Finset (Fin (m + 1) × Fin (m + 1)) :=
        (Finset.univ : Finset (Fin m)).image fun i =>
          (⟨i.1, by omega⟩, ⟨i.1 + 1, by omega⟩)
      let backward : Finset (Fin (m + 1) × Fin (m + 1)) :=
        (Finset.univ : Finset (Fin m)).image fun i =>
          (⟨i.1 + 1, by omega⟩, ⟨i.1, by omega⟩)
      have forwardCard : forward.card = m := by
        rw [Finset.card_image_of_injective]
        · simp
        · intro a b same
          simp only [Prod.mk.injEq, Fin.mk.injEq] at same
          exact Fin.ext same.1
      have backwardCard : backward.card = m := by
        rw [Finset.card_image_of_injective]
        · simp
        · intro a b same
          simp only [Prod.mk.injEq, Fin.mk.injEq] at same
          exact Fin.ext same.2
      have disjoint : Disjoint forward backward := by
        rw [Finset.disjoint_left]
        intro pair inForward inBackward
        simp only [forward, Finset.mem_image, Finset.mem_univ, true_and] at inForward
        simp only [backward, Finset.mem_image, Finset.mem_univ, true_and] at inBackward
        obtain ⟨i, rfl⟩ := inForward
        obtain ⟨j, same⟩ := inBackward
        simp only [Prod.mk.injEq, Fin.mk.injEq] at same
        omega
      have split : ((Finset.univ : Finset (Fin (m + 1) × Fin (m + 1))).filter
          fun pair : Fin (m + 1) × Fin (m + 1) =>
            (SimpleGraph.pathGraph (m + 1)).Adj pair.1 pair.2) = forward ∪ backward := by
        ext pair
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, forward,
          backward, Finset.mem_image, SimpleGraph.pathGraph_adj]
        constructor
        · rintro (h | h)
          · left
            refine ⟨⟨pair.1.1, by omega⟩, ?_⟩
            ext <;> simp [h]
          · right
            refine ⟨⟨pair.2.1, by omega⟩, ?_⟩
            ext <;> simp [h]
        · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩)
          · left; rfl
          · right; rfl
      rw [split, Finset.card_union_of_disjoint disjoint, forwardCard, backwardCard]
      omega

/-- **The external stubs of an ambient-cubic induced window** number exactly
`δ·order − 2(order − 1)`.  The addition form avoids hiding a
truncated subtraction in the generic graph statement. -/
theorem externalStubList_length_add_internal_eq_stubCount {order threshold : Nat}
    (window : Finset object.Vertex)
    (induces : object.InducesWindow order window)
    (cubic : ∀ vertex ∈ window, object.degree vertex = threshold) :
    (externalStubList object window).length + 2 * (order - 1) =
      threshold * order := by
  classical
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  letI : DecidableEq object.Vertex := object.vertices.decEq
  obtain ⟨⟨embedding⟩, cardinality⟩ := induces
  let inside : Finset (object.Vertex × object.Vertex) :=
    (window ×ˢ window).filter fun pair : object.Vertex × object.Vertex =>
      object.graph.Adj pair.1 pair.2
  let outside : Finset (object.Vertex × object.Vertex) :=
    (window ×ˢ Finset.univ).filter fun pair : object.Vertex × object.Vertex =>
      pair.2 ∉ window ∧ object.graph.Adj pair.1 pair.2
  have outsideCard : outside.card = (externalStubList object window).length := by
    rw [← List.toFinset_card_of_nodup (externalStubList_nodup object window)]
    apply congrArg Finset.card
    ext pair
    simp only [outside, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true,
      List.mem_toFinset, mem_externalStubList]
  have insideFibre : ∀ vertex ∈ window,
      (inside.filter fun pair : object.Vertex × object.Vertex => pair.1 = vertex) =
        ((object.graph.neighborFinset vertex).filter (· ∈ window)).image (Prod.mk vertex) := by
    intro vertex vertexMem
    ext pair
    simp only [inside, Finset.mem_filter, Finset.mem_product, Finset.mem_image,
      SimpleGraph.mem_neighborFinset]
    constructor
    · rintro ⟨⟨⟨_, second⟩, adjacent⟩, rfl⟩
      exact ⟨pair.2, ⟨adjacent, second⟩, rfl⟩
    · rintro ⟨w, ⟨adjacent, second⟩, rfl⟩
      exact ⟨⟨⟨vertexMem, second⟩, adjacent⟩, rfl⟩
  have outsideFibre : ∀ vertex ∈ window,
      (outside.filter fun pair : object.Vertex × object.Vertex => pair.1 = vertex) =
        ((object.graph.neighborFinset vertex).filter (· ∉ window)).image (Prod.mk vertex) := by
    intro vertex vertexMem
    ext pair
    simp only [outside, Finset.mem_filter, Finset.mem_product, Finset.mem_image,
      SimpleGraph.mem_neighborFinset, Finset.mem_univ, and_true]
    constructor
    · rintro ⟨⟨_, ⟨second, adjacent⟩⟩, rfl⟩
      exact ⟨pair.2, ⟨adjacent, second⟩, rfl⟩
    · rintro ⟨w, ⟨adjacent, second⟩, rfl⟩
      exact ⟨⟨vertexMem, ⟨second, adjacent⟩⟩, rfl⟩
  have degreeSplit :
      ∑ vertex ∈ window, object.degree vertex = inside.card + outside.card := by
    have insideSum : inside.card =
        ∑ vertex ∈ window, ((object.graph.neighborFinset vertex).filter (· ∈ window)).card := by
      rw [Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (t := window)]
      · refine Finset.sum_congr rfl fun vertex vertexMem => ?_
        rw [insideFibre vertex vertexMem,
          Finset.card_image_of_injective _ (Prod.mk_right_injective vertex)]
      · intro pair member
        exact (Finset.mem_product.1 (Finset.mem_filter.1 member).1).1
    have outsideSum : outside.card =
        ∑ vertex ∈ window, ((object.graph.neighborFinset vertex).filter (· ∉ window)).card := by
      rw [Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (t := window)]
      · refine Finset.sum_congr rfl fun vertex vertexMem => ?_
        rw [outsideFibre vertex vertexMem,
          Finset.card_image_of_injective _ (Prod.mk_right_injective vertex)]
      · intro pair member
        exact (Finset.mem_product.1 (Finset.mem_filter.1 member).1).1
    rw [insideSum, outsideSum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun vertex _ => ?_
    have := Finset.card_filter_add_card_filter_not
      (s := object.graph.neighborFinset vertex) (p := (· ∈ window))
    rw [this]
    simp [FiniteObject.degree, SimpleGraph.card_neighborFinset_eq_degree]
  have insideCard : inside.card = 2 * (order - 1) := by
    rw [← card_pathGraph_adjPairs order]
    let toVertex : Fin order → object.Vertex := fun index => (embedding index).1
    have toVertexInj : Function.Injective toVertex := by
      intro a b same
      exact embedding.injective (Subtype.ext same)
    have toVertexRange : ∀ vertex ∈ window, ∃ index, toVertex index = vertex := by
      intro vertex member
      have imageCard : (Finset.univ.image toVertex).card = order := by
        rw [Finset.card_image_of_injective _ toVertexInj]; simp
      have imageSubset : Finset.univ.image toVertex ⊆ window := by
        intro v hv
        obtain ⟨index, _, rfl⟩ := Finset.mem_image.1 hv
        exact (embedding index).2
      have imageEq : Finset.univ.image toVertex = window :=
        Finset.eq_of_subset_of_card_le imageSubset (by rw [imageCard, cardinality])
      rw [← imageEq] at member
      obtain ⟨index, _, eq⟩ := Finset.mem_image.1 member
      exact ⟨index, eq⟩
    symm
    apply Finset.card_bij (fun (pair : Fin order × Fin order) _ =>
      (toVertex pair.1, toVertex pair.2))
    · intro pair member
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at member
      simp only [inside, Finset.mem_filter, Finset.mem_product]
      exact ⟨⟨(embedding pair.1).2, (embedding pair.2).2⟩, embedding.map_adj_iff.2 member⟩
    · intro a _ b _ same
      simp only [Prod.mk.injEq] at same
      exact Prod.ext (toVertexInj same.1) (toVertexInj same.2)
    · intro pair member
      simp only [inside, Finset.mem_filter, Finset.mem_product] at member
      obtain ⟨i, hi⟩ := toVertexRange pair.1 member.1.1
      obtain ⟨j, hj⟩ := toVertexRange pair.2 member.1.2
      refine ⟨(i, j), ?_, by simp [hi, hj]⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      apply embedding.map_adj_iff.1
      change object.graph.Adj (toVertex i) (toVertex j)
      rw [hi, hj]
      exact member.2
  have degreeConst : ∑ vertex ∈ window, object.degree vertex = threshold * order := by
    rw [Finset.sum_congr rfl cubic, Finset.sum_const, cardinality, smul_eq_mul, Nat.mul_comm]
  omega

end StubCount


/-!
The multiplicity, high-degree-loss, and overlap estimates belong to the actual
first-failure incidence published at node `[153]`.  This module does not
reconstruct that incidence from the ambient graph.
-/

end Germ

end Hypostructure.Graph.ColdCorridor
