import Hypostructure.Graph.Target
import Hypostructure.Graph.Strategy.Official.Features.DeletionFanIncidence

/-!
# Fan-compatible open ports at a high centre

This file is the graph-mathematics content of nodes `[69]` and `[79]` of the
manuscript: `def:heavy-center-triangular-port` (open and triangular surplus
ports), `lem:heavy-neighbourhood-normal-form`, `def:fan-compatible-open-ports`,
`lem:same-center-open-port-compatibility`,
`lem:heavy-center-triangular-alternative` and
`cor:heavy-center-local-dichotomy`.

Everything is stated over a bare `Graph.FiniteObject`.  The two ambient facts
that the manuscript's invariants supply are isolated in `LocalHypotheses`:

* every edge of `G` has an endpoint of degree exactly three (invariants 3 and 4,
  i.e. edge-deletion criticality; `LocalHypotheses.ofDeletionCriticality`
  reads it off the framework's `DeletionCriticalityCertificate` at threshold
  `3`, which is itself the graph reading of the two entries Core appended at
  manuscript nodes `[9]`--`[10]`, `Graph.deletionCriticalityOfLedger`);
* `G` carries no accepted cycle and length four is accepted (the
  Mersenne-return target of invariant 1, specialised to the four-cycle
  `2^2`; `HasCycleWithLength` is the framework's cycle target).

All shoulder data is the framework's `outsideIncidences` schedule, so no second
neighbour model is introduced.
-/

namespace Hypostructure.Graph.TypeBOpenPorts

open Hypostructure.Graph
open Hypostructure.Graph.Strategy.Official.Features.DeletionFanIncidence
open scoped Sym2

universe u v

variable {object : FiniteObject.{u}}

/-! ## Surplus ports and their shoulder schedules -/

/-- A surplus port `p = (h, x)` of `def:surplus-ports`: an ordered edge from its
centre `h` to its endpoint `x`. -/
structure Port (object : FiniteObject.{u}) where
  /-- The centre `c(p) = h`. -/
  center : object.Vertex
  /-- The endpoint `x(p) = x`. -/
  endpoint : object.Vertex
  /-- `hx` is an edge of `G`. -/
  adjacent : object.graph.Adj center endpoint

namespace Port

variable (p : Port object)

/-- The shoulder schedule `s(p)`: the neighbours of the endpoint other than the
centre, in the ambient scan order.  This is literally the framework's
`outsideIncidences` list, not a second neighbour model. -/
def shoulders : List object.Vertex :=
  outsideIncidences object p.center p.endpoint

variable {p}

theorem mem_shoulders_iff (z : object.Vertex) :
    z ∈ p.shoulders ↔ z ≠ p.center ∧ object.graph.Adj p.endpoint z := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  rw [shoulders, outsideIncidences,
    (object.orderedNeighbors_nodup p.endpoint).mem_erase_iff,
    object.mem_orderedNeighbors_iff]

theorem shoulder_adj {z : object.Vertex} (member : z ∈ p.shoulders) :
    object.graph.Adj p.endpoint z :=
  (mem_shoulders_iff z).mp member |>.2

theorem shoulder_ne_center {z : object.Vertex} (member : z ∈ p.shoulders) :
    z ≠ p.center :=
  (mem_shoulders_iff z).mp member |>.1

variable (p)

theorem shoulders_nodup : p.shoulders.Nodup := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  rw [shoulders, outsideIncidences]
  exact (object.orderedNeighbors_nodup p.endpoint).erase _

theorem center_not_mem_shoulders : p.center ∉ p.shoulders :=
  fun member => shoulder_ne_center member rfl

theorem endpoint_not_mem_shoulders : p.endpoint ∉ p.shoulders :=
  fun member => (object.graph.irrefl (shoulder_adj member))

/-- With a cubic endpoint the shoulder schedule is the two-element pair
`s(p) = {a_p, b_p}` of `def:surplus-ports`. -/
theorem shoulders_length (cubic : object.degree p.endpoint = 3) :
    p.shoulders.length = 2 := by
  have counted : p.shoulders.length + 1 = object.degree p.endpoint :=
    outsideIncidences_length object p.adjacent
  omega

/-- `def:heavy-center-triangular-port`: the port is triangular when its shoulder
chord `e_p^* = a_p b_p` is an edge of `G`. -/
def IsTriangular : Prop :=
  ∃ left ∈ p.shoulders, ∃ right ∈ p.shoulders, object.graph.Adj left right

/-- `def:heavy-center-triangular-port`: the port is open when its shoulder chord
is absent from `G`. -/
def IsOpen : Prop :=
  ¬ p.IsTriangular

instance decidableIsTriangular : Decidable p.IsTriangular := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  letI : DecidableRel object.graph.Adj := object.decideAdj
  unfold IsTriangular
  infer_instance

instance decidableIsOpen : Decidable p.IsOpen := by
  unfold IsOpen
  infer_instance

/-- The two local Type B carriers of a port: the incidences of the endpoint that
avoid the centre, recorded as ambient edges. -/
def shoulderCarriers : List (Sym2 object.Vertex) :=
  p.shoulders.map fun shoulder => s(p.endpoint, shoulder)

theorem shoulderCarriers_length :
    p.shoulderCarriers.length = p.shoulders.length :=
  List.length_map _

theorem shoulderCarriers_nodup : p.shoulderCarriers.Nodup := by
  refine p.shoulders_nodup.map_on ?_
  intro left leftMem right rightMem equal
  rcases Sym2.eq_iff.mp equal with ⟨_, same⟩ | ⟨endpointEq, _⟩
  · exact same
  · exact absurd (endpointEq ▸ shoulder_adj rightMem) (object.graph.irrefl)

end Port

/-! ## Standing local hypotheses -/

/-- The two ambient facts consumed by the local Type B split at a high centre.

`cubicEndpoint` is invariant 3 (edge-deletion criticality); together with
`4 ≤ d_G(h)` it yields invariant 4 (high-degree independence) and part (a) of
`lem:heavy-neighbourhood-normal-form`.  `fourAccepted` is the four-cycle
instance `4 = 2 ^ 2` of the registered dyadic-cycle target -- a fact about the
target predicate, discharged at the registration site.  The absence of that
cycle is deliberately *not* a field here: it is read off the incoming residual
as `ctx.avoids`. -/
structure LocalHypotheses (LengthOK : Nat → Prop)
    (object : FiniteObject.{u}) : Prop where
  /-- Every edge of `G` has an endpoint of degree exactly three. -/
  cubicEndpoint : ∀ ⦃left right : object.Vertex⦄, object.graph.Adj left right →
    object.degree left = 3 ∨ object.degree right = 3
  /-- Four is an accepted cycle length.  This is a fact about the *registered
  target predicate*, discharged once at the registration site (for the EG target
  `4 = 2 ^ 2`); it is not a hypothesis about the graph. -/
  fourAccepted : LengthOK 4

namespace LocalHypotheses

variable {LengthOK : Nat → Prop}

/-- The framework's deletion-criticality certificate at threshold three supplies
the cubic-endpoint hypothesis; the minimal counterexample context supplies the
missing accepted cycle. -/
theorem ofDeletionCriticality
    {Baseline : FiniteObject.{u} → Prop}
    {BranchState : FiniteObject.{u} → Type v}
    {profile : DeletionCriticalityProfile Baseline}
    {ctx : Core.MinimalCounterexampleContext
      (problem Baseline BranchState) (HasCycleWithLength LengthOK)
      (lexicographicProgress Baseline BranchState)}
    (thresholdThree : profile.threshold = 3)
    (certificate : DeletionCriticalityCertificate profile ctx)
    (fourAccepted : LengthOK 4) :
    LocalHypotheses LengthOK ctx.G where
  cubicEndpoint := by
    intro left right adjacent
    have endpoint := certificate.tightEndpoint ⟨(left, right), adjacent⟩
    change ctx.G.degree left = profile.threshold ∨
      ctx.G.degree right = profile.threshold at endpoint
    rw [thresholdThree] at endpoint
    exact endpoint
  fourAccepted := fourAccepted

/-- A closed walk on four pairwise-compatible adjacencies would be an accepted
four-cycle, so no such configuration exists.

The absence of the cycle is **not** a hypothesis: it is `ctx.avoids`, the
target-avoidance the minimal-counterexample node already established and carries
on the residual.  A node that needed to *establish* it would register the cycle
schedule as a CT1 outcome and let Core route the hit to the target; a node
downstream of that, like this one, simply reads the avoiding fact. -/
theorem not_four_cycle
    {Baseline : FiniteObject.{u} → Prop}
    {BranchState : FiniteObject.{u} → Type v}
    {ctx : Core.MinimalCounterexampleContext
      (problem Baseline BranchState) (HasCycleWithLength LengthOK)
      (lexicographicProgress Baseline BranchState)}
    (hypotheses : LocalHypotheses LengthOK ctx.G)
    {first second third fourth : ctx.G.Vertex}
    (firstSecond : ctx.G.graph.Adj first second)
    (secondThird : ctx.G.graph.Adj second third)
    (thirdFourth : ctx.G.graph.Adj third fourth)
    (fourthFirst : ctx.G.graph.Adj fourth first)
    (firstThird : first ≠ third) (secondFourth : second ≠ fourth) : False := by
  have walkCycle :
      (SimpleGraph.Walk.cons firstSecond
        (SimpleGraph.Walk.cons secondThird
          (SimpleGraph.Walk.cons thirdFourth
            (SimpleGraph.Walk.cons fourthFirst .nil)))).IsCycle := by
    rw [SimpleGraph.Walk.cons_isCycle_iff]
    refine ⟨?_, ?_⟩
    · rw [SimpleGraph.Walk.isPath_def]
      simp [firstSecond.ne', secondThird.ne, thirdFourth.ne, fourthFirst.ne,
        firstThird.symm, secondFourth]
    · simp [firstSecond.ne, firstSecond.ne', secondThird.ne, fourthFirst.ne',
        firstThird, secondFourth]
  refine ctx.avoids ⟨⟨first, _, walkCycle, ?_⟩⟩
  simpa using hypotheses.fourAccepted

end LocalHypotheses

/-! ## `lem:heavy-neighbourhood-normal-form` -/

/-- The high-neighbourhood normal form at one high centre `h`.  Parts (a), (b)
and (c) are exactly the three fields. -/
structure NormalForm (object : FiniteObject.{u})
    (center : object.Vertex) : Prop where
  /-- `h` is a high centre: `d_G(h) ≥ 4`. -/
  high : 4 ≤ object.degree center
  /-- (a) Every vertex of `N_G(h)` has degree three. -/
  neighbourCubic : ∀ ⦃vertex : object.Vertex⦄,
    object.graph.Adj center vertex → object.degree vertex = 3
  /-- (b) `G[N_G(h)]` is a matching: a neighbour of `h` has at most one
  neighbour inside `N_G(h)`. -/
  inducedMatching : ∀ ⦃middle left right : object.Vertex⦄,
    object.graph.Adj center middle → object.graph.Adj center left →
    object.graph.Adj center right → object.graph.Adj middle left →
    object.graph.Adj middle right → left = right
  /-- (c) Two distinct neighbours of `h` have no common neighbour outside
  `{h}`. -/
  noCommonNeighbourOutside : ∀ ⦃left right other : object.Vertex⦄,
    object.graph.Adj center left → object.graph.Adj center right →
    left ≠ right → other ≠ center →
    object.graph.Adj left other → object.graph.Adj right other → False

namespace LocalHypotheses

variable {LengthOK : Nat → Prop}

/-- `lem:heavy-neighbourhood-normal-form`.

Parts (b) and (c) rest on the absence of an accepted four-cycle, which is read
off the incoming residual (`ctx.avoids`) rather than assumed. -/
theorem normalForm
    {Baseline : FiniteObject.{u} → Prop}
    {BranchState : FiniteObject.{u} → Type v}
    {ctx : Core.MinimalCounterexampleContext
      (problem Baseline BranchState) (HasCycleWithLength LengthOK)
      (lexicographicProgress Baseline BranchState)}
    (hypotheses : LocalHypotheses LengthOK ctx.G)
    {center : ctx.G.Vertex} (high : 4 ≤ ctx.G.degree center) :
    NormalForm ctx.G center where
  high := high
  neighbourCubic := by
    intro vertex adjacent
    rcases hypotheses.cubicEndpoint adjacent with centerCubic | vertexCubic
    · omega
    · exact vertexCubic
  inducedMatching := by
    intro middle left right centerMiddle centerLeft centerRight middleLeft
      middleRight
    by_contra distinct
    exact hypotheses.not_four_cycle centerLeft middleLeft.symm middleRight
      centerRight.symm centerMiddle.ne distinct
  noCommonNeighbourOutside := by
    intro left right other centerLeft centerRight distinct otherNeCenter
      leftOther rightOther
    exact hypotheses.not_four_cycle centerLeft leftOther rightOther.symm
      centerRight.symm (Ne.symm otherNeCenter) distinct

end LocalHypotheses

namespace NormalForm

variable {center : object.Vertex}

/-- Invariant 4 at the level of one centre: a high centre has no high
neighbour. -/
theorem neighbour_not_high (normal : NormalForm object center)
    {vertex : object.Vertex} (adjacent : object.graph.Adj center vertex) :
    ¬ 4 ≤ object.degree vertex := by
  rw [normal.neighbourCubic adjacent]
  omega

/-- At a high centre every port has a two-element shoulder pair. -/
theorem shoulders_length (normal : NormalForm object center)
    {p : Port object} (portCenter : p.center = center) :
    p.shoulders.length = 2 :=
  p.shoulders_length (normal.neighbourCubic (portCenter ▸ p.adjacent))

end NormalForm

/-! ## `def:fan-compatible-open-ports` -/

/-- `def:fan-compatible-open-ports`.  Two distinct open ports `p = (h, x)` and
`q = (h, y)` at the same centre are fan-compatible when
`x ∉ s(q)`, `y ∉ s(p)` and `s(p) ∩ s(q) = ∅`. -/
structure FanCompatible (p q : Port object) : Prop where
  /-- Both ports have the same centre `h`. -/
  sameCenter : p.center = q.center
  /-- `p` is open. -/
  leftOpen : p.IsOpen
  /-- `q` is open. -/
  rightOpen : q.IsOpen
  /-- The ports are distinct. -/
  endpointsNe : p.endpoint ≠ q.endpoint
  /-- `x ∉ s(q)`. -/
  leftNotShoulder : p.endpoint ∉ q.shoulders
  /-- `y ∉ s(p)`. -/
  rightNotShoulder : q.endpoint ∉ p.shoulders
  /-- `s(p) ∩ s(q) = ∅`. -/
  shouldersDisjoint : ∀ ⦃z : object.Vertex⦄, z ∈ p.shoulders →
    z ∉ q.shoulders

instance decidableFanCompatible (p q : Port object) :
    Decidable (FanCompatible p q) := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  exact decidable_of_iff
    (p.center = q.center ∧ p.IsOpen ∧ q.IsOpen ∧ p.endpoint ≠ q.endpoint ∧
      p.endpoint ∉ q.shoulders ∧ q.endpoint ∉ p.shoulders ∧
      ∀ z ∈ p.shoulders, z ∉ q.shoulders)
    ⟨fun data => ⟨data.1, data.2.1, data.2.2.1, data.2.2.2.1, data.2.2.2.2.1,
        data.2.2.2.2.2.1, fun _ member => data.2.2.2.2.2.2 _ member⟩,
      fun compatible => ⟨compatible.sameCenter, compatible.leftOpen,
        compatible.rightOpen, compatible.endpointsNe,
        compatible.leftNotShoulder, compatible.rightNotShoulder,
        fun _ member => compatible.shouldersDisjoint member⟩⟩

namespace FanCompatible

variable {p q : Port object}

theorem list_disjoint (compatible : FanCompatible p q) :
    p.shoulders.Disjoint q.shoulders :=
  fun _ left right => compatible.shouldersDisjoint left right

/-- Fan-compatibility is symmetric. -/
theorem symm (compatible : FanCompatible p q) : FanCompatible q p where
  sameCenter := compatible.sameCenter.symm
  leftOpen := compatible.rightOpen
  rightOpen := compatible.leftOpen
  endpointsNe := compatible.endpointsNe.symm
  leftNotShoulder := compatible.rightNotShoulder
  rightNotShoulder := compatible.leftNotShoulder
  shouldersDisjoint := fun _ left right => compatible.shouldersDisjoint right left

/-- The local Type B support of a compatible pair: the two endpoints together
with the two shoulder pairs. -/
def localSupport (p q : Port object) : List object.Vertex :=
  p.endpoint :: q.endpoint :: (p.shoulders ++ q.shoulders)

theorem center_not_mem_localSupport (compatible : FanCompatible p q) :
    p.center ∉ localSupport p q := by
  simp only [localSupport, List.mem_cons, List.mem_append, not_or]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro equal
    have adjacency : object.graph.Adj p.center p.endpoint := p.adjacent
    rw [equal] at adjacency
    exact object.graph.irrefl adjacency
  · intro equal
    have adjacency : object.graph.Adj p.center q.endpoint := by
      rw [compatible.sameCenter]
      exact q.adjacent
    rw [equal] at adjacency
    exact object.graph.irrefl adjacency
  · exact p.center_not_mem_shoulders
  · rw [compatible.sameCenter]
    exact q.center_not_mem_shoulders

/-- The six local vertices of a compatible pair are pairwise distinct.  All
three clauses of `def:fan-compatible-open-ports` are used. -/
theorem localSupport_nodup (compatible : FanCompatible p q) :
    (localSupport p q).Nodup := by
  refine List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨?_, ?_⟩⟩
  · simp only [List.mem_cons, List.mem_append, not_or]
    exact ⟨compatible.endpointsNe, p.endpoint_not_mem_shoulders,
      compatible.leftNotShoulder⟩
  · simp only [List.mem_append, not_or]
    exact ⟨compatible.rightNotShoulder, q.endpoint_not_mem_shoulders⟩
  · exact List.Nodup.append p.shoulders_nodup q.shoulders_nodup
      compatible.list_disjoint

theorem localSupport_length {center : object.Vertex}
    (normal : NormalForm object center)
    (compatible : FanCompatible p q) (portCenter : p.center = center) :
    (localSupport p q).length = 6 := by
  have leftLength : p.shoulders.length = 2 := normal.shoulders_length portCenter
  have rightLength : q.shoulders.length = 2 :=
    normal.shoulders_length (compatible.sameCenter ▸ portCenter)
  simp only [localSupport, List.length_cons, List.length_append, leftLength,
    rightLength]

/-- The four non-`h` incidences of a compatible pair are pairwise distinct local
carriers.  This is the counting step used by `lem:compatible-pair-fan-closure`
and quoted in the proof of `cor:compatible-pair-typeB-routing`. -/
theorem carriers_nodup (compatible : FanCompatible p q) :
    (p.shoulderCarriers ++ q.shoulderCarriers).Nodup := by
  refine List.Nodup.append p.shoulderCarriers_nodup q.shoulderCarriers_nodup ?_
  intro carrier leftMem rightMem
  rw [Port.shoulderCarriers, List.mem_map] at leftMem rightMem
  obtain ⟨leftShoulder, leftShoulderMem, leftEq⟩ := leftMem
  obtain ⟨rightShoulder, rightShoulderMem, rightEq⟩ := rightMem
  rcases Sym2.eq_iff.mp (leftEq.trans rightEq.symm) with
    ⟨endpointEq, _⟩ | ⟨endpointEq, shoulderEq⟩
  · exact compatible.endpointsNe endpointEq
  · exact compatible.leftNotShoulder (endpointEq ▸ rightShoulderMem)

theorem carriers_length {center : object.Vertex}
    (normal : NormalForm object center)
    (compatible : FanCompatible p q) (portCenter : p.center = center) :
    (p.shoulderCarriers ++ q.shoulderCarriers).length = 4 := by
  rw [List.length_append, Port.shoulderCarriers_length,
    Port.shoulderCarriers_length, normal.shoulders_length portCenter,
    normal.shoulders_length (compatible.sameCenter ▸ portCenter)]

end FanCompatible

/-! ## `lem:same-center-open-port-compatibility` -/

/-- `lem:same-center-open-port-compatibility`.  Distinct open ports at the same
high centre whose endpoints are nonadjacent are fan-compatible. -/
theorem fanCompatible_of_endpoints_nonadjacent
    {center : object.Vertex}
    (normal : NormalForm object center) {p q : Port object}
    (leftCenter : p.center = center) (rightCenter : q.center = center)
    (leftOpen : p.IsOpen) (rightOpen : q.IsOpen)
    (endpointsNe : p.endpoint ≠ q.endpoint)
    (nonadjacent : ¬ object.graph.Adj p.endpoint q.endpoint) :
    FanCompatible p q where
  sameCenter := leftCenter.trans rightCenter.symm
  leftOpen := leftOpen
  rightOpen := rightOpen
  endpointsNe := endpointsNe
  leftNotShoulder := fun member =>
    nonadjacent (Port.shoulder_adj member).symm
  rightNotShoulder := fun member =>
    nonadjacent (Port.shoulder_adj member)
  shouldersDisjoint := by
    intro shoulder leftMember rightMember
    exact normal.noCommonNeighbourOutside (leftCenter ▸ p.adjacent)
      (rightCenter ▸ q.adjacent) endpointsNe
      (leftCenter ▸ Port.shoulder_ne_center leftMember)
      (Port.shoulder_adj leftMember) (Port.shoulder_adj rightMember)

/-! ## Port counting at a centre

The ports at one centre are enumerated by their endpoints, in the ambient
neighbour order of `Graph.Finite`; the triangular/open dichotomy of
`def:heavy-center-triangular-port` splits that schedule in two.  Nothing here
assumes the absence of a cycle: the only structural input is `NormalForm`, which
`LocalHypotheses.normalForm` derives from the residual's `ctx.avoids`. -/

/-- The triangular ports at `center`, listed by endpoint in the ambient
neighbour order: the neighbours `x` of `center` whose port `(center, x)` is
triangular. -/
def triangularPorts (object : FiniteObject.{u}) (center : object.Vertex) :
    List object.Vertex :=
  (object.orderedNeighbors center).filter fun endpoint =>
    @dite Bool (object.graph.Adj center endpoint)
      (object.decideAdj center endpoint)
      (fun adjacent => decide (Port.mk center endpoint adjacent).IsTriangular)
      (fun _ => false)

/-- The open ports at `center`, listed by endpoint in the ambient neighbour
order. -/
def openPorts (object : FiniteObject.{u}) (center : object.Vertex) :
    List object.Vertex :=
  (object.orderedNeighbors center).filter fun endpoint =>
    @dite Bool (object.graph.Adj center endpoint)
      (object.decideAdj center endpoint)
      (fun adjacent => decide (Port.mk center endpoint adjacent).IsOpen)
      (fun _ => false)

theorem adj_of_mem_triangularPorts {center endpoint : object.Vertex}
    (member : endpoint ∈ triangularPorts object center) :
    object.graph.Adj center endpoint := by
  rw [triangularPorts, List.mem_filter] at member
  exact (object.mem_orderedNeighbors_iff center endpoint).mp member.1

theorem adj_of_mem_openPorts {center endpoint : object.Vertex}
    (member : endpoint ∈ openPorts object center) :
    object.graph.Adj center endpoint := by
  rw [openPorts, List.mem_filter] at member
  exact (object.mem_orderedNeighbors_iff center endpoint).mp member.1

theorem mem_triangularPorts_iff (p : Port object) :
    p.endpoint ∈ triangularPorts object p.center ↔ p.IsTriangular := by
  rw [triangularPorts, List.mem_filter, dif_pos p.adjacent]
  simp [p.adjacent]

theorem mem_openPorts_iff (p : Port object) :
    p.endpoint ∈ openPorts object p.center ↔ p.IsOpen := by
  rw [openPorts, List.mem_filter, dif_pos p.adjacent]
  simp [p.adjacent]

theorem triangularPorts_nodup (object : FiniteObject.{u})
    (center : object.Vertex) : (triangularPorts object center).Nodup :=
  (object.orderedNeighbors_nodup center).filter _

theorem openPorts_nodup (object : FiniteObject.{u}) (center : object.Vertex) :
    (openPorts object center).Nodup :=
  (object.orderedNeighbors_nodup center).filter _

private theorem length_filter_add_length_filter_of_complement {α : Type u}
    (left right : α → Bool) (list : List α)
    (complement : ∀ item ∈ list, right item = !left item) :
    (list.filter left).length + (list.filter right).length = list.length := by
  rw [List.filter_congr complement, ← List.length_eq_length_filter_add]

/-- The two schedules split the ports at the centre: every port is triangular or
open, and never both. -/
theorem triangularPorts_length_add_openPorts_length (object : FiniteObject.{u})
    (center : object.Vertex) :
    (triangularPorts object center).length + (openPorts object center).length
      = object.degree center := by
  rw [triangularPorts, openPorts,
    length_filter_add_length_filter_of_complement _ _ _ ?complement,
    object.orderedNeighbors_length center]
  case complement =>
    intro endpoint member
    have adjacent : object.graph.Adj center endpoint :=
      (object.mem_orderedNeighbors_iff center endpoint).mp member
    rw [dif_pos adjacent, dif_pos adjacent]
    exact decide_not

/-! ## `lem:heavy-center-triangular-alternative` -/

/-- The clique-in-a-matching step.  If no two distinct open ports at the centre
are fan-compatible then, by `lem:same-center-open-port-compatibility`, the open
endpoints are pairwise adjacent, i.e. they span a clique inside `N_G(h)`; part
(b) of `lem:heavy-neighbourhood-normal-form` makes `G[N_G(h)]` a matching, and a
matching carries no triangle. -/
theorem openPorts_length_le_two {center : object.Vertex}
    (normal : NormalForm object center)
    (noCompatiblePair : ∀ ⦃p q : Port object⦄, p.center = center →
      q.center = center → p.IsOpen → q.IsOpen → p.endpoint ≠ q.endpoint →
      ¬ FanCompatible p q) :
    (openPorts object center).length ≤ 2 := by
  by_contra tooMany
  have endpointsAdj : ∀ {left right : object.Vertex},
      left ∈ openPorts object center → right ∈ openPorts object center →
      left ≠ right → object.graph.Adj left right := by
    intro left right leftMember rightMember distinct
    by_contra nonadjacent
    let leftPort : Port object := ⟨center, left, adj_of_mem_openPorts leftMember⟩
    let rightPort : Port object :=
      ⟨center, right, adj_of_mem_openPorts rightMember⟩
    have leftOpen : leftPort.IsOpen := (mem_openPorts_iff leftPort).mp leftMember
    have rightOpen : rightPort.IsOpen :=
      (mem_openPorts_iff rightPort).mp rightMember
    exact noCompatiblePair (p := leftPort) (q := rightPort) rfl rfl leftOpen
      rightOpen distinct
      (fanCompatible_of_endpoints_nonadjacent normal (p := leftPort)
        (q := rightPort) rfl rfl leftOpen rightOpen distinct nonadjacent)
  have index0 : 0 < (openPorts object center).length := by omega
  have index1 : 1 < (openPorts object center).length := by omega
  have index2 : 2 < (openPorts object center).length := by omega
  have nodup := openPorts_nodup object center
  set first := (openPorts object center)[0]'index0
  set second := (openPorts object center)[1]'index1
  set third := (openPorts object center)[2]'index2
  have firstMember : first ∈ openPorts object center := List.getElem_mem index0
  have secondMember : second ∈ openPorts object center := List.getElem_mem index1
  have thirdMember : third ∈ openPorts object center := List.getElem_mem index2
  have firstSecondNe : first ≠ second := by
    intro equal
    have := (nodup.getElem_inj_iff (hi := index0) (hj := index1)).mp equal
    omega
  have firstThirdNe : first ≠ third := by
    intro equal
    have := (nodup.getElem_inj_iff (hi := index0) (hj := index2)).mp equal
    omega
  have secondThirdNe : second ≠ third := by
    intro equal
    have := (nodup.getElem_inj_iff (hi := index1) (hj := index2)).mp equal
    omega
  exact firstThirdNe
    (normal.inducedMatching (adj_of_mem_openPorts secondMember)
      (adj_of_mem_openPorts firstMember) (adj_of_mem_openPorts thirdMember)
      (endpointsAdj firstMember secondMember firstSecondNe).symm
      (endpointsAdj secondMember thirdMember secondThirdNe))

/-- `lem:heavy-center-triangular-alternative`, manuscript node `[69]`.  At a
centre of degree `k` carrying no fan-compatible pair of open ports, at least
`k - 2` of the `k` ports are triangular. -/
theorem heavyCenterTriangularAlternative {center : object.Vertex}
    (normal : NormalForm object center)
    (noCompatiblePair : ∀ ⦃p q : Port object⦄, p.center = center →
      q.center = center → p.IsOpen → q.IsOpen → p.endpoint ≠ q.endpoint →
      ¬ FanCompatible p q) :
    object.degree center - 2 ≤ (triangularPorts object center).length := by
  have partition := triangularPorts_length_add_openPorts_length object center
  have bound := openPorts_length_le_two normal noCompatiblePair
  omega

/-- The "in particular" clause of `lem:heavy-center-triangular-alternative`: a
heavy centre (`d_G(h) ≥ 5`) with no fan-compatible open pair has at least three
triangular ports. -/
theorem three_le_triangularPorts_length {center : object.Vertex}
    (normal : NormalForm object center) (heavy : 5 ≤ object.degree center)
    (noCompatiblePair : ∀ ⦃p q : Port object⦄, p.center = center →
      q.center = center → p.IsOpen → q.IsOpen → p.endpoint ≠ q.endpoint →
      ¬ FanCompatible p q) :
    3 ≤ (triangularPorts object center).length := by
  have bound := heavyCenterTriangularAlternative normal noCompatiblePair
  omega

/-- `cor:heavy-center-local-dichotomy`, manuscript node `[79]`.  At a heavy
centre either some two open ports are fan-compatible, or the triangular ports
already number at least `d_G(h) - 2`, hence at least three. -/
theorem heavyCenterLocalDichotomy {center : object.Vertex}
    (normal : NormalForm object center) (heavy : 5 ≤ object.degree center) :
    (∃ p q : Port object, p.center = center ∧ FanCompatible p q) ∨
      (object.degree center - 2 ≤ (triangularPorts object center).length ∧
        3 ≤ (triangularPorts object center).length) := by
  by_cases compatiblePair :
      ∃ p q : Port object, p.center = center ∧ FanCompatible p q
  · exact Or.inl compatiblePair
  · have noCompatiblePair : ∀ ⦃p q : Port object⦄, p.center = center →
        q.center = center → p.IsOpen → q.IsOpen → p.endpoint ≠ q.endpoint →
        ¬ FanCompatible p q := by
      intro p q leftCenter _ _ _ _ compatible
      exact compatiblePair ⟨p, q, leftCenter, compatible⟩
    exact Or.inr ⟨heavyCenterTriangularAlternative normal noCompatiblePair,
      three_le_triangularPorts_length normal heavy noCompatiblePair⟩

end Hypostructure.Graph.TypeBOpenPorts
