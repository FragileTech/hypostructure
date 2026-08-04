import Hypostructure.Graph.TypeBFanClosedPorts

/-!
# The degree-four local branch and triangular fan cores

This file is the graph-mathematics content of manuscript nodes `[78]`
(`degree4`) and `[79]` (`profile`) of Figure 7 in
`original_erdos_64_proof.tex`:

* `cor:degree-four-local-activation` -- `degreeFourLocalActivation` and its
  port form `degreeFourLocalActivation_ports`, together with the routing
  assertion of case (ii) (`triangularPairTypeBRouting`);
* `def:triangular-fan-core` -- `TriangularCore`, its shoulder pairs, its
  vertex support `V(F_h(𝒯_h))`, the shoulder-completion incidences and their
  central / cross-triangular / outside trichotomy;
* the degree-four fan profile of node `[79]`: centre surplus `1`,
  `0 ≤ c(𝔉) ≤ 4`, and `D_B(𝔉) = c(𝔉) - 7/4`.

Nothing is redefined here.  Ports, shoulder schedules, the open/triangular
dichotomy, fan-compatibility, the high-neighbourhood normal form, the
triangular and open port schedules at a centre and the counting split between
them are `Hypostructure.Graph.TypeBOpenPorts`; the certificate-marked fan is
`Hypostructure.Graph.TypeBMarkedFan`; the assigned fan-window `Profile`, its
`closedCount` `c(𝔉)` and its `closedNeighbourDeficit`
`D_B(𝔉) = c(𝔉) - (3 - (k+1)α)` are `Hypostructure.Graph.TypeBFanClosedPorts`,
with the discharge rate `α` read from the registered presentation.
In particular `D_B = c - (3 - 5α)` -- the manuscript's `c - 7/4` at
`α = 1/4` -- is *derived* from the ambient definition by substituting the local
observable `d_G(h) = 4`; it is not restated.

Everything is phrased through local observables: the degree of the centre at
hand, the object's own neighbour and vertex schedules, and the data of a
`Profile` built over the object.  No parameter stands for a global property of
the graph.

`NormalForm` -- the only ambient structural input -- is an explicit argument of
every theorem that needs it, exactly as in
`TypeBOpenPorts.heavyCenterTriangularAlternative`.  No hypothesis in this file
asserts the absence of a structure; the four-cycle absence behind `NormalForm`
is read off the incoming residual by
`TypeBOpenPorts.LocalHypotheses.normalForm` (`ctx.avoids`), and the failure of
the fan-compatible alternative appears only as the *negative side of a proved
dichotomy* (`degreeFourLocalActivation`), never as an assumption.

`TriangularCore` is pure data -- a centre and a list of port vertices, with no
propositional fields -- in the same shape as `Profile`; every well-formedness
fact about it is a hypothesis of the theorem that needs it and is discharged
for the object-derived canonical cores in `canonicalCore` / `degreeFourCores`.
-/

namespace Hypostructure.Graph.TypeBDegreeFour

open Hypostructure.Graph
open Hypostructure.Graph.TypeBOpenPorts
open Hypostructure.Graph.TypeBMarkedFan
open Hypostructure.Graph.TypeBFanClosedPorts
open Hypostructure.Graph.Strategy.Official.Features.DeletionFanIncidence
open Hypostructure.Graph.ReceiverLoad (LoadCapacityProfile)

universe u

variable {object : FiniteObject.{u}}

/-! ## `cor:degree-four-local-activation`, node `[78]`

The heavy-centre dichotomy `cor:heavy-center-local-dichotomy` is stated for
`d_G(h) ≥ 5` and yields three triangular ports.  The degree-four centre is the
*other* branch of `[68]`: it yields exactly the weaker conclusion of two
triangular ports, which is what the manuscript's degree-four activation
records.  Both come from the same counting split
`triangularPorts_length_add_openPorts_length` together with
`openPorts_length_le_two`, so nothing is reproved. -/

/-- `cor:degree-four-local-activation`, manuscript node `[78]`.

At a high centre of degree exactly four, either two open ports at the centre
are fan-compatible, or at least two of the four ports are triangular.

The second alternative is *not* an assumption that no compatible pair exists:
it is the negative side of this dichotomy, produced here. -/
theorem degreeFourLocalActivation {center : object.Vertex}
    (normal : NormalForm object center) (degreeFour : object.degree center = 4) :
    (∃ p q : Port object, p.center = center ∧ FanCompatible p q) ∨
      2 ≤ (triangularPorts object center).length := by
  by_cases compatiblePair :
      ∃ p q : Port object, p.center = center ∧ FanCompatible p q
  · exact Or.inl compatiblePair
  · refine Or.inr ?_
    have noCompatiblePair : ∀ ⦃p q : Port object⦄, p.center = center →
        q.center = center → p.IsOpen → q.IsOpen → p.endpoint ≠ q.endpoint →
        ¬ FanCompatible p q := by
      intro p q leftCenter _ _ _ _ compatible
      exact compatiblePair ⟨p, q, leftCenter, compatible⟩
    have bound := heavyCenterTriangularAlternative normal noCompatiblePair
    omega

/-- Two distinct triangular ports are read off the triangular port schedule as
soon as it has length at least two.  The schedule is nodup, so its first two
entries are distinct port vertices at the same centre. -/
theorem exists_two_triangular_ports {center : object.Vertex}
    (two : 2 ≤ (triangularPorts object center).length) :
    ∃ p q : Port object, p.center = center ∧ q.center = center ∧
      p.IsTriangular ∧ q.IsTriangular ∧ p.endpoint ≠ q.endpoint := by
  have index0 : 0 < (triangularPorts object center).length := by omega
  have index1 : 1 < (triangularPorts object center).length := by omega
  set first := (triangularPorts object center)[0]'index0 with firstDef
  set second := (triangularPorts object center)[1]'index1 with secondDef
  have firstMember : first ∈ triangularPorts object center :=
    List.getElem_mem index0
  have secondMember : second ∈ triangularPorts object center :=
    List.getElem_mem index1
  have distinct : first ≠ second := by
    intro equal
    have :=
      ((triangularPorts_nodup object center).getElem_inj_iff
        (hi := index0) (hj := index1)).mp equal
    omega
  refine ⟨⟨center, first, adj_of_mem_triangularPorts firstMember⟩,
    ⟨center, second, adj_of_mem_triangularPorts secondMember⟩, rfl, rfl, ?_, ?_,
    distinct⟩
  · exact (mem_triangularPorts_iff
      ⟨center, first, adj_of_mem_triangularPorts firstMember⟩).mp firstMember
  · exact (mem_triangularPorts_iff
      ⟨center, second, adj_of_mem_triangularPorts secondMember⟩).mp secondMember

/-- `cor:degree-four-local-activation` in port form: at a centre of degree four
either two open ports are fan-compatible, or two distinct ports are
triangular. -/
theorem degreeFourLocalActivation_ports {center : object.Vertex}
    (normal : NormalForm object center) (degreeFour : object.degree center = 4) :
    (∃ p q : Port object, p.center = center ∧ FanCompatible p q) ∨
      (∃ p q : Port object, p.center = center ∧ q.center = center ∧
        p.IsTriangular ∧ q.IsTriangular ∧ p.endpoint ≠ q.endpoint) := by
  rcases degreeFourLocalActivation normal degreeFour with compatible | two
  · exact Or.inl compatible
  · exact Or.inr (exists_two_triangular_ports two)

/-! ## The shoulder pair of a triangular port

`def:triangular-fan-core` writes `N_G(x_i) = {h, a_i, b_i}` and `S_i =
{a_i, b_i}`, so that `x_i a_i b_i x_i` is a triangle.  Both facts are derived:
the two-element shoulder schedule is `NormalForm.shoulders_length`, and the
chord `a_i b_i` is the content of `Port.IsTriangular`. -/

/-- `def:triangular-fan-core`, the shoulder pair `S_i = {a_i, b_i}` of a
triangular port at a high centre, together with the triangle
`x_i a_i b_i x_i`.

This is also the step quoted in case (ii) of
`cor:degree-four-local-activation`: the two triangle edges at `x_i` are
precisely the two non-`h` incidences of the port vertex, so assigning them to
the fan envelope is exactly clause (b) of `def:fan-closed-port`. -/
theorem triangularShoulderPair {center : object.Vertex}
    (normal : NormalForm object center) {p : Port object}
    (portCenter : p.center = center) (triangular : p.IsTriangular) :
    ∃ a b : object.Vertex, p.shoulders = [a, b] ∧ a ≠ b ∧
      object.graph.Adj p.endpoint a ∧ object.graph.Adj p.endpoint b ∧
      object.graph.Adj a b := by
  obtain ⟨a, b, listEq⟩ :=
    List.length_eq_two.mp (normal.shoulders_length portCenter)
  have nodup : ([a, b] : List object.Vertex).Nodup := listEq ▸ p.shoulders_nodup
  have distinct : a ≠ b := by simpa using nodup
  have leftMem : a ∈ p.shoulders := by rw [listEq]; simp
  have rightMem : b ∈ p.shoulders := by rw [listEq]; simp
  refine ⟨a, b, listEq, distinct, Port.shoulder_adj leftMem,
    Port.shoulder_adj rightMem, ?_⟩
  obtain ⟨left, leftMember, right, rightMember, chord⟩ := triangular
  rw [listEq] at leftMember rightMember
  simp only [List.mem_cons, List.not_mem_nil, or_false] at leftMember rightMember
  rcases leftMember with rfl | rfl <;> rcases rightMember with rfl | rfl
  · exact absurd chord (object.graph.irrefl)
  · exact chord
  · exact chord.symm
  · exact absurd chord (object.graph.irrefl)

/-! ## `def:triangular-fan-core`, node `[79]`

The triangular fan core generated by a set `𝒯_h = {p_i = (h, x_i) : i ∈ I}` of
triangular ports at `h` is the induced subgraph on
`{h} ∪ {x_i} ∪ ⋃_i S_i`.

`TriangularCore` records exactly the generating data -- the centre and the
schedule of port vertices -- and has **no** propositional fields.  Triangularity
of the listed ports and their adjacency to the centre are hypotheses of the
theorems that need them, discharged below for the object-derived canonical
cores.  The shoulder pairs are the framework's `outsideIncidences` schedule, so
no second neighbour model is introduced. -/

/-- `def:triangular-fan-core`.  The generating data of a triangular fan core
`F_h(𝒯_h)`: the centre `h` and the port vertices `x_i`, `i ∈ I`, in the
object's own schedule order.  Pure data, exactly like
`TypeBFanClosedPorts.Profile`. -/
structure TriangularCore (object : FiniteObject.{u}) where
  /-- The centre `h`. -/
  center : object.Vertex
  /-- The port vertices `x_i`, `i ∈ I`, of the generating triangular ports. -/
  portVertices : List object.Vertex

namespace TriangularCore

variable (core : TriangularCore object)

/-- The shoulder pair `S_i = s(p_i)` of a listed port vertex: the incidences of
`x_i` avoiding the centre, in the ambient scan order.  This is literally
`Port.shoulders`, taken from the framework's `outsideIncidences`. -/
def shoulders (portVertex : object.Vertex) : List object.Vertex :=
  outsideIncidences object core.center portVertex

/-- The union `⋃_{i ∈ I} S_i` of all shoulder pairs, in schedule order. -/
def allShoulders : List object.Vertex :=
  core.portVertices.flatMap core.shoulders

/-- The vertex set `V(F_h(𝒯_h)) = {h} ∪ {x_i : i ∈ I} ∪ ⋃_i S_i` of the
triangular fan core. -/
def support : Finset object.Vertex :=
  letI : DecidableEq object.Vertex := object.vertices.decEq
  insert core.center (core.portVertices ++ core.allShoulders).toFinset

variable {core}

theorem mem_shoulders_iff {portVertex vertex : object.Vertex} :
    vertex ∈ core.shoulders portVertex ↔
      vertex ≠ core.center ∧ object.graph.Adj portVertex vertex := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  rw [shoulders, outsideIncidences,
    (object.orderedNeighbors_nodup portVertex).mem_erase_iff,
    object.mem_orderedNeighbors_iff]

/-- A listed port vertex's shoulder schedule is the shoulder schedule of the
corresponding surplus port; no second shoulder model is used. -/
theorem shoulders_eq_port_shoulders {p : Port object}
    (portCenter : p.center = core.center) :
    core.shoulders p.endpoint = p.shoulders := by
  rw [shoulders, Port.shoulders, portCenter]

theorem shoulder_adj {portVertex vertex : object.Vertex}
    (member : vertex ∈ core.shoulders portVertex) :
    object.graph.Adj portVertex vertex :=
  (mem_shoulders_iff).mp member |>.2

theorem shoulder_ne_center {portVertex vertex : object.Vertex}
    (member : vertex ∈ core.shoulders portVertex) : vertex ≠ core.center :=
  (mem_shoulders_iff).mp member |>.1

theorem mem_support_iff (vertex : object.Vertex) :
    vertex ∈ core.support ↔
      vertex = core.center ∨ vertex ∈ core.portVertices ∨
        ∃ portVertex ∈ core.portVertices, vertex ∈ core.shoulders portVertex := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  simp [support, allShoulders, List.mem_flatMap]

theorem center_mem_support : core.center ∈ core.support :=
  (mem_support_iff core.center).2 (Or.inl rfl)

theorem portVertex_mem_support {portVertex : object.Vertex}
    (member : portVertex ∈ core.portVertices) : portVertex ∈ core.support :=
  (mem_support_iff portVertex).2 (Or.inr (Or.inl member))

theorem shoulder_mem_support {portVertex vertex : object.Vertex}
    (portMember : portVertex ∈ core.portVertices)
    (member : vertex ∈ core.shoulders portVertex) : vertex ∈ core.support :=
  (mem_support_iff vertex).2 (Or.inr (Or.inr ⟨portVertex, portMember, member⟩))

variable (core)

/-! ### Shoulder-completion incidences and their landings -/

/-- `def:triangular-fan-core`.  A *shoulder-completion incidence* at a shoulder
`s ∈ S_i` is an edge `s y ∈ E(G)` with `y ∉ {x_i, s_i'}`, where `s_i'` is the
other shoulder of the same port. -/
def IsShoulderCompletion (portVertex shoulder target : object.Vertex) : Prop :=
  portVertex ∈ core.portVertices ∧ shoulder ∈ core.shoulders portVertex ∧
    object.graph.Adj shoulder target ∧ target ≠ portVertex ∧
    ∀ other ∈ core.shoulders portVertex, other ≠ shoulder → target ≠ other

/-- `def:triangular-fan-core`: the completion is *central* when `y = h`. -/
def IsCentralLanding (target : object.Vertex) : Prop := target = core.center

/-- `def:triangular-fan-core`: the completion is *cross-triangular* when
`y ∈ ⋃_{j ≠ i} S_j`. -/
def IsCrossLanding (portVertex target : object.Vertex) : Prop :=
  ∃ other ∈ core.portVertices, other ≠ portVertex ∧
    target ∈ core.shoulders other

/-- `def:triangular-fan-core`: the completion is *outside* when
`y ∉ V(F_h(𝒯_h)) ∪ N_G(h)`.  This is the first edge by which the displayed
core attaches to the rest of the graph.

This is a *classification* of a landing produced by the trichotomy below, not a
hypothesis: nothing in this file ever assumes that a landing is outside. -/
def IsOutsideLanding (target : object.Vertex) : Prop :=
  target ∉ core.support ∧ ¬ object.graph.Adj core.center target

variable {core}

/-- Part (d) of `lem:triangular-shoulder-completion`: no shoulder-completion
incidence lands in `N_G(h)`.

Both the port vertex `x_i` and a landing `y ∈ N_G(h)` are neighbours of `h`;
they are distinct because `y ≠ x_i` is part of being a completion incidence;
and the shoulder `s ≠ h` is a common neighbour of the two.  Part (c) of
`lem:heavy-neighbourhood-normal-form` forbids exactly that. -/
theorem not_adj_center_of_shoulderCompletion
    (normal : NormalForm object core.center)
    (portsAdjacent : ∀ portVertex ∈ core.portVertices,
      object.graph.Adj core.center portVertex)
    {portVertex shoulder target : object.Vertex}
    (completion : core.IsShoulderCompletion portVertex shoulder target) :
    ¬ object.graph.Adj core.center target := by
  obtain ⟨portMember, shoulderMember, chord, targetNePort, _⟩ := completion
  intro centerTarget
  exact normal.noCommonNeighbourOutside (portsAdjacent portVertex portMember)
    centerTarget (Ne.symm targetNePort) (shoulder_ne_center shoulderMember)
    (shoulder_adj shoulderMember) chord.symm

/-- The three landing kinds of `def:triangular-fan-core` are pairwise
exclusive.  Together with `shoulderCompletion_trichotomy` this makes the
manuscript's "exactly one of the following" an honest statement, and it needs no
structural input at all. -/
theorem landings_pairwise_exclusive {portVertex target : object.Vertex} :
    ¬ (core.IsCentralLanding target ∧ core.IsCrossLanding portVertex target) ∧
      ¬ (core.IsCentralLanding target ∧ core.IsOutsideLanding target) ∧
      ¬ (core.IsCrossLanding portVertex target ∧
        core.IsOutsideLanding target) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨central, _, _, _, targetShoulder⟩
    exact shoulder_ne_center targetShoulder central
  · rintro ⟨central, notSupport, _⟩
    exact notSupport (by rw [central]; exact center_mem_support)
  · rintro ⟨⟨_, otherMember, _, targetShoulder⟩, notSupport, _⟩
    exact notSupport (shoulder_mem_support otherMember targetShoulder)

/-- `lem:triangular-first-landing`, the exhaustiveness of the three landings of
`def:triangular-fan-core`.  Every shoulder-completion incidence in a triangular
fan core is central, cross-triangular, or outside; by
`landings_pairwise_exclusive` it is exactly one of them.

The only structural input is the high-neighbourhood normal form at the centre;
`portsAdjacent` is a well-formedness fact about the generating data, discharged
for the object-derived cores by `canonicalCore_portsAdjacent`. -/
theorem shoulderCompletion_trichotomy
    (normal : NormalForm object core.center)
    (portsAdjacent : ∀ portVertex ∈ core.portVertices,
      object.graph.Adj core.center portVertex)
    {portVertex shoulder target : object.Vertex}
    (completion : core.IsShoulderCompletion portVertex shoulder target) :
    core.IsCentralLanding target ∨ core.IsCrossLanding portVertex target ∨
      core.IsOutsideLanding target := by
  by_cases central : target = core.center
  · exact Or.inl central
  have notNeighbour : ¬ object.graph.Adj core.center target :=
    not_adj_center_of_shoulderCompletion normal portsAdjacent completion
  obtain ⟨portMember, shoulderMember, chord, targetNePort, otherShoulder⟩ :=
    completion
  by_cases inSupport : target ∈ core.support
  · refine Or.inr (Or.inl ?_)
    rcases (mem_support_iff target).1 inSupport with
      isCenter | isPort | ⟨other, otherMember, targetShoulder⟩
    · exact absurd isCenter central
    · exact absurd (portsAdjacent target isPort) notNeighbour
    · refine ⟨other, otherMember, ?_, targetShoulder⟩
      rintro rfl
      by_cases sameShoulder : target = shoulder
      · exact object.graph.irrefl (sameShoulder ▸ chord)
      · exact otherShoulder target targetShoulder
          (fun equal => sameShoulder equal) rfl
  · exact Or.inr (Or.inr ⟨inSupport, notNeighbour⟩)

end TriangularCore

/-! ## The enumerable carrier of degree-four triangular fan cores

The manuscript's `𝒯_h` may be any nonempty set of triangular ports at `h`.  The
canonical object-derived choice is the full triangular port schedule
`triangularPorts` of `TypeBOpenPorts`, so the cores of a given object form a
finite list produced from the object's own vertex and neighbour schedules --
nothing is authored. -/

/-- The canonical triangular fan core at a centre: the core generated by *all*
triangular ports at the centre, in the object's own neighbour order. -/
def canonicalCore (object : FiniteObject.{u}) (center : object.Vertex) :
    TriangularCore object where
  center := center
  portVertices := triangularPorts object center

@[simp] theorem canonicalCore_center (object : FiniteObject.{u})
    (center : object.Vertex) : (canonicalCore object center).center = center :=
  rfl

@[simp] theorem canonicalCore_portVertices (object : FiniteObject.{u})
    (center : object.Vertex) :
    (canonicalCore object center).portVertices = triangularPorts object center :=
  rfl

/-- Every port vertex of a canonical core is a neighbour of the centre: the
well-formedness hypothesis of `shoulderCompletion_trichotomy` is discharged. -/
theorem canonicalCore_portsAdjacent (object : FiniteObject.{u})
    (center : object.Vertex) :
    ∀ portVertex ∈ (canonicalCore object center).portVertices,
      object.graph.Adj (canonicalCore object center).center portVertex :=
  fun _ member => adj_of_mem_triangularPorts member

/-- Every port of a canonical core really is a triangular port, so the core is
generated by a set of triangular ports in the sense of
`def:triangular-fan-core`. -/
theorem canonicalCore_portsTriangular (object : FiniteObject.{u})
    (center : object.Vertex) :
    ∀ portVertex ∈ (canonicalCore object center).portVertices,
      ∃ p : Port object, p.center = center ∧ p.endpoint = portVertex ∧
        p.IsTriangular := by
  intro portVertex member
  refine ⟨⟨center, portVertex, adj_of_mem_triangularPorts member⟩, rfl, rfl, ?_⟩
  exact (mem_triangularPorts_iff
    ⟨center, portVertex, adj_of_mem_triangularPorts member⟩).mp member

theorem canonicalCore_injective (object : FiniteObject.{u}) :
    Function.Injective (canonicalCore object) := by
  intro left right equal
  have := congrArg TriangularCore.center equal
  simpa using this

/-- The degree-four centres of the object, in its own vertex scan order.  A
local observable: the filter reads only the degree of each vertex. -/
def degreeFourCenters (object : FiniteObject.{u}) : List object.Vertex :=
  object.orderedVertices.filter fun vertex => decide (object.degree vertex = 4)

@[simp] theorem mem_degreeFourCenters_iff (object : FiniteObject.{u})
    (vertex : object.Vertex) :
    vertex ∈ degreeFourCenters object ↔ object.degree vertex = 4 := by
  simp [degreeFourCenters]

theorem degreeFourCenters_nodup (object : FiniteObject.{u}) :
    (degreeFourCenters object).Nodup :=
  object.orderedVertices_nodup.filter _

/-- **The enumerable carrier of degree-four triangular fan cores.**  One
canonical triangular fan core per degree-four centre, generated from the
object's own vertex schedule and its own triangular port schedules.  A
downstream node scans this list. -/
def degreeFourCores (object : FiniteObject.{u}) : List (TriangularCore object) :=
  (degreeFourCenters object).map (canonicalCore object)

theorem mem_degreeFourCores_iff (object : FiniteObject.{u})
    (core : TriangularCore object) :
    core ∈ degreeFourCores object ↔
      object.degree core.center = 4 ∧
        core.portVertices = triangularPorts object core.center := by
  rw [degreeFourCores, List.mem_map]
  constructor
  · rintro ⟨center, member, rfl⟩
    exact ⟨(mem_degreeFourCenters_iff object center).1 member, rfl⟩
  · rintro ⟨degreeFour, portsEq⟩
    refine ⟨core.center, (mem_degreeFourCenters_iff object core.center).2 degreeFour, ?_⟩
    obtain ⟨center, ports⟩ := core
    simp only [canonicalCore, TriangularCore.mk.injEq, true_and]
    exact portsEq.symm

theorem degreeFourCores_nodup (object : FiniteObject.{u}) :
    (degreeFourCores object).Nodup :=
  (degreeFourCenters_nodup object).map (canonicalCore_injective object)

theorem degree_eq_four_of_mem_degreeFourCores {object : FiniteObject.{u}}
    {core : TriangularCore object} (member : core ∈ degreeFourCores object) :
    object.degree core.center = 4 :=
  ((mem_degreeFourCores_iff object core).1 member).1

theorem portsAdjacent_of_mem_degreeFourCores {object : FiniteObject.{u}}
    {core : TriangularCore object} (member : core ∈ degreeFourCores object) :
    ∀ portVertex ∈ core.portVertices,
      object.graph.Adj core.center portVertex := by
  intro portVertex portMember
  rw [((mem_degreeFourCores_iff object core).1 member).2] at portMember
  exact adj_of_mem_triangularPorts portMember

/-- The scanning form of `cor:degree-four-local-activation`: at every enumerated
degree-four core, either the centre carries a fan-compatible pair of open ports,
or the core already lists at least two generating triangular ports. -/
theorem degreeFourCores_activation {object : FiniteObject.{u}}
    {core : TriangularCore object} (member : core ∈ degreeFourCores object)
    (normal : NormalForm object core.center) :
    (∃ p q : Port object, p.center = core.center ∧ FanCompatible p q) ∨
      2 ≤ core.portVertices.length := by
  obtain ⟨degreeFour, portsEq⟩ := (mem_degreeFourCores_iff object core).1 member
  rw [portsEq]
  exact degreeFourLocalActivation normal degreeFour

/-! ## The degree-four fan profile, node `[79]`

The manuscript panel records three quantities at a degree-four fan centre:
the centre surplus is `1`, the closed-neighbour count satisfies `0 ≤ c ≤ 4`,
and the closed-neighbour deficit is `D_B = c - 7/4`. -/

/-- The surplus port schedule at a centre, in the object's own neighbour order:
the ports beyond the three base ports of `def:surplus-ports`.  This is the
framework's `excessPorts` at the cubic baseline `3`, not a second port model. -/
def surplusPorts (object : FiniteObject.{u}) (center : object.Vertex) :
    List object.Vertex :=
  Core.Strategy.Official.Features.DeletionFanAccounting.excessPorts 3
    (object.orderedNeighbors center)

/-- The centre surplus of `def:surplus-ports`: `|P_exc(h)| = d_G(h) - 3`. -/
theorem surplusPorts_length (object : FiniteObject.{u})
    (center : object.Vertex) :
    (surplusPorts object center).length = object.degree center - 3 := by
  rw [surplusPorts,
    Core.Strategy.Official.Features.DeletionFanAccounting.excess_length,
    object.orderedNeighbors_length]

/-- Node `[79]`, first quantity: a degree-four centre carries surplus `1`. -/
theorem surplusPorts_length_of_degree_four {center : object.Vertex}
    (degreeFour : object.degree center = 4) :
    (surplusPorts object center).length = 1 := by
  rw [surplusPorts_length, degreeFour]

/-- `c(𝔉)` counts a subset of the fan rim, so it never exceeds `d_G(h)`. -/
theorem closedCount_le_degree (profile : Profile object) :
    profile.closedCount ≤ object.degree profile.marked.fan.hub := by
  rw [← profile.marked.rim_card_eq_degree]
  refine Finset.card_le_card ?_
  intro vertex member
  exact (Profile.mem_closedNeighbours_iff vertex).1 member |>.1

/-- Node `[79]`, second quantity: at a degree-four fan centre `0 ≤ c(𝔉) ≤ 4`. -/
theorem closedCount_le_four (profile : Profile object)
    (degreeFour : object.degree profile.marked.fan.hub = 4) :
    profile.closedCount ≤ 4 := by
  have bound := closedCount_le_degree profile
  omega

/-- Node `[79]`, third quantity: `D_B(𝔉) = c(𝔉) - (3 - 5α)`, the manuscript's
`c(𝔉) - 7/4` at the registered `α = 1/4`.

This is the ambient `closedNeighbourDeficit = c - (3 - (k+1)α)` of
`def:typeB-multiclosed-residual` with the *local observable* `k = d_G(h) = 4`
substituted; the statement is not an equality of two copies of the same
expression, and it fails without the degree hypothesis. -/
theorem closedNeighbourDeficit_of_degree_four (profile : Profile object)
    (ledger : LoadCapacityProfile)
    (degreeFour : object.degree profile.marked.fan.hub = 4) :
    profile.closedNeighbourDeficit ledger
      = (profile.closedCount : ℚ) - (3 - 5 * ledger.dischargeRate) := by
  rw [Profile.closedNeighbourDeficit, degreeFour]
  push_cast
  ring

/-- The degree-four deficit window implied by `0 ≤ c ≤ 4` and
`D_B = c - (3 - 5α)`, namely `[5α - 3, 1 + 5α]`.  At `α = 1/4` this is the
manuscript's `[-7/4, 9/4]`. -/
theorem closedNeighbourDeficit_window (profile : Profile object)
    (ledger : LoadCapacityProfile)
    (degreeFour : object.degree profile.marked.fan.hub = 4) :
    5 * ledger.dischargeRate - 3 ≤ profile.closedNeighbourDeficit ledger ∧
      profile.closedNeighbourDeficit ledger ≤ 1 + 5 * ledger.dischargeRate := by
  have deficit := closedNeighbourDeficit_of_degree_four profile ledger degreeFour
  have upper : (profile.closedCount : ℚ) ≤ 4 := by
    exact_mod_cast closedCount_le_four profile degreeFour
  have lower : (0 : ℚ) ≤ (profile.closedCount : ℚ) := by positivity
  constructor <;> · rw [deficit]; linarith

/-- **Node `[79]`, the degree-four fan profile.**  At an assigned Type B
fan-window profile whose certificate-marked centre has degree four, the centre
surplus is `1`, the closed-neighbour count lies in `0 ≤ c ≤ 4`, and the
closed-neighbour deficit is exactly `D_B = c - (3 - 5α)`, hence lies in
`[5α - 3, 1 + 5α]` -- the manuscript's `c - 7/4` and `[-7/4, 9/4]` at
`α = 1/4`. -/
theorem degreeFourFanProfile (profile : Profile object)
    (ledger : LoadCapacityProfile)
    (degreeFour : object.degree profile.marked.fan.hub = 4) :
    (surplusPorts object profile.marked.fan.hub).length = 1 ∧
      profile.closedCount ≤ 4 ∧
      profile.closedNeighbourDeficit ledger
          = (profile.closedCount : ℚ) - (3 - 5 * ledger.dischargeRate) ∧
      5 * ledger.dischargeRate - 3 ≤ profile.closedNeighbourDeficit ledger ∧
      profile.closedNeighbourDeficit ledger ≤ 1 + 5 * ledger.dischargeRate :=
  ⟨surplusPorts_length_of_degree_four degreeFour,
    closedCount_le_four profile degreeFour,
    closedNeighbourDeficit_of_degree_four profile ledger degreeFour,
    (closedNeighbourDeficit_window profile ledger degreeFour).1,
    (closedNeighbourDeficit_window profile ledger degreeFour).2⟩

/-! ## The routing assertion of `cor:degree-four-local-activation`

`prop:fan-closed-port-typeB-routing` at `r = 2`, `k = 4` gives
`D_B(𝔉_h) ≥ 2 - (3 - 5α) = 5α - 1 > 0`, the manuscript's
`2 - (11 - 4)/4 = 1/4 > 0` at `α = 1/4`.  Nothing is reproved: the general
routing is `TypeBFanClosedPorts.fanClosedPortTypeBRouting` and only the degree
of the centre is specialised.  This is the *sharp instance* the recorded
constraint `ReceiverLoad.LoadCapacityProfile.dischargeRate_gt` was read off:
`c = 2` and `k = 4` here, so the strict positivity is exactly `5α > 1`. -/

/-- `prop:fan-closed-port-typeB-routing` specialised to a degree-four centre:
a family of at least two fan-closed surplus ports forces
`D_B(𝔉_h) = c - (3 - 5α) ≥ 5α - 1 > 0`. -/
theorem degreeFourFanClosedRouting (profile : Profile object)
    (ledger : LoadCapacityProfile)
    (normal : NormalForm object profile.marked.fan.hub)
    (degreeFour : object.degree profile.marked.fan.hub = 4)
    {ports : Finset object.Vertex}
    (fanClosed : ∀ vertex ∈ ports, ∃ p : Port object,
      p.endpoint = vertex ∧ profile.IsFanClosed p)
    (two : 2 ≤ ports.card) :
    2 ≤ profile.closedCount ∧
      profile.closedNeighbourDeficit ledger
          = (profile.closedCount : ℚ) - (3 - 5 * ledger.dischargeRate) ∧
      5 * ledger.dischargeRate - 1 ≤ profile.closedNeighbourDeficit ledger ∧
      0 < profile.closedNeighbourDeficit ledger := by
  obtain ⟨counted, _, deficitBound, positive⟩ :=
    fanClosedPortTypeBRouting profile ledger normal fanClosed two
  refine ⟨le_trans two counted,
    closedNeighbourDeficit_of_degree_four profile ledger degreeFour, ?_, positive⟩
  rw [degreeFour] at deficitBound
  push_cast at deficitBound
  linarith

/-- Case (ii) of `cor:degree-four-local-activation`, manuscript node `[78]`.

Two distinct surplus ports at a degree-four certificate-marked centre, recorded
as remainder-side fan neighbours with their two non-`h` incidences assigned to
the fan envelope, are two fan-closed ports; hence

`D_B(𝔉_h) = c(𝔉_h) - (3 - 5α) ≥ 2 - (3 - 5α) = 5α - 1 > 0`, the manuscript's
`c(𝔉_h) - 7/4 ≥ 2 - 7/4 = 1/4 > 0` at `α = 1/4`.

For a *triangular* port the two assigned incidences are exactly the two
triangle edges `x a_p`, `x b_p` -- that identification is
`triangularShoulderPair`.  Triangularity itself is not a hypothesis here: the
statement holds for any two recorded and assigned ports with distinct
endpoints, so the triangular case is an instance rather than an extra
assumption. -/
theorem triangularPairTypeBRouting (profile : Profile object)
    (ledger : LoadCapacityProfile)
    (normal : NormalForm object profile.marked.fan.hub)
    (degreeFour : object.degree profile.marked.fan.hub = 4)
    {p q : Port object}
    (leftCenter : p.center = profile.marked.fan.hub)
    (rightCenter : q.center = profile.marked.fan.hub)
    (distinct : p.endpoint ≠ q.endpoint)
    (leftRemainder : p.endpoint ∈ profile.remainder)
    (rightRemainder : q.endpoint ∈ profile.remainder)
    (leftAssigned : ∀ shoulder ∈ p.shoulders, shoulder ∈ profile.envelope)
    (rightAssigned : ∀ shoulder ∈ q.shoulders, shoulder ∈ profile.envelope) :
    2 ≤ profile.closedCount ∧
      profile.closedNeighbourDeficit ledger
          = (profile.closedCount : ℚ) - (3 - 5 * ledger.dischargeRate) ∧
      5 * ledger.dischargeRate - 1 ≤ profile.closedNeighbourDeficit ledger ∧
      0 < profile.closedNeighbourDeficit ledger := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  have leftClosed : profile.IsFanClosed p := ⟨leftCenter, leftRemainder, leftAssigned⟩
  have rightClosed : profile.IsFanClosed q :=
    ⟨rightCenter, rightRemainder, rightAssigned⟩
  have pairCard : ({p.endpoint, q.endpoint} : Finset object.Vertex).card = 2 :=
    Finset.card_pair distinct
  have fanClosed : ∀ vertex ∈ ({p.endpoint, q.endpoint} : Finset object.Vertex),
      ∃ port : Port object, port.endpoint = vertex ∧ profile.IsFanClosed port := by
    intro vertex member
    rcases Finset.mem_insert.1 member with rfl | member
    · exact ⟨p, rfl, leftClosed⟩
    · rw [Finset.mem_singleton] at member
      subst member
      exact ⟨q, rfl, rightClosed⟩
  exact degreeFourFanClosedRouting profile ledger normal degreeFour fanClosed
    (by rw [pairCard])

/-! ## Non-vacuity

Every hypothesis above is realised simultaneously by an explicit finite graph:
a centre of degree four whose four cubic neighbours each carry a private
*triangular* shoulder pair.  The high-neighbourhood normal form holds at the
centre, all four of its ports are triangular (so case (ii) of
`cor:degree-four-local-activation` is the live alternative), the centre carries
a genuine fan certificate, the enumerable carrier lists exactly this core, and
the assigned profile that records two of the triangular ports yields
`D_B = c - 7/4 ≥ 1/4 > 0`. -/

namespace Witness

/-- Generating relation of the witness: the centre `0` joined to `1, 2, 3, 4`;
each `i ∈ {1,2,3,4}` joined to its private shoulder pair `2i+3, 2i+4`; and each
shoulder pair joined by its chord, which makes every port triangular. -/
def rel (left right : Fin 13) : Prop :=
  (left.val = 0 ∧ 1 ≤ right.val ∧ right.val ≤ 4) ∨
    (1 ≤ left.val ∧ left.val ≤ 4 ∧
      (right.val = 2 * left.val + 3 ∨ right.val = 2 * left.val + 4)) ∨
    (right.val = left.val + 1 ∧
      (left.val = 5 ∨ left.val = 7 ∨ left.val = 9 ∨ left.val = 11))

instance decidableRel (left right : Fin 13) : Decidable (rel left right) := by
  unfold rel; infer_instance

/-- The witness graph: a degree-four centre with four cubic neighbours, each
carrying a private shoulder pair joined by its chord. -/
def coreObject : FiniteObject where
  Vertex := Fin 13
  graph := SimpleGraph.fromRel rel
  vertices := inferInstance
  decideAdj := by
    intro left right
    simp only [SimpleGraph.fromRel_adj]
    infer_instance

/-- The degree-four centre `h`. -/
def hub : coreObject.Vertex := (0 : Fin 13)

/-- The port vertex `x_1` of the first triangular port. -/
def leftEndpoint : coreObject.Vertex := (1 : Fin 13)

/-- The port vertex `x_2` of the second triangular port. -/
def rightEndpoint : coreObject.Vertex := (2 : Fin 13)

theorem degree_hub : coreObject.degree hub = 4 := by decide

theorem adj_left : coreObject.graph.Adj hub leftEndpoint := by
  letI : DecidableRel coreObject.graph.Adj := coreObject.decideAdj
  decide

theorem adj_right : coreObject.graph.Adj hub rightEndpoint := by
  letI : DecidableRel coreObject.graph.Adj := coreObject.decideAdj
  decide

/-- The high-neighbourhood normal form holds at the witness centre. -/
def coreNormalForm : NormalForm coreObject hub := by
  letI : DecidableRel coreObject.graph.Adj := coreObject.decideAdj
  letI : Fintype coreObject.Vertex := inferInstanceAs (Fintype (Fin 13))
  letI : DecidableEq coreObject.Vertex := inferInstanceAs (DecidableEq (Fin 13))
  have key : ∀ left right other : coreObject.Vertex,
      coreObject.graph.Adj hub left → coreObject.graph.Adj hub right →
      left ≠ right → other ≠ hub → coreObject.graph.Adj left other →
      ¬ coreObject.graph.Adj right other := by decide
  refine ⟨by decide, by decide, by decide, ?_⟩
  intro left right other centerLeft centerRight distinct otherNeHub leftOther
    rightOther
  exact key left right other centerLeft centerRight distinct otherNeHub
    leftOther rightOther

/-- The first surplus port `p = (h, x_1)`. -/
def leftPort : Port coreObject := ⟨hub, leftEndpoint, adj_left⟩

/-- The second surplus port `q = (h, x_2)`. -/
def rightPort : Port coreObject := ⟨hub, rightEndpoint, adj_right⟩

theorem leftPort_triangular : leftPort.IsTriangular := by
  letI : DecidableRel coreObject.graph.Adj := coreObject.decideAdj
  letI : DecidableEq coreObject.Vertex := inferInstanceAs (DecidableEq (Fin 13))
  decide

theorem rightPort_triangular : rightPort.IsTriangular := by
  letI : DecidableRel coreObject.graph.Adj := coreObject.decideAdj
  letI : DecidableEq coreObject.Vertex := inferInstanceAs (DecidableEq (Fin 13))
  decide

/-- All four ports at the witness centre are triangular, so the fan-compatible
alternative of `cor:degree-four-local-activation` is genuinely absent here and
the second alternative is the live one. -/
theorem triangularPorts_length : (triangularPorts coreObject hub).length = 4 := by
  letI : DecidableRel coreObject.graph.Adj := coreObject.decideAdj
  letI : DecidableEq coreObject.Vertex := inferInstanceAs (DecidableEq (Fin 13))
  decide

/-- `cor:degree-four-local-activation` fires on a concrete graph, in its port
form. -/
theorem activation_fires :
    (∃ p q : Port coreObject, p.center = hub ∧ FanCompatible p q) ∨
      (∃ p q : Port coreObject, p.center = hub ∧ q.center = hub ∧
        p.IsTriangular ∧ q.IsTriangular ∧ p.endpoint ≠ q.endpoint) :=
  degreeFourLocalActivation_ports coreNormalForm degree_hub

/-- The witness centre is the unique degree-four centre, and the enumerable
carrier lists exactly its canonical triangular fan core. -/
theorem degreeFourCores_witness :
    canonicalCore coreObject hub ∈ degreeFourCores coreObject ∧
      (canonicalCore coreObject hub).portVertices.length = 4 := by
  refine ⟨(mem_degreeFourCores_iff coreObject (canonicalCore coreObject hub)).2
    ⟨degree_hub, rfl⟩, ?_⟩
  rw [canonicalCore_portVertices]
  exact triangularPorts_length

/-- The shoulder-completion trichotomy of `def:triangular-fan-core` is available
at the witness core: its well-formedness hypothesis is discharged. -/
theorem trichotomy_available
    {portVertex shoulder target : coreObject.Vertex}
    (completion : (canonicalCore coreObject hub).IsShoulderCompletion
      portVertex shoulder target) :
    (canonicalCore coreObject hub).IsCentralLanding target ∨
      (canonicalCore coreObject hub).IsCrossLanding portVertex target ∨
      (canonicalCore coreObject hub).IsOutsideLanding target :=
  TriangularCore.shoulderCompletion_trichotomy coreNormalForm
    (canonicalCore_portsAdjacent coreObject hub) completion

/-- Four pairwise `C₂`-compatible window coordinates for the four neighbours,
drawn from the independent set of `dIndep_card_eight_witness`. -/
def fanIndex : Fin 13 → Index := fun vertex =>
  match vertex.val with
  | 1 => 0
  | 2 => 8
  | 3 => 1
  | 4 => 9
  | _ => 11

/-- The centre carries a genuine fan certificate, so the fan is
certificate-marked in the sense of `def:marked-typeB-fan`. -/
def markedFan : Marked coreObject := by
  refine markedOfLabelling coreObject hub (by decide)
    (fun vertex => Label.ofIndex (fanIndex vertex)) ?_
  letI : DecidableRel coreObject.graph.Adj := coreObject.decideAdj
  letI : DecidableEq coreObject.Vertex := inferInstanceAs (DecidableEq (Fin 13))
  letI : Fintype coreObject.Vertex := inferInstanceAs (Fintype (Fin 13))
  have key : ∀ left right : coreObject.Vertex, coreObject.graph.Adj hub left →
      coreObject.graph.Adj hub right → left ≠ right →
      gap (fanIndex left) (fanIndex right) ≠ 0 ∧
        gap (fanIndex left) (fanIndex right) ≠ 4 ∧
        gap (fanIndex left) (fanIndex right) ≠ 12 := by decide
  intro left leftAdj right rightAdj distinct
  exact wedgeSafe_ofIndex (key left right leftAdj rightAdj distinct)

/-- An assigned profile with empty packed-window union and everything carried by
the fan envelope. -/
def coreProfile : Profile coreObject where
  marked := markedFan
  window := ∅
  envelope := coreObject.vertexFinset

/-- Node `[79]` fires on a concrete graph: the degree-four fan profile has
centre surplus `1`, `c ≤ 4`, and `D_B = c - (3 - 5α)`. -/
theorem profile_fires (ledger : LoadCapacityProfile) :
    (surplusPorts coreObject coreProfile.marked.fan.hub).length = 1 ∧
      coreProfile.closedCount ≤ 4 ∧
      coreProfile.closedNeighbourDeficit ledger
        = (coreProfile.closedCount : ℚ) - (3 - 5 * ledger.dischargeRate) ∧
      5 * ledger.dischargeRate - 3 ≤ coreProfile.closedNeighbourDeficit ledger ∧
      coreProfile.closedNeighbourDeficit ledger
        ≤ 1 + 5 * ledger.dischargeRate :=
  degreeFourFanProfile coreProfile ledger degree_hub

/-- Case (ii) of `cor:degree-four-local-activation` fires on a concrete graph:
the two triangular ports produce two fan-closed ports and the deficit
`D_B = c - (3 - 5α) ≥ 5α - 1 > 0`. -/
theorem routing_fires (ledger : LoadCapacityProfile) :
    2 ≤ coreProfile.closedCount ∧
      coreProfile.closedNeighbourDeficit ledger
        = (coreProfile.closedCount : ℚ) - (3 - 5 * ledger.dischargeRate) ∧
      5 * ledger.dischargeRate - 1 ≤ coreProfile.closedNeighbourDeficit ledger ∧
      0 < coreProfile.closedNeighbourDeficit ledger := by
  letI : DecidableEq coreObject.Vertex := inferInstanceAs (DecidableEq (Fin 13))
  refine triangularPairTypeBRouting coreProfile ledger coreNormalForm degree_hub
    (p := leftPort) (q := rightPort) rfl rfl (by decide) ?_ ?_ ?_ ?_
  · rw [Profile.mem_remainder_iff]
    exact ⟨(mem_neighbourRim coreObject hub leftEndpoint).2 adj_left,
      Finset.notMem_empty leftEndpoint⟩
  · rw [Profile.mem_remainder_iff]
    exact ⟨(mem_neighbourRim coreObject hub rightEndpoint).2 adj_right,
      Finset.notMem_empty rightEndpoint⟩
  · intro shoulder _
    exact coreObject.mem_vertexFinset shoulder
  · intro shoulder _
    exact coreObject.mem_vertexFinset shoulder

/-- The two triangle edges at a triangular port really are its two non-`h`
incidences (`def:triangular-fan-core`, `S_i = {a_i, b_i}`). -/
theorem shoulderPair_fires :
    ∃ a b : coreObject.Vertex, leftPort.shoulders = [a, b] ∧ a ≠ b ∧
      coreObject.graph.Adj leftPort.endpoint a ∧
      coreObject.graph.Adj leftPort.endpoint b ∧ coreObject.graph.Adj a b :=
  triangularShoulderPair coreNormalForm rfl leftPort_triangular

end Witness

end Hypostructure.Graph.TypeBDegreeFour
