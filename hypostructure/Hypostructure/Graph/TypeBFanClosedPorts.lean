import Hypostructure.Graph.ReceiverLoad
import Hypostructure.Graph.HighCentrePorts
import Hypostructure.Graph.TypeBMarkedFan

/-!
# Fan-closed surplus ports and the local Type B closed-neighbour deficit

This file is the graph-mathematics content of manuscript node `[72]`
(`typeBfan`) of `erdos_64_proof.tex`:

* `def:fan-closed-port` -- `Profile.IsFanClosed`;
* `lem:compatible-pair-fan-closure` -- `compatiblePairFanClosure`;
* `prop:fan-closed-port-typeB-routing` (parts (a) and (b)) --
  `fanClosedPortTypeBRouting`;
* `cor:compatible-pair-typeB-routing` -- `compatiblePairTypeBRouting`.

Nothing here is redefined: the ports, their shoulder schedules, the
open/triangular dichotomy, fan-compatibility and the high-neighbourhood normal
form are `Hypostructure.Graph.TypeBOpenPorts`; the certificate-marked fan and
its cubic-closed neighbours are `Hypostructure.Graph.TypeBMarkedFan`.

The assigned Type B fan-window profile `𝔉_h` is `Profile`: a certificate-marked
fan (`def:marked-typeB-fan`), the packed-window union `W`, and the vertex
support carried by the fan envelope.  `Profile` has **no** propositional
fields; the remainder side `R = G - W` of
`def:typeB-window-incidence-profile` is *derived* as `rim \ W`, not assumed.

`NormalForm` -- the only ambient structural input -- is an explicit argument of
every theorem that needs it, exactly as in
`TypeBOpenPorts.heavyCenterTriangularAlternative`.  No hypothesis anywhere in
this file asserts the absence of a structure; the four-cycle absence behind
`NormalForm` is read off the incoming residual by
`TypeBOpenPorts.LocalHypotheses.normalForm` (`ctx.avoids`).

The closed-neighbour deficit `D_B(𝔉) = c(𝔉) - (3 - (k+1)α)` of
`def:typeB-multiclosed-residual` is rational, and is formalised over `ℚ`.  Its
subtrahend is not a literal: it is the Step 1 closed-neighbourhood charge
`(3 - k - α) + c(-α) + (k - c)(1 - α) = 3 - (k+1)α - c` of
the manuscript's Step 1 closed-neighbourhood charge, so the discharge rate
`α` is read as the reciprocal of the registered `loadMultiplier`.  At the
registered scale `loadMultiplier = 4` this is the manuscript's
`c(𝔉) - (11 - k)/4`.
-/

namespace Hypostructure.Graph.TypeBFanClosedPorts

open Hypostructure.Graph
open Hypostructure.Graph.TypeBMarkedFan
open Hypostructure.Graph.ReceiverLoad (LoadCapacityProfile)

universe u

variable {object : FiniteObject.{u}}

/-! ## Decidability of cubic-closedness

`TypeBMarkedFan.Marked.IsCubicClosed` quantifies over the vertex type, which is
finite and has decidable adjacency, so the predicate is decidable.  This is
what lets `c(𝔉)` be an honest `Finset.card`. -/

instance decidableIsCubicClosed (marked : Marked object)
    (support : Finset object.Vertex) (vertex : object.Vertex) :
    Decidable (marked.IsCubicClosed support vertex) := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  letI : Fintype object.Vertex := @FinEnum.instFintype _ object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  unfold Marked.IsCubicClosed
  infer_instance

/-! ## Assigned Type B fan-window profiles -/

/-- An assigned Type B fan-window profile `𝔉_h` at one centre, carrying exactly
the data used by `def:fan-closed-port`:

* a certificate-marked Type B fan at `h` (`def:marked-typeB-fan`);
* the packed-window union `W` of `def:typeB-window-incidence-profile`;
* the vertex support carried by the assigned fan envelope, in the same shape
  the marked fan already uses for cubic-closedness.

There are no propositional fields: everything the manuscript requires of the
profile is derived below. -/
structure Profile (object : FiniteObject.{u}) where
  /-- The certificate-marked Type B fan at the centre `h`. -/
  marked : Marked object
  /-- The union `W` of the fixed maximal packed induced `P₁₃` windows. -/
  window : Finset object.Vertex
  /-- The vertices carried by the assigned fan envelope. -/
  envelope : Finset object.Vertex

namespace Profile

variable (profile : Profile object)

/-- The remainder-side fan neighbours of `def:typeB-window-incidence-profile`:
the rim vertices lying in `R = G - W`. -/
def remainder : Finset object.Vertex :=
  letI : DecidableEq object.Vertex := object.vertices.decEq
  profile.marked.fan.rim \ profile.window

variable {profile}

theorem mem_remainder_iff (vertex : object.Vertex) :
    vertex ∈ profile.remainder ↔
      vertex ∈ profile.marked.fan.rim ∧ vertex ∉ profile.window := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  rw [remainder, Finset.mem_sdiff]

theorem mem_rim_of_mem_remainder {vertex : object.Vertex}
    (member : vertex ∈ profile.remainder) : vertex ∈ profile.marked.fan.rim :=
  (mem_remainder_iff vertex).1 member |>.1

theorem not_mem_window_of_mem_remainder {vertex : object.Vertex}
    (member : vertex ∈ profile.remainder) : vertex ∉ profile.window :=
  (mem_remainder_iff vertex).1 member |>.2

variable (profile)

/-! ## `def:typeB-window-incidence-profile`: the two incidence kinds -/

/-- A *window incidence* of a remainder-side fan neighbour `u`: an edge `u z`
whose outside endpoint lies in the packed-window union `W`. -/
def IsWindowIncidence (source target : object.Vertex) : Prop :=
  source ∉ profile.window ∧ object.graph.Adj source target ∧
    target ∈ profile.window

/-- A *non-window fan incidence* of a remainder-side fan neighbour `u`: an edge
`u z` with `z ∉ W ∪ {h}`. -/
def IsNonWindowIncidence (source target : object.Vertex) : Prop :=
  source ∉ profile.window ∧ object.graph.Adj source target ∧
    target ∉ profile.window ∧ target ≠ profile.marked.fan.hub

/-! ## `def:fan-closed-port` -/

/-- `def:fan-closed-port`.  The surplus port `p = (h, x)` is *fan-closed* in the
assigned profile when

* (a) the port vertex `x` is recorded as a remainder-side fan neighbour of `h`;
* (b) the two non-`h` incidences `x a_p` and `x b_p` are assigned to the fan
  envelope.

Clause (c) of the manuscript -- each assigned incidence is recorded as either a
window incidence or a non-window fan incidence -- is deliberately *not* a
field: it is proved for every fan-closed port in
`IsFanClosed.incidence_classified` below, so nothing is assumed that the
profile does not already determine. -/
def IsFanClosed (endpoint : object.Vertex) : Prop :=
  endpoint ∈ profile.remainder ∧
    ∀ shoulder, IsShoulder object profile.marked.fan.hub endpoint shoulder →
      shoulder ∈ profile.envelope

variable {profile}

namespace IsFanClosed

variable {endpoint : object.Vertex}

theorem remainder_mem (closed : profile.IsFanClosed endpoint) :
    endpoint ∈ profile.remainder := closed.1

theorem envelope_mem (closed : profile.IsFanClosed endpoint)
    {shoulder : object.Vertex}
    (member : IsShoulder object profile.marked.fan.hub endpoint shoulder) :
    shoulder ∈ profile.envelope :=
  closed.2 shoulder member

/-- Clause (c) of `def:fan-closed-port`, discharged rather than assumed: each
incidence assigned by a fan-closed port is a window incidence or a non-window
fan incidence in the sense of `def:typeB-window-incidence-profile`. -/
theorem incidence_classified (closed : profile.IsFanClosed endpoint)
    {shoulder : object.Vertex}
    (member : IsShoulder object profile.marked.fan.hub endpoint shoulder) :
    profile.IsWindowIncidence endpoint shoulder ∨
      profile.IsNonWindowIncidence endpoint shoulder := by
  have outside : endpoint ∉ profile.window :=
    not_mem_window_of_mem_remainder closed.remainder_mem
  have adjacency : object.graph.Adj endpoint shoulder := member.1
  by_cases inWindow : shoulder ∈ profile.window
  · exact Or.inl ⟨outside, adjacency, inWindow⟩
  · exact Or.inr ⟨outside, adjacency, inWindow, member.2⟩

/-- The manuscript's step "`x` has internal fan degree `3` in the assigned
envelope, so it is cubic-closed in the sense of `def:marked-typeB-fan`".  The
cubicity of `x` is `lem:heavy-neighbourhood-normal-form`, supplied as the
structural input `normal`. -/
theorem isCubicClosed (normal : NormalForm object 3 profile.marked.fan.hub)
    (closed : profile.IsFanClosed endpoint) :
    profile.marked.IsCubicClosed profile.envelope endpoint := by
  have hubAdj : object.graph.Adj profile.marked.fan.hub endpoint :=
    (profile.marked.rim_eq_neighbourhood endpoint).1
      (mem_rim_of_mem_remainder closed.remainder_mem)
  refine ⟨mem_rim_of_mem_remainder closed.remainder_mem,
    normal.neighbourTight hubAdj, ?_⟩
  intro other adjacency notHub
  exact closed.envelope_mem ⟨adjacency, notHub⟩

end IsFanClosed

/-! ## The closed-neighbour count and deficit
(`def:typeB-multiclosed-residual`) -/

variable (profile)

/-- The cubic-closed fan neighbours recorded by the profile: the set counted by
`c(𝔉)` in `def:typeB-multiclosed-residual`. -/
def closedNeighbours : Finset object.Vertex := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  classical
  exact profile.marked.fan.rim.filter fun vertex =>
    profile.marked.IsCubicClosed profile.envelope vertex ∧
      vertex ∈ profile.remainder

/-- `c(𝔉) = |{u ∈ N(h) : u is cubic-closed in 𝔉}|`. -/
def closedCount : Nat := profile.closedNeighbours.card

/-- The closed-neighbour deficit `D_B(𝔉) = c(𝔉) - (3 - (k+1)α)` of
`def:typeB-multiclosed-residual`, over the rationals, with the discharge rate
`α` read from the registered presentation.  At `α = 1/4` the subtrahend is
`3 - (k+1)/4 = (11 - k)/4`, the manuscript's own spelling. -/
def closedNeighbourDeficit (ledger : LoadCapacityProfile) : ℚ :=
  (profile.closedCount : ℚ) -
    (3 - ((object.degree profile.marked.fan.hub : ℚ) + 1) *
      (1 / (ledger.loadMultiplier : ℚ)))

variable {profile}

theorem mem_closedNeighbours_iff (vertex : object.Vertex) :
    vertex ∈ profile.closedNeighbours ↔
      vertex ∈ profile.marked.fan.rim ∧
        (profile.marked.IsCubicClosed profile.envelope vertex ∧
          vertex ∈ profile.remainder) := by
  classical
  simpa [closedNeighbours] using
    (Finset.mem_filter (s := profile.marked.fan.rim)
      (p := fun vertex =>
        profile.marked.IsCubicClosed profile.envelope vertex ∧
          vertex ∈ profile.remainder) (a := vertex))

/-- The recording convention of `def:typeB-window-incidence-profile` holds by
construction: a profile records the assigned fan neighbours *that lie in the
remainder side*, so every closed neighbour lies in `R = G - W`.  A theorem about
the profile, never a hypothesis. -/
theorem closedNeighbours_subset_remainder {vertex : object.Vertex}
    (member : vertex ∈ profile.closedNeighbours) :
    vertex ∈ profile.remainder :=
  ((mem_closedNeighbours_iff vertex).1 member).2.2

theorem mem_closedNeighbours_of_isFanClosed
    (normal : NormalForm object 3 profile.marked.fan.hub)
    {endpoint : object.Vertex} (closed : profile.IsFanClosed endpoint) :
    endpoint ∈ profile.closedNeighbours :=
  (mem_closedNeighbours_iff endpoint).2
    ⟨mem_rim_of_mem_remainder closed.remainder_mem,
      closed.isCubicClosed normal, closed.remainder_mem⟩

end Profile

/-! ## `lem:compatible-pair-fan-closure` -/

/-- `lem:compatible-pair-fan-closure`, manuscript node `[72]`.

Let `p = (h, x)` and `q = (h, y)` be fan-compatible open ports at `h`.  In any
assigned profile that records `x` and `y` as remainder-side fan neighbours and
assigns the four incidences `x a_p`, `x b_p`, `y a_q`, `y b_q` to the fan
envelope, `p` and `q` are two distinct fan-closed ports, and those four
incidences are pairwise distinct as local incidence carriers.

The distinctness of the carriers is `FanCompatible.carriers_nodup`, which uses
all three clauses of `def:fan-compatible-open-ports`.  The global B2 clause of
the manuscript statement is outside this file (see the module note). -/
theorem compatiblePairFanClosure (profile : Profile object)
    {left right : object.Vertex}
    (compatible : FanCompatible object profile.marked.fan.hub left right)
    (leftRemainder : left ∈ profile.remainder)
    (rightRemainder : right ∈ profile.remainder)
    (leftAssigned : ∀ shoulder,
      IsShoulder object profile.marked.fan.hub left shoulder →
        shoulder ∈ profile.envelope)
    (rightAssigned : ∀ shoulder,
      IsShoulder object profile.marked.fan.hub right shoulder →
        shoulder ∈ profile.envelope) :
    profile.IsFanClosed left ∧ profile.IsFanClosed right ∧ left ≠ right := by
  exact ⟨⟨leftRemainder, leftAssigned⟩, ⟨rightRemainder, rightAssigned⟩,
    compatible.endpointsNe⟩

/-! ## `prop:fan-closed-port-typeB-routing` -/

/-- Part (a) of `prop:fan-closed-port-typeB-routing`: a family `𝒬` of
fan-closed surplus ports at `h`, indexed by its pairwise distinct port
vertices, contributes at least `|𝒬|` cubic-closed neighbours of `h`. -/
theorem card_le_closedCount (profile : Profile object)
    (normal : NormalForm object 3 profile.marked.fan.hub)
    {ports : Finset object.Vertex}
    (fanClosed : ∀ vertex ∈ ports, profile.IsFanClosed vertex) :
    ports.card ≤ profile.closedCount := by
  refine Finset.card_le_card ?_
  intro vertex member
  exact Profile.mem_closedNeighbours_of_isFanClosed normal (fanClosed vertex member)

/-- `prop:fan-closed-port-typeB-routing`, parts (a) and (b), manuscript node
`[72]`.

At a certificate-marked fan centre `h` of degree `k` carrying a family of
`r ≥ 2` fan-closed surplus ports:

* the ports contribute at least `r` cubic-closed neighbours;
* `D_B(𝔉_h) ≥ r - (3 - (k+1)α) ≥ (k+1)α - 1 > 0`.

`k ≥ 4` is `Marked.highDegree`, already part of the certificate-marked fan, so
no degree hypothesis is added here.  The strict positivity is the sharp instance
of the recorded design constraint
`ReceiverLoad.LoadCapacityProfile.dischargeRate_gt` (`5α > 1`): at `c = 2` and
`k = 4` the deficit is exactly `5α - 1`, so this is the place the constraint was
read off, and no hypothesis is added here either.  At `α = 1/4` the three
displayed quantities are the manuscript's `r - (11-k)/4`, `(k-3)/4` and
`1/4 > 0`. -/
theorem fanClosedPortTypeBRouting (profile : Profile object)
    (ledger : LoadCapacityProfile)
    (normal : NormalForm object 3 profile.marked.fan.hub)
    (scale : ledger.loadMultiplier = 4)
    {ports : Finset object.Vertex}
    (fanClosed : ∀ vertex ∈ ports, profile.IsFanClosed vertex)
    (two : 2 ≤ ports.card) :
    ports.card ≤ profile.closedCount ∧
      (ports.card : ℚ) -
          (3 - ((object.degree profile.marked.fan.hub : ℚ) + 1)
            * (1 / (ledger.loadMultiplier : ℚ)))
        ≤ profile.closedNeighbourDeficit ledger ∧
      ((object.degree profile.marked.fan.hub : ℚ) + 1) *
          (1 / (ledger.loadMultiplier : ℚ)) - 1
        ≤ profile.closedNeighbourDeficit ledger ∧
      0 < profile.closedNeighbourDeficit ledger := by
  have counted : ports.card ≤ profile.closedCount :=
    card_le_closedCount profile normal fanClosed
  have countedCast : (ports.card : ℚ) ≤ (profile.closedCount : ℚ) := by
    exact_mod_cast counted
  have twoCast : (2 : ℚ) ≤ (profile.closedCount : ℚ) := by
    exact_mod_cast le_trans two counted
  have highCast : (4 : ℚ) ≤ (object.degree profile.marked.fan.hub : ℚ) := by
    exact_mod_cast profile.marked.highDegree
  have rateNonneg : (0 : ℚ) ≤ 1 / (ledger.loadMultiplier : ℚ) := by positivity
  have sharp : (1 : ℚ) < 5 * (1 / (ledger.loadMultiplier : ℚ)) := by
    rw [scale]
    norm_num
  have degreeRate :
      5 * (1 / (ledger.loadMultiplier : ℚ))
        ≤ ((object.degree profile.marked.fan.hub : ℚ) + 1) *
          (1 / (ledger.loadMultiplier : ℚ)) :=
    mul_le_mul_of_nonneg_right (by linarith) rateNonneg
  refine ⟨counted, ?_, ?_, ?_⟩ <;>
    · unfold Profile.closedNeighbourDeficit
      linarith

/-! ## `cor:compatible-pair-typeB-routing` -/

/-- `cor:compatible-pair-typeB-routing`, manuscript node `[72]` fed from node
`[69]`.

A fan-compatible open pair at a certificate-marked centre `h`, recorded and
assigned by the profile, supplies the two fan-closed ports demanded by
`prop:fan-closed-port-typeB-routing`, hence

`D_B(𝔉_h) ≥ (k+1)α - 1 > 0`, the manuscript's `(k - 3)/4 > 0` at `α = 1/4`.

The absence of the direct-cycle, target-defect, compression and delocalization
alternatives is *not* a hypothesis here: those alternatives gate the B1 ledger
entry, not the deficit bound, and this statement asserts only the bound. -/
theorem compatiblePairTypeBRouting (profile : Profile object)
    (ledger : LoadCapacityProfile)
    (normal : NormalForm object 3 profile.marked.fan.hub)
    (scale : ledger.loadMultiplier = 4) {left right : object.Vertex}
    (compatible : FanCompatible object profile.marked.fan.hub left right)
    (leftRemainder : left ∈ profile.remainder)
    (rightRemainder : right ∈ profile.remainder)
    (leftAssigned : ∀ shoulder,
      IsShoulder object profile.marked.fan.hub left shoulder →
        shoulder ∈ profile.envelope)
    (rightAssigned : ∀ shoulder,
      IsShoulder object profile.marked.fan.hub right shoulder →
        shoulder ∈ profile.envelope) :
    2 ≤ profile.closedCount ∧
      ((object.degree profile.marked.fan.hub : ℚ) + 1) *
          (1 / (ledger.loadMultiplier : ℚ)) - 1
        ≤ profile.closedNeighbourDeficit ledger ∧
      0 < profile.closedNeighbourDeficit ledger := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  obtain ⟨leftClosed, rightClosed, distinct⟩ :=
    compatiblePairFanClosure profile compatible leftRemainder
      rightRemainder leftAssigned rightAssigned
  have pairCard : ({left, right} : Finset object.Vertex).card = 2 :=
    Finset.card_pair distinct
  have fanClosed : ∀ vertex ∈ ({left, right} : Finset object.Vertex),
      profile.IsFanClosed vertex := by
    intro vertex member
    rcases Finset.mem_insert.1 member with rfl | member
    · exact leftClosed
    · rw [Finset.mem_singleton] at member
      subst member
      exact rightClosed
  obtain ⟨counted, _, deficitBound, positive⟩ :=
    fanClosedPortTypeBRouting profile ledger normal scale fanClosed
      (by rw [pairCard])
  rw [pairCard] at counted
  exact ⟨counted, deficitBound, positive⟩

/-! ## Non-vacuity

Every hypothesis above is realised simultaneously by an explicit finite graph:
a centre of degree four whose four neighbours are cubic with private shoulder
pairs.  The centre carries a genuine fan certificate, the high-neighbourhood
normal form holds at it, two of its ports are fan-compatible open ports, and
the profile that records them yields a strictly positive deficit.  Hence
`compatiblePairTypeBRouting` -- and with it `fanClosedPortTypeBRouting`, whose
hypotheses it discharges -- is not vacuous. -/

namespace Witness

/-- Generating relation of the witness: the centre `0` joined to `1, 2, 3, 4`,
and each `i ∈ {1,2,3,4}` joined to its own shoulder pair `2i+3, 2i+4`. -/
def rel (left right : Fin 13) : Prop :=
  (left.val = 0 ∧ 1 ≤ right.val ∧ right.val ≤ 4) ∨
    (1 ≤ left.val ∧ left.val ≤ 4 ∧
      (right.val = 2 * left.val + 3 ∨ right.val = 2 * left.val + 4))

instance decidableRel (left right : Fin 13) : Decidable (rel left right) := by
  unfold rel; infer_instance

/-- The witness graph: a degree-four centre with four cubic neighbours, each
carrying a private, chordless shoulder pair. -/
def fanObject : FiniteObject where
  Vertex := Fin 13
  graph := SimpleGraph.fromRel rel
  vertices := inferInstance
  decideAdj := by
    intro left right
    simp only [SimpleGraph.fromRel_adj]
    infer_instance

/-- The high centre `h`. -/
def hub : fanObject.Vertex := (0 : Fin 13)

/-- The port vertex `x` of the first open port. -/
def leftEndpoint : fanObject.Vertex := (1 : Fin 13)

/-- The port vertex `y` of the second open port. -/
def rightEndpoint : fanObject.Vertex := (2 : Fin 13)

theorem degree_hub : fanObject.degree hub = 4 := by decide

theorem adj_left : fanObject.graph.Adj hub leftEndpoint := by
  letI : DecidableRel fanObject.graph.Adj := fanObject.decideAdj
  decide

theorem adj_right : fanObject.graph.Adj hub rightEndpoint := by
  letI : DecidableRel fanObject.graph.Adj := fanObject.decideAdj
  decide

/-- The high-neighbourhood normal form of `lem:heavy-neighbourhood-normal-form`
holds at the witness centre. -/
def fanNormalForm : NormalForm fanObject 3 hub := by
  letI : DecidableRel fanObject.graph.Adj := fanObject.decideAdj
  letI : Fintype fanObject.Vertex := inferInstanceAs (Fintype (Fin 13))
  letI : DecidableEq fanObject.Vertex := inferInstanceAs (DecidableEq (Fin 13))
  have key : ∀ left right other : fanObject.Vertex,
      fanObject.graph.Adj hub left → fanObject.graph.Adj hub right →
      left ≠ right → other ≠ hub → fanObject.graph.Adj left other →
      ¬ fanObject.graph.Adj right other := by decide
  refine ⟨by decide, by decide, ?_⟩
  intro left right other centerLeft centerRight distinct _nonadjacent otherNeHub
    leftOther rightOther
  exact key left right other centerLeft centerRight distinct otherNeHub
    leftOther rightOther

/-- The two ports are a fan-compatible pair of open ports. -/
theorem compatible : FanCompatible fanObject hub leftEndpoint rightEndpoint := by
  letI : DecidableRel fanObject.graph.Adj := fanObject.decideAdj
  letI : DecidableEq fanObject.Vertex := inferInstanceAs (DecidableEq (Fin 13))
  letI : Fintype fanObject.Vertex := inferInstanceAs (Fintype (Fin 13))
  have leftOpen : IsOpenPort fanObject hub leftEndpoint := by
    rintro ⟨left, right, leftShoulder, rightShoulder, chord⟩
    simp [IsShoulder, fanObject, rel, hub, leftEndpoint] at leftShoulder rightShoulder chord
    omega
  have rightOpen : IsOpenPort fanObject hub rightEndpoint := by
    rintro ⟨left, right, leftShoulder, rightShoulder, chord⟩
    simp [IsShoulder, fanObject, rel, hub, rightEndpoint] at leftShoulder rightShoulder chord
    omega
  exact fanCompatible_of_endpoints_nonadjacent fanNormalForm adj_left adj_right
    (by decide) (by decide) leftOpen rightOpen

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
def markedFan : Marked fanObject := by
  refine markedOfLabelling fanObject hub (by decide)
    (fun vertex => Label.ofIndex (fanIndex vertex)) ?_
  letI : DecidableRel fanObject.graph.Adj := fanObject.decideAdj
  letI : DecidableEq fanObject.Vertex := inferInstanceAs (DecidableEq (Fin 13))
  letI : Fintype fanObject.Vertex := inferInstanceAs (Fintype (Fin 13))
  have key : ∀ left right : fanObject.Vertex, fanObject.graph.Adj hub left →
      fanObject.graph.Adj hub right → left ≠ right →
      gap (fanIndex left) (fanIndex right) ≠ 0 ∧
        gap (fanIndex left) (fanIndex right) ≠ 4 ∧
        gap (fanIndex left) (fanIndex right) ≠ 12 := by decide
  intro left leftAdj right rightAdj distinct
  exact wedgeSafe_ofIndex (key left right leftAdj rightAdj distinct)

/-- An assigned profile with empty packed-window union and everything carried by
the fan envelope. -/
def fanProfile : Profile fanObject where
  marked := markedFan
  window := ∅
  envelope := fanObject.vertexFinset

/-- `cor:compatible-pair-typeB-routing` fires on a concrete graph: the
compatible open pair produces two fan-closed ports and a strictly positive
closed-neighbour deficit. -/
theorem routing_fires (ledger : LoadCapacityProfile)
    (scale : ledger.loadMultiplier = 4) :
    2 ≤ fanProfile.closedCount ∧
      ((fanObject.degree fanProfile.marked.fan.hub : ℚ) + 1)
            * (1 / (ledger.loadMultiplier : ℚ)) - 1
        ≤ fanProfile.closedNeighbourDeficit ledger ∧
      0 < fanProfile.closedNeighbourDeficit ledger := by
  refine compatiblePairTypeBRouting fanProfile ledger fanNormalForm scale compatible
    ?_ ?_ ?_ ?_
  · rw [Profile.mem_remainder_iff]
    exact ⟨(mem_neighbourRim fanObject hub leftEndpoint).2 adj_left,
      Finset.notMem_empty leftEndpoint⟩
  · rw [Profile.mem_remainder_iff]
    exact ⟨(mem_neighbourRim fanObject hub rightEndpoint).2 adj_right,
      Finset.notMem_empty rightEndpoint⟩
  · intro shoulder _
    exact fanObject.mem_vertexFinset shoulder
  · intro shoulder _
    exact fanObject.mem_vertexFinset shoulder

end Witness

end Hypostructure.Graph.TypeBFanClosedPorts
