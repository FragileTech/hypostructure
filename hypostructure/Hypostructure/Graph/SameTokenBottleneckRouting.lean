import Hypostructure.Graph.DecoratedHandoffEnvelope
import Hypostructure.Graph.SameTokenRoutingGerms
import Hypostructure.Graph.HomogeneousTokenCap
import Hypostructure.Graph.NamedSurplusExits
import Hypostructure.Graph.CapacityTokenAssignment

/-!
# `lem:same-token-bottleneck-routing`

> Assume `G` survives the sparse surplus exits.  Let `t ∈ 𝔗_cap` and
> `r ∈ 𝔕_st`.  If a role-homogeneous same-token matching or star in the
> role-fibre graph `H_{t,r}` has more than `Q_geom` edges, then one of the
> following occurs: (a) a sparse surplus exit occurs; or (b) the support
> produces a decorated Type B handoff fan envelope, hence is routed to the Type
> B fan ledger.

The manuscript's proof has three steps, and all three are already owned
elsewhere in this tree; this module composes them and states the lemma.

* The **pigeonhole**: "since there are only `Q_geom` routing labels, two
  distinct edges `π₁, π₂ ∈ 𝓜` have the same routing label".  That is
  `SameTokenRoutingGerms.exists_same_routingLabel`, at the counted alphabet of
  `def:same-token-routing-germs`.
* The **germ dichotomy**: the two routing germs from the carrier of `t` toward
  the two selected demands are parallel, or they have a first separator.  That
  is `SameTokenRoutingGerms.parallel_or_firstSeparator` on the germs' own vertex
  lists, and `DecoratedHandoff.Separation` is the separated configuration with
  its switch support `S_z`.
* The **reading of each configuration**: at the separator the identification of
  the two declared response coordinates is *absorbed* -- target-defective,
  target-complete on a proper support, or complete only after adjoining a larger
  connected support, which are the manuscript's quotient, compression and
  delocalization exits -- or it is *surviving*, and then `d_G(z) ≥ 4` and the
  separated tails are the decorated handoff data of
  `def:decorated-fan-envelope`.  Those are `DecoratedHandoff.Absorbed`,
  `DecoratedHandoff.four_le_degree_of_surviving`,
  `DecoratedHandoff.envelopeOfSeparation` and
  `DecoratedHandoff.admissible_of_envelope`.

Nothing is re-derived: the separated half of the argument is the *same*
configuration Type A exit `(7)` is made of, so it is read off
`Graph/DecoratedHandoffEnvelope.lean` rather than rebuilt at the token.  What
this module adds is the statement at a same-token bottleneck and the
composition.

The routing germs themselves are not constructed here.  `Z(π;t,r)` is
`def:same-token-routing-germs`' declared support and its connector germs are
declared data of `def:declared-coordinate-signature`, so the caller supplies the
separated configuration; what the lemma owes, and discharges, is that *every*
such configuration is one of the manuscript's two outcomes.

No paper label is a value here, no baseline, scale or window order is known, and
the target, the boundary-degree profile, the high-degree predicate and the
absorbing relation are all parameters.
-/

namespace Hypostructure.Graph.SameTokenRoutingGerms

open Hypostructure
open Hypostructure.Graph.DecoratedHandoff
open Hypostructure.Graph.SameTokenBlockerRoles

universe u

variable {object : FiniteObject.{u}}

/-- **`lem:same-token-bottleneck-routing`, at one separated pair of routing
germs.**

Either the identification at the first separator is absorbed -- which is the
manuscript's sparse surplus exit, in the three readings
`def:named-surplus-exits` gives it -- or the separator survives, and then the
separated connector tails are admissible decorated Type B handoff fan data and
the bottleneck is routed to the Type B fan ledger.

The two arms are `DecoratedHandoff.absorbed_or_surviving`, which is the excluded
middle on the absorbed classification and therefore exhaustive; what each arm
*is* is the content.  The surviving arm's degree bound `d_G(z) ≥ 4` is
`lem:typeA-cubic-switch-absorption`, and the envelope is
`lem:typeA-high-degree-handoff` at the same configuration. -/
theorem bottleneckRouting {support : Finset object.Vertex}
    {receiver outside : object.Vertex}
    {separation : Separation object support receiver outside}
    {LengthOK : Nat → Prop}
    {Uncompressible WindowFree : Finset object.Vertex → Prop}
    {HighDegree : object.Vertex → Prop}
    {Absorbing : object.Vertex → object.Vertex → object.Vertex → Prop}
    (Target : FiniteObject.{u} → Prop)
    (reading : SwitchReading separation) (Enlarges : Prop)
    (armLeft armRight : List object.Vertex)
    (armLeftIssued : armLeft.head? = some separation.nextLeft)
    (armRightIssued : armRight.head? = some separation.nextRight)
    (armLeftChain : armLeft.IsChain object.graph.Adj)
    (armRightChain : armRight.IsChain object.graph.Adj)
    (armLeftNodup : armLeft.Nodup) (armRightNodup : armRight.Nodup)
    (armLeftLands : ∃ terminal, armLeft.getLast? = some terminal ∧
      terminal ∈ support)
    (armRightLands : ∃ terminal, armRight.getLast? = some terminal ∧
      terminal ∈ support)
    (armLeftInterior : ∀ vertex ∈ armLeft,
      vertex ∈ support ∨ vertex = separation.separator →
      armLeft.getLast? = some vertex)
    (armRightInterior : ∀ vertex ∈ armRight,
      vertex ∈ support ∨ vertex = separation.separator →
      armRight.getLast? = some vertex)
    (highOfDegree : ∀ vertex : object.Vertex,
      3 < object.degree vertex → HighDegree vertex)
    (avoids : ¬ Graph.HasCycleWithLength LengthOK object)
    (denied : ¬ Absorbing separation.separator separation.nextLeft
      separation.nextRight)
    (deniedSwap : ¬ Absorbing separation.separator separation.nextRight
      separation.nextLeft)
    (windowFree : WindowFree support)
    (uncompressible : ∀ piece : Finset object.Vertex, Uncompressible piece) :
    Absorbed Target reading Enlarges ∨
      (3 < object.degree separation.separator ∧
        ∃ envelope : Envelope object LengthOK HighDegree Absorbing,
          Admissible object LengthOK Uncompressible WindowFree envelope) := by
  classical
  rcases absorbed_or_surviving (separation := separation) Target reading Enlarges with
    absorbed | surviving
  · exact .inl absorbed
  · have high : 3 < object.degree separation.separator :=
      four_le_degree_of_surviving surviving
    refine .inr ⟨high, envelopeOfSeparation separation armLeft armRight
      armLeftIssued armRightIssued armLeftChain armRightChain armLeftNodup
      armRightNodup armLeftLands armRightLands armLeftInterior armRightInterior
      (highOfDegree _ high) avoids denied deniedSwap, ?_⟩
    exact admissible_of_envelope avoids windowFree uncompressible

/-- **The pigeonhole the lemma opens with, at the counted alphabet.**

A role-homogeneous same-token pattern with more than `Q_geom` edges carries two
distinct edges with the same routing label -- the two selected surplus demands
whose connector data agree in token, blocker type, token subtype and
boundary-degree fibre, which is what the germ dichotomy above is applied to. -/
theorem exists_same_routingLabel_of_patternBound {Pattern : Type v}
    [DecidableEq Pattern] {Label : Type} [Fintype Label] [DecidableEq Label]
    (pattern : Finset Pattern) (label : Pattern → Label)
    (large : patternBound Label ≤ pattern.card) :
    ∃ first ∈ pattern, ∃ second ∈ pattern,
      first ≠ second ∧ label first = label second :=
  exists_same_routingLabel pattern label
    (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) large)

/-- **The two selected surplus demands the lemma routes.**

*"Since there are only `Q_geom` routing labels, two distinct edges
`π₁, π₂ ∈ 𝓜` have the same routing label.  If `𝓜` is a star, choose the two
noncentral endpoints of `π₁` and `π₂`; if `𝓜` is a matching, choose an endpoint
from each edge.  In both cases we obtain two distinct selected surplus
demands."*

Both readings are discharged here, at the pattern `cor:forced-same-token-scale`
produces: a matching's two edges are disjoint, so any endpoint of one differs
from any endpoint of the other, and a star's two edges share only the centre, so
their noncentral endpoints differ.  The pairs are two-element sets, which is
what `def:same-token-patterns` makes `H_{t,r}`'s edges. -/
theorem exists_routed_demands {Demand : Type v} [DecidableEq Demand]
    {Label : Type} [Fintype Label] [DecidableEq Label]
    (pattern : Finset (Finset Demand)) (label : Finset Demand → Label)
    (pairs : ∀ edge ∈ pattern, edge.card = 2)
    (structured : PatternFamily.IsMatching pattern ∨
      ∃ centre : Demand, PatternFamily.IsStar pattern centre)
    (large : patternBound Label ≤ pattern.card) :
    ∃ first ∈ pattern, ∃ second ∈ pattern,
      first ≠ second ∧ label first = label second ∧
        ∃ left ∈ first, ∃ right ∈ second, left ≠ right := by
  classical
  obtain ⟨first, firstMem, second, secondMem, distinct, sameLabel⟩ :=
    exists_same_routingLabel_of_patternBound pattern label large
  refine ⟨first, firstMem, second, secondMem, distinct, sameLabel, ?_⟩
  rcases structured with matching | ⟨centre, star⟩
  · -- A matching: the two edges are disjoint, so any two endpoints differ.
    obtain ⟨left, leftMem⟩ : first.Nonempty :=
      Finset.card_pos.1 (by rw [pairs first firstMem]; omega)
    obtain ⟨right, rightMem⟩ : second.Nonempty :=
      Finset.card_pos.1 (by rw [pairs second secondMem]; omega)
    refine ⟨left, leftMem, right, rightMem, ?_⟩
    intro equal
    exact matching first firstMem second secondMem distinct left leftMem
      (equal ▸ rightMem)
  · -- A star: each edge is the centre together with one other demand, and those
    -- two differ, or the edges would coincide.
    have decompose : ∀ edge ∈ pattern, ∃ other,
        other ≠ centre ∧ other ∈ edge ∧ edge = {centre, other} := by
      intro edge member
      have centreMem := star edge member
      have card := pairs edge member
      obtain ⟨other, otherMem⟩ : (edge.erase centre).Nonempty := by
        refine Finset.card_pos.1 ?_
        rw [Finset.card_erase_of_mem centreMem, card]
        omega
      refine ⟨other, (Finset.mem_erase.1 otherMem).1,
        (Finset.mem_erase.1 otherMem).2, ?_⟩
      refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
      · intro item inside
        rcases Finset.mem_insert.1 inside with rfl | inside
        · exact centreMem
        · rw [Finset.mem_singleton.1 inside]
          exact (Finset.mem_erase.1 otherMem).2
      · rw [card, Finset.card_insert_of_notMem
          (by simp [Ne.symm (Finset.mem_erase.1 otherMem).1]), Finset.card_singleton]
    obtain ⟨left, leftNe, leftMem, leftEq⟩ := decompose first firstMem
    obtain ⟨right, rightNe, rightMem, rightEq⟩ := decompose second secondMem
    refine ⟨left, leftMem, right, rightMem, ?_⟩
    intro equal
    exact distinct (by rw [leftEq, rightEq, equal])

/-! ## `ρ_t`, the routing label of a pair

*"The routing label of a pair in `Π_{t,r}` records the same-token role `r`, the
subtype of `t`, the ordered endpoint of the pair under discussion, the local
open/triangular status of the corresponding selected ports, the boundary-degree
profile of the bounded port supports `T(p),T(q)`, the `P₁₃`-label entries
appearing in the bounded part of the support, and the suppressed-chord flag when
the blocker has type (f)."*

Four of the seven coordinates are read off the object and the branch's own data:
`sub(t)` off the token's constructor, the two port statuses off the selected
ports' own shoulders, and the chord flag off the pair's canonical blocker.  The
remaining three -- the role and the two alphabet readings -- are the declared
maps `def:declared-coordinate-signature` and the `P₁₃` labelling supply. -/

/-- **The local open/triangular status of a selected port.**

`lem:sparse-port-activation`'s own dichotomy: the port is *triangular* when two
of its shoulders are adjacent -- the manuscript's triangle `x a_p b_p x` -- and
*open* otherwise. -/
noncomputable def portStatus (object : FiniteObject.{u}) (threshold : Nat)
    (port : object.Vertex × object.Vertex) : PortStatus := by
  classical
  exact
    if _ : ∃ member : port ∈ object.excessPorts threshold,
        ∃ left ∈ (object.surplusPortOfMem member).shoulders,
          ∃ right ∈ (object.surplusPortOfMem member).shoulders,
            left ≠ right ∧ object.graph.Adj left right then
      .triangular
    else
      .openPort

variable {Coordinate Chord : Type v}

/-- **The suppressed-chord flag**: set exactly when the pair's canonical blocker
has type (f), the arithmetic chord-set obstruction. -/
def chordSetFlag {object : FiniteObject.{u}}
    (blocker : FiniteObject.Blocker object Coordinate Chord) : Bool :=
  match blocker with
  | .arithmeticChordSet _ => true
  | _ => false

/-- **`ρ_t`, the routing label of a pair**, at the token `t` and the declared
readings of `def:declared-coordinate-signature` and the `P₁₃` labelling.

Every coordinate is the one the definition names, in the definition's own
order. -/
noncomputable def pairDemands {object : FiniteObject.{u}}
    (pair : Finset (object.Vertex × object.Vertex)) :
    Option ((object.Vertex × object.Vertex) × (object.Vertex × object.Vertex)) :=
  match pair.toList with
  | first :: second :: _ => some (first, second)
  | _ => none

/-- **`ρ_t`, the routing label of a pair**, at the token `t` and the declared
readings of `def:declared-coordinate-signature` and the `P₁₃` labelling.

Every coordinate is the one the definition names, in the definition's own order,
and every one of them is read off **the pair itself**: its two demands `p, q`
are its own two members in the object's enumeration order, so the port statuses
and the two boundary-degree profiles are `T(p)`'s and `T(q)`'s.  That is what
makes a label collision give the *same boundary-degree fibre*, which is one of
the two consequences `lem:same-token-bottleneck-routing` spends. -/
noncomputable def pairRoutingLabel {object : FiniteObject.{u}}
    {BoundaryProfile WindowLabel : Type} [Inhabited BoundaryProfile]
    (threshold : Nat)
    (activation : FiniteObject.DemandActivation object Coordinate Chord)
    (token : FiniteObject.CapacityToken object)
    (roleOf : Finset (object.Vertex × object.Vertex) → Role)
    (endpointOf : Finset (object.Vertex × object.Vertex) → Fin 2)
    (profileOf : object.Vertex × object.Vertex → BoundaryProfile)
    (windowLabelOf : Finset (object.Vertex × object.Vertex) → WindowLabel)
    (pair : Finset (object.Vertex × object.Vertex)) :
    RoutingLabel BoundaryProfile WindowLabel :=
  (roleOf pair,
    FiniteObject.CapacityToken.subtype token,
    endpointOf pair,
    (match pairDemands pair with
      | none => (PortStatus.openPort, PortStatus.openPort)
      | some (left, right) =>
          (portStatus object threshold left, portStatus object threshold right)),
    (match pairDemands pair with
      | none => (default, default)
      | some (left, right) => (profileOf left, profileOf right)),
    windowLabelOf pair,
    match FiniteObject.canonicalBlocker activation pair with
    | none => false
    | some blocker => chordSetFlag blocker)

/-- **The manuscript's pigeonhole, at `ρ_t` itself.**

*"Since there are only `Q_geom` routing labels, two distinct edges
`π₁, π₂ ∈ 𝓜` have the same routing label."*  Applied to the label the
definition declares, not to an arbitrary labelling: `Q_geom` is
`Fintype.card` of the seven-coordinate alphabet and the pattern exceeds it. -/
theorem exists_same_pairRoutingLabel {object : FiniteObject.{u}}
    {BoundaryProfile WindowLabel : Type}
    [Fintype BoundaryProfile] [DecidableEq BoundaryProfile]
    [Inhabited BoundaryProfile]
    [Fintype WindowLabel] [DecidableEq WindowLabel] (threshold : Nat)
    (activation : FiniteObject.DemandActivation object Coordinate Chord)
    (token : FiniteObject.CapacityToken object)
    (roleOf : Finset (object.Vertex × object.Vertex) → Role)
    (endpointOf : Finset (object.Vertex × object.Vertex) → Fin 2)
    (profileOf : object.Vertex × object.Vertex → BoundaryProfile)
    (windowLabelOf : Finset (object.Vertex × object.Vertex) → WindowLabel)
    (pattern : Finset (Finset (object.Vertex × object.Vertex)))
    (large : geometricPatternBound BoundaryProfile WindowLabel ≤ pattern.card) :
    ∃ first ∈ pattern, ∃ second ∈ pattern, first ≠ second ∧
      pairRoutingLabel threshold activation token roleOf endpointOf profileOf
          windowLabelOf first =
        pairRoutingLabel threshold activation token roleOf endpointOf profileOf
          windowLabelOf second := by
  classical
  exact exists_same_routingLabel_of_patternBound pattern
    (pairRoutingLabel threshold activation token roleOf endpointOf profileOf
      windowLabelOf) large

/-! ## The routed configuration `def:same-token-routing-germs` declares -/

/-- **`def:same-token-routing-germs`' own routed pair at one bottleneck.**

*"A routing germ of `π` at `t` is one of the declared connector germs in
`Z(π;t,r)` which starts at the primitive carrier of `t` and ends at one of the
two selected port supports `T(p)` or `T(q)`."*

Two such germs, and nothing else.  This is the definition's own object: the
germs run inside `Z`, they are issued from `κ(t)`, and they land in the selected
supports.  It is **not** `def:typeA-continuation-classes`' configuration --
those germs leave through a completion port and carry a switch support presented
as a proper boundaried atom with a registered profile certificate, which is
exit `(7)`'s object and not this one. -/
structure GermPair (object : FiniteObject.{u})
    [DecidableEq object.Vertex] where
  /-- `Z(π;t,r)`, the routing support the declared signature generates. -/
  routingSupport : Finset object.Vertex
  /-- `κ(t)`, the primitive carrier both germs are issued from. -/
  carrier : object.Vertex
  /-- `T(p) ∪ T(q)`, the two selected port supports. -/
  selected : Finset object.Vertex
  /-- The first routing germ. -/
  left : RoutingGerm object.Vertex routingSupport carrier selected
  /-- and the second. -/
  right : RoutingGerm object.Vertex routingSupport carrier selected
  /-- **Each germ is the manuscript's "ordered path `Γ`".**
  `def:typeA-continuation-classes`, which `def:same-token-routing-germs` takes
  its connector germs from, builds a germ out of a *return* -- so a germ is a
  walk of the object and it is simple.  `RoutingGerm` is stated over an abstract
  item type and cannot say so; here the items are the object's own vertices and
  it can. -/
  leftChain : left.path.IsChain object.graph.Adj
  /-- and the second germ is a walk. -/
  rightChain : right.path.IsChain object.graph.Adj
  /-- The first germ is simple. -/
  leftNodup : left.path.Nodup
  /-- and so is the second. -/
  rightNodup : right.path.Nodup

/-- **The germ dichotomy of `lem:same-token-bottleneck-routing`.**

*"If the germs are parallel, ...  It remains that the two germs have a first
separator `z`."*

At the definition's own germs this is `parallel_or_firstSeparator`, and its only
inputs are that both germs are issued from `κ(t)` -- which is `RoutingGerm`'s
own `issued` field.  Nothing is assumed and no boundaried atom is involved. -/
theorem GermPair.dichotomy {object : FiniteObject.{u}}
    [DecidableEq object.Vertex] (pair : GermPair object) :
    Parallel pair.left.path pair.right.path pair.selected ∨
      ∃ separator,
        firstSeparator pair.left.path pair.right.path = some separator ∧
          ¬ EnteredTogether pair.left.path pair.right.path pair.selected :=
  parallel_or_firstSeparator pair.selected pair.left.issued pair.right.issued


/-- **`def:named-surplus-exits` (d)**, as the absorbed classification's third
alternative: *"If context-universality holds only after adjoining a larger
connected support, the support is a proper or global delocalization."*

This is exactly `SparseSurplusExit.delocalization`'s own data -- a strictly
smaller representative meeting the baseline whose target transfers back -- and
it is spelled out rather than left as a free proposition, because a free
proposition can be taken to be `True` and would make the absorbed case
vacuous. -/
def Delocalizes (Baseline Target : FiniteObject.{u} → Prop)
    (object : FiniteObject.{u}) : Prop :=
  ∃ representative : FiniteObject.{u},
    representative.LexicographicallySmaller object ∧ Baseline representative ∧
      (Target representative → Target object)

/-- **The third absorbed alternative is a sparse surplus exit**, by the
constructor `def:named-surplus-exits` gives it. -/
theorem sparseSurplusExit_of_delocalizes {Baseline : FiniteObject.{u} → Prop}
    {LengthOK : Nat → Prop} {object : FiniteObject.{u}}
    (delocalizes : Delocalizes Baseline (Graph.HasCycleWithLength LengthOK)
      object) :
    Graph.SparseSurplusExit Baseline (Graph.HasCycleWithLength LengthOK)
      LengthOK object := by
  obtain ⟨representative, smaller, baseline, transfer⟩ := delocalizes
  exact .delocalization representative smaller baseline transfer

/-- **`def:same-token-routing-germs`' routed configuration at one bottleneck.**

*"A routing germ of `π` at `t` is one of the declared connector germs in
`Z(π;t,r)` which starts at the primitive carrier of `t` and ends at one of the
two selected port supports `T(p)` or `T(q)`."*

The two germs, their first separator and the switch support's declared reading
are exactly the data `lem:same-token-bottleneck-routing` takes apart, and they
are the declared connector germs of the two selected demands the pigeonhole
produced -- not a fresh construction.  Bundling them is what lets a node carry
one bottleneck and read its outcome. -/
structure RoutedBottleneck (object : FiniteObject.{u})
    (HighDegree : object.Vertex → Prop)
    (Absorbing : object.Vertex → object.Vertex → object.Vertex → Prop) where
  /-- The selected port supports the germs land in. -/
  support : Finset object.Vertex
  /-- The primitive carrier of `t`, which both germs are issued from. -/
  carrier : object.Vertex
  /-- The first step both germs take out of the carrier. -/
  outside : object.Vertex
  /-- The two germs, with their maximal common prefix and their first
  separator. -/
  separation : Separation object support carrier outside
  /-- The switch support's declared reading of the two response coordinates. -/
  reading : SwitchReading separation
  /-- The two separated connector tails. -/
  armLeft : List object.Vertex
  /-- and the second. -/
  armRight : List object.Vertex
  armLeftIssued : armLeft.head? = some separation.nextLeft
  armRightIssued : armRight.head? = some separation.nextRight
  armLeftChain : armLeft.IsChain object.graph.Adj
  armRightChain : armRight.IsChain object.graph.Adj
  armLeftNodup : armLeft.Nodup
  armRightNodup : armRight.Nodup
  armLeftLands : ∃ terminal, armLeft.getLast? = some terminal ∧ terminal ∈ support
  armRightLands : ∃ terminal, armRight.getLast? = some terminal ∧ terminal ∈ support
  armLeftInterior : ∀ vertex ∈ armLeft,
    vertex ∈ support ∨ vertex = separation.separator →
    armLeft.getLast? = some vertex
  armRightInterior : ∀ vertex ∈ armRight,
    vertex ∈ support ∨ vertex = separation.separator →
    armRight.getLast? = some vertex
  /-- `d_G(z) ≥ 4` is what makes the separator a handoff centre. -/
  highOfDegree : ∀ vertex : object.Vertex,
    3 < object.degree vertex → HighDegree vertex
  denied : ¬ Absorbing separation.separator separation.nextLeft
    separation.nextRight
  deniedSwap : ¬ Absorbing separation.separator separation.nextRight
    separation.nextLeft

/-- **`lem:same-token-bottleneck-routing`, applied.**

At a declared routed bottleneck the manuscript's two outcomes are exhaustive:
the identification at the first separator is absorbed -- its three readings are
the quotient, compression and delocalization exits of
`def:named-surplus-exits` -- or the separator survives, and then `d_G(z) ≥ 4`
and the separated tails are admissible decorated Type B handoff fan data. -/
theorem RoutedBottleneck.outcome {object : FiniteObject.{u}}
    {Baseline : FiniteObject.{u} → Prop} {LengthOK : Nat → Prop} {order : Nat}
    {HighDegree : object.Vertex → Prop}
    {Absorbing : object.Vertex → object.Vertex → object.Vertex → Prop}
    (bottleneck : RoutedBottleneck object HighDegree Absorbing)
    (avoids : ¬ Graph.HasCycleWithLength LengthOK object)
    (uncompressible : ∀ piece : Finset object.Vertex,
      ¬ Graph.Strategy.InterfaceReplacement.CompressibleSupport Baseline
        (Graph.HasCycleWithLength LengthOK) object piece)
    (windowFree : Graph.InducedPathFree (object.induce bottleneck.support) order) :
    Absorbed (Graph.HasCycleWithLength LengthOK) bottleneck.reading
        (Delocalizes Baseline (Graph.HasCycleWithLength LengthOK) object) ∨
      (3 < object.degree bottleneck.separation.separator ∧
        ∃ envelope : Envelope object LengthOK HighDegree Absorbing,
          Admissible object LengthOK
            (fun piece => ¬ Graph.Strategy.InterfaceReplacement.CompressibleSupport
              Baseline (Graph.HasCycleWithLength LengthOK) object piece)
            (fun piece => Graph.InducedPathFree (object.induce piece) order)
            envelope) :=
  bottleneckRouting (Graph.HasCycleWithLength LengthOK) bottleneck.reading
    (Delocalizes Baseline (Graph.HasCycleWithLength LengthOK) object)
    bottleneck.armLeft bottleneck.armRight bottleneck.armLeftIssued
    bottleneck.armRightIssued bottleneck.armLeftChain bottleneck.armRightChain
    bottleneck.armLeftNodup bottleneck.armRightNodup bottleneck.armLeftLands
    bottleneck.armRightLands bottleneck.armLeftInterior
    bottleneck.armRightInterior bottleneck.highOfDegree avoids
    bottleneck.denied bottleneck.deniedSwap windowFree uncompressible

end Hypostructure.Graph.SameTokenRoutingGerms
