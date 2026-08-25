import Hypostructure.Graph.TypeBEnvelopeCharge
import Hypostructure.Graph.VisibleReceiverEntry
import Hypostructure.Graph.TraceBasinAlternatives

/-!
# Decorated-envelope absorption at zero-surplus handoff pieces

The absorption half of `lem:decorated-envelope-deficit-bound`, together with
`lem:window-handoff-center-accounting`: how a negative zero-surplus handoff
piece supplies the per-piece data the committed family engine
`TypeBEnvelopeCharge.envelopeFamilyNegativePart_le_degreeSurplus` consumes.

## What is absorbed

On a zero-surplus piece the canonical routing sends every full vertex to one
receiver, and a *saturated* receiver is one whose routed load has reached the
registered multiple of its port count.  The engine's routing clause reads the
canonical `traceReceiver?` of the piece itself, so the absorbed set must be
closed under it: absorbing a receiver would force absorbing its entire routed
fibre.  The absorbed set here is therefore the manuscript's own excess:

  `absorbedExcess = ⋃_{w saturated} E(w)`,

the visible-first excess basins `E(w) = ℒ(w) ∖ A(w)` of
`def:typeA-excess-basin`, over the saturated receivers.  This is exactly the
part of the piece the exit-`(7)` handoff pays — the same loads whose trace
basins produce the surviving first separators — and it removes saturation
without touching the routing:

* the absorbed vertices are full, so no receiver is absorbed and the canonical
  route of an off-absorbed full vertex lands off the absorbed set
  (`routes_off_absorbedExcess`);
* off the absorbed set a saturated receiver retains only its payable loads
  `A(w)`, of which there are at most `s·q(w) − 1`, and an unsaturated receiver
  retains at most its own load, so every receiver satisfies the engine's
  unsaturation clause (`unsaturated_off_absorbedExcess`);
* zero ambient surplus caps every internal degree at the baseline
  (`capped_of_ambientSurplus_zero`).

`offAbsorbed_of_absorbedExcess` packages the four per-piece clauses in the
engine's exact shapes, and `card_absorbedExcess` identifies the absorbed
cardinality with `Σ_w |E(w)|`, the quantity the fan side must cover.

## The fan side

`lem:typeA-cubic-switch-absorption` and `lem:typeA-high-degree-handoff`: the
surviving first separator of two connector germs through one completion port is
the handoff centre.  The committed geometry
(`exists_separation_of_traceSurvivingSeparator`) is: the germs are rooted at
the receiver, the separator lies outside the counted core, and its two
separated next incidences — the envelope's assigned first neighbours — sit on
the receiver's own germ paths immediately after it.  The receiver is adjacent
to the separator exactly when the separator is the port's outside end; in
general the connection is through the germ, not an edge.

At such a centre the fan slots are the cubic-closed neighbours of
`def:typeB-multiclosed-residual`.  On the branch every neighbour of a high
centre sits exactly at the baseline (`lem:heavy-neighbourhood-normal-form`,
committed as `HighCentreNormalForm.NormalForm.neighbourTight`), so a fan
envelope containing the neighbours' non-centre incidences closes the whole
neighbourhood: `closedCount = d_G(h)` (`closedCount_eq_degree_of_tight`), and
the separation itself supplies two distinct closed slots
(`pair_le_closedCount_of_separation`).
`card_absorbedExcess_le_of_centreAssignment` converts a per-receiver assignment
of excess basins to distinct centres into the engine's `covered` clause.

## `lem:window-handoff-center-accounting`

A handoff centre is charged to its own ambient surplus token `d_G(h) − δ`,
whether it lies in the remainder or in a packed window: the token is positive
because the surviving separator has ambient degree at least four
(`exists_tokenCentre_of_traceSurvivingSeparator`), each centre of a
deduplicated family supplies at least one token
(`card_le_ambientSurplus_of_high`), and the family charge is inside the global
surplus through the committed `ambientSurplus_le_degreeSurplus`.  The
manuscript's alternative — the label-collision exit at the producing receiver —
is carried as a disjunct, never restated (`collision_or_tokenCentre`).

`envelopeFamily_of_absorbedExcess` assembles all of it into one call of the
committed engine: pairwise-disjoint per-piece centre families
(`def:decorated-typeB-envelope-support`'s partition, committed as
`GroupedEnvelopes.disjoint_componentCentres`) and the per-piece covered bound
are the only data the consumer still supplies.

Nothing here is specialized to a manuscript: the baseline, the discharge scale
and the mass factor are parameters and no registered numeral is written.  The
`3` in the token theorems is the committed intrinsic incidence count of
`DecoratedHandoff.four_le_degree_of_surviving` — the root incidence and the two
separated next incidences — and the conversion to the registered baseline is
the branch's own hypothesis, exactly as in the committed
`exists_envelope_of_traceSurvivingSeparator`.
-/

namespace Hypostructure.Graph.DecoratedAbsorption

open Hypostructure
open Hypostructure.Graph
open Hypostructure.Graph.TypeBFanIncidence
open scoped BigOperators

universe u v

variable {object : FiniteObject.{u}}

open scoped Classical

/-! ## The off-absorbed clauses at a zero-surplus piece -/

/-- **`capped` at `σ(X) = 0`.**  Zero ambient surplus caps every ambient — and
hence every internal — degree of the piece at the baseline. -/
theorem capped_of_ambientSurplus_zero (object : FiniteObject.{u})
    (piece : Finset object.Vertex) (threshold : Nat)
    (surplusZero : object.ambientSurplus piece threshold = 0) :
    ∀ vertex ∈ piece, object.internalDegree piece vertex ≤ threshold := by
  intro vertex member
  have zero : object.degree vertex - threshold = 0 := by
    have := (Finset.sum_eq_zero_iff.mp surplusZero) vertex member
    simpa using this
  have degreeLe : object.degree vertex ≤ threshold := by omega
  exact le_trans (object.internalDegree_le_degree piece vertex) degreeLe

/-- The canonical routing is a function: the fibres `ℒ(w)` of distinct
receivers are disjoint. -/
theorem routedLoads_disjoint (object : FiniteObject.{u})
    (support : Finset object.Vertex) (threshold : Nat)
    {left right : object.Vertex} (different : left ≠ right) :
    Disjoint (object.routedLoads support threshold left)
      (object.routedLoads support threshold right) := by
  classical
  rw [Finset.disjoint_left]
  intro load leftMember rightMember
  have leftRoute := ((FiniteObject.mem_routedLoads object).mp leftMember).2.2
  have rightRoute := ((FiniteObject.mem_routedLoads object).mp rightMember).2.2
  exact different (Option.some.inj (leftRoute.symm.trans rightRoute))

/-- The restricted load is the routed fibre with the exceptional set removed. -/
theorem restrictedLoad_eq_card_sdiff (object : FiniteObject.{u})
    (support excluded : Finset object.Vertex) (threshold : Nat)
    (receiver : object.Vertex) :
    object.restrictedLoad support excluded threshold receiver =
      (object.routedLoads support threshold receiver \ excluded).card := by
  classical
  unfold FiniteObject.restrictedLoad FiniteObject.routedLoads
  congr 1
  ext vertex
  simp only [Finset.mem_filter, Finset.mem_sdiff]
  tauto

/-- **`L(w | ∖ H) ≤ L(w)`**: restricting to any exceptional set only removes
arrivals. -/
theorem restrictedLoad_le_routedLoad (object : FiniteObject.{u})
    (support excluded : Finset object.Vertex) (threshold : Nat)
    (receiver : object.Vertex) :
    object.restrictedLoad support excluded threshold receiver ≤
      object.routedLoad support threshold receiver := by
  classical
  rw [restrictedLoad_eq_card_sdiff, FiniteObject.routedLoad_eq_card]
  exact Finset.card_le_card Finset.sdiff_subset

/-- Membership in the visible-first excess basin `E(w) = ℒ(w) ∖ A(w)`. -/
theorem mem_excessBasin {support : Finset object.Vertex} {threshold scale : Nat}
    {receiver vertex : object.Vertex} :
    vertex ∈ VisibleEntry.excessBasin object support threshold scale receiver ↔
      vertex ∈ object.routedLoads support threshold receiver ∧
        vertex ∉ VisibleEntry.payableSet object support threshold scale
          receiver := by
  letI : DecidableEq object.Vertex := vertexDecEq object
  unfold VisibleEntry.excessBasin
  exact Finset.mem_sdiff

/-- The excess basin consists of routed loads. -/
theorem excessBasin_subset_routedLoads (object : FiniteObject.{u})
    (support : Finset object.Vertex) (threshold scale : Nat)
    (receiver : object.Vertex) :
    VisibleEntry.excessBasin object support threshold scale receiver ⊆
      object.routedLoads support threshold receiver :=
  fun _vertex member => (mem_excessBasin.mp member).1

/-- Membership in the saturated-receiver family. -/
theorem mem_saturatedReceivers {support : Finset object.Vertex}
    {threshold scale : Nat} {receiver : object.Vertex} :
    receiver ∈ VisibleEntry.saturatedReceivers object support threshold scale ↔
      object.IsReceiver support threshold receiver ∧
        object.Saturated support threshold scale receiver := by
  classical
  unfold VisibleEntry.saturatedReceivers
  simp only [Finset.mem_filter, FiniteObject.mem_receivers]

/-- **The absorbed part of a handoff piece**: the visible-first excess basins of
its saturated receivers.  This is the manuscript's `⋃_w E(w)` — the loads the
exit-`(7)` decorated envelope pays — read as the exceptional set of the
engine's off-absorbed discharge. -/
noncomputable def absorbedExcess (object : FiniteObject.{u})
    (support : Finset object.Vertex) (threshold scale : Nat) :
    Finset object.Vertex := by
  classical
  exact (VisibleEntry.saturatedReceivers object support threshold
      scale).biUnion
    fun receiver =>
      VisibleEntry.excessBasin object support threshold scale receiver

theorem mem_absorbedExcess {support : Finset object.Vertex}
    {threshold scale : Nat} {vertex : object.Vertex} :
    vertex ∈ absorbedExcess object support threshold scale ↔
      ∃ receiver ∈
          VisibleEntry.saturatedReceivers object support threshold scale,
        vertex ∈ VisibleEntry.excessBasin object support threshold scale
          receiver := by
  classical
  unfold absorbedExcess
  exact Finset.mem_biUnion

/-- An absorbed vertex is a full vertex of the piece: it lies in the piece and
spends the whole baseline internally. -/
theorem full_of_mem_absorbedExcess {support : Finset object.Vertex}
    {threshold scale : Nat} {vertex : object.Vertex}
    (member : vertex ∈ absorbedExcess object support threshold scale) :
    vertex ∈ support ∧ object.internalDegree support vertex = threshold := by
  obtain ⟨receiver, _saturated, excess⟩ := mem_absorbedExcess.mp member
  have routed := (mem_excessBasin.mp excess).1
  have data := (FiniteObject.mem_routedLoads object).mp routed
  exact ⟨data.1, data.2.1⟩

/-- **`absorbedSubset`.**  The absorbed excess lies inside the piece. -/
theorem absorbedExcess_subset (object : FiniteObject.{u})
    (support : Finset object.Vertex) (threshold scale : Nat) :
    absorbedExcess object support threshold scale ⊆ support :=
  fun _vertex member => (full_of_mem_absorbedExcess member).1

/-- **`routes` off the absorbed excess.**  The absorbed vertices are full, so no
receiver is absorbed: the committed total routing of the piece
(`lem:typeA-receiver-loads`, node `[88]`'s shape) already lands off the
absorbed set. -/
theorem routes_off_absorbedExcess (object : FiniteObject.{u})
    (piece : Finset object.Vertex) (threshold scale : Nat)
    (routed : ∀ vertex ∈ piece,
      object.internalDegree piece vertex = threshold →
      ∃ receiver : object.Vertex,
        object.traceReceiver? piece threshold vertex = some receiver ∧
          object.IsReceiver piece threshold receiver) :
    ∀ vertex ∈ piece \ absorbedExcess object piece threshold scale,
      object.internalDegree piece vertex = threshold →
      ∃ receiver : object.Vertex,
        object.traceReceiver? piece threshold vertex = some receiver ∧
          object.IsReceiver piece threshold receiver ∧
            receiver ∉ absorbedExcess object piece threshold scale := by
  intro vertex member full
  obtain ⟨receiver, route, isReceiver⟩ :=
    routed vertex (Finset.mem_sdiff.mp member).1 full
  refine ⟨receiver, route, isReceiver, fun absorbed => ?_⟩
  have fullDegree := (full_of_mem_absorbedExcess absorbed).2
  have below := isReceiver.2
  omega

/-- **`unsaturated` off the absorbed excess.**  A saturated receiver retains
only its payable loads — at most `s·q(w) − 1` of them, by
`def:typeA-excess-basin`'s payable-set cap — and an unsaturated receiver
retains at most its own unsaturated load.  This is the saturation-removal step
of the absorption: *"the remaining receiver load becomes unsaturated"*. -/
theorem unsaturated_off_absorbedExcess (object : FiniteObject.{u})
    (piece : Finset object.Vertex) (threshold scale : Nat)
    (scalePos : 1 ≤ scale) :
    ∀ receiver ∈ object.receivers piece threshold \
        absorbedExcess object piece threshold scale,
      1 + object.restrictedLoad piece
          (absorbedExcess object piece threshold scale) threshold receiver ≤
        scale * object.missingPorts piece threshold receiver := by
  intro receiver member
  have isReceiver :=
    FiniteObject.mem_receivers.mp (Finset.mem_sdiff.mp member).1
  have portPos : 1 ≤ object.missingPorts piece threshold receiver := by
    have below := isReceiver.2
    unfold FiniteObject.missingPorts
    omega
  have scaledPos : 1 ≤ scale * object.missingPorts piece threshold receiver := by
    have := Nat.mul_le_mul scalePos portPos
    simpa using this
  have restrictedEq := restrictedLoad_eq_card_sdiff object piece
    (absorbedExcess object piece threshold scale) threshold receiver
  by_cases saturated : object.Saturated piece threshold scale receiver
  · -- the whole excess basin is absorbed: only payable loads remain
    have contained : object.routedLoads piece threshold receiver \
        absorbedExcess object piece threshold scale ⊆
        VisibleEntry.payableSet object piece threshold scale receiver := by
      intro load loadMember
      obtain ⟨routedMember, fresh⟩ := Finset.mem_sdiff.mp loadMember
      by_contra notPayable
      exact fresh (mem_absorbedExcess.mpr ⟨receiver,
        mem_saturatedReceivers.mpr ⟨isReceiver, saturated⟩,
        mem_excessBasin.mpr ⟨routedMember, notPayable⟩⟩)
    have counted := Finset.card_le_card contained
    have payable := VisibleEntry.card_payableSet_le object piece threshold scale
      receiver
    omega
  · have bound :=
      (object.not_saturated_iff piece threshold scale receiver).mp saturated
    have monotone := restrictedLoad_le_routedLoad object piece
      (absorbedExcess object piece threshold scale) threshold receiver
    omega

/-- **The per-piece package.**  At a zero-surplus piece with the committed
total routing, the absorbed excess discharges all four per-piece hypotheses of
`TypeBEnvelopeCharge.envelopeFamilyNegativePart_le_degreeSurplus`, each in the
engine's exact shape. -/
theorem offAbsorbed_of_absorbedExcess (object : FiniteObject.{u})
    (piece : Finset object.Vertex) (threshold scale : Nat)
    (scalePos : 1 ≤ scale)
    (surplusZero : object.ambientSurplus piece threshold = 0)
    (routed : ∀ vertex ∈ piece,
      object.internalDegree piece vertex = threshold →
      ∃ receiver : object.Vertex,
        object.traceReceiver? piece threshold vertex = some receiver ∧
          object.IsReceiver piece threshold receiver) :
    absorbedExcess object piece threshold scale ⊆ piece ∧
      (∀ vertex ∈ piece \ absorbedExcess object piece threshold scale,
        object.internalDegree piece vertex ≤ threshold) ∧
      (∀ vertex ∈ piece \ absorbedExcess object piece threshold scale,
        object.internalDegree piece vertex = threshold →
        ∃ receiver : object.Vertex,
          object.traceReceiver? piece threshold vertex = some receiver ∧
            object.IsReceiver piece threshold receiver ∧
              receiver ∉ absorbedExcess object piece threshold scale) ∧
      ∀ receiver ∈ object.receivers piece threshold \
          absorbedExcess object piece threshold scale,
        1 + object.restrictedLoad piece
            (absorbedExcess object piece threshold scale) threshold receiver ≤
          scale * object.missingPorts piece threshold receiver :=
  ⟨absorbedExcess_subset object piece threshold scale,
    fun vertex member => capped_of_ambientSurplus_zero object piece threshold
      surplusZero vertex (Finset.mem_sdiff.mp member).1,
    routes_off_absorbedExcess object piece threshold scale routed,
    unsaturated_off_absorbedExcess object piece threshold scale scalePos⟩

/-- **`|absorbed| = Σ_w |E(w)|`.**  The absorbed cardinality of a piece is the
sum of the excess basins of its saturated receivers — the exact quantity the
fan side of `lem:decorated-envelope-deficit-bound` covers. -/
theorem card_absorbedExcess (object : FiniteObject.{u})
    (piece : Finset object.Vertex) (threshold scale : Nat) :
    (absorbedExcess object piece threshold scale).card =
      ∑ receiver ∈
          VisibleEntry.saturatedReceivers object piece threshold scale,
        (VisibleEntry.excessBasin object piece threshold scale receiver).card
    := by
  classical
  unfold absorbedExcess
  refine Finset.card_biUnion ?_
  intro left _leftMember right _rightMember different
  exact Disjoint.mono
    (excessBasin_subset_routedLoads object piece threshold scale left)
    (excessBasin_subset_routedLoads object piece threshold scale right)
    (routedLoads_disjoint object piece threshold different)

/-! ## The fan slots at a handoff centre -/

/-- A neighbour of the centre sitting exactly at the baseline, with its
non-centre incidences inside the fan envelope, is a cubic-closed fan slot. -/
theorem mem_closedNeighbours_of_tight {threshold : Nat}
    {envelope : Finset object.Vertex} {centre first : object.Vertex}
    (adjacent : object.graph.Adj centre first)
    (tight : object.degree first = threshold)
    (closed : ∀ other : object.Vertex, object.graph.Adj first other →
      other ≠ centre → other ∈ envelope) :
    first ∈ closedNeighbours object threshold envelope centre :=
  mem_closedNeighbours_iff.mpr ⟨adjacent, tight, closed⟩

/-- **`c(𝔉_h) = d_G(h)` at a tight closed neighbourhood.**  On the branch every
neighbour of a high centre sits exactly at the baseline
(`lem:heavy-neighbourhood-normal-form`'s committed `neighbourTight`), so a fan
envelope containing the neighbours' non-centre incidences closes the whole
neighbourhood.  This is the manuscript's worst case `c ≤ k` of
`lem:decorated-envelope-deficit-bound` realized exactly. -/
theorem closedCount_eq_degree_of_tight (object : FiniteObject.{u})
    (threshold : Nat) (envelope : Finset object.Vertex)
    (centre : object.Vertex)
    (tight : ∀ first : object.Vertex, object.graph.Adj centre first →
      object.degree first = threshold)
    (closed : ∀ first : object.Vertex, object.graph.Adj centre first →
      ∀ other : object.Vertex, object.graph.Adj first other →
        other ≠ centre → other ∈ envelope) :
    closedCount object threshold envelope centre = object.degree centre := by
  classical
  have closedAll : ∀ first ∈ (object.orderedNeighbors centre).toFinset,
      IsCubicClosed object threshold envelope centre first := by
    intro first member
    have adjacent := (object.mem_orderedNeighbors_iff centre first).mp
      (List.mem_toFinset.mp member)
    exact ⟨adjacent, tight first adjacent, closed first adjacent⟩
  unfold TypeBFanIncidence.closedCount TypeBFanIncidence.closedNeighbours
  rw [Finset.filter_true_of_mem closedAll,
    List.toFinset_card_of_nodup (object.orderedNeighbors_nodup centre)]
  exact object.orderedNeighbors_length centre

/-- **The separation supplies two fan slots.**  The two separated next
incidences of a committed `Separation` are distinct neighbours of the
separator; at a tight closed neighbourhood they are cubic-closed, so the
centre carries at least two slots.  The `2` is the pair itself — the two
continuation classes that separate — not a registered constant. -/
theorem pair_le_closedCount_of_separation {support : Finset object.Vertex}
    {receiver outside : object.Vertex}
    (separation : DecoratedHandoff.Separation object support receiver outside)
    {threshold : Nat} {envelope : Finset object.Vertex}
    (tight : ∀ first : object.Vertex,
      object.graph.Adj separation.separator first →
      object.degree first = threshold)
    (closed : ∀ first : object.Vertex,
      object.graph.Adj separation.separator first →
      ∀ other : object.Vertex, object.graph.Adj first other →
        other ≠ separation.separator → other ∈ envelope) :
    2 ≤ closedCount object threshold envelope separation.separator := by
  classical
  have leftMember : separation.nextLeft ∈
      closedNeighbours object threshold envelope separation.separator :=
    mem_closedNeighbours_of_tight separation.nextLeft_adj
      (tight _ separation.nextLeft_adj) (closed _ separation.nextLeft_adj)
  have rightMember : separation.nextRight ∈
      closedNeighbours object threshold envelope separation.separator :=
    mem_closedNeighbours_of_tight separation.nextRight_adj
      (tight _ separation.nextRight_adj) (closed _ separation.nextRight_adj)
  have paired : ({separation.nextLeft, separation.nextRight} :
      Finset object.Vertex) ⊆
      closedNeighbours object threshold envelope separation.separator := by
    intro vertex member
    rcases Finset.mem_insert.mp member with rfl | inner
    · exact leftMember
    · rw [Finset.mem_singleton.mp inner]
      exact rightMember
  have counted := Finset.card_le_card paired
  rw [Finset.card_insert_of_notMem (by simp [separation.distinct]),
    Finset.card_singleton] at counted
  exact counted

/-! ## The committed handoff geometry -/

/-- **The geometry of alternative (d), read off the committed fields.**  A
surviving first separator of `Route8.TraceBasin.TraceSurvivingSeparator` yields
a committed `Separation` whose germs are rooted at the receiver: the separator
has ambient degree at least four (`lem:typeA-cubic-switch-absorption`, the
committed `four_le_degree_of_surviving`), and its two separated next
incidences — the envelope's assigned first neighbours — lie on the receiver's
own germ paths.  The receiver is adjacent to the separator exactly when the
separator is the port's outside end; the general connection is the germ. -/
theorem exists_separation_of_traceSurvivingSeparator
    {support : Finset object.Vertex} {threshold : Nat} {LengthOK : Nat → Prop}
    {receiver load : object.Vertex} {basin : Finset object.Vertex}
    (separated : Route8.TraceBasin.TraceSurvivingSeparator object support
      threshold LengthOK receiver load basin) :
    ∃ outside : object.Vertex,
      ∃ separation : DecoratedHandoff.Separation object support receiver
          outside,
        3 < object.degree separation.separator ∧
          separation.left.path.head? = some receiver ∧
          separation.nextLeft ∈ separation.left.path ∧
          separation.nextRight ∈ separation.right.path := by
  obtain ⟨family, _loadMember, leftLoad, rightLoad, leftMember, rightMember,
    _distinct, separation, _leftPath, _rightPath, reading, surviving⟩ :=
    separated
  refine ⟨family.outside, separation,
    DecoratedHandoff.four_le_degree_of_surviving surviving,
    separation.left.rooted, ?_, ?_⟩
  · rw [separation.leftEq]
    simp
  · rw [separation.rightEq]
    simp

/-- **`lem:window-handoff-center-accounting`, the token half.**  The surviving
separator is a centre above the baseline, so it supplies its own positive
ambient surplus token — whether it lies in the remainder or in a packed
window.  The conversion from the committed intrinsic bound `3 < d_G(z)` to the
registered baseline is the branch's own hypothesis, exactly as in the
committed `exists_envelope_of_traceSurvivingSeparator`. -/
theorem exists_tokenCentre_of_traceSurvivingSeparator
    {support : Finset object.Vertex} {threshold : Nat} {LengthOK : Nat → Prop}
    {receiver load : object.Vertex} {basin : Finset object.Vertex}
    (separated : Route8.TraceBasin.TraceSurvivingSeparator object support
      threshold LengthOK receiver load basin)
    (high : ∀ vertex : object.Vertex, 3 < object.degree vertex →
      threshold < object.degree vertex) :
    ∃ centre : object.Vertex, threshold < object.degree centre ∧
      1 ≤ object.degree centre - threshold := by
  obtain ⟨_outside, separation, degreeBound, _rooted, _left, _right⟩ :=
    exists_separation_of_traceSurvivingSeparator separated
  have highCentre := high separation.separator degreeBound
  exact ⟨separation.separator, highCentre, by omega⟩

/-- **`lem:window-handoff-center-accounting`, the dichotomy.**  Either the
label-collision exit occurs at the producing receiver — carried as the
branch's own disjunct, never restated — or the handoff centre supplies its
positive surplus token. -/
theorem collision_or_tokenCentre {support : Finset object.Vertex}
    {threshold : Nat} {LengthOK : Nat → Prop} {receiver load : object.Vertex}
    {basin : Finset object.Vertex} (Collision : Prop)
    (accounted : Collision ∨
      Route8.TraceBasin.TraceSurvivingSeparator object support threshold
        LengthOK receiver load basin)
    (high : ∀ vertex : object.Vertex, 3 < object.degree vertex →
      threshold < object.degree vertex) :
    Collision ∨
      ∃ centre : object.Vertex, threshold < object.degree centre ∧
        1 ≤ object.degree centre - threshold :=
  accounted.imp id fun separated =>
    exists_tokenCentre_of_traceSurvivingSeparator separated high

/-- **Each centre of a high family supplies at least one token**:
`|H| ≤ σ(H)`.  With the committed `ambientSurplus_le_degreeSurplus` this puts
the whole grouped charge inside the global surplus, independent of window
membership — the accounting consequence
`lem:window-handoff-center-accounting` feeds into
`def:typeB-residual-mass`. -/
theorem card_le_ambientSurplus_of_high (object : FiniteObject.{u})
    (centres : Finset object.Vertex) (threshold : Nat)
    (high : ∀ centre ∈ centres, threshold < object.degree centre) :
    centres.card ≤ object.ambientSurplus centres threshold := by
  unfold FiniteObject.ambientSurplus
  calc centres.card = ∑ _centre ∈ centres, 1 :=
        Finset.card_eq_sum_ones centres
    _ ≤ ∑ centre ∈ centres, (object.degree centre - threshold) := by
        refine Finset.sum_le_sum fun centre member => ?_
        have := high centre member
        omega

/-! ## The covered clause -/

/-- **The absorbed excess is covered by assigned fan slots.**  Assign each
saturated receiver's excess basin to one centre — distinct receivers to
distinct centres, as `def:decorated-typeB-envelope-support`'s incidence
components guarantee for the committed grouped family — with the basin inside
the centre's cubic-closed count.  The absorbed cardinality of the piece is
then covered by the family's closed counts: the engine's `covered` clause at
one piece. -/
theorem card_absorbedExcess_le_of_centreAssignment (object : FiniteObject.{u})
    (piece : Finset object.Vertex) (threshold scale : Nat)
    (centres : Finset object.Vertex)
    (fanEnvelope : object.Vertex → Finset object.Vertex)
    (centreOf : object.Vertex → object.Vertex)
    (maps : ∀ receiver ∈
        VisibleEntry.saturatedReceivers object piece threshold scale,
      centreOf receiver ∈ centres)
    (injective : ∀ left ∈
        VisibleEntry.saturatedReceivers object piece threshold scale,
      ∀ right ∈ VisibleEntry.saturatedReceivers object piece threshold scale,
        centreOf left = centreOf right → left = right)
    (slots : ∀ receiver ∈
        VisibleEntry.saturatedReceivers object piece threshold scale,
      (VisibleEntry.excessBasin object piece threshold scale receiver).card ≤
        closedCount object threshold (fanEnvelope (centreOf receiver))
          (centreOf receiver)) :
    (absorbedExcess object piece threshold scale).card ≤
      ∑ centre ∈ centres,
        closedCount object threshold (fanEnvelope centre) centre := by
  classical
  rw [card_absorbedExcess]
  calc ∑ receiver ∈
          VisibleEntry.saturatedReceivers object piece threshold scale,
        (VisibleEntry.excessBasin object piece threshold scale receiver).card
      ≤ ∑ receiver ∈
            VisibleEntry.saturatedReceivers object piece threshold scale,
          closedCount object threshold (fanEnvelope (centreOf receiver))
            (centreOf receiver) := Finset.sum_le_sum slots
    _ = ∑ centre ∈ (VisibleEntry.saturatedReceivers object piece threshold
            scale).image centreOf,
          closedCount object threshold (fanEnvelope centre) centre := by
        have injOn : Set.InjOn centreOf
            ↑(VisibleEntry.saturatedReceivers object piece threshold scale) :=
          fun left leftMember right rightMember =>
            injective left (Finset.mem_coe.mp leftMember) right
              (Finset.mem_coe.mp rightMember)
        exact (Finset.sum_image
          (f := fun centre =>
            closedCount object threshold (fanEnvelope centre) centre)
          injOn).symm
    _ ≤ ∑ centre ∈ centres,
          closedCount object threshold (fanEnvelope centre) centre := by
        refine Finset.sum_le_sum_of_subset ?_
        intro centre member
        obtain ⟨receiver, receiverMember, imageEq⟩ := Finset.mem_image.mp member
        exact imageEq ▸ maps receiver receiverMember

/-! ## The family assembly -/

/-- **The absorption half of `lem:decorated-envelope-deficit-bound`, family
form.**  At a family of pairwise-disjoint zero-surplus handoff pieces, the
absorbed excess supplies every per-piece hypothesis of the committed engine
`TypeBEnvelopeCharge.envelopeFamilyNegativePart_le_degreeSurplus`; the
per-piece centre families are pairwise disjoint — the incidence-component
partition of `def:decorated-typeB-envelope-support`, committed as
`GroupedEnvelopes.disjoint_componentCentres` — and the per-piece covered
bounds sum into the global one.  The conclusion is the summed handoff-piece
negative part inside `F·s·σ(G)`, the estimate the node-`[123]` unified deficit
consumes for the handoff pieces. -/
theorem envelopeFamily_of_absorbedExcess
    {threshold dischargeScale massFactor : Nat}
    {Core : Type v} (object : FiniteObject.{u}) (cores : Finset Core)
    (corePiece : Core → Finset object.Vertex)
    (centresAt : Core → Finset object.Vertex)
    (fanEnvelope : object.Vertex → Finset object.Vertex)
    (slack : threshold + 2 + dischargeScale ≤ massFactor * dischargeScale)
    (scalePos : 1 ≤ dischargeScale)
    (baseline : ∀ vertex : object.Vertex, threshold ≤ object.degree vertex)
    (surplusZero : ∀ core ∈ cores,
      object.ambientSurplus (corePiece core) threshold = 0)
    (routed : ∀ core ∈ cores, ∀ vertex ∈ corePiece core,
      object.internalDegree (corePiece core) vertex = threshold →
      ∃ receiver : object.Vertex,
        object.traceReceiver? (corePiece core) threshold vertex =
            some receiver ∧
          object.IsReceiver (corePiece core) threshold receiver)
    (high : ∀ core ∈ cores, ∀ centre ∈ centresAt core,
      threshold < object.degree centre)
    (centresDisjoint : ∀ ⦃left : Core⦄, left ∈ cores →
      ∀ ⦃right : Core⦄, right ∈ cores → left ≠ right →
        Disjoint (centresAt left) (centresAt right))
    (assigned : ∀ core ∈ cores,
      (absorbedExcess object (corePiece core) threshold dischargeScale).card ≤
        ∑ centre ∈ centresAt core,
          closedCount object threshold (fanEnvelope centre) centre) :
    ∑ core ∈ cores,
        ((corePiece core).card -
          dischargeScale *
            object.positiveDeficiency (corePiece core) threshold) ≤
      massFactor * dischargeScale * object.degreeSurplus threshold := by
  classical
  have disjointFamilies : (↑cores : Set Core).PairwiseDisjoint centresAt :=
    fun left leftMember right rightMember different =>
      centresDisjoint (Finset.mem_coe.mp leftMember)
        (Finset.mem_coe.mp rightMember) different
  refine TypeBEnvelopeCharge.envelopeFamilyNegativePart_le_degreeSurplus
    (massFactor := massFactor) object cores corePiece
    (fun core =>
      absorbedExcess object (corePiece core) threshold dischargeScale)
    (cores.biUnion centresAt) fanEnvelope slack baseline ?_ ?_ ?_ ?_ ?_ ?_
  · intro centre member
    obtain ⟨core, coreMember, centreMember⟩ := Finset.mem_biUnion.mp member
    exact high core coreMember centre centreMember
  · intro core _member
    exact absorbedExcess_subset object (corePiece core) threshold dischargeScale
  · intro core coreMember vertex member
    exact capped_of_ambientSurplus_zero object (corePiece core) threshold
      (surplusZero core coreMember) vertex (Finset.mem_sdiff.mp member).1
  · intro core coreMember
    exact routes_off_absorbedExcess object (corePiece core) threshold
      dischargeScale (routed core coreMember)
  · intro core _coreMember
    exact unsaturated_off_absorbedExcess object (corePiece core) threshold
      dischargeScale scalePos
  · calc ∑ core ∈ cores,
          (absorbedExcess object (corePiece core) threshold
            dischargeScale).card
        ≤ ∑ core ∈ cores, ∑ centre ∈ centresAt core,
            closedCount object threshold (fanEnvelope centre) centre :=
          Finset.sum_le_sum assigned
      _ = ∑ centre ∈ cores.biUnion centresAt,
            closedCount object threshold (fanEnvelope centre) centre :=
          (Finset.sum_biUnion disjointFamilies).symm

end Hypostructure.Graph.DecoratedAbsorption
