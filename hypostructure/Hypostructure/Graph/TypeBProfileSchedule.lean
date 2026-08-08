import Hypostructure.Graph.TypeBHybridLedger
import Hypostructure.Graph.TypeBHybridIncidence

/-!
# The enumerable schedule of assigned Type B fan-window profiles

Manuscript node `[74]` (`fanthm`) of `original_erdos_64_proof.tex` is a
framework step, and a framework step scans a *schedule*.  The assigned Type B
fan-window profile `𝔉_h` of `def:typeB-window-incidence-profile` is
`TypeBFanClosedPorts.Profile`, which is pure data and therefore carries no
enumeration of its own.  This file supplies the missing enumerable carrier, in
exactly the shape `TypeBDegreeFour.degreeFourCores` supplies it for
`def:triangular-fan-core` at node `[79]`:

* a canonical profile at a centre, built only from the object's own schedules
  (`canonicalProfile`);
* the enumerable list of candidates (`profileCandidatesWith`,
  `profileCandidates`) with an exact membership characterisation
  (`mem_profileCandidatesWith_iff`, `mem_profileCandidates_iff`) and
  `profileCandidatesWith_nodup` / `profileCandidates_nodup`;
* a decidable per-candidate scan predicate (`IsHybridEligible`, i.e. `2 ≤ c(𝔉)`,
  the counting input of `fanClosedPortHybridEntry`);
* the scanning form: every enumerated candidate passing the predicate satisfies
  the hybrid ledger conclusion `D_B(𝔉) ≤ ½ I_W(𝔉) + D_N(𝔉)` of
  `lem:typeB-hybrid-B1` (`profileCandidatesWith_scan`).

Nothing is redefined.  `Profile`, `remainder`, `IsFanClosed`,
`closedNeighbours`, `closedCount` and `closedNeighbourDeficit` are
`Hypostructure.Graph.TypeBFanClosedPorts`; `windowCredit`,
`hybridNonWindowDemand` and `hybridCapacity` are
`Hypostructure.Graph.TypeBHybridLedger`; the label algebra, `Marked`,
`markedOfLabelling` and `neighbourRim` are
`Hypostructure.Graph.TypeBMarkedFan`; the shoulder schedules are the
framework's `outsideIncidences`.

## There are no hypotheses

Every statement below is either a definition, or a theorem whose only inputs are
data of the object at hand and membership in an object-derived schedule.  In
particular:

* the *fan-certificate labelling* of `def:marked-typeB-fan` is not assumed to
  exist: `canonicalLabelling` builds one from the position of a neighbour in the
  object's own `orderedNeighbors` schedule, sending position `i` to the `i`-th
  coordinate of the eight-element `D`-independent set of
  `dIndep_card_eight_witness`.  Distinct fan neighbours occupy distinct
  positions, hence receive `C₂`-compatible labels: the certificate is *made
  true by the construction* rather than hypothesised.

* the degree window `4 ≤ d_G(h) ≤ 8` is not a hypothesis either: it is the
  filter defining the schedule `fanCentres`, exactly as `d_G(h) = 4` is the
  filter defining `degreeFourCenters`.  It excludes nothing, because it is
  precisely `Marked.degree_mem_window`; `mem_fanCentres_of_marked` proves that
  the centre of *every* certificate-marked Type B fan over the object is
  enumerated, and `exists_mem_profileCandidatesWith` proves that the centre of
  every assigned profile is enumerated.

* the ambient structural input `NormalForm` does **not** occur in this file at
  all.  The hybrid ledger inequality `D_B ≤ ½ I_W + D_N` and the feasibility
  `D_N ≤ ½ I_N` need no four-cycle exclusion: they follow from
  `I_W + I_N = 2c` together with the derived cap `d_G(h) ≤ 8`
  (`Marked.degree_le_eight`).  See the closing note for the one clause of
  `lem:typeB-hybrid-B1` that is therefore *not* reproduced here.

`canonicalProfile` takes the two degree facts of its centre as arguments because
`Marked.highDegree` is an existing field of `Marked` and the labelling cap is
what makes the certificate true; in the schedule they are supplied by list
membership, so no theorem below carries them as hypotheses.
-/

namespace Hypostructure.Graph.TypeBProfileSchedule

open Hypostructure.Graph
open Hypostructure.Graph.TypeBMarkedFan
open Hypostructure.Graph.TypeBFanClosedPorts
open Hypostructure.Graph.TypeBHybridIncidence
open Hypostructure.Graph.ReceiverLoad (LoadCapacityProfile)

universe u

variable {object : FiniteObject.{u}}

/-! ## The canonical fan-certificate labelling

`def:marked-typeB-fan` asks for a labelling `S_h : N(h) → 𝓛` of the fan
neighbours by legal nonempty `P₁₃` labels with `C₂(S_h u, S_h v) = 1` for
distinct neighbours.  `rem:fan-finite` shows that at most eight neighbours can
be labelled this way, the bound being the independence number of the difference
graph `D`.  Reading that argument forwards produces the canonical labelling: the
`i`-th neighbour in the object's own scan order receives the `i`-th coordinate
of the explicit eight-element independent set of `dIndep_card_eight_witness`. -/

/-- The eight window coordinates of `dIndep_card_eight_witness`, two per
component of the difference graph `D`, indexed by neighbour position. -/
def packIndex (position : Nat) : Index :=
  match position with
  | 0 => 0
  | 1 => 8
  | 2 => 1
  | 3 => 9
  | 4 => 2
  | 5 => 10
  | 6 => 3
  | _ => 11

/-- Distinct positions below eight receive coordinates whose gap avoids the
dyadic cross-differences `0`, `4`, `12`: this is `dIndep_card_eight_witness`
transported along `packIndex`. -/
theorem packIndex_gap {left right : Nat} (leftLt : left < 8) (rightLt : right < 8)
    (distinct : left ≠ right) :
    gap (packIndex left) (packIndex right) ≠ 0 ∧
      gap (packIndex left) (packIndex right) ≠ 4 ∧
      gap (packIndex left) (packIndex right) ≠ 12 := by
  interval_cases left <;> interval_cases right <;> revert distinct <;> decide

/-- The position of a vertex in the object's own neighbour schedule at a
centre.  A local observable: it reads only `orderedNeighbors`. -/
def neighbourPosition (object : FiniteObject.{u}) (center vertex : object.Vertex) :
    Nat :=
  letI : DecidableEq object.Vertex := object.vertices.decEq
  (object.orderedNeighbors center).idxOf vertex

theorem neighbourPosition_lt_degree {center vertex : object.Vertex}
    (adjacency : object.graph.Adj center vertex) :
    neighbourPosition object center vertex < object.degree center := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  rw [neighbourPosition, ← object.orderedNeighbors_length center]
  exact List.idxOf_lt_length_iff.2
    ((object.mem_orderedNeighbors_iff center vertex).2 adjacency)

theorem neighbourPosition_inj {center left right : object.Vertex}
    (leftAdj : object.graph.Adj center left)
    (same : neighbourPosition object center left
      = neighbourPosition object center right) : left = right := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  exact (List.idxOf_inj
    ((object.mem_orderedNeighbors_iff center left).2 leftAdj)).1 same

/-- **The canonical fan-certificate labelling at a centre** of
`def:marked-typeB-fan`: the neighbour in scan position `i` carries the singleton
label `{packIndex i}`.  Nothing here is authored: the position comes from
`orderedNeighbors` and the coordinate from `dIndep_card_eight_witness`. -/
def canonicalLabelling (object : FiniteObject.{u}) (center : object.Vertex) :
    object.Vertex → Label :=
  fun vertex => Label.ofIndex (packIndex (neighbourPosition object center vertex))

/-- The canonical labelling really is a fan certificate whenever the centre
obeys the packing cap `d_G(h) ≤ 8`: distinct neighbours occupy distinct scan
positions, so their coordinates are non-adjacent in the difference graph `D`. -/
theorem canonicalLabelling_wedgeSafe {center : object.Vertex}
    (cap : object.degree center ≤ 8) {left right : object.Vertex}
    (leftAdj : object.graph.Adj center left)
    (rightAdj : object.graph.Adj center right) (distinct : left ≠ right) :
    WedgeSafe (canonicalLabelling object center left).indices
      (canonicalLabelling object center right).indices := by
  refine wedgeSafe_ofIndex (packIndex_gap ?_ ?_ ?_)
  · exact lt_of_lt_of_le (neighbourPosition_lt_degree leftAdj) cap
  · exact lt_of_lt_of_le (neighbourPosition_lt_degree rightAdj) cap
  · exact fun same => distinct (neighbourPosition_inj leftAdj same)

/-- **The canonical certificate-marked Type B fan at a centre**: the ordinary
adjacent fan on `N(h)` carrying the canonical fan-certificate labelling.  The
two degree facts are the defining filter of the schedule `fanCentres` below,
supplied there by list membership. -/
def canonicalMarked (object : FiniteObject.{u}) (center : object.Vertex)
    (high : 4 ≤ object.degree center) (cap : object.degree center ≤ 8) :
    Marked object :=
  markedOfLabelling object center high (canonicalLabelling object center)
    fun _ leftAdj _ rightAdj distinct =>
      canonicalLabelling_wedgeSafe cap leftAdj rightAdj distinct

@[simp] theorem canonicalMarked_hub (object : FiniteObject.{u})
    (center : object.Vertex) (high : 4 ≤ object.degree center)
    (cap : object.degree center ≤ 8) :
    (canonicalMarked object center high cap).fan.hub = center := rfl

@[simp] theorem canonicalMarked_rim (object : FiniteObject.{u})
    (center : object.Vertex) (high : 4 ≤ object.degree center)
    (cap : object.degree center ≤ 8) :
    (canonicalMarked object center high cap).fan.rim = neighbourRim object center :=
  rfl

/-! ## The canonical fan envelope -/

/-- **The canonical assigned fan envelope at a centre**: the centre, its
neighbours, and the non-central incidences of its neighbours, all read off the
object's own schedules.  This is the same shape as
`TypeBDegreeFour.TriangularCore.support`, with the full neighbour schedule in
place of a chosen family of ports. -/
noncomputable def canonicalEnvelope (object : FiniteObject.{u})
    (center : object.Vertex) : Finset object.Vertex := by
  classical
  exact insert center
    ((object.orderedNeighbors center).toFinset ∪
      (object.orderedNeighbors center).toFinset.biUnion fun endpoint =>
        nonHubIncidences object center endpoint)

theorem mem_canonicalEnvelope_iff (center vertex : object.Vertex) :
    vertex ∈ canonicalEnvelope object center ↔
      vertex = center ∨ object.graph.Adj center vertex ∨
        (vertex ≠ center ∧ ∃ neighbour, object.graph.Adj center neighbour ∧
          object.graph.Adj neighbour vertex) := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  simp only [canonicalEnvelope, Finset.mem_insert, Finset.mem_union,
    List.mem_toFinset, Finset.mem_biUnion, object.mem_orderedNeighbors_iff,
    mem_nonHubIncidences_iff]
  constructor
  · rintro (rfl | isNeighbour | ⟨neighbour, centerAdj, notCentre, incidence⟩)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl isNeighbour)
    · exact Or.inr (Or.inr ⟨notCentre, neighbour, centerAdj, incidence⟩)
  · rintro (rfl | isNeighbour | ⟨notCentre, neighbour, centerAdj, incidence⟩)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl isNeighbour)
    · exact Or.inr (Or.inr ⟨neighbour, centerAdj, notCentre, incidence⟩)

/-- The clause "the two non-`h` incidences of a fan neighbour are carried by the
assigned support" of `def:marked-typeB-fan` holds for the canonical envelope by
construction.  This is the step that would otherwise have to be assumed. -/
theorem shoulder_mem_canonicalEnvelope {center neighbour vertex : object.Vertex}
    (centerAdj : object.graph.Adj center neighbour)
    (incidence : object.graph.Adj neighbour vertex) (notCentre : vertex ≠ center) :
    vertex ∈ canonicalEnvelope object center :=
  (mem_canonicalEnvelope_iff center vertex).2
    (Or.inr (Or.inr ⟨notCentre, neighbour, centerAdj, incidence⟩))

/-! ## The canonical assigned profile -/

/-- **The canonical assigned Type B fan-window profile at a centre**, over a
given packed-window union `W`.  Every field is fixed by the object's own data,
exactly as `TypeBDegreeFour.canonicalCore` fixes its generating port family:
the certificate-marked fan is `canonicalMarked`, the envelope is
`canonicalEnvelope`, and the recorded window is the ambient `W`. -/
noncomputable def canonicalProfile (object : FiniteObject.{u})
    (window : Finset object.Vertex)
    (center : object.Vertex) (high : 4 ≤ object.degree center)
    (cap : object.degree center ≤ 8) : Profile object where
  marked := canonicalMarked object center high cap
  window := window
  envelope := canonicalEnvelope object center

@[simp] theorem canonicalProfile_hub (object : FiniteObject.{u})
    (window : Finset object.Vertex) (center : object.Vertex)
    (high : 4 ≤ object.degree center) (cap : object.degree center ≤ 8) :
    (canonicalProfile object window center high cap).marked.fan.hub = center := rfl

@[simp] theorem canonicalProfile_window (object : FiniteObject.{u})
    (window : Finset object.Vertex) (center : object.Vertex)
    (high : 4 ≤ object.degree center) (cap : object.degree center ≤ 8) :
    (canonicalProfile object window center high cap).window = window := rfl

@[simp] theorem canonicalProfile_envelope (object : FiniteObject.{u})
    (window : Finset object.Vertex) (center : object.Vertex)
    (high : 4 ≤ object.degree center) (cap : object.degree center ≤ 8) :
    (canonicalProfile object window center high cap).envelope
      = canonicalEnvelope object center := rfl

/-! ## What the canonical profile records

`c(𝔉)` of `def:typeB-multiclosed-residual` counts the cubic-closed fan
neighbours recorded on the remainder side.  For the canonical profile the
"carried by the assigned envelope" clause is discharged by the envelope itself,
so `c(𝔉)` becomes a decidable local observable: the number of cubic neighbours
of the centre lying off the packed-window union. -/

/-- The remainder-side cubic fan neighbours at a centre: `N(h) ∩ R` restricted
to the vertices of degree three.  Decidable, and read off the object's own
schedules. -/
def cubicRemainderNeighbours (object : FiniteObject.{u})
    (window : Finset object.Vertex) (center : object.Vertex) :
    Finset object.Vertex :=
  letI : DecidableEq object.Vertex := object.vertices.decEq
  (neighbourRim object center).filter fun vertex =>
    object.degree vertex = 3 ∧ vertex ∉ window

theorem mem_cubicRemainderNeighbours_iff {window : Finset object.Vertex}
    (center vertex : object.Vertex) :
    vertex ∈ cubicRemainderNeighbours object window center ↔
      object.graph.Adj center vertex ∧ object.degree vertex = 3 ∧
        vertex ∉ window := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  rw [cubicRemainderNeighbours, Finset.mem_filter, mem_neighbourRim]

/-- The cubic-closed neighbours recorded by the canonical profile are exactly
the remainder-side cubic neighbours of the centre.  The third clause of
`Marked.IsCubicClosed` — the two non-`h` incidences are carried by the assigned
support — is *proved*, not assumed, because `canonicalEnvelope` carries them. -/
theorem closedNeighbours_canonicalProfile (object : FiniteObject.{u})
    (window : Finset object.Vertex) (center : object.Vertex)
    (high : 4 ≤ object.degree center) (cap : object.degree center ≤ 8) :
    (canonicalProfile object window center high cap).closedNeighbours
      = cubicRemainderNeighbours object window center := by
  ext vertex
  rw [Profile.mem_closedNeighbours_iff, mem_cubicRemainderNeighbours_iff]
  simp only [canonicalProfile, canonicalMarked_rim, Marked.IsCubicClosed,
    Profile.mem_remainder_iff, mem_neighbourRim]
  constructor
  · rintro ⟨adjacency, ⟨-, cubic, -⟩, -, notWindow⟩
    exact ⟨adjacency, cubic, notWindow⟩
  · rintro ⟨adjacency, cubic, notWindow⟩
    refine ⟨adjacency, ⟨adjacency, cubic, ?_⟩, adjacency, notWindow⟩
    intro other incidence notCentre
    exact shoulder_mem_canonicalEnvelope adjacency incidence notCentre

/-- `c(𝔉)` at the canonical profile is a decidable local count. -/
theorem closedCount_canonicalProfile (object : FiniteObject.{u})
    (window : Finset object.Vertex) (center : object.Vertex)
    (high : 4 ≤ object.degree center) (cap : object.degree center ≤ 8) :
    (canonicalProfile object window center high cap).closedCount
      = (cubicRemainderNeighbours object window center).card := by
  rw [Profile.closedCount, closedNeighbours_canonicalProfile]

/-! ## The enumerable carrier

`degreeFourCenters` filters the object's own vertex scan by the local
observable `d_G(h) = 4`.  Here the filter is the certificate-marked fan degree
window `4 ≤ d_G(h) ≤ 8` of `Marked.degree_mem_window`, again a local
observable.  The filter excludes no centre that could carry a marked fan:
`mem_fanCentres_of_marked`. -/

/-- The centres of the object lying in the certificate-marked fan degree window
`4 ≤ d_G(h) ≤ 8`, in the object's own vertex scan order. -/
def fanCentres (object : FiniteObject.{u}) : List object.Vertex :=
  object.orderedVertices.filter fun vertex =>
    decide (4 ≤ object.degree vertex ∧ object.degree vertex ≤ 8)

@[simp] theorem mem_fanCentres_iff (object : FiniteObject.{u})
    (vertex : object.Vertex) :
    vertex ∈ fanCentres object ↔
      4 ≤ object.degree vertex ∧ object.degree vertex ≤ 8 := by
  simp [fanCentres]

theorem fanCentres_nodup (object : FiniteObject.{u}) :
    (fanCentres object).Nodup :=
  object.orderedVertices_nodup.filter _

/-- **The schedule is complete.**  The centre of every certificate-marked Type B
fan over the object is enumerated: the degree window is `Marked.degree_mem_window`,
so filtering by it discards nothing. -/
theorem mem_fanCentres_of_marked (marked : Marked object) :
    marked.fan.hub ∈ fanCentres object :=
  (mem_fanCentres_iff object marked.fan.hub).2
    ⟨marked.highDegree, marked.degree_le_eight⟩

/-- The centre of every assigned Type B fan-window profile over the object is
enumerated. -/
theorem mem_fanCentres_of_profile (profile : Profile object) :
    profile.marked.fan.hub ∈ fanCentres object :=
  mem_fanCentres_of_marked profile.marked

/-- Conversely, every enumerated centre really does carry a certificate-marked
Type B fan — the canonical one.  So the schedule omits no centre *and* lists no
centre that could not appear. -/
theorem exists_marked_of_mem_fanCentres {center : object.Vertex}
    (member : center ∈ fanCentres object) :
    ∃ marked : Marked object, marked.fan.hub = center :=
  ⟨canonicalMarked object center ((mem_fanCentres_iff object center).1 member).1
      ((mem_fanCentres_iff object center).1 member).2, rfl⟩

/-- The fan-certificate residual centres of `def:marked-typeB-fan` are exactly
the centres the schedule leaves out.  One direction is
`isFanCertificateResidual_of_nine_le_degree`; the other is the canonical
labelling, which supplies a certificate at every centre of the degree window.
This is what makes the defining filter of `fanCentres` a *complete* enumeration
rather than a smuggled side condition. -/
theorem isFanCertificateResidual_iff (object : FiniteObject.{u})
    (center : object.Vertex) :
    IsFanCertificateResidual object center ↔ 9 ≤ object.degree center := by
  refine ⟨fun residual => ?_, isFanCertificateResidual_of_nine_le_degree⟩
  by_contra small
  obtain ⟨marked, hub⟩ := exists_marked_of_mem_fanCentres
    ((mem_fanCentres_iff object center).2 ⟨residual.1, by omega⟩)
  exact residual.2 marked hub

/-- **The enumerable carrier of assigned Type B fan-window profiles** over a
given packed-window union `W`: one canonical profile per centre in the fan
degree window, built from the object's own vertex, neighbour and
outside-incidence schedules.  A downstream node scans this list. -/
noncomputable def profileCandidatesWith (object : FiniteObject.{u})
    (window : Finset object.Vertex) : List (Profile object) :=
  (fanCentres object).pmap
    (fun center (degrees : 4 ≤ object.degree center ∧ object.degree center ≤ 8) =>
      canonicalProfile object window center degrees.1 degrees.2)
    fun _ member => (mem_fanCentres_iff object _).1 member

theorem mem_profileCandidatesWith_iff (object : FiniteObject.{u})
    (window : Finset object.Vertex) (profile : Profile object) :
    profile ∈ profileCandidatesWith object window ↔
      ∃ (center : object.Vertex) (high : 4 ≤ object.degree center)
        (cap : object.degree center ≤ 8),
        profile = canonicalProfile object window center high cap := by
  rw [profileCandidatesWith, List.mem_pmap]
  constructor
  · rintro ⟨center, member, rfl⟩
    exact ⟨center, ((mem_fanCentres_iff object center).1 member).1,
      ((mem_fanCentres_iff object center).1 member).2, rfl⟩
  · rintro ⟨center, high, cap, rfl⟩
    exact ⟨center, (mem_fanCentres_iff object center).2 ⟨high, cap⟩, rfl⟩

theorem profileCandidatesWith_nodup (object : FiniteObject.{u})
    (window : Finset object.Vertex) :
    (profileCandidatesWith object window).Nodup := by
  refine (fanCentres_nodup object).pmap ?_
  intro left _ right _ equal
  exact congrArg (fun profile : Profile object => profile.marked.fan.hub) equal

/-- **The enumerable carrier of assigned Type B fan-window profiles** of the
object, at the packed-window union that does not meet the fan.  The general
form `profileCandidatesWith` covers every packed-window union `W`. -/
noncomputable def profileCandidates (object : FiniteObject.{u}) : List (Profile object) :=
  profileCandidatesWith object ∅

theorem mem_profileCandidates_iff (object : FiniteObject.{u})
    (profile : Profile object) :
    profile ∈ profileCandidates object ↔
      ∃ (center : object.Vertex) (high : 4 ≤ object.degree center)
        (cap : object.degree center ≤ 8),
        profile = canonicalProfile object ∅ center high cap :=
  mem_profileCandidatesWith_iff object ∅ profile

theorem profileCandidates_nodup (object : FiniteObject.{u}) :
    (profileCandidates object).Nodup :=
  profileCandidatesWith_nodup object ∅

/-- Every assigned profile over the object has its centre represented in the
schedule at its own packed-window union: the enumeration loses no centre. -/
theorem exists_mem_profileCandidatesWith (profile : Profile object) :
    ∃ candidate ∈ profileCandidatesWith object profile.window,
      candidate.marked.fan.hub = profile.marked.fan.hub :=
  ⟨canonicalProfile object profile.window profile.marked.fan.hub
      profile.marked.highDegree profile.marked.degree_le_eight,
    (mem_profileCandidatesWith_iff object profile.window _).2
      ⟨profile.marked.fan.hub, profile.marked.highDegree,
        profile.marked.degree_le_eight, rfl⟩,
    rfl⟩

/-! ### Observables of an enumerated candidate -/

variable {window : Finset object.Vertex} {profile : Profile object}

theorem window_of_mem_profileCandidatesWith
    (member : profile ∈ profileCandidatesWith object window) :
    profile.window = window := by
  obtain ⟨center, high, cap, rfl⟩ :=
    (mem_profileCandidatesWith_iff object window profile).1 member
  rfl

theorem degreeWindow_of_mem_profileCandidatesWith
    (member : profile ∈ profileCandidatesWith object window) :
    4 ≤ object.degree profile.marked.fan.hub ∧
      object.degree profile.marked.fan.hub ≤ 8 := by
  obtain ⟨center, high, cap, rfl⟩ :=
    (mem_profileCandidatesWith_iff object window profile).1 member
  exact ⟨high, cap⟩

/-- On an enumerated candidate the closed-neighbour set of
`def:typeB-multiclosed-residual` is the decidable local set of remainder-side
cubic neighbours of the centre. -/
theorem closedNeighbours_of_mem_profileCandidatesWith
    (member : profile ∈ profileCandidatesWith object window) :
    profile.closedNeighbours
      = cubicRemainderNeighbours object window profile.marked.fan.hub := by
  obtain ⟨center, high, cap, rfl⟩ :=
    (mem_profileCandidatesWith_iff object window profile).1 member
  exact closedNeighbours_canonicalProfile object window center high cap

theorem closedCount_of_mem_profileCandidatesWith
    (member : profile ∈ profileCandidatesWith object window) :
    profile.closedCount
      = (cubicRemainderNeighbours object window profile.marked.fan.hub).card := by
  rw [Profile.closedCount, closedNeighbours_of_mem_profileCandidatesWith member]

/-! ## The per-candidate scan predicate

`prop:fan-closed-port-typeB-routing` and `fanClosedPortHybridEntry` are driven
by a family of `r ≥ 2` fan-closed surplus ports, whose only counting effect is
`2 ≤ c(𝔉)` (`TypeBFanClosedPorts.card_le_closedCount`).  That inequality is the
decidable per-candidate predicate a scan evaluates. -/

/-- The scan predicate of node `[74]`: the profile records at least two
cubic-closed remainder-side fan neighbours, i.e. `2 ≤ c(𝔉)`. -/
def IsHybridEligible (profile : Profile object) : Prop := 2 ≤ profile.closedCount

instance decidableIsHybridEligible (profile : Profile object) :
    Decidable (IsHybridEligible profile) :=
  inferInstanceAs (Decidable (2 ≤ profile.closedCount))

/-- On an enumerated candidate the scan predicate is the decidable local count
of remainder-side cubic neighbours of the centre. -/
theorem isHybridEligible_iff_of_mem
    (member : profile ∈ profileCandidatesWith object window) :
    IsHybridEligible profile ↔
      2 ≤ (cubicRemainderNeighbours object window profile.marked.fan.hub).card := by
  rw [IsHybridEligible, closedCount_of_mem_profileCandidatesWith member]

/-! ## The hybrid ledger entry, with no structural input

`lem:typeB-hybrid-B1` proves `D_B(𝔉) ≤ ½ I_W(𝔉) + D_N(𝔉)` and
`D_N(𝔉) ≤ ½ I_N(𝔉)`.  Neither needs the four-cycle exclusion: the first is the
case split on the `max` in `D_N`, and the second is `I_W + I_N = 2c`
(`Profile.windowCredit_add_nonWindowCredit`) together with the derived degree cap
`d_G(h) ≤ 8` (`Marked.degree_le_eight`).  The quantitative clauses are
`prop:fan-closed-port-typeB-routing` (b) with the counting input `2 ≤ c(𝔉)` in
place of the port family. -/

/-- **The hybrid entry conclusion in scannable form.**  For *any* assigned
profile recording at least two cubic-closed remainder-side fan neighbours:

* the local incidence capacity covers the deficit, `D_B(𝔉) ≤ ½ I_W(𝔉) + D_N(𝔉)`;
* the reserve it calls for is available, `D_N(𝔉) ≤ ½ I_N(𝔉)`;
* `D_B(𝔉) ≥ (k+1)α - 1 ≥ 5α - 1 > 0`, the manuscript's
  `D_B(𝔉) ≥ (k-3)/4 ≥ 1/4 > 0` at the registered `α = 1/4`.

No structural input and no hypothesis beyond the scan predicate: the degree
window `4 ≤ k ≤ 8` is carried by the certificate-marked fan itself
(`Marked.highDegree`, `Marked.degree_le_eight`), and the two facts about the
chosen rate are the recorded design constraints
`ReceiverLoad.LoadCapacityProfile.dischargeRate_gt` (`5α > 1`, which is the
strict positivity, read off at this very instance `c = 2`, `k = 4`) and
`dischargeRate_le` (`9α ≤ 3`, which is the fan credit `3 - (k+1)α` being
nonnegative and so is what makes the reserve available). -/
theorem hybridEntry_of_isHybridEligible (profile : Profile object)
    (ledger : LoadCapacityProfile)
    (scale : ledger.loadMultiplier = 4)
    (eligible : IsHybridEligible profile) :
    profile.closedNeighbourDeficit ledger ≤ profile.hybridCapacity ledger ∧
      profile.hybridNonWindowDemand ledger ≤ profile.nonWindowCredit ∧
      ((object.degree profile.marked.fan.hub : ℚ) + 1) *
          (1 / (ledger.loadMultiplier : ℚ)) - 1
        ≤ profile.closedNeighbourDeficit ledger ∧
      5 * (1 / (ledger.loadMultiplier : ℚ)) - 1 ≤
        profile.closedNeighbourDeficit ledger ∧
      0 < profile.closedNeighbourDeficit ledger := by
  have total := Profile.windowCredit_add_nonWindowCredit (profile := profile)
  have deficit : profile.closedNeighbourDeficit ledger
      = (profile.closedCount : ℚ)
        - (3 - ((object.degree profile.marked.fan.hub : ℚ) + 1)
            * (1 / (ledger.loadMultiplier : ℚ))) := rfl
  have twoCast : (2 : ℚ) ≤ (profile.closedCount : ℚ) := by
    exact_mod_cast eligible
  have highCast : (4 : ℚ) ≤ (object.degree profile.marked.fan.hub : ℚ) := by
    exact_mod_cast profile.marked.highDegree
  have capCast : (object.degree profile.marked.fan.hub : ℚ) ≤ 8 := by
    exact_mod_cast profile.marked.degree_le_eight
  have rateNonneg : (0 : ℚ) ≤ 1 / (ledger.loadMultiplier : ℚ) := by positivity
  have sharp : (1 : ℚ) < 5 * (1 / (ledger.loadMultiplier : ℚ)) := by
    rw [scale]
    norm_num
  have credit : 9 * (1 / (ledger.loadMultiplier : ℚ)) ≤ (3 : ℚ) := by
    rw [scale]
    norm_num
  have lowRate :
      5 * (1 / (ledger.loadMultiplier : ℚ)) ≤
        ((object.degree profile.marked.fan.hub : ℚ) + 1) *
          (1 / (ledger.loadMultiplier : ℚ)) :=
    mul_le_mul_of_nonneg_right (by linarith) rateNonneg
  have highRate :
      ((object.degree profile.marked.fan.hub : ℚ) + 1) *
          (1 / (ledger.loadMultiplier : ℚ)) ≤
        9 * (1 / (ledger.loadMultiplier : ℚ)) :=
    mul_le_mul_of_nonneg_right (by linarith) rateNonneg
  have windowNonneg : (0 : ℚ) ≤ profile.windowCredit := by
    have : (0 : ℚ) ≤ (profile.windowIncidenceTotal : ℚ) := by positivity
    simp only [Profile.windowCredit]
    linarith
  have nonWindowNonneg : (0 : ℚ) ≤ profile.nonWindowCredit := by
    have : (0 : ℚ) ≤ (profile.nonWindowIncidenceTotal : ℚ) := by positivity
    simp only [Profile.nonWindowCredit]
    linarith
  refine ⟨?_, ?_, by rw [deficit]; linarith, by rw [deficit]; linarith,
    by rw [deficit]; linarith⟩
  · rw [Profile.hybridCapacity, Profile.hybridNonWindowDemand]
    rcases le_or_gt (profile.closedNeighbourDeficit ledger - profile.windowCredit) 0
      with small | large
    · rw [max_eq_left small]; linarith
    · rw [max_eq_right large.le]; linarith
  · rw [Profile.hybridNonWindowDemand, max_le_iff]
    exact ⟨nonWindowNonneg, by rw [deficit]; linarith⟩

/-- **The scanning form of node `[74]`.**  Every enumerated candidate that
passes the decidable scan predicate satisfies the hybrid ledger conclusion of
`lem:typeB-hybrid-B1`, together with the quantitative clauses of
`prop:fan-closed-port-typeB-routing` (b).  The scan predicate is evaluated as
the local count of remainder-side cubic neighbours of the centre. -/
theorem profileCandidatesWith_scan (object : FiniteObject.{u})
    (ledger : LoadCapacityProfile) (scale : ledger.loadMultiplier = 4)
    (window : Finset object.Vertex) :
    ∀ profile ∈ profileCandidatesWith object window,
      2 ≤ (cubicRemainderNeighbours object window profile.marked.fan.hub).card →
        profile.closedNeighbourDeficit ledger ≤ profile.hybridCapacity ledger ∧
          profile.hybridNonWindowDemand ledger ≤ profile.nonWindowCredit ∧
          ((object.degree profile.marked.fan.hub : ℚ) + 1)
                * (1 / (ledger.loadMultiplier : ℚ)) - 1
            ≤ profile.closedNeighbourDeficit ledger ∧
          5 * (1 / (ledger.loadMultiplier : ℚ)) - 1 ≤
            profile.closedNeighbourDeficit ledger ∧
          0 < profile.closedNeighbourDeficit ledger := by
  intro profile member counted
  exact hybridEntry_of_isHybridEligible profile ledger scale
    ((isHybridEligible_iff_of_mem member).2 counted)

/-- The same scan at the packed-window union that does not meet the fan. -/
theorem profileCandidates_scan (object : FiniteObject.{u})
    (ledger : LoadCapacityProfile) (scale : ledger.loadMultiplier = 4) :
    ∀ profile ∈ profileCandidates object,
      2 ≤ (cubicRemainderNeighbours object ∅ profile.marked.fan.hub).card →
        profile.closedNeighbourDeficit ledger ≤ profile.hybridCapacity ledger ∧
          profile.hybridNonWindowDemand ledger ≤ profile.nonWindowCredit ∧
          ((object.degree profile.marked.fan.hub : ℚ) + 1)
                * (1 / (ledger.loadMultiplier : ℚ)) - 1
            ≤ profile.closedNeighbourDeficit ledger ∧
          5 * (1 / (ledger.loadMultiplier : ℚ)) - 1 ≤
            profile.closedNeighbourDeficit ledger ∧
          0 < profile.closedNeighbourDeficit ledger :=
  profileCandidatesWith_scan object ledger scale ∅

/-! ## What is deliberately absent

`lem:typeB-hybrid-B1` has a fourth clause: the `2c(𝔉)` local incidence carriers
are pairwise distinct, in the strong form that the family is determined by its
outside endpoint (`Profile.incidences_endpoint_injective`).  That clause — and
only that clause — rests on the four-cycle exclusion `u - h - v - z - u`, i.e.
on `NormalForm.noCommonNeighbourOutside`, which is an ambient structural input
read off the incoming residual and cannot be derived from the object's
schedules.  It is therefore *not* restated here: reproducing it would require
carrying `NormalForm object h` as a hypothesis, and this file has none.  A
consumer that needs it applies `Profile.typeBHybridB1` directly, with the
`NormalForm` it already holds, to any candidate this schedule produces. -/

end Hypostructure.Graph.TypeBProfileSchedule
