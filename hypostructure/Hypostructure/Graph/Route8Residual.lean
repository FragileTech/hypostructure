import Hypostructure.Graph.Route8Closure

/-!
# The route-8 carrier residual of one object

`def:typeA-route8-carriers` presents an indexed entry by the support it lives
on, the declared coordinates and values of its reading, and the optional target
events carried by event coordinates.  A `Presentation` is exactly that data,
at one ambient object, and the
carrier vocabulary of `Route8.Entry` is *derived* from it: the entry's carrier
supply is the support's own cut, and a coordinate's carrier support is the set
of cut edges its event uses.

With the presentation in that shape, `lem:typeA-carrier-cut-parity` is a
theorem about the object rather than a clause: `Route8.two_le_card_crossingCarriers`
applies to every coordinate whose event both meets the support and leaves it,
so the small-core collapse of `Route8.Entry.collapse_of_alpha_le_one` has its
hypothesis discharged by the ambient graph.

A `Residual` is a presentation together with the clauses the manuscript's own
definitions attach to it: the large-budget deficit of
`def:typeA-large-budget-deficit`, the burden of `lem:typeA-route8-burden`, the
absence clause (R2) of `def:typeA-true-route8-residual`, the
target-complete-minimality of the assigned trace basins
(`def:typeA-trace-basin`), and the canonical exit-`(4)` family membership rule of
`def:typeA-exit4-family` (Q5).  Every *consequence* below -- two or more
essential carriers, the existence of a two-carrier entry, the terminal
impossibility -- is derived from those clauses and from nothing else.
-/

namespace Hypostructure.Graph.Route8

open Hypostructure
open Hypostructure.Core.Finite

universe u

/-! ## Cut edges of a support -/

variable {object : FiniteObject.{u}}

attribute [local instance] vertexDecEq

/-- The object's vertex schedule is a finite type. -/
def vertexFintype (object : FiniteObject.{u}) : Fintype object.Vertex :=
  @FinEnum.instFintype _ object.vertices

attribute [local instance] vertexFintype

/-- The object's edge set is finite: its vertices are, and its adjacency is
decidable. -/
noncomputable def edgeFintype (object : FiniteObject.{u}) :
    Fintype object.graph.edgeSet := by
  letI := vertexFintype object
  letI := vertexDecEq object
  classical
  exact SimpleGraph.fintypeEdgeSet (G := object.graph)

attribute [local instance] edgeFintype

/-- The support's own cut: the edges of the object with exactly one endpoint
inside it.  This is `∂_E X` read as an unoriented incidence set; its cardinality
is the support's positive deficiency when every support vertex sits at the
baseline. -/
noncomputable def cutEdges (object : FiniteObject.{u})
    (support : Finset object.Vertex) : Finset (Sym2 object.Vertex) :=
  letI : DecidablePred fun edge : Sym2 object.Vertex =>
      ∃ inside ∈ edge, ∃ outside ∈ edge, inside ∈ support ∧ outside ∉ support :=
    fun _ => Classical.propDecidable _
  object.graph.edgeFinset.filter fun edge =>
    ∃ inside ∈ edge, ∃ outside ∈ edge, inside ∈ support ∧ outside ∉ support

theorem mem_cutEdges {support : Finset object.Vertex}
    {edge : Sym2 object.Vertex} :
    edge ∈ cutEdges object support ↔
      edge ∈ object.graph.edgeFinset ∧
        ∃ inside ∈ edge, ∃ outside ∈ edge,
          inside ∈ support ∧ outside ∉ support := by
  rw [cutEdges]
  simp only [Finset.mem_filter]

/-- A closed walk's crossings are cut edges of the support. -/
theorem crossingCarriers_subset_cutEdges {support : Finset object.Vertex}
    {base : object.Vertex} (walk : object.graph.Walk base base) :
    crossingCarriers support walk ⊆ cutEdges object support := by
  intro edge member
  rw [crossingCarriers, List.mem_toFinset, CutParity.crossingEdges,
    List.mem_map] at member
  obtain ⟨dart, filtered, shape⟩ := member
  rw [List.mem_filter] at filtered
  have crossing : CutParity.crosses (G := object.graph)
      (S := (support : Set object.Vertex)) dart = true := by
    simpa using filtered.2
  have adjacency : object.graph.Adj dart.fst dart.snd := dart.adj
  refine mem_cutEdges.mpr ⟨?_, ?_⟩
  · rw [← shape]
    exact SimpleGraph.mem_edgeFinset.mpr dart.edge_mem
  · -- exactly one endpoint of the dart lies in the support
    rw [CutParity.crosses, CutParity.side, CutParity.side, bne_iff_ne, ne_eq,
      decide_eq_decide] at crossing
    rw [← shape]
    by_cases first : dart.fst ∈ support
    · refine ⟨dart.fst, ?_, dart.snd, ?_, first, ?_⟩
      · simp [SimpleGraph.Dart.edge]
      · simp [SimpleGraph.Dart.edge]
      · intro second
        exact crossing (by simp [first, second] : dart.fst ∈ (support : Set object.Vertex) ↔
          dart.snd ∈ (support : Set object.Vertex))
    · have second : dart.snd ∈ support := by
        by_contra missing
        exact crossing (by
          constructor
          · intro inside; exact absurd inside first
          · intro inside; exact absurd inside missing)
      refine ⟨dart.snd, ?_, dart.fst, ?_, second, first⟩
      · simp [SimpleGraph.Dart.edge]
      · simp [SimpleGraph.Dart.edge]

/-- The cut as an exact finite schedule, which is the shape a carrier core is
selected against. -/
noncomputable def cutSchedule (object : FiniteObject.{u})
    (support : Finset object.Vertex) : Enumeration (Sym2 object.Vertex) :=
  Enumeration.ofNodupList (cutEdges object support).toList
    (Finset.nodup_toList _)

@[simp] theorem cutSchedule_toFinset (support : Finset object.Vertex) :
    (cutSchedule object support).toFinset = cutEdges object support := by
  ext edge
  simp [cutSchedule, Enumeration.toFinset, Enumeration.ofNodupList]

/-! ## Presented entries -/

/-- A simple closed target event attached to one declared coordinate.  This is
separate from the coordinate's value and declared support: D1 boundary-degree
coordinates, for example, have both of those but do not themselves assert a
cycle event. -/
structure CoordinateEvent (object : FiniteObject.{u}) where
  base : object.Vertex
  walk : object.graph.Walk base base
  isCycle : walk.IsCycle

/-- **`def:typeA-route8-carriers`, presented at one object.**

One indexed entry: the support it lives on, its declared coordinate family,
each coordinate's value and finite declared support, the optional target event
of event coordinates, and the boundaried reading that retains a given set of
coordinates.  Carrier data is not stored -- it is read off the optional events
below. -/
structure PresentedEntry (object : FiniteObject.{u}) where
  /-- `V(X)`: the support the entry's boundary incidences leave. -/
  support : Finset object.Vertex
  /-- The labelled interface the entry's readings are presented on. -/
  interface : Boundary.{u}
  /-- The declared coordinate index of the reading `ρ_u(B_u)`. -/
  Coordinate : Type u
  /-- Decidable equality on the declared coordinates. -/
  coordinateDecEq : DecidableEq Coordinate
  /-- The declared coordinate family. -/
  coordinates : Finset Coordinate
  /-- The value type of each declared coordinate.  It is dependent because the
  D1--D8 families do not share an artificial common codomain. -/
  Value : Coordinate → Type u
  /-- The actual value of every declared coordinate. -/
  value : (r : Coordinate) → Value r
  /-- The finite support declared by every coordinate, independently of
  whether that coordinate carries a target event. -/
  declaredSupport : Coordinate → Finset object.Vertex
  /-- The target event, only when the coordinate is an event coordinate. -/
  event? : Coordinate → Option (CoordinateEvent object)
  /-- The reading retaining exactly a set of declared coordinates. -/
  state : Finset Coordinate → BoundaryPiece interface

namespace PresentedEntry

variable (presented : PresentedEntry object)

attribute [instance] PresentedEntry.coordinateDecEq

/-- The carrier support a declared coordinate records: the cut edges of the
entry's support that its event uses. -/
noncomputable def car (r : presented.Coordinate) : Finset (Sym2 object.Vertex) :=
  match presented.event? r with
  | none => ∅
  | some event => crossingCarriers presented.support event.walk

/-- A declared coordinate is *crossing* when its event both meets the entry's
support and leaves it.  This is the manuscript's *mixed internal* event: it uses
an edge inside the basin and an edge outside the support. -/
def Crossing (r : presented.Coordinate) : Prop :=
  exists event : CoordinateEvent object,
    presented.event? r = some event /\
      (exists inside, inside ∈ event.walk.support /\ inside ∈ presented.support) /\
        exists outside, outside ∈ event.walk.support /\ outside ∉ presented.support

/-- The declared coordinates whose events cross the entry's own cut. -/
noncomputable def crossingCoordinates : Finset presented.Coordinate :=
  letI : DecidablePred presented.Crossing := fun _ => Classical.propDecidable _
  presented.coordinates.filter presented.Crossing

theorem mem_crossingCoordinates {r : presented.Coordinate} :
    r ∈ presented.crossingCoordinates ↔
      r ∈ presented.coordinates ∧ presented.Crossing r := by
  rw [crossingCoordinates]
  simp only [Finset.mem_filter]

/-- **`lem:typeA-carrier-cut-parity` at a presented entry.**  A crossing
coordinate records at least two distinct carriers. -/
theorem two_le_card_car {r : presented.Coordinate}
    (crossing : presented.Crossing r) :
    2 ≤ (presented.car r).card := by
  obtain ⟨event, eventEq, ⟨inside, insideMember, insideSupport⟩,
    outside, outsideMember, outsideSupport⟩ := crossing
  rw [car, eventEq]
  exact two_le_card_crossingCarriers presented.support event.isCycle
    insideMember insideSupport outsideMember outsideSupport

/-- Every crossing coordinate records at least two carriers. -/
theorem two_le_card_car_of_mem {r : presented.Coordinate}
    (member : r ∈ presented.crossingCoordinates) :
    2 ≤ (presented.car r).card :=
  presented.two_le_card_car (presented.mem_crossingCoordinates.mp member).2

/-- The carrier vocabulary of the presented entry: `Route8.Entry` at the
support's own cut. -/
noncomputable def toEntry (Target : FiniteObject.{u} → Prop) :
    Entry Target (Sym2 object.Vertex) where
  boundary := presented.interface
  carriers := cutSchedule object presented.support
  Coordinate := presented.Coordinate
  coordinateDecEq := presented.coordinateDecEq
  coordinates := presented.coordinates
  car := presented.car
  car_subset := by
    intro r _member
    rw [cutSchedule_toFinset]
    rw [car]
    split
    · exact Finset.empty_subset _
    · rename_i event _eventEq
      exact crossingCarriers_subset_cutEdges event.walk
  state := presented.state

end PresentedEntry

/-! ## The residual: data, and the clauses the ledger carries -/

/-- **The route-8 carrier data of an object.**

This is `def:typeA-route8-carriers`' indexed family `Ξ(𝒳)` together with the
numbers a census reads: the boundary-incidence supply the collection is counted
inside, the discharge scale of `lem:typeA-route8-burden`, the private-carrier
threshold of a two-carrier entry, the deficit `D_A(𝒳)`, and the remainder size
`|R|`.

It carries **no mathematical clause**.  Every statement the manuscript attaches
to a route-8 residual -- the absence clause (R2) of
`def:typeA-true-route8-residual`, the target-complete-minimality (R4) of the
assigned trace basins, the burden of `lem:typeA-route8-burden`, the large-budget
deficit of `def:typeA-large-budget-deficit`, and the registered rate condition --
is a *fact*, published on the canonical ledger by the row that establishes the
arm and read from it by exact key.  The only propositions below are the
well-formedness of the data itself: a coordinate is recorded by a simple cycle,
and an entry's own cut lies inside the collection's supply. -/
structure Data (Target : FiniteObject.{u} → Prop)
    (object : FiniteObject.{u}) where
  /-- The index of `Ξ(𝒳)`. -/
  Index : Type u
  /-- Decidable equality on indexed entries. -/
  indexDecEq : DecidableEq Index
  /-- `Ξ(𝒳)`: the indexed entries of the collection. -/
  entries : Finset Index
  /-- The presented carrier data of each indexed entry. -/
  presented : Index → PresentedEntry object
  /-- The ambient boundary-incidence supply of the collection. -/
  ambient : Finset (Sym2 object.Vertex)
  /-- Well-formedness: every entry's own cut lies inside that supply. -/
  cut_subset : ∀ index ∈ entries,
    cutEdges object (presented index).support ⊆ ambient
  /-- The index of `𝒳` itself: the Type A supports the entries live on. -/
  SupportIndex : Type u
  /-- Decidable equality on supports. -/
  supportDecEq : DecidableEq SupportIndex
  /-- `𝒳`: the collection's Type A supports. -/
  supports : Finset SupportIndex
  /-- The support an indexed entry `ξ = (X, w, u, B_u)` lives on. -/
  supportOf : Index → SupportIndex
  /-- Well-formedness: an entry's support is one of the collection's. -/
  supportOf_mem : ∀ index ∈ entries, supportOf index ∈ supports
  /-- `¼|V(X)| − def⁺(X)`, the per-support summand of
  `def:typeA-large-budget-deficit`. -/
  deficiencyAt : SupportIndex → Nat
  /-- `S_sil^exc(X)`, the unpaid silent excess count of a support. -/
  silentExcessAt : SupportIndex → Nat
  /-- The scale the burden discharges at, `lem:typeA-route8-burden`'s factor. -/
  discharge : Nat
  /-- The private-carrier threshold of a two-carrier entry. -/
  threshold : Nat
  /-- `|R|`, the remainder the large-budget clause is stated against. -/
  remainderSize : Nat

namespace Data

variable {Target : FiniteObject.{u} → Prop} (data : Data Target object)

attribute [instance] Data.indexDecEq

attribute [instance] Data.supportDecEq

/-- **`D_A(𝒳)`** of `def:typeA-large-budget-deficit`: the sum of the per-support
deficits over the collection.  It is the manuscript's sum, not a free number. -/
noncomputable def deficiency : Nat :=
  ∑ support ∈ data.supports, data.deficiencyAt support

/-- The indexed entries living on one support of the collection. -/
def entriesAt (support : data.SupportIndex) : Finset data.Index :=
  data.entries.filter fun index => data.supportOf index = support

/-- The indexed entries, as the carrier collection a census runs over. -/
noncomputable def collection : Collection Target (Sym2 object.Vertex) where
  Index := data.Index
  indexDecEq := data.indexDecEq
  entries := data.entries
  entry := fun index => (data.presented index).toEntry Target
  ambient := data.ambient
  carriers_subset := by
    intro index member
    simpa [PresentedEntry.toEntry] using data.cut_subset index member

/-- The carrier vocabulary of one indexed entry. -/
@[reducible] noncomputable def entry (index : data.Index) :
    Entry Target (Sym2 object.Vertex) :=
  (data.presented index).toEntry Target

/-- `α(ξ)` at an indexed entry. -/
@[reducible] noncomputable def alpha (index : data.Index) : Nat :=
  (data.entry index).alpha

/-- `π(ξ)` at an indexed entry. -/
@[reducible] noncomputable def privateCount (index : data.Index) : Nat :=
  data.collection.privateCount index

/-- A *two-carrier* entry: at most `threshold` private carriers
(`def:typeA-route8-carriers`). -/
@[reducible] def TwoCarrier (index : data.Index) : Prop :=
  data.collection.TwoCarrier data.threshold index

/-! ### The manuscript's clauses, as propositions about the data

Each is stated here so that the vocabulary can name it and a row can prove or
consume it.  None of them is a field of anything. -/

/-- **The surviving trace of one indexed entry**: clauses (R2) and (R4) of
`def:typeA-true-route8-residual` composed exactly as
`lem:typeA-one-terminal-collapse` composes them.

`def:typeA-trace-basin` makes the assigned basin target-complete-minimal, so a
*nontrivial* target-complete quotient of its reading fires one of the four
alternatives (a)--(d), which are exits `(4)`, `(5)`, `(6)`, `(7)`; (R2) says
those are absent.  The quotient in question is the manuscript's `ρ°_𝒞`, which
retains the boundary profile and forgets exactly the coordinates whose declared
support crosses the entry's cut, so the composite says: `ρ°_𝒞` is a *proper*
quotient -- it does not agree with the core reading. -/
def SurvivingTrace (index : data.Index) : Prop :=
  (data.presented index).state
      ((data.entry index).retained (data.entry index).essentialCore \
        (data.presented index).crossingCoordinates) ≠
    (data.entry index).restriction (data.entry index).essentialCore

/-- **Exit `(4)` at one indexed entry**, as clause (Q5) of
`def:typeA-exit4-family` generates it, with the three data the clause names:

* the entry is two-carrier -- `lem:typeA-two-carrier-deletion-canonical`'s
  hypothesis `π_𝒳(ξ) ≤ 2`;
* the witnessing event is *declared* -- `lem:typeA-deletion-witness-declared`:
  the deletion forgets a declared coordinate of the core reading whose carrier
  support contains the deleted carrier;
* the deletion quotient is separated by a compatible outside context, which is
  `lem:typeA-carrier-deletion-exit`'s target defect. -/
def ExitFour (index : data.Index) : Prop :=
  data.TwoCarrier index ∧
    ∃ carrier ∈ (data.entry index).essentialCore,
      (∃ r ∈ (data.entry index).coordinates,
          (data.entry index).car r ⊆ (data.entry index).essentialCore ∧
            carrier ∈ (data.entry index).car r) ∧
        Response.TargetDefect Target
          ((data.entry index).restriction
            ((data.entry index).essentialCore.erase carrier))
          ((data.entry index).restriction (data.entry index).essentialCore)

/-- **`lem:typeA-silent-excess-count` at node `[94]`**, as
`lem:typeA-route8-burden` cites it: with no completion port carrying four
visible receiver-entry returns, the unpaid silent excess of a support is at
least `discharge·(¼|V(X)| − def⁺(X))`. -/
def SilentExcessCount : Prop :=
  ∀ support ∈ data.supports,
    data.discharge * data.deficiencyAt support ≤ data.silentExcessAt support

/-- **`lem:typeA-reduced-silent-residual` at node `[94]`**, as
`lem:typeA-route8-burden` cites it: with exits `(4)`--`(7)` absent, every unpaid
silent excess vertex of a support has a target-complete-minimal trace basin, so
the indexed pairs `(u, B_u)` on that support are at least as many. -/
def BasinAssignment : Prop :=
  ∀ support ∈ data.supports,
    data.silentExcessAt support ≤ (data.entriesAt support).card

/-- **`lem:typeA-route8-burden`**: `N_basin(𝒳) ≥ discharge·D_A(𝒳)`. -/
def Burden : Prop :=
  data.discharge * data.deficiency ≤ data.entries.card

/-- **`def:typeA-large-budget-deficit`**, cleared of denominators against the
boundary supply ceiling: `D_A ≥ (1/discharge − τ)·|R|`. -/
def LargeBudgetDeficit : Prop :=
  data.remainderSize ≤
    data.discharge * data.deficiency + data.discharge * data.ambient.card

/-- **The node-`[113]` bound against the basin count**: the burden already
substituted into the large-budget deficit.  This is the single reading the
census spends. -/
def BasinDeficit : Prop :=
  data.remainderSize ≤ data.entries.card + data.discharge * data.ambient.card

/-- **The registered rate condition.**  At the manuscript's threshold `2` and
discharge `4` it is `13·τ_win|R| < 3|R|`, i.e. `τ_win < 3/13`. -/
def Rate : Prop :=
  ((data.threshold + 1) * data.discharge + 1) * data.ambient.card <
    (data.threshold + 1) * data.remainderSize

/-! ### The consequences, all derived -/

/-- **`lem:typeA-one-terminal-collapse`.**

An indexed entry whose trace survives has at least two essential carriers.  With
at most one, cut parity leaves no crossing coordinate retained, so `ρ°_𝒞` agrees
with the core reading -- and the surviving-trace clause says it does not. -/
theorem two_le_alpha {index : data.Index}
    (surviving : data.SurvivingTrace index) : 2 ≤ data.alpha index := by
  by_contra small
  refine surviving ?_
  have same :=
    Entry.retained_sdiff_eq_of_alpha_le_one (data.entry index)
      (crossing := (data.presented index).crossingCoordinates)
      (fun r member => (data.presented index).two_le_card_car_of_mem member)
      (show (data.entry index).alpha ≤ 1 by
        have small' : ¬ 2 ≤ (data.entry index).alpha := small
        omega)
  exact congrArg (data.presented index).state same

/-- **`lem:typeA-essential-deletion-witness`, `lem:typeA-deletion-witness-declared`,
`lem:typeA-two-carrier-deletion-canonical` and `lem:typeA-carrier-deletion-exit`,
composed.**

A two-carrier entry with a nontrivial carrier core realizes exit `(4)`: the core
is nonempty, inclusion-minimality separates the core reading from the deletion
of any of its carriers, and that separation *is* clause (Q5)'s canonical
exit-`(4)` quotient. -/
theorem exitFour_of_twoCarrier {index : data.Index}
    (twoCarrier : data.TwoCarrier index) (core : 2 ≤ data.alpha index) :
    data.ExitFour index := by
  obtain ⟨carrier, member⟩ :=
    Finset.card_pos.mp (by
      have positive : 2 ≤ (data.entry index).essentialCore.card := core
      omega : 0 < (data.entry index).essentialCore.card)
  exact ⟨twoCarrier, carrier, member,
    (data.entry index).exists_forgotten_coordinate member,
    (data.entry index).deletion_targetDefect member⟩

/-- **`prop:typeA-route8-carrier-reduction`.**

A collection whose node-`[113]` bound and rate condition hold contains a
two-carrier entry: otherwise every entry has `threshold + 1` private carriers,
and the disjointness census collides with the bound. -/
theorem exists_twoCarrier (deficit : data.BasinDeficit) (rate : data.Rate) :
    ∃ index ∈ data.entries, data.TwoCarrier index :=
  data.collection.exists_twoCarrier (threshold := data.threshold)
    (discharge := data.discharge) deficit rate

/-- **`lem:typeA-route8-burden`, proved.**

*"For each `X ∈ 𝒳` ... `lem:typeA-silent-excess-count` applies to `X` and gives
`S_sil^exc(X) ≥ 4(¼|V(X)| − def⁺(X))`.  By `lem:typeA-reduced-silent-residual`,
every unpaid silent excess vertex counted by `S_sil^exc(X)` has a
target-complete-minimal trace basin unless one of exits (4)--(7) occurs.  Those
exits are absent by hypothesis.  Counting the resulting indexed pairs `(u, B_u)`
and summing the displayed inequality over `X ∈ 𝒳` proves
`N_basin(𝒳) ≥ 4·D_A(𝒳)`."*

The two cited readings are the hypotheses; the counting and the summation are
this proof.  `N_basin(𝒳)` is `|Ξ(𝒳)|` and the indexed entries are partitioned by
the support they live on, which is what turns the per-support inequalities into
the collection-wide one. -/
theorem burden_of_silentExcess (silentExcess : data.SilentExcessCount)
    (basins : data.BasinAssignment) : data.Burden := by
  classical
  calc data.discharge * data.deficiency
      = ∑ support ∈ data.supports,
          data.discharge * data.deficiencyAt support := by
        rw [deficiency, Finset.mul_sum]
    _ ≤ ∑ support ∈ data.supports, data.silentExcessAt support :=
        Finset.sum_le_sum silentExcess
    _ ≤ ∑ support ∈ data.supports, (data.entriesAt support).card :=
        Finset.sum_le_sum basins
    _ = data.entries.card :=
        (Finset.card_eq_sum_card_fiberwise data.supportOf_mem).symm

/-! ### The manuscript's clauses, each a proposition the ledger can carry

Every clause below is a proposition, so every one of them can be -- and is -- a
registered fact.  The three large-budget readings depend on the collection, so
they travel with the existential node `[109]` commits; the two exit clauses are
statements about the *object*, so they are decided once, before the arm is
entered, exactly where the manuscript decides them: nodes `[101]` and `[103]`. -/

/-- **Node `[109]` with `[111]`--`[112]`: a large-budget route-8 collection.**

The two node-`[94]` readings `lem:typeA-route8-burden` cites, the large-budget
clause of `def:typeA-large-budget-deficit`, and the registered rate condition.
The burden itself is *not* here: it is proved from the first two by
`burden_of_silentExcess` below, exactly as the manuscript proves it. -/
structure LargeBudget : Prop where
  /-- `lem:typeA-silent-excess-count`. -/
  silentExcess : data.SilentExcessCount
  /-- `lem:typeA-reduced-silent-residual`. -/
  basins : data.BasinAssignment
  /-- `def:typeA-large-budget-deficit`. -/
  deficit : data.LargeBudgetDeficit
  /-- The registered rate condition. -/
  rate : data.Rate

/-- **Node `[113]`: the same collection with the burden already substituted.**
This is the single reading the census spends. -/
structure Reduced : Prop where
  /-- The node-`[113]` bound against the basin count. -/
  deficit : data.BasinDeficit
  /-- The registered rate condition. -/
  rate : data.Rate

/-- **Node `[122]`: a two-carrier entry.**  The remaining clauses of
`def:typeA-terminal-two-carrier` -- (T2) at the entry and (T3) at its carrier
core -- are the ledger facts of nodes `[101]`/`[103]` and `[116]`, so the package
the census produces carries only what the census itself establishes. -/
def TwoCarrierEntry : Prop :=
  ∃ index ∈ data.entries, data.TwoCarrier index

variable {data}

/-- **Nodes `[111]`--`[113]`.**  The burden turns the large-budget deficit into
the bound against the basin count. -/
theorem Reduced.of_largeBudget (large : data.LargeBudget) : data.Reduced where
  deficit :=
    deficit_le_basins
      (data.burden_of_silentExcess large.silentExcess large.basins)
      large.deficit
  rate := large.rate

/-- **`prop:typeA-route8-carrier-reduction`.**  A reduced large-budget
collection contains a two-carrier entry. -/
theorem Reduced.twoCarrierEntry (reduced : data.Reduced) :
    data.TwoCarrierEntry :=
  data.exists_twoCarrier reduced.deficit reduced.rate

/-- **`thm:typeA-two-carrier-nogo`.**

The terminal two-carrier obstruction is uninhabited.  (T4) is the census entry,
(T2) is nodes `[101]`/`[103]`'s exit absences, (T3) is node `[116]`'s carrier
core, and (T5) is the deletion witness inclusion-minimality forces; the entry
therefore realizes exit `(4)`, which node `[101]` denies. -/
theorem no_twoCarrierEntry
    (core : ∀ index ∈ data.entries, data.SurvivingTrace index →
      2 ≤ data.alpha index)
    (surviving : ∀ index ∈ data.entries, data.SurvivingTrace index)
    (free : ∀ index ∈ data.entries, ¬ data.ExitFour index)
    (package : data.TwoCarrierEntry) : False := by
  obtain ⟨index, member, twoCarrier⟩ := package
  exact free index member
    (data.exitFour_of_twoCarrier twoCarrier
      (core index member (surviving index member)))

end Data

/-- **Node `[101]`, no arm: exit `(4)` is absent.**  No indexed entry of any
route-8 carrier data on the object realizes the canonical exit-`(4)` quotient of
clause (Q5).  This is (R2) of `def:typeA-true-route8-residual` for exit `(4)`. -/
def ExitFourFree (Target : FiniteObject.{u} → Prop)
    (object : FiniteObject.{u}) : Prop :=
  ∀ data : Data Target object, ∀ index ∈ data.entries, ¬ data.ExitFour index

/-- **Node `[103]`, no arm: exit `(5)` is absent.**  The internal-forgetting
reading `ρ°_𝒞` of every indexed entry is a *proper* quotient of the core
reading, so alternative (b) of `def:typeA-trace-basin` -- a nontrivial
target-complete quotient, which is exit `(5)`, the target-complete compression --
does not occur.  With `ExitFourFree` this is what
`lem:typeA-one-terminal-collapse` spends. -/
def TraceSurviving (Target : FiniteObject.{u} → Prop)
    (object : FiniteObject.{u}) : Prop :=
  ∀ data : Data Target object, ∀ index ∈ data.entries, data.SurvivingTrace index

end Hypostructure.Graph.Route8
