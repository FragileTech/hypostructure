import Hypostructure.Graph.CutParity
import Hypostructure.Graph.Route8Carrier

/-!
# Carrier cores: cut parity, the small-core collapse, and the census squeeze

Three things happen to a carrier core, and this module owns all three.

*Cut parity.*  A declared coordinate whose target event is a simple cycle that
meets the support and also leaves it uses at least **two** distinct boundary
incidences of the support.  A cycle crosses every cut an even number of times
and a simple cycle cannot repeat a cut edge, so the parity bound is
`Graph.CutParity`'s, read at the support's own cut.

*The small-core collapse.*  A core of at most one carrier therefore retains no
coordinate that both meets the support internally and leaves it: retaining one
would need two carriers inside a set of size at most one.  The further reading
that forgets exactly the coordinates using an internal incidence is then the
same reading, so it is target-complete -- and a *nontrivial* target-complete
quotient of a target-complete-minimal reading is precisely what that
minimality forbids.  This is the mechanism of `lem:typeA-one-terminal-collapse`;
which alternative the minimality clause fires is the reading's own datum.

*The census squeeze.*  Disjoint private carriers give an upper bound on an
indexed count; a burden gives a lower bound; and the two collide
exactly when the registered rate condition holds.  All of it is integer
arithmetic on the readings the ledger already carries -- no constant is
written here.
-/

namespace Hypostructure.Graph.Route8

open Hypostructure
open Hypostructure.Core.Finite

universe u

/-! ## Cut parity at a support's own cut -/

section CutParity

variable {object : FiniteObject.{u}} (support : Finset object.Vertex)

/-- Vertices of a finite object have decidable equality: the object's own vertex
schedule decides it.  Every carrier `Finset` below is taken at this instance, so
no two of them disagree about what a carrier set is. -/
def vertexDecEq (object : FiniteObject.{u}) : DecidableEq object.Vertex :=
  object.vertices.decEq

attribute [local instance] vertexDecEq

/-- The distinct boundary incidences of `support` that a closed walk uses. -/
noncomputable def crossingCarriers {base : object.Vertex}
    (walk : object.graph.Walk base base) : Finset (Sym2 object.Vertex) :=
  (CutParity.crossingEdges (G := object.graph)
    (S := (support : Set object.Vertex)) walk).toFinset

/-- **`lem:typeA-carrier-cut-parity`.**

A simple cycle that visits the support and also leaves it uses at least two
distinct boundary incidences of the support.  Both halves are `CutParity`'s: a
closed walk crosses a cut an even number of times, and a simple cycle uses no
cut edge twice. -/
theorem two_le_card_crossingCarriers {base : object.Vertex}
    {walk : object.graph.Walk base base} (cycle : walk.IsCycle)
    {inside outside : object.Vertex}
    (insideMember : inside ∈ walk.support) (insideSupport : inside ∈ support)
    (outsideMember : outside ∈ walk.support)
    (outsideSupport : outside ∉ support) :
    2 ≤ (crossingCarriers support walk).card := by
  refine CutParity.two_le_card_crossingEdges (G := object.graph)
    (S := (support : Set object.Vertex)) cycle ?_
  -- One of the two exhibited vertices is on the opposite side from the base.
  by_cases baseSide : base ∈ support
  · refine CutParity.crossings_pos (G := object.graph)
      (S := (support : Set object.Vertex)) walk outsideMember ?_
    simp [CutParity.side, outsideSupport, baseSide]
  · refine CutParity.crossings_pos (G := object.graph)
      (S := (support : Set object.Vertex)) walk insideMember ?_
    simp [CutParity.side, insideSupport, baseSide]

end CutParity

/-! ## The small-core collapse -/

namespace Entry

variable {Target : FiniteObject.{u} → Prop} {Carrier : Type u}
variable [DecidableEq Carrier] (entry : Entry Target Carrier)

/-- **A core of at most one carrier retains no cut-crossing coordinate.**

`lem:typeA-carrier-cut-parity` gives every coordinate that meets the reading
internally *and* leaves its support at least two distinct carriers.  A core with
at most one carrier retains no such coordinate, since a retained coordinate's
whole carrier support lies inside the core. -/
theorem not_mem_retained_of_alpha_le_one {crossing : Finset entry.Coordinate}
    (parity : ∀ r ∈ crossing, 2 ≤ (entry.car r).card)
    (small : entry.alpha ≤ 1) {r : entry.Coordinate}
    (member : r ∈ crossing) :
    r ∉ entry.retained entry.essentialCore := by
  intro retainedMember
  rw [mem_retained] at retainedMember
  have two := parity r member
  have member := retainedMember
  have bounded : (entry.car r).card ≤ entry.essentialCore.card :=
    Finset.card_le_card member.2
  rw [← alpha] at bounded
  omega

/-- **The internal-forgetting reading is the core reading itself, when the core
is small.**

The manuscript's `ρ°_𝒞` retains the boundary profile and forgets exactly the
coordinates whose declared support uses an internal incidence.  With at most one
essential carrier none of those coordinates is retained in the first place, so
the two readings have the same declared coordinates.  This is the step
`lem:typeA-one-terminal-collapse` spends `lem:typeA-internal-quotient-mixed` and
`lem:typeA-carrier-cut-parity` on. -/
theorem retained_sdiff_eq_of_alpha_le_one {crossing : Finset entry.Coordinate}
    (parity : ∀ r ∈ crossing, 2 ≤ (entry.car r).card)
    (small : entry.alpha ≤ 1) :
    entry.retained entry.essentialCore \ crossing =
      entry.retained entry.essentialCore := by
  refine Finset.sdiff_eq_self_of_disjoint (Finset.disjoint_left.mpr ?_)
  intro r retainedMember member
  exact entry.not_mem_retained_of_alpha_le_one parity small member retainedMember

/-- **`lem:typeA-one-terminal-collapse`, the collapse itself.**

*"Assume `|𝒞| ≤ 1` ... we claim that `ρ|_𝒞 → ρ°_𝒞` is target-complete ... The
nontrivial target-complete quotient above is precisely failure alternative (b)
in the definition of target-complete-minimality, unless one of the other
alternatives occurs first."*

The claim is the previous theorem: with a small core the internal-forgetting
reading *is* the core reading, so nothing separates them.  What the alternatives
are is not decided here -- `minimality` is the reading's own
target-complete-minimality clause, and this theorem is the proof that its
hypothesis is met. -/
theorem collapse_of_alpha_le_one {crossing : Finset entry.Coordinate}
    {Alternatives : Prop}
    (parity : ∀ r ∈ crossing, 2 ≤ (entry.car r).card)
    (minimality :
      entry.state (entry.retained entry.essentialCore \ crossing) =
        entry.restriction entry.essentialCore →
      Alternatives)
    (small : entry.alpha ≤ 1) :
    Alternatives := by
  refine minimality ?_
  rw [entry.retained_sdiff_eq_of_alpha_le_one parity small, restriction]

/-- The entry-level small-core-collapse fact consumed by the ledger. -/
def SmallCoreCollapseFacts : Prop :=
  ∀ {crossing : Finset entry.Coordinate} {Alternatives : Prop},
    (∀ r ∈ crossing, 2 ≤ (entry.car r).card) →
    (entry.state (entry.retained entry.essentialCore \ crossing) =
      entry.restriction entry.essentialCore →
      Alternatives) →
    entry.alpha ≤ 1 →
    Alternatives

theorem smallCoreCollapseFacts : entry.SmallCoreCollapseFacts := by
  intro crossing Alternatives parity minimality small
  exact entry.collapse_of_alpha_le_one parity minimality small

end Entry

/-! ## The census squeeze -/

/-- **`prop:typeA-route8-carrier-reduction`, the arithmetic.**

Three integer readings collide:

* `deficit` -- `ambient ≤ basins + discharge·supply`, the node-`[113]` bound
  `D_A ≥ (1/discharge − τ)·|R|` cleared of denominators and with the burden
  `N_basin ≥ discharge·D_A` already substituted for the deficit;
* `budget`  -- `floor·N_basin ≤ supply`, the disjoint private carriers against
  the boundary-incidence supply;
* `rate`    -- `(floor·discharge + 1)·supply < floor·ambient`, the registered
  rate condition.  At the manuscript's `floor = 3` and `discharge = 4` it is
  `13·τ_win|R| < 3|R|`, i.e. `τ_win < 3/13`.

No constant appears: every one of them is a reading the branch carries. -/
theorem census_contradiction
    {floor discharge basins supply ambient : Nat}
    (deficit : ambient ≤ basins + discharge * supply)
    (budget : floor * basins ≤ supply)
    (rate : (floor * discharge + 1) * supply < floor * ambient) :
    False := by
  have scaled : floor * ambient ≤ floor * basins + floor * (discharge * supply) := by
    have step : floor * ambient ≤ floor * (basins + discharge * supply) :=
      Nat.mul_le_mul_left _ deficit
    rwa [Nat.mul_add] at step
  have assoc : floor * (discharge * supply) = floor * discharge * supply :=
    (mul_assoc _ _ _).symm
  rw [assoc] at scaled
  have expand : (floor * discharge + 1) * supply =
      floor * discharge * supply + supply := by
    rw [add_mul, one_mul]
  omega

/-- **The node-`[113]` bound against the basin count.**

`lem:typeA-route8-burden`'s `N_basin ≥ discharge·D_A` substituted into
`def:typeA-large-budget-deficit`'s `|R| ≤ discharge·D_A + discharge·supply`.
This is the single reading the census spends, and it is *derived* from the two
ledger facts the branch carries. -/
theorem deficit_le_basins {discharge deficiency basins supply ambient : Nat}
    (burden : discharge * deficiency ≤ basins)
    (largeBudget : ambient ≤ discharge * deficiency + discharge * supply) :
    ambient ≤ basins + discharge * supply := by
  omega

/-- **The indexed route-`8` reduction.**

This is the carrier-reduction step without a secondary collection object.  The
selected residual supplies a finite family of entries and a finite carrier
supply through the ledger.  If every selected entry had more than `threshold`
private carriers, the indexed private-carrier census would contradict the
registered rate bound; hence the ledger can append the selected terminal
two-carrier fact for one entry of the same incoming family. -/
theorem exists_indexedTwoCarrier
    {Target : FiniteObject.{u} → Prop} {Carrier Index : Type u}
    [DecidableEq Carrier] [DecidableEq Index]
    (entries : Finset Index) (entry : Index → Entry Target Carrier)
    (supply : Finset Carrier)
    (carriers_subset :
      ∀ index ∈ entries, (entry index).carriers.toFinset ⊆ supply)
    {threshold discharge ambient : Nat}
    (deficit : ambient ≤ entries.card + discharge * supply.card)
    (rate : ((threshold + 1) * discharge + 1) * supply.card <
      (threshold + 1) * ambient) :
    ∃ index ∈ entries, IndexedTwoCarrier entries entry threshold index := by
  classical
  by_contra missing
  simp only [not_exists, not_and] at missing
  have lower :
      ∀ index ∈ entries,
        threshold + 1 ≤ indexedPrivateCount entries entry index := by
    intro index index_mem
    have not_two : ¬ IndexedTwoCarrier entries entry threshold index :=
      missing index index_mem
    unfold IndexedTwoCarrier at not_two
    omega
  exact census_contradiction deficit
    (indexedCardMul_le_supply entries entry supply carriers_subset lower) rate

/-- **`prop:typeA-route8-carrier-reduction`, ledger-input form.**

This is the form used by the spine: burden and large-budget are separate facts
on the incoming route-`8` residual ledger.  Their only job here is to produce
the cleared deficit inequality spent by `exists_indexedTwoCarrier`. -/
theorem exists_indexedTwoCarrier_of_burden_of_largeBudget
    {Target : FiniteObject.{u} → Prop} {Carrier Index : Type u}
    [DecidableEq Carrier] [DecidableEq Index]
    (entries : Finset Index) (entry : Index → Entry Target Carrier)
    (supply : Finset Carrier)
    (carriers_subset :
      ∀ index ∈ entries, (entry index).carriers.toFinset ⊆ supply)
    {threshold discharge deficiency ambient : Nat}
    (burden : discharge * deficiency ≤ entries.card)
    (largeBudget : ambient ≤ discharge * deficiency + discharge * supply.card)
    (rate : ((threshold + 1) * discharge + 1) * supply.card <
      (threshold + 1) * ambient) :
    ∃ index ∈ entries, IndexedTwoCarrier entries entry threshold index :=
  exists_indexedTwoCarrier entries entry supply carriers_subset
    (deficit_le_basins burden largeBudget) rate

end Hypostructure.Graph.Route8
