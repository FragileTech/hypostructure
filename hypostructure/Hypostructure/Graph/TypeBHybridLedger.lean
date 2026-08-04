import Hypostructure.Graph.TypeBFanClosedPorts

/-!
# The hybrid window / non-window incidence ledger of one Type B fan

This file is the graph-mathematics content of manuscript nodes `[74]`/`[82]`
(`fanthm`) of `original_erdos_64_proof.tex`:

* `def:typeB-hybrid-incidence` -- the support classification
  `c_W / c_M / c_I`, the incidence counts `I_W = 2c_W + c_M` and
  `I_N = c_M + 2c_I`, and the hybrid non-window demand
  `D_N = max{0, D_B - ½ I_W}` (`Profile.hybridNonWindowDemand`), together with
  the manuscript's "equivalently" reformulation
  `D_N = max{0, ½ I_N - (3 - (k+1)α)}` (`Profile.hybridNonWindowDemand_eq`),
  the manuscript's `(11-k)/4` at the registered `α = 1/4`;
* `lem:typeB-hybrid-incidence-budget` -- `typeBHybridIncidenceBudget`;
* `lem:typeB-hybrid-B1` -- `typeBHybridB1`;
* clause (c) of `prop:fan-closed-port-typeB-routing` --
  `fanClosedPortHybridEntry`.

Nothing is redefined.  The profile, the two incidence kinds
`Profile.IsWindowIncidence` / `Profile.IsNonWindowIncidence`, the fan-closed
ports, the closed-neighbour count `c(𝔉)` and the deficit `D_B(𝔉)` are all
`Hypostructure.Graph.TypeBFanClosedPorts`; the certificate-marked fan and its
degree cap `d_G(h) ≤ 8` are `Hypostructure.Graph.TypeBMarkedFan`; the ports,
their shoulder schedules and `NormalForm` are
`Hypostructure.Graph.TypeBOpenPorts`.

## What the structural input is, and what it is not

The only structural input is `NormalForm object h`
(`lem:heavy-neighbourhood-normal-form`), passed as an explicit argument exactly
as in `TypeBOpenPorts.heavyCenterTriangularAlternative` and
`TypeBFanClosedPorts.fanClosedPortTypeBRouting`.  It is obtained downstream from
the residual by `TypeBOpenPorts.LocalHypotheses.normalForm`, which reads the
four-cycle avoidance off `ctx.avoids`.  **No hypothesis anywhere in this file
asserts the absence of a structure**: there is no `¬ HasCycleWithLength`, no
"direct fan-window cycle does not occur", no "target-defect / compression /
delocalization alternative is excluded".  The manuscript's proof of
`lem:typeB-hybrid-incidence-budget` uses only dyadic safety at the four-cycle
`u - h - v - z - u`, which is precisely
`NormalForm.noCommonNeighbourOutside`.

There are no hypotheses.  `def:typeB-window-incidence-profile` says a profile
*records the assigned fan neighbours that lie in the remainder side*, so
`closedNeighbours` is filtered to the remainder by construction and
`closedNeighbours_subset_remainder` is a theorem about every profile.

## Incidences are half-edges

A window incidence of the manuscript is the *triple* `(u, P, i)`, so it carries
its owner `u`.  Accordingly `Profile.incidences` is a finite set of pairs
`(u, z)` with `u` a cubic-closed fan neighbour and `z` one of its two non-`h`
endpoints.  This is what makes the manuscript's count `I_W + I_N = 2c` correct.
The manuscript's disjointness assertion ("two different closed neighbours cannot
use the same non-`h` vertex") is proved in the strong form
`incidences_endpoint_injective`: the whole family of `2c` incidences is
determined by its outside endpoint.

All rational quantities are over `ℚ`, consistently with
`Profile.closedNeighbourDeficit`.
-/

namespace Hypostructure.Graph.TypeBFanClosedPorts

open Hypostructure.Graph
open Hypostructure.Graph.TypeBOpenPorts
open Hypostructure.Graph.TypeBMarkedFan
open Hypostructure.Graph.Strategy.Official.Features.DeletionFanIncidence
open Hypostructure.Graph.ReceiverLoad (LoadCapacityProfile)

universe u v

variable {object : FiniteObject.{u}}

/-! ## Two counting helpers -/

/-- Two complementary boolean predicates split a list. -/
private theorem countP_add_countP_of_complement {α : Type v}
    (left right : α → Bool) (list : List α)
    (complement : ∀ item ∈ list, right item = !left item) :
    list.countP left + list.countP right = list.length := by
  rw [List.countP_eq_length_filter, List.countP_eq_length_filter,
    List.filter_congr complement, ← List.length_eq_length_filter_add]

/-- An indicator sum is a filtered cardinality. -/
private theorem sum_ite_const {α : Type v} (support : Finset α)
    (P : α → Prop) [DecidablePred P] (value : Nat) :
    ∑ item ∈ support, (if P item then value else 0)
      = (support.filter P).card * value := by
  rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]

namespace Profile

/-! ## Decidability of the two incidence kinds -/

instance decidableIsWindowIncidence (profile : Profile object)
    (source target : object.Vertex) :
    Decidable (profile.IsWindowIncidence source target) :=
  letI : DecidableEq object.Vertex := object.vertices.decEq
  letI : DecidableRel object.graph.Adj := object.decideAdj
  inferInstanceAs (Decidable (source ∉ profile.window ∧
    object.graph.Adj source target ∧ target ∈ profile.window))

instance decidableIsNonWindowIncidence (profile : Profile object)
    (source target : object.Vertex) :
    Decidable (profile.IsNonWindowIncidence source target) :=
  letI : DecidableEq object.Vertex := object.vertices.decEq
  letI : DecidableRel object.graph.Adj := object.decideAdj
  inferInstanceAs (Decidable (source ∉ profile.window ∧
    object.graph.Adj source target ∧
    target ∉ profile.window ∧ target ≠ profile.marked.fan.hub))

/-! ## The two non-`h` incidences of a fan neighbour -/

/-- The two non-`h` incidences of a fan neighbour `u`, in the ambient scan
order.  This is literally the shoulder schedule `s(p)` of the port `p = (h, u)`
(`Port.shoulders`, i.e. the framework's `outsideIncidences`); no second
neighbour model is introduced. -/
def outsideNeighbours (profile : Profile object) (u : object.Vertex) :
    List object.Vertex :=
  outsideIncidences object profile.marked.fan.hub u

theorem outsideNeighbours_eq_shoulders {profile : Profile object}
    {p : Port object} (center : p.center = profile.marked.fan.hub) :
    profile.outsideNeighbours p.endpoint = p.shoulders := by
  rw [outsideNeighbours, Port.shoulders, center]

theorem mem_outsideNeighbours_iff (profile : Profile object)
    (u z : object.Vertex) :
    z ∈ profile.outsideNeighbours u ↔
      z ≠ profile.marked.fan.hub ∧ object.graph.Adj u z := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  rw [outsideNeighbours, outsideIncidences,
    (object.orderedNeighbors_nodup u).mem_erase_iff,
    object.mem_orderedNeighbors_iff]

theorem outsideNeighbours_nodup (profile : Profile object) (u : object.Vertex) :
    (profile.outsideNeighbours u).Nodup := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  rw [outsideNeighbours, outsideIncidences]
  exact (object.orderedNeighbors_nodup u).erase _

/-- A cubic-closed fan neighbour has exactly two non-`h` incidences: this is
`N_G(u) = {h, a_u, b_u}` of `def:marked-typeB-fan`. -/
theorem outsideNeighbours_length {profile : Profile object} {u : object.Vertex}
    (member : u ∈ profile.closedNeighbours) :
    (profile.outsideNeighbours u).length = 2 := by
  obtain ⟨rimMember, closed⟩ := (mem_closedNeighbours_iff u).1 member
  have adjacency : object.graph.Adj profile.marked.fan.hub u :=
    (profile.marked.rim_eq_neighbourhood u).1 rimMember
  have counted := outsideIncidences_length object adjacency
  rw [closed.1.2.1] at counted
  simp only [outsideNeighbours]
  omega

theorem hub_adj_of_mem_closedNeighbours {profile : Profile object}
    {u : object.Vertex} (member : u ∈ profile.closedNeighbours) :
    object.graph.Adj profile.marked.fan.hub u :=
  (profile.marked.rim_eq_neighbourhood u).1 ((mem_closedNeighbours_iff u).1 member).1

/-! ## `def:typeB-window-incidence-profile`: the support type of a neighbour -/

/-- The number of window incidences among the two non-`h` incidences of `u`. -/
def windowIncidenceCount (profile : Profile object) (u : object.Vertex) : Nat :=
  (profile.outsideNeighbours u).countP fun z =>
    decide (profile.IsWindowIncidence u z)

/-- The number of non-window fan incidences among the two non-`h` incidences of
`u`. -/
def nonWindowIncidenceCount (profile : Profile object)
    (u : object.Vertex) : Nat :=
  (profile.outsideNeighbours u).countP fun z =>
    decide (profile.IsNonWindowIncidence u z)

/-- On a remainder-side cubic-closed neighbour the two incidence kinds of
`def:typeB-window-incidence-profile` are complementary, so its two non-`h`
incidences split into window and non-window ones.  This is what makes the
classification into window-, mixed- and internal-supported exhaustive. -/
theorem windowIncidenceCount_add_nonWindowIncidenceCount
    {profile : Profile object} {u : object.Vertex}
    (member : u ∈ profile.closedNeighbours) (recorded : u ∈ profile.remainder) :
    profile.windowIncidenceCount u + profile.nonWindowIncidenceCount u = 2 := by
  have outside : u ∉ profile.window := not_mem_window_of_mem_remainder recorded
  have complement : ∀ z ∈ profile.outsideNeighbours u,
      decide (profile.IsNonWindowIncidence u z)
        = !decide (profile.IsWindowIncidence u z) := by
    intro z member'
    obtain ⟨neHub, adjacency⟩ := (mem_outsideNeighbours_iff profile u z).1 member'
    by_cases inWindow : z ∈ profile.window
    · have windowIncidence : profile.IsWindowIncidence u z :=
        ⟨outside, adjacency, inWindow⟩
      have notNonWindow : ¬ profile.IsNonWindowIncidence u z := by
        rintro ⟨-, -, notIn, -⟩
        exact notIn inWindow
      simp [windowIncidence, notNonWindow]
    · have nonWindowIncidence : profile.IsNonWindowIncidence u z :=
        ⟨outside, adjacency, inWindow, neHub⟩
      have notWindow : ¬ profile.IsWindowIncidence u z := by
        rintro ⟨-, -, isIn⟩
        exact inWindow isIn
      simp [nonWindowIncidence, notWindow]
  rw [windowIncidenceCount, nonWindowIncidenceCount,
    countP_add_countP_of_complement _ _ _ complement]
  exact outsideNeighbours_length member

/-- The window-supported cubic-closed neighbours: two window incidences. -/
def windowSupported (profile : Profile object) : Finset object.Vertex :=
  profile.closedNeighbours.filter fun u => profile.windowIncidenceCount u = 2

/-- The mixed-supported cubic-closed neighbours: one window incidence and one
non-window fan incidence. -/
def mixedSupported (profile : Profile object) : Finset object.Vertex :=
  profile.closedNeighbours.filter fun u => profile.windowIncidenceCount u = 1

/-- The internal-supported cubic-closed neighbours: two non-window fan
incidences. -/
def internalSupported (profile : Profile object) : Finset object.Vertex :=
  profile.closedNeighbours.filter fun u => profile.nonWindowIncidenceCount u = 2

/-- `c_W(𝔉)`. -/
def windowSupportedCount (profile : Profile object) : Nat :=
  profile.windowSupported.card

/-- `c_M(𝔉)`. -/
def mixedSupportedCount (profile : Profile object) : Nat :=
  profile.mixedSupported.card

/-- `c_I(𝔉)`. -/
def internalSupportedCount (profile : Profile object) : Nat :=
  profile.internalSupported.card

/-- `def:typeB-hybrid-incidence`: the window-incidence count
`I_W(𝔉) = 2c_W + c_M`. -/
def windowIncidenceTotal (profile : Profile object) : Nat :=
  2 * profile.windowSupportedCount + profile.mixedSupportedCount

/-- `def:typeB-hybrid-incidence`: the non-window incidence count
`I_N(𝔉) = c_M + 2c_I`. -/
def nonWindowIncidenceTotal (profile : Profile object) : Nat :=
  profile.mixedSupportedCount + 2 * profile.internalSupportedCount

/-- `def:typeB-hybrid-incidence`: `c = c_W + c_M + c_I`. -/
theorem supportClasses_card {profile : Profile object}
    :
    profile.windowSupportedCount + profile.mixedSupportedCount
        + profile.internalSupportedCount
      = profile.closedCount := by
  have key : ∀ u ∈ profile.closedNeighbours,
      (1 : Nat)
        = (if profile.windowIncidenceCount u = 2 then 1 else 0)
          + (if profile.windowIncidenceCount u = 1 then 1 else 0)
          + (if profile.nonWindowIncidenceCount u = 2 then 1 else 0) := by
    intro u member
    have split := windowIncidenceCount_add_nonWindowIncidenceCount member
      (closedNeighbours_subset_remainder member)
    by_cases two : profile.windowIncidenceCount u = 2
    · have : profile.nonWindowIncidenceCount u = 0 := by omega
      simp [two, this]
    by_cases one : profile.windowIncidenceCount u = 1
    · have : profile.nonWindowIncidenceCount u = 1 := by omega
      simp [one, this]
    · have zero : profile.windowIncidenceCount u = 0 := by omega
      have : profile.nonWindowIncidenceCount u = 2 := by omega
      simp [zero, this]
  have expand :
      profile.closedCount
        = ∑ u ∈ profile.closedNeighbours,
            ((if profile.windowIncidenceCount u = 2 then 1 else 0)
              + (if profile.windowIncidenceCount u = 1 then 1 else 0)
              + (if profile.nonWindowIncidenceCount u = 2 then 1 else 0)) := by
    rw [closedCount, Finset.card_eq_sum_ones]
    exact Finset.sum_congr rfl key
  rw [expand, Finset.sum_add_distrib, Finset.sum_add_distrib,
    sum_ite_const, sum_ite_const, sum_ite_const]
  simp only [windowSupportedCount, mixedSupportedCount, internalSupportedCount,
    windowSupported, mixedSupported, internalSupported, Nat.mul_one]

theorem sum_windowIncidenceCount {profile : Profile object}
    :
    ∑ u ∈ profile.closedNeighbours, profile.windowIncidenceCount u
      = profile.windowIncidenceTotal := by
  have key : ∀ u ∈ profile.closedNeighbours,
      profile.windowIncidenceCount u
        = (if profile.windowIncidenceCount u = 2 then 2 else 0)
          + (if profile.windowIncidenceCount u = 1 then 1 else 0) := by
    intro u member
    have split := windowIncidenceCount_add_nonWindowIncidenceCount member
      (closedNeighbours_subset_remainder member)
    by_cases two : profile.windowIncidenceCount u = 2
    · simp [two]
    by_cases one : profile.windowIncidenceCount u = 1
    · simp [one]
    · have zero : profile.windowIncidenceCount u = 0 := by omega
      simp [zero]
  rw [Finset.sum_congr rfl key, Finset.sum_add_distrib, sum_ite_const,
    sum_ite_const, windowIncidenceTotal]
  simp only [windowSupportedCount, mixedSupportedCount, windowSupported,
    mixedSupported, Nat.mul_one]
  omega

theorem sum_nonWindowIncidenceCount {profile : Profile object}
    :
    ∑ u ∈ profile.closedNeighbours, profile.nonWindowIncidenceCount u
      = profile.nonWindowIncidenceTotal := by
  have key : ∀ u ∈ profile.closedNeighbours,
      profile.nonWindowIncidenceCount u
        = (if profile.nonWindowIncidenceCount u = 2 then 2 else 0)
          + (if profile.windowIncidenceCount u = 1 then 1 else 0) := by
    intro u member
    have split := windowIncidenceCount_add_nonWindowIncidenceCount member
      (closedNeighbours_subset_remainder member)
    by_cases two : profile.windowIncidenceCount u = 2
    · have zero : profile.nonWindowIncidenceCount u = 0 := by omega
      simp [zero, two]
    by_cases one : profile.windowIncidenceCount u = 1
    · have : profile.nonWindowIncidenceCount u = 1 := by omega
      simp [one, this]
    · have zero : profile.windowIncidenceCount u = 0 := by omega
      have : profile.nonWindowIncidenceCount u = 2 := by omega
      simp [zero, this]
  rw [Finset.sum_congr rfl key, Finset.sum_add_distrib, sum_ite_const,
    sum_ite_const, nonWindowIncidenceTotal]
  simp only [internalSupportedCount, mixedSupportedCount, internalSupported,
    mixedSupported, Nat.mul_one]
  omega

/-- `I_W(𝔉) + I_N(𝔉) = 2c(𝔉)`: the cubic-closed neighbours use exactly `2c`
incidences, each recorded as a window incidence or a non-window fan
incidence. -/
theorem windowIncidenceTotal_add_nonWindowIncidenceTotal
    {profile : Profile object} :
    profile.windowIncidenceTotal + profile.nonWindowIncidenceTotal
      = 2 * profile.closedCount := by
  have classes := supportClasses_card (profile := profile)
  simp only [windowIncidenceTotal, nonWindowIncidenceTotal]
  omega

/-! ## The local incidence carriers -/

/-- The local Type B incidence carriers of the fan: the half-edge incidences
`(u, z)` with `u` a cubic-closed fan neighbour of `h` and `z` one of its two
non-`h` endpoints.  Recording the owner `u` is faithful to
`def:typeB-window-incidence-profile`, whose window incidence is the triple
`(u, P, i)`. -/
def incidences (profile : Profile object) :
    Finset (object.Vertex × object.Vertex) :=
  letI : DecidableEq object.Vertex := object.vertices.decEq
  profile.closedNeighbours.biUnion fun u =>
    (profile.outsideNeighbours u).toFinset.image fun z => (u, z)

theorem mem_incidences_iff (profile : Profile object)
    (e : object.Vertex × object.Vertex) :
    e ∈ profile.incidences ↔
      e.1 ∈ profile.closedNeighbours ∧ e.2 ∈ profile.outsideNeighbours e.1 := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  constructor
  · intro member
    rw [incidences, Finset.mem_biUnion] at member
    obtain ⟨u, uMember, imageMember⟩ := member
    rw [Finset.mem_image] at imageMember
    obtain ⟨z, zMember, rfl⟩ := imageMember
    exact ⟨uMember, List.mem_toFinset.1 zMember⟩
  · rintro ⟨first, second⟩
    rw [incidences, Finset.mem_biUnion]
    exact ⟨e.1, first,
      Finset.mem_image.2 ⟨e.2, List.mem_toFinset.2 second, rfl⟩⟩

/-- Blocks of the incidence family carried by distinct owners are disjoint. -/
private theorem disjoint_of_fst {α : Type v} [DecidableEq α] {u v : α}
    (distinct : u ≠ v) (left right : Finset (α × α))
    (leftOwner : ∀ e ∈ left, e.1 = u) (rightOwner : ∀ e ∈ right, e.1 = v) :
    Disjoint left right := by
  rw [Finset.disjoint_left]
  intro e leftMember rightMember
  exact distinct ((leftOwner e leftMember).symm.trans (rightOwner e rightMember))

/-- The fan uses exactly `2c(𝔉)` local incidence carriers.  Only simplicity of
`G` enters: "one closed neighbour cannot use the same non-`h` endpoint twice". -/
theorem card_incidences (profile : Profile object) :
    profile.incidences.card = 2 * profile.closedCount := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  have blocks : ∀ u ∈ profile.closedNeighbours,
      ((profile.outsideNeighbours u).toFinset.image
        fun z => ((u, z) : object.Vertex × object.Vertex)).card = 2 := by
    intro u member
    rw [Finset.card_image_of_injective _ (fun a b same => (Prod.mk.injEq ..).mp same |>.2),
      List.toFinset_card_of_nodup (profile.outsideNeighbours_nodup u),
      outsideNeighbours_length member]
  rw [incidences, Finset.card_biUnion, Finset.sum_congr rfl blocks,
    Finset.sum_const, smul_eq_mul, closedCount, Nat.mul_comm]
  intro u uMember v vMember distinct
  refine disjoint_of_fst distinct _ _ ?_ ?_ <;>
    · intro e member
      obtain ⟨z, -, rfl⟩ := Finset.mem_image.1 member
      rfl

/-- **The disjointness step of `lem:typeB-hybrid-incidence-budget`.**  The
`2c(𝔉)` non-`h` incidences of the cubic-closed neighbours of `h` are pairwise
distinct carriers, in the strong form: the whole family is determined by its
outside endpoint.

The manuscript's argument is exactly the one used here.  If a non-`h` vertex `z`
were incident with two distinct cubic-closed neighbours `u` and `v`, then
`u - h - v - z - u` would be a four-cycle; that configuration is excluded by
`NormalForm.noCommonNeighbourOutside`, i.e. by the target avoidance already
carried on the residual, and *not* by any hypothesis of this theorem. -/
theorem incidences_endpoint_injective (profile : Profile object)
    (normal : NormalForm object profile.marked.fan.hub)
    {e f : object.Vertex × object.Vertex}
    (eMember : e ∈ profile.incidences) (fMember : f ∈ profile.incidences)
    (sameEndpoint : e.2 = f.2) : e = f := by
  obtain ⟨eClosed, eOutside⟩ := (mem_incidences_iff profile e).1 eMember
  obtain ⟨fClosed, fOutside⟩ := (mem_incidences_iff profile f).1 fMember
  obtain ⟨eNeHub, eAdj⟩ := (mem_outsideNeighbours_iff profile e.1 e.2).1 eOutside
  obtain ⟨-, fAdj⟩ := (mem_outsideNeighbours_iff profile f.1 f.2).1 fOutside
  by_cases sameOwner : e.1 = f.1
  · exact Prod.ext sameOwner sameEndpoint
  · exfalso
    have fAdj' : object.graph.Adj f.1 e.2 := by rw [sameEndpoint]; exact fAdj
    exact normal.noCommonNeighbourOutside
      (hub_adj_of_mem_closedNeighbours eClosed)
      (hub_adj_of_mem_closedNeighbours fClosed) sameOwner eNeHub eAdj fAdj'

/-- Distinct cubic-closed neighbours share no non-`h` endpoint: the manuscript's
own phrasing of the previous theorem. -/
theorem outsideNeighbours_disjoint (profile : Profile object)
    (normal : NormalForm object profile.marked.fan.hub)
    {u v : object.Vertex} (uMember : u ∈ profile.closedNeighbours)
    (vMember : v ∈ profile.closedNeighbours) (distinct : u ≠ v)
    {z : object.Vertex} (uIncidence : z ∈ profile.outsideNeighbours u)
    (vIncidence : z ∈ profile.outsideNeighbours v) : False := by
  have equal :
      ((u, z) : object.Vertex × object.Vertex) = (v, z) :=
    incidences_endpoint_injective profile normal
      ((mem_incidences_iff profile (u, z)).2 ⟨uMember, uIncidence⟩)
      ((mem_incidences_iff profile (v, z)).2 ⟨vMember, vIncidence⟩) rfl
  exact distinct ((Prod.mk.injEq ..).mp equal).1

/-- The packed-window incidence carriers of `def:typeB-ledger-carriers` (c). -/
def windowIncidences (profile : Profile object) :
    Finset (object.Vertex × object.Vertex) :=
  profile.incidences.filter fun e => profile.IsWindowIncidence e.1 e.2

/-- The non-window fan incidence carriers of `def:typeB-ledger-carriers` (d). -/
def nonWindowIncidences (profile : Profile object) :
    Finset (object.Vertex × object.Vertex) :=
  profile.incidences.filter fun e => profile.IsNonWindowIncidence e.1 e.2

private theorem card_filter_block (profile : Profile object)
    (u : object.Vertex) (P : object.Vertex → object.Vertex → Prop)
    [∀ a b, Decidable (P a b)] :
    letI : DecidableEq object.Vertex := object.vertices.decEq
    (((profile.outsideNeighbours u).toFinset.image
        fun z => ((u, z) : object.Vertex × object.Vertex)).filter
      fun e => P e.1 e.2).card
      = (profile.outsideNeighbours u).countP fun z => decide (P u z) := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  rw [Finset.filter_image,
    Finset.card_image_of_injective _ (fun a b same => (Prod.mk.injEq ..).mp same |>.2),
    List.countP_eq_length_filter,
    ← List.toFinset_card_of_nodup
      ((profile.outsideNeighbours_nodup u).filter _),
    List.toFinset_filter]
  simp

private theorem card_incidences_filter (profile : Profile object)
    (P : object.Vertex → object.Vertex → Prop) [∀ a b, Decidable (P a b)] :
    (profile.incidences.filter fun e => P e.1 e.2).card
      = ∑ u ∈ profile.closedNeighbours,
          (profile.outsideNeighbours u).countP fun z => decide (P u z) := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  rw [incidences, Finset.filter_biUnion, Finset.card_biUnion]
  · exact Finset.sum_congr rfl fun u _ => card_filter_block profile u P
  · intro u uMember v vMember distinct
    refine disjoint_of_fst distinct _ _ ?_ ?_ <;>
      · intro e member
        obtain ⟨z, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_filter.1 member).1
        rfl

/-- The window incidences of the fan number exactly `I_W(𝔉) = 2c_W + c_M`. -/
theorem card_windowIncidences {profile : Profile object}
    :
    profile.windowIncidences.card = profile.windowIncidenceTotal := by
  rw [windowIncidences,
    card_incidences_filter profile fun a b => profile.IsWindowIncidence a b]
  exact sum_windowIncidenceCount

/-- The non-window fan incidences of the fan number exactly
`I_N(𝔉) = c_M + 2c_I`. -/
theorem card_nonWindowIncidences {profile : Profile object}
    :
    profile.nonWindowIncidences.card = profile.nonWindowIncidenceTotal := by
  rw [nonWindowIncidences,
    card_incidences_filter profile fun a b => profile.IsNonWindowIncidence a b]
  exact sum_nonWindowIncidenceCount

/-! ## `def:typeB-hybrid-incidence`: the hybrid ledger -/

/-- Half-credit supplied by the packed-window incidences: `½ I_W(𝔉)`. -/
def windowCredit (profile : Profile object) : ℚ :=
  (profile.windowIncidenceTotal : ℚ) / 2

/-- Half-credit available on the non-window fan incidences: `½ I_N(𝔉)`. -/
def nonWindowCredit (profile : Profile object) : ℚ :=
  (profile.nonWindowIncidenceTotal : ℚ) / 2

/-- `def:typeB-hybrid-incidence`: the hybrid non-window demand
`D_N(𝔉) = max{0, D_B(𝔉) - ½ I_W(𝔉)}`. -/
def hybridNonWindowDemand (profile : Profile object)
    (ledger : LoadCapacityProfile) : ℚ :=
  max 0 (profile.closedNeighbourDeficit ledger - profile.windowCredit)

/-- `def:typeB-candidate-ledger` (b): the capacity of the hybrid fan entry --
all the packed-window half-credit, plus exactly enough non-window half-credit to
cover the remaining demand `D_N(𝔉)`. -/
def hybridCapacity (profile : Profile object)
    (ledger : LoadCapacityProfile) : ℚ :=
  profile.windowCredit + profile.hybridNonWindowDemand ledger

/-- The total local incidence capacity is `½ I_W + ½ I_N = c(𝔉)`. -/
theorem windowCredit_add_nonWindowCredit {profile : Profile object}
    :
    profile.windowCredit + profile.nonWindowCredit
      = (profile.closedCount : ℚ) := by
  have totals : profile.windowIncidenceTotal + profile.nonWindowIncidenceTotal
      = 2 * profile.closedCount :=
    windowIncidenceTotal_add_nonWindowIncidenceTotal (profile := profile)
  have cast : (profile.windowIncidenceTotal : ℚ)
      + (profile.nonWindowIncidenceTotal : ℚ) = 2 * (profile.closedCount : ℚ) := by
    exact_mod_cast congrArg (fun n : Nat => (n : ℚ)) totals
  simp only [windowCredit, nonWindowCredit]
  linarith

/-- The manuscript's "Equivalently" clause of `def:typeB-hybrid-incidence`:
`D_N(𝔉) = max{0, ½ I_N(𝔉) - (3 - (k+1)α)}`, which at `α = 1/4` is the
manuscript's `max{0, ½ I_N(𝔉) - (11-k)/4}`.

This is not a restatement by definitional unfolding: the left-hand side is
built from `D_B` and the window credit, the right-hand side from the non-window
credit and the fan credit, and the two are matched by `I_W + I_N = 2c`. -/
theorem hybridNonWindowDemand_eq {profile : Profile object}
    (ledger : LoadCapacityProfile) :
    profile.hybridNonWindowDemand ledger
      = max 0 (profile.nonWindowCredit
          - (3 - ((object.degree profile.marked.fan.hub : ℚ) + 1)
              * ledger.dischargeRate)) := by
  have total := windowCredit_add_nonWindowCredit (profile := profile)
  have deficit : profile.closedNeighbourDeficit ledger
      = (profile.closedCount : ℚ)
        - (3 - ((object.degree profile.marked.fan.hub : ℚ) + 1)
            * ledger.dischargeRate) := rfl
  rw [hybridNonWindowDemand, deficit]
  congr 1
  linarith

/-! ## `lem:typeB-hybrid-incidence-budget` -/

/-- **`lem:typeB-hybrid-incidence-budget`**, manuscript node `[74]`.

Let `𝔉` be a Type B fan-window profile at a certificate-marked centre `h`,
recording its cubic-closed neighbours on the remainder side.  Then:

* the `2c(𝔉)` non-`h` incidences of the cubic-closed neighbours are pairwise
  distinct local carriers, and no two of them share an outside endpoint;
* they split into exactly `I_W(𝔉)` window incidences and `I_N(𝔉)` non-window
  fan incidences;
* the half-credit they carry totals `½ I_W + ½ I_N = c(𝔉)`, which pays
  `D_B(𝔉)` with slack `3 - (k+1)α ≥ 3 - 9α`;
* after the window half-credit is applied, the non-window half-credit still
  available, `½ I_N(𝔉)`, is at least the remaining demand `D_N(𝔉)`.

The degree cap `k ≤ 8` is `Marked.degree_le_eight`, derived from the fan
certificate; it is not assumed.  The four-cycle exclusion behind the
disjointness is `NormalForm`, not a hypothesis of this statement.

The slack clause is generic: it reduces to `(k+1)α ≤ 9α`, i.e. to the degree
cap alone.  The final clause is the one that reads the recorded fan-credit
constraint `ReceiverLoad.LoadCapacityProfile.dischargeRate_le` (`9α ≤ 3`): its
live branch is `D_B(𝔉) ≤ c(𝔉)`, that is, the fan credit `3 - (k+1)α` is
nonnegative, and `k = 8` is exactly where that is sharpest.  At `α = 1/4` the
slack is the manuscript's `(11-k)/4 ≥ 3/4`. -/
theorem typeBHybridIncidenceBudget (profile : Profile object)
    (ledger : LoadCapacityProfile)
    (normal : NormalForm object profile.marked.fan.hub)
    :
    profile.incidences.card = 2 * profile.closedCount ∧
      (∀ e ∈ profile.incidences, ∀ f ∈ profile.incidences, e.2 = f.2 → e = f) ∧
      profile.windowIncidences.card = profile.windowIncidenceTotal ∧
      profile.nonWindowIncidences.card = profile.nonWindowIncidenceTotal ∧
      profile.windowCredit + profile.nonWindowCredit
          = (profile.closedCount : ℚ) ∧
      profile.closedNeighbourDeficit ledger + (3 - 9 * ledger.dischargeRate)
          ≤ profile.windowCredit + profile.nonWindowCredit ∧
      profile.hybridNonWindowDemand ledger ≤ profile.nonWindowCredit := by
  have total := windowCredit_add_nonWindowCredit (profile := profile)
  have cap : (object.degree profile.marked.fan.hub : ℚ) ≤ 8 := by
    exact_mod_cast profile.marked.degree_le_eight
  have rateNonneg := ledger.dischargeRate_nonneg
  have credit := ledger.nine_mul_dischargeRate_le_three
  have degreeRate :
      ((object.degree profile.marked.fan.hub : ℚ) + 1) * ledger.dischargeRate
        ≤ 9 * ledger.dischargeRate :=
    mul_le_mul_of_nonneg_right (by linarith) rateNonneg
  have deficit : profile.closedNeighbourDeficit ledger
      = (profile.closedCount : ℚ)
        - (3 - ((object.degree profile.marked.fan.hub : ℚ) + 1)
            * ledger.dischargeRate) := rfl
  have windowNonneg : (0 : ℚ) ≤ profile.windowCredit := by
    have : (0 : ℚ) ≤ (profile.windowIncidenceTotal : ℚ) := by positivity
    simp only [windowCredit]
    linarith
  have nonWindowNonneg : (0 : ℚ) ≤ profile.nonWindowCredit := by
    have : (0 : ℚ) ≤ (profile.nonWindowIncidenceTotal : ℚ) := by positivity
    simp only [nonWindowCredit]
    linarith
  refine ⟨card_incidences profile, ?_, card_windowIncidences,
    card_nonWindowIncidences, total, by rw [deficit]; linarith, ?_⟩
  · intro e eMember f fMember same
    exact incidences_endpoint_injective profile normal eMember fMember same
  · rw [hybridNonWindowDemand, max_le_iff]
    exact ⟨nonWindowNonneg, by rw [deficit]; linarith⟩

/-! ## `lem:typeB-hybrid-B1` -/

/-- **`lem:typeB-hybrid-B1`**, manuscript node `[74]`.

The packed-window incidences together with the local internal/mixed incidence
reserve form a fan ledger entry of total capacity at least `D_B(𝔉)`, and the
reserve it calls for is genuinely available: `D_N(𝔉) ≤ ½ I_N(𝔉)`, on carriers
that are pairwise distinct.

`hybridCapacity` is `½ I_W + D_N`; the inequality `D_B ≤ ½ I_W + D_N` is a
genuine case split on the `max` in `D_N`, not an unfolding. -/
theorem typeBHybridB1 (profile : Profile object)
    (ledger : LoadCapacityProfile)
    (normal : NormalForm object profile.marked.fan.hub)
    :
    profile.closedNeighbourDeficit ledger ≤ profile.hybridCapacity ledger ∧
      profile.hybridNonWindowDemand ledger ≤ profile.nonWindowCredit ∧
      profile.windowIncidences.card + profile.nonWindowIncidences.card
          = 2 * profile.closedCount ∧
      (∀ e ∈ profile.incidences, ∀ f ∈ profile.incidences,
        e.2 = f.2 → e = f) := by
  obtain ⟨-, injective, windowCard, nonWindowCard, -, -, feasible⟩ :=
    typeBHybridIncidenceBudget profile ledger normal
  refine ⟨?_, feasible, ?_, injective⟩
  · rw [hybridCapacity, hybridNonWindowDemand]
    rcases le_or_gt (profile.closedNeighbourDeficit ledger - profile.windowCredit) 0
      with small | large
    · rw [max_eq_left small]; linarith
    · rw [max_eq_right large.le]; linarith
  · rw [windowCard, nonWindowCard]
    exact windowIncidenceTotal_add_nonWindowIncidenceTotal

end Profile

/-! ## Clause (c) of `prop:fan-closed-port-typeB-routing` -/

/-- **`prop:fan-closed-port-typeB-routing`, clause (c)**, manuscript node
`[72]` closed by node `[74]`.

At a certificate-marked centre `h` carrying a family `𝒬` of `r ≥ 2` fan-closed
surplus ports, the hybrid B1 ledger supplies local incidence capacity at least
`D_B(𝔉_h)`, and the paying incidences include the two non-`h` incidences
`x a_p` and `x b_p` of every fan-closed port `p = (h, x) ∈ 𝒬`, each classified
by `def:typeB-window-incidence-profile` as a window incidence or a non-window
fan incidence.

Parts (a) and (b) are `fanClosedPortTypeBRouting`; this completes the
proposition's local content. -/
theorem fanClosedPortHybridEntry (profile : Profile object)
    (ledger : LoadCapacityProfile)
    (normal : NormalForm object profile.marked.fan.hub)
    {ports : Finset object.Vertex}
    (fanClosed : ∀ vertex ∈ ports, ∃ p : Port object,
      p.endpoint = vertex ∧ profile.IsFanClosed p)
    (two : 2 ≤ ports.card) :
    profile.closedNeighbourDeficit ledger ≤ profile.hybridCapacity ledger ∧
      ((object.degree profile.marked.fan.hub : ℚ) + 1) * ledger.dischargeRate - 1
          ≤ profile.closedNeighbourDeficit ledger ∧
      0 < profile.closedNeighbourDeficit ledger ∧
      (∀ p : Port object, profile.IsFanClosed p → ∀ shoulder ∈ p.shoulders,
        (p.endpoint, shoulder) ∈ profile.incidences ∧
          ((p.endpoint, shoulder) ∈ profile.windowIncidences ∨
            (p.endpoint, shoulder) ∈ profile.nonWindowIncidences)) := by
  obtain ⟨-, -, deficitBound, positive⟩ :=
    fanClosedPortTypeBRouting profile ledger normal fanClosed two
  obtain ⟨capacity, -, -, -⟩ := Profile.typeBHybridB1 profile ledger normal
  refine ⟨capacity, deficitBound, positive, ?_⟩
  intro p closed shoulder member
  have owner : p.endpoint ∈ profile.closedNeighbours :=
    Profile.mem_closedNeighbours_of_isFanClosed normal closed
  have incidence : shoulder ∈ profile.outsideNeighbours p.endpoint := by
    rw [Profile.outsideNeighbours_eq_shoulders closed.center]
    exact member
  have carrier : (p.endpoint, shoulder) ∈ profile.incidences :=
    (Profile.mem_incidences_iff profile (p.endpoint, shoulder)).2 ⟨owner, incidence⟩
  refine ⟨carrier, ?_⟩
  rcases closed.incidence_classified member with window | nonWindow
  · exact Or.inl (Finset.mem_filter.2 ⟨carrier, window⟩)
  · exact Or.inr (Finset.mem_filter.2 ⟨carrier, nonWindow⟩)

/-! ## Non-vacuity

The witness graph of `TypeBFanClosedPorts.Witness` is reused, now with a
packed-window union that actually meets the fan: it carries both non-`h`
incidences of the neighbour `1`, exactly one of the two non-`h` incidences of
`2`, and neither incidence of `3` and `4`.  All three support classes of
`def:typeB-hybrid-incidence` are therefore nonempty, `I_W` and `I_N` are both
nonzero, and the hybrid demand `D_N` is a strictly positive proper part of
`D_B`, so the ledger inequality proved above is not attained by a degenerate
`I_W = 0` or `D_N = 0` configuration. -/


namespace Witness

local instance vertexDecEq : DecidableEq fanObject.Vertex :=
  inferInstanceAs (DecidableEq (Fin 13))

local instance vertexFintype : Fintype fanObject.Vertex :=
  inferInstanceAs (Fintype (Fin 13))

local instance adjDecidable : DecidableRel fanObject.graph.Adj := fanObject.decideAdj

/-- The four fan neighbours of the witness centre. -/
def rimOne : fanObject.Vertex := (1 : Fin 13)
/-- The second fan neighbour. -/
def rimTwo : fanObject.Vertex := (2 : Fin 13)
/-- The third fan neighbour. -/
def rimThree : fanObject.Vertex := (3 : Fin 13)
/-- The fourth fan neighbour. -/
def rimFour : fanObject.Vertex := (4 : Fin 13)
/-- Both shoulders of `rimOne` lie in the packed-window union. -/
def winFive : fanObject.Vertex := (5 : Fin 13)
/-- The second shoulder of `rimOne`. -/
def winSix : fanObject.Vertex := (6 : Fin 13)
/-- One of the two shoulders of `rimTwo`. -/
def winSeven : fanObject.Vertex := (7 : Fin 13)

/-- A packed-window union meeting the fan: `winFive` and `winSix` are the two
shoulders of the fan neighbour `rimOne`, and `winSeven` is one of the two
shoulders of `rimTwo`. -/
def hybridWindow : Finset fanObject.Vertex := {winFive, winSix, winSeven}

/-- The assigned profile whose window union is `hybridWindow`. -/
def hybridProfile : Profile fanObject where
  marked := markedFan
  window := hybridWindow
  envelope := fanObject.vertexFinset

theorem hybridProfile_window : hybridProfile.window = hybridWindow := rfl

/-- `N(h) = {1, 2, 3, 4}` in the witness. -/
theorem adj_hub_iff (vertex : fanObject.Vertex) :
    fanObject.graph.Adj hub vertex ↔
      (vertex = rimOne ∨ vertex = rimTwo ∨ vertex = rimThree ∨
        vertex = rimFour) := by
  revert vertex
  decide

theorem hub_adj_of_mem_rim {vertex : fanObject.Vertex}
    (member : vertex ∈ hybridProfile.marked.fan.rim) :
    fanObject.graph.Adj hub vertex :=
  (hybridProfile.marked.rim_eq_neighbourhood vertex).1 member

theorem mem_rim_of_hub_adj {vertex : fanObject.Vertex}
    (adjacency : fanObject.graph.Adj hub vertex) :
    vertex ∈ hybridProfile.marked.fan.rim :=
  (hybridProfile.marked.rim_eq_neighbourhood vertex).2 adjacency

/-- The fan rim of the witness. -/
theorem hybrid_rim :
    hybridProfile.marked.fan.rim
      = ({rimOne, rimTwo, rimThree, rimFour} : Finset fanObject.Vertex) := by
  ext vertex
  simp only [Finset.mem_insert, Finset.mem_singleton]
  exact ⟨fun member => (adj_hub_iff vertex).1 (hub_adj_of_mem_rim member),
    fun member => mem_rim_of_hub_adj ((adj_hub_iff vertex).2 member)⟩

/-- Every fan neighbour of the witness is cubic-closed: the assigned envelope
carries the whole vertex schedule. -/
theorem hybrid_closedNeighbours :
    hybridProfile.closedNeighbours = hybridProfile.marked.fan.rim := by
  classical
  refine Finset.filter_true_of_mem ?_
  intro vertex member
  have separated : ∀ v : fanObject.Vertex, fanObject.graph.Adj hub v →
      ¬ (v = winFive ∨ v = winSix ∨ v = winSeven) := by decide
  have outside : vertex ∉ hybridProfile.window := by
    simp only [hybridProfile_window, hybridWindow, Finset.mem_insert,
      Finset.mem_singleton]
    exact separated vertex (hub_adj_of_mem_rim member)
  exact ⟨⟨member, fanNormalForm.neighbourCubic (hub_adj_of_mem_rim member),
      fun other _ _ => fanObject.mem_vertexFinset other⟩,
    (Profile.mem_remainder_iff vertex).2 ⟨member, outside⟩⟩

theorem hybrid_closedCount : hybridProfile.closedCount = 4 := by
  rw [Profile.closedCount, hybrid_closedNeighbours,
    hybridProfile.marked.rim_card_eq_degree]
  exact degree_hub


/-! The window-incidence counts of the four fan neighbours: `rimOne` is
window-supported, `rimTwo` is mixed-supported, and `rimThree`, `rimFour` are
internal-supported. -/

theorem count_rimOne : hybridProfile.windowIncidenceCount rimOne = 2 := by decide

theorem count_rimTwo : hybridProfile.windowIncidenceCount rimTwo = 1 := by decide

theorem count_rimThree : hybridProfile.windowIncidenceCount rimThree = 0 := by
  decide

theorem count_rimFour : hybridProfile.windowIncidenceCount rimFour = 0 := by
  decide

theorem nonWindowCount_rimOne :
    hybridProfile.nonWindowIncidenceCount rimOne = 0 := by decide

theorem nonWindowCount_rimTwo :
    hybridProfile.nonWindowIncidenceCount rimTwo = 1 := by decide

theorem nonWindowCount_rimThree :
    hybridProfile.nonWindowIncidenceCount rimThree = 2 := by decide

theorem nonWindowCount_rimFour :
    hybridProfile.nonWindowIncidenceCount rimFour = 2 := by decide

theorem hybrid_windowSupported :
    hybridProfile.windowSupported = ({rimOne} : Finset fanObject.Vertex) := by
  ext vertex
  rw [Profile.windowSupported, Finset.mem_filter, hybrid_closedNeighbours,
    hybrid_rim]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨rimMember, count⟩
    rcases rimMember with rfl | rfl | rfl | rfl
    · rfl
    · rw [count_rimTwo] at count; exact absurd count (by decide)
    · rw [count_rimThree] at count; exact absurd count (by decide)
    · rw [count_rimFour] at count; exact absurd count (by decide)
  · rintro rfl
    exact ⟨Or.inl rfl, count_rimOne⟩

theorem hybrid_mixedSupported :
    hybridProfile.mixedSupported = ({rimTwo} : Finset fanObject.Vertex) := by
  ext vertex
  rw [Profile.mixedSupported, Finset.mem_filter, hybrid_closedNeighbours,
    hybrid_rim]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨rimMember, count⟩
    rcases rimMember with rfl | rfl | rfl | rfl
    · rw [count_rimOne] at count; exact absurd count (by decide)
    · rfl
    · rw [count_rimThree] at count; exact absurd count (by decide)
    · rw [count_rimFour] at count; exact absurd count (by decide)
  · rintro rfl
    exact ⟨Or.inr (Or.inl rfl), count_rimTwo⟩

theorem hybrid_internalSupported :
    hybridProfile.internalSupported
      = ({rimThree, rimFour} : Finset fanObject.Vertex) := by
  ext vertex
  rw [Profile.internalSupported, Finset.mem_filter, hybrid_closedNeighbours,
    hybrid_rim]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨rimMember, count⟩
    rcases rimMember with rfl | rfl | rfl | rfl
    · rw [nonWindowCount_rimOne] at count; exact absurd count (by decide)
    · rw [nonWindowCount_rimTwo] at count; exact absurd count (by decide)
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨Or.inr (Or.inr (Or.inl rfl)), nonWindowCount_rimThree⟩
    · exact ⟨Or.inr (Or.inr (Or.inr rfl)), nonWindowCount_rimFour⟩

theorem hybrid_windowSupportedCount : hybridProfile.windowSupportedCount = 1 := by
  rw [Profile.windowSupportedCount, hybrid_windowSupported, Finset.card_singleton]

theorem hybrid_mixedSupportedCount : hybridProfile.mixedSupportedCount = 1 := by
  rw [Profile.mixedSupportedCount, hybrid_mixedSupported, Finset.card_singleton]

theorem hybrid_internalSupportedCount :
    hybridProfile.internalSupportedCount = 2 := by
  rw [Profile.internalSupportedCount, hybrid_internalSupported,
    Finset.card_pair (by decide : rimThree ≠ rimFour)]

theorem hybrid_windowIncidenceTotal :
    hybridProfile.windowIncidenceTotal = 3 := by
  rw [Profile.windowIncidenceTotal, hybrid_windowSupportedCount,
    hybrid_mixedSupportedCount]

theorem hybrid_nonWindowIncidenceTotal :
    hybridProfile.nonWindowIncidenceTotal = 5 := by
  rw [Profile.nonWindowIncidenceTotal, hybrid_mixedSupportedCount,
    hybrid_internalSupportedCount]

theorem hybrid_degree : fanObject.degree hybridProfile.marked.fan.hub = 4 :=
  degree_hub

/-- The ledger of `def:typeB-hybrid-incidence` evaluated on the witness:
`c = 4`, `k = 4`, `D_B = 1 + 5α`, `c_W = 1`, `c_M = 1`, `c_I = 2`, `I_W = 3`,
`I_N = 5`, `D_N = 5α - 1/2`, and the hybrid capacity is exactly
`1 + 5α = D_B`.  At the registered `α = 1/4` these are the manuscript's
`9/4`, `3/2`, `5/2`, `3/4` and `9/4`.

The demand is a genuine positive proper part of the deficit at every profile,
not only at the registered one: `D_N = 5α - 1/2 > 1/2` is exactly the recorded
`5α > 1` of `dischargeRate_gt`. -/
theorem hybrid_ledger (ledger : LoadCapacityProfile) :
    hybridProfile.closedNeighbourDeficit ledger
        = 1 + 5 * ledger.dischargeRate ∧
      hybridProfile.windowCredit = 3 / 2 ∧
      hybridProfile.nonWindowCredit = 5 / 2 ∧
      hybridProfile.hybridNonWindowDemand ledger
        = 5 * ledger.dischargeRate - 1 / 2 ∧
      hybridProfile.hybridCapacity ledger = 1 + 5 * ledger.dischargeRate := by
  have sharp := ledger.one_lt_five_mul_dischargeRate
  have deficit : hybridProfile.closedNeighbourDeficit ledger
      = 1 + 5 * ledger.dischargeRate := by
    rw [Profile.closedNeighbourDeficit, hybrid_closedCount, hybrid_degree]
    push_cast
    ring
  have window : hybridProfile.windowCredit = 3 / 2 := by
    rw [Profile.windowCredit, hybrid_windowIncidenceTotal]
    norm_num
  have nonWindow : hybridProfile.nonWindowCredit = 5 / 2 := by
    rw [Profile.nonWindowCredit, hybrid_nonWindowIncidenceTotal]
    norm_num
  have demand : hybridProfile.hybridNonWindowDemand ledger
      = 5 * ledger.dischargeRate - 1 / 2 := by
    rw [Profile.hybridNonWindowDemand, deficit, window,
      max_eq_right (by linarith)]
    ring
  exact ⟨deficit, window, nonWindow, demand, by
    rw [Profile.hybridCapacity, window, demand]; ring⟩

/-- `lem:typeB-hybrid-incidence-budget` and `lem:typeB-hybrid-B1` fire on the
witness, on a profile in which all three support classes of
`def:typeB-hybrid-incidence` occur, so neither `I_W = 0` nor `D_N = 0`
trivialises the ledger inequality. -/
theorem hybridB1_fires (ledger : LoadCapacityProfile) :
    hybridProfile.closedNeighbourDeficit ledger
        ≤ hybridProfile.hybridCapacity ledger ∧
      hybridProfile.hybridNonWindowDemand ledger
        ≤ hybridProfile.nonWindowCredit ∧
      hybridProfile.windowIncidences.card
          + hybridProfile.nonWindowIncidences.card
        = 2 * hybridProfile.closedCount ∧
      0 < hybridProfile.windowSupportedCount ∧
      0 < hybridProfile.mixedSupportedCount ∧
      0 < hybridProfile.internalSupportedCount := by
  obtain ⟨capacity, feasible, split, -⟩ :=
    Profile.typeBHybridB1 hybridProfile ledger fanNormalForm
  refine ⟨capacity, feasible, split, ?_, ?_, ?_⟩
  · rw [hybrid_windowSupportedCount]; omega
  · rw [hybrid_mixedSupportedCount]; omega
  · rw [hybrid_internalSupportedCount]; omega

end Witness

end Hypostructure.Graph.TypeBFanClosedPorts
