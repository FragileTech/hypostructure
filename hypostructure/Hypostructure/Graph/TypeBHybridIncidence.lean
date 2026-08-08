import Hypostructure.Graph.TypeBFanIncidence

/-!
# The hybrid fan-window incidence ledger

`def:typeB-window-incidence-profile`, `def:typeB-hybrid-incidence`,
`lem:typeB-hybrid-incidence-budget` and `lem:typeB-hybrid-B1`: the local half of
the Type B bridge, node `[74]`/`[82]`.

A positive-deficit marked fan at `h` has to pay its own closed-neighbour deficit
`D_B` out of local carriers, and the carriers it has are the non-`h` incidences of
its cubic-closed neighbours.  Each such incidence is a *window incidence* when its
far endpoint lies in the packed-window union `W` and a *non-window fan incidence*
otherwise, and each carries half-credit.  Writing `I_W` and `I_N` for the two
counts, the ledger pays

  `½·I_W + ½·I_N = ½·(δ−1)·c ≥ c ≥ D_B + (δ − (k+1)α) ≥ D_B`,

the middle step because a cubic-closed neighbour has `δ − 1 ≥ 2` non-`h`
incidences, and the last because the marked-fan cap keeps the slack
`δ − (k+1)α` nonnegative.  The manuscript's own display is the `δ = 3` case:
`½I_W + ½I_N = ½·2c = c` with slack `(11−k)/4 ≥ 3/4`.

## The one thing that has to be proved

That the carriers really are *distinct*.  If a vertex `z ≠ h` were incident with
two distinct cubic-closed neighbours `u, v`, the same reserve unit would be spent
twice — and the manuscript's answer is that this cannot happen, because
`u − h − v − z − u` is a quadrilateral and the selected object avoids it.  That is
`endpoints_not_shared`, and it is the only place this module looks at the graph
rather than at arithmetic.

## Scale

Half-credits, so every comparison is carried at `2s` — the same scale
`TypeBRefinedSupport.CandidateEntry.pays` uses, which is what lets a hybrid entry
be *that* structure's `chosen` field.  No reciprocal appears and nothing rounds.
-/

namespace Hypostructure.Graph.TypeBHybridIncidence

open Hypostructure
open Hypostructure.Graph.TypeBFanIncidence

universe u

variable {object : FiniteObject.{u}}

open scoped Classical

/-! ## `def:typeB-window-incidence-profile`: the two non-`h` incidences -/

/-- **The non-`h` incidences of a fan neighbour**: its neighbours other than the
centre.  For a cubic-closed neighbour these are the manuscript's `xa_p` and
`xb_p`. -/
noncomputable def nonHubIncidences (object : FiniteObject.{u})
    (centre owner : object.Vertex) : Finset object.Vertex :=
  ((object.orderedNeighbors owner).toFinset).erase centre

theorem mem_nonHubIncidences_iff {centre owner other : object.Vertex} :
    other ∈ nonHubIncidences object centre owner ↔
      other ≠ centre ∧ object.graph.Adj owner other := by
  simp [nonHubIncidences, object.mem_orderedNeighbors_iff]

/-- **A cubic-closed neighbour has exactly `δ − 1` non-`h` incidences.**  It sits
at the baseline and the centre is one of its neighbours. -/
theorem card_nonHubIncidences {threshold : Nat}
    {envelope : Finset object.Vertex} {centre owner : object.Vertex}
    (closed : IsCubicClosed object threshold envelope centre owner) :
    (nonHubIncidences object centre owner).card = threshold - 1 := by
  obtain ⟨adjacent, cubic, _assigned⟩ := closed
  have member : centre ∈ (object.orderedNeighbors owner).toFinset := by
    simp [object.mem_orderedNeighbors_iff, adjacent.symm]
  have total : (object.orderedNeighbors owner).toFinset.card = threshold := by
    rw [List.toFinset_card_of_nodup (object.orderedNeighbors_nodup owner),
      object.orderedNeighbors_length owner, cubic]
  rw [nonHubIncidences, Finset.card_erase_of_mem member, total]

/-! ## `def:typeB-hybrid-incidence`: `I_W` and `I_N` -/

/-- **`I_W(𝔉)`**, the window-incidence count: the non-`h` incidences of the
cubic-closed neighbours whose far endpoint lies in the packed-window union. -/
noncomputable def windowIncidences (object : FiniteObject.{u}) (threshold : Nat)
    (envelope windowSupport : Finset object.Vertex) (centre : object.Vertex) :
    Nat :=
  ∑ owner ∈ closedNeighbours object threshold envelope centre,
    ((nonHubIncidences object centre owner) ∩ windowSupport).card

/-- **`I_N(𝔉)`**, the non-window fan-incidence count. -/
noncomputable def nonWindowIncidences (object : FiniteObject.{u})
    (threshold : Nat) (envelope windowSupport : Finset object.Vertex)
    (centre : object.Vertex) : Nat :=
  ∑ owner ∈ closedNeighbours object threshold envelope centre,
    ((nonHubIncidences object centre owner) \ windowSupport).card

/-- **`I_W + I_N = (δ − 1)·c`.**

Every non-`h` incidence is a window incidence or a non-window one and not both,
so the two counts split the `(δ − 1)·c` incidences the cubic-closed neighbours
carry.  At the manuscript's `δ = 3` this is its `2c`. -/
theorem windowIncidences_add_nonWindowIncidences (object : FiniteObject.{u})
    (threshold : Nat) (envelope windowSupport : Finset object.Vertex)
    (centre : object.Vertex) :
    windowIncidences object threshold envelope windowSupport centre +
        nonWindowIncidences object threshold envelope windowSupport centre =
      (threshold - 1) * closedCount object threshold envelope centre := by
  rw [windowIncidences, nonWindowIncidences, ← Finset.sum_add_distrib]
  rw [closedCount, Finset.card_eq_sum_ones, Finset.mul_sum]
  refine Finset.sum_congr rfl fun owner member => ?_
  have closed : IsCubicClosed object threshold envelope centre owner :=
    mem_closedNeighbours_iff.mp member
  rw [Finset.card_inter_add_card_sdiff, card_nonHubIncidences closed,
    Nat.mul_one]

/-! ## The canonical finite incidence carrier -/

/-- The paper's actual non-hub incidence carriers, with the same packed-window
support that classifies them into `I_W` and `I_N`.  The support parameter is
part of the carrier's type-level provenance even though the union of the two
classes is independent of which side an endpoint lies on. -/
noncomputable def incidences (object : FiniteObject.{u}) (threshold : Nat)
    (envelope windowSupport : Finset object.Vertex) (centre : object.Vertex) :
    Finset (object.Vertex × object.Vertex) := by
  classical
  exact (closedNeighbours object threshold envelope centre).biUnion fun owner =>
    (nonHubIncidences object centre owner).image fun other => (owner, other)

/-- Membership in the canonical carrier is exactly ownership by a cubic-closed
fan neighbour and membership in that owner's non-hub incidence set. -/
theorem mem_incidences_iff (object : FiniteObject.{u}) (threshold : Nat)
    (envelope windowSupport : Finset object.Vertex) (centre : object.Vertex)
    (incidence : object.Vertex × object.Vertex) :
    incidence ∈ incidences object threshold envelope windowSupport centre ↔
      incidence.1 ∈ closedNeighbours object threshold envelope centre ∧
        incidence.2 ∈ nonHubIncidences object centre incidence.1 := by
  classical
  constructor
  · intro member
    rw [incidences, Finset.mem_biUnion] at member
    obtain ⟨owner, ownerMember, imageMember⟩ := member
    obtain ⟨other, otherMember, equal⟩ := Finset.mem_image.mp imageMember
    rw [← equal]
    exact ⟨ownerMember, otherMember⟩
  · rintro ⟨ownerMember, otherMember⟩
    rw [incidences, Finset.mem_biUnion]
    exact ⟨incidence.1, ownerMember,
      Finset.mem_image.mpr ⟨incidence.2, otherMember, rfl⟩⟩

/-- The canonical carriers whose far endpoint lies in the packed-window union. -/
noncomputable def windowIncidenceSet (object : FiniteObject.{u}) (threshold : Nat)
    (envelope windowSupport : Finset object.Vertex) (centre : object.Vertex) :
    Finset (object.Vertex × object.Vertex) :=
  (incidences object threshold envelope windowSupport centre).filter
    (fun incidence => incidence.2 ∈ windowSupport)

/-- The canonical carriers whose far endpoint lies on the remainder side. -/
noncomputable def nonWindowIncidenceSet (object : FiniteObject.{u})
    (threshold : Nat) (envelope windowSupport : Finset object.Vertex)
    (centre : object.Vertex) : Finset (object.Vertex × object.Vertex) :=
  (incidences object threshold envelope windowSupport centre).filter
    (fun incidence => incidence.2 ∉ windowSupport)

/-- The two paper classes partition the canonical incidence carrier exactly. -/
theorem incidences_eq_window_union_nonWindow (object : FiniteObject.{u})
    (threshold : Nat) (envelope windowSupport : Finset object.Vertex)
    (centre : object.Vertex) :
    incidences object threshold envelope windowSupport centre =
      windowIncidenceSet object threshold envelope windowSupport centre ∪
        nonWindowIncidenceSet object threshold envelope windowSupport centre := by
  classical
  ext incidence
  by_cases window : incidence.2 ∈ windowSupport <;>
    simp [windowIncidenceSet, nonWindowIncidenceSet, window]

/-- The two sides of the packed-window partition are disjoint. -/
theorem windowIncidenceSet_disjoint_nonWindow (object : FiniteObject.{u})
    (threshold : Nat) (envelope windowSupport : Finset object.Vertex)
    (centre : object.Vertex) :
    Disjoint (windowIncidenceSet object threshold envelope windowSupport centre)
      (nonWindowIncidenceSet object threshold envelope windowSupport centre) := by
  classical
  rw [Finset.disjoint_left]
  intro incidence windowMember nonWindowMember
  exact (Finset.mem_filter.mp nonWindowMember).2
    (Finset.mem_filter.mp windowMember).2

private theorem incidenceBlocks_disjoint (object : FiniteObject.{u})
    {centre left right : object.Vertex} (different : left ≠ right) :
    Disjoint
      ((nonHubIncidences object centre left).image fun other => (left, other))
      ((nonHubIncidences object centre right).image fun other => (right, other)) := by
  classical
  rw [Finset.disjoint_left]
  intro incidence leftMember rightMember
  obtain ⟨leftOther, _, leftEqual⟩ := Finset.mem_image.mp leftMember
  obtain ⟨rightOther, _, rightEqual⟩ := Finset.mem_image.mp rightMember
  apply different
  exact congrArg Prod.fst (leftEqual.trans rightEqual.symm)

/-- The canonical carrier has exactly the two incidence counts recorded by the
paper: no incidence is omitted and none is counted twice. -/
theorem card_incidences_eq_window_add_nonWindow (object : FiniteObject.{u})
    (threshold : Nat) (envelope windowSupport : Finset object.Vertex)
    (centre : object.Vertex) :
    (incidences object threshold envelope windowSupport centre).card =
      windowIncidences object threshold envelope windowSupport centre +
        nonWindowIncidences object threshold envelope windowSupport centre := by
  classical
  have blockCard : ∀ owner ∈ closedNeighbours object threshold envelope centre,
      ((nonHubIncidences object centre owner).image
        fun other => (owner, other)).card = threshold - 1 := by
    intro owner ownerMember
    rw [Finset.card_image_of_injective _
      (fun left right equal => congrArg Prod.snd equal)]
    exact card_nonHubIncidences (mem_closedNeighbours_iff.mp ownerMember)
  calc
    (incidences object threshold envelope windowSupport centre).card =
        ∑ owner ∈ closedNeighbours object threshold envelope centre,
          ((nonHubIncidences object centre owner).image
            fun other => (owner, other)).card := by
      rw [incidences, Finset.card_biUnion]
      intro left _ right _ different
      exact incidenceBlocks_disjoint object different
    _ = (threshold - 1) *
        (closedNeighbours object threshold envelope centre).card := by
      rw [Finset.sum_congr rfl blockCard, Finset.sum_const, smul_eq_mul,
        Nat.mul_comm]
    _ = windowIncidences object threshold envelope windowSupport centre +
        nonWindowIncidences object threshold envelope windowSupport centre := by
      simpa [closedCount] using
        (windowIncidences_add_nonWindowIncidences object threshold envelope
          windowSupport centre).symm

/-- The cardinal partition follows from the literal disjoint union. -/
theorem card_incidences_eq_card_window_add_card_nonWindow
    (object : FiniteObject.{u}) (threshold : Nat)
    (envelope windowSupport : Finset object.Vertex) (centre : object.Vertex) :
    (incidences object threshold envelope windowSupport centre).card =
      (windowIncidenceSet object threshold envelope windowSupport centre).card +
        (nonWindowIncidenceSet object threshold envelope windowSupport centre).card := by
  rw [incidences_eq_window_union_nonWindow object threshold envelope windowSupport
      centre,
    Finset.card_union_of_disjoint
      (windowIncidenceSet_disjoint_nonWindow object threshold envelope
        windowSupport centre)]

/-! ## `lem:typeB-hybrid-incidence-budget`, first paragraph

The carriers are distinct.  This is the only graph-theoretic step of the module,
and it is the manuscript's own: a shared endpoint is a quadrilateral. -/

/-- **No vertex other than the centre is incident with two distinct cubic-closed
neighbours.**

`u − h − v − z − u` is a simple `4`-cycle: `u ≠ v` by hypothesis, `z ≠ h` by
hypothesis, and the remaining distinctness is adjacency.  An object avoiding the
accepted lengths carries none, once the quadrilateral is accepted. -/
theorem endpoints_not_shared {LengthOK : Nat → Prop} {threshold : Nat}
    {envelope : Finset object.Vertex} {centre left right shared : object.Vertex}
    (avoids : ¬ HasCycleWithLength LengthOK object)
    (quadrilateralAccepted : LengthOK 4)
    (leftClosed : IsCubicClosed object threshold envelope centre left)
    (rightClosed : IsCubicClosed object threshold envelope centre right)
    (distinct : left ≠ right)
    (leftIncidence : shared ∈ nonHubIncidences object centre left)
    (rightIncidence : shared ∈ nonHubIncidences object centre right) : False := by
  obtain ⟨sharedNeCentre, leftAdjacent⟩ := mem_nonHubIncidences_iff.mp leftIncidence
  obtain ⟨-, rightAdjacent⟩ := mem_nonHubIncidences_iff.mp rightIncidence
  exact not_quadrilateral avoids quadrilateralAccepted
    leftClosed.1.symm rightClosed.1 rightAdjacent leftAdjacent.symm distinct
    (Ne.symm sharedNeCentre)

/-! ## `lem:typeB-hybrid-incidence-budget`, the payment -/

/-- **`s·D_B ≤ ½·s·(I_W + I_N)` at the scale `2s`: the hybrid entry pays.**

The two hypotheses are the manuscript's: `δ ≥ 3`, so a cubic-closed neighbour
carries at least two incidences, and the marked-fan slack `k + 1 ≤ s·δ`, which is
where `k ≤ α(D)` is spent — the manuscript's "and `k ≤ 8`, this total capacity
pays `D_B` with slack at least `(11−k)/4 ≥ 3/4`". -/
theorem hybridCapacity_pays (object : FiniteObject.{u})
    (threshold dischargeScale : Nat)
    (envelope windowSupport : Finset object.Vertex) (centre : object.Vertex)
    (baseline : 3 ≤ threshold)
    (slack : object.degree centre + 1 ≤ dischargeScale * threshold) :
    2 * scaledDeficit object threshold dischargeScale envelope centre ≤
      (dischargeScale : Int) *
        ((windowIncidences object threshold envelope windowSupport centre : Int) +
          (nonWindowIncidences object threshold envelope windowSupport centre :
            Int)) := by
  have split :=
    windowIncidences_add_nonWindowIncidences object threshold envelope
      windowSupport centre
  have two_le : 2 * closedCount object threshold envelope centre ≤
      (threshold - 1) * closedCount object threshold envelope centre := by
    exact Nat.mul_le_mul_right _ (by omega)
  have slackInt : ((object.degree centre : Int) + 1) ≤
      (dischargeScale : Int) * (threshold : Int) := by
    exact_mod_cast slack
  have splitInt :
      ((windowIncidences object threshold envelope windowSupport centre : Int) +
          (nonWindowIncidences object threshold envelope windowSupport centre :
            Int)) =
        ((threshold - 1 : Nat) : Int) *
          (closedCount object threshold envelope centre : Int) := by
    exact_mod_cast congrArg (fun n : Nat => (n : Int)) split
  have twoLeInt :
      2 * (closedCount object threshold envelope centre : Int) ≤
        ((threshold - 1 : Nat) : Int) *
          (closedCount object threshold envelope centre : Int) := by
    exact_mod_cast two_le
  have scaleNonneg : (0 : Int) ≤ (dischargeScale : Int) := Int.natCast_nonneg _
  rw [splitInt, scaledDeficit]
  nlinarith [mul_le_mul_of_nonneg_left twoLeInt scaleNonneg, slackInt,
    scaleNonneg]

/-! ## `def:typeB-hybrid-incidence`: the remaining non-window demand -/

/-- **`D_N(𝔉)`** at the scale `2s`: `max{0, D_B − ½I_W}`. -/
noncomputable def nonWindowDemand (object : FiniteObject.{u})
    (threshold dischargeScale : Nat)
    (envelope windowSupport : Finset object.Vertex) (centre : object.Vertex) :
    Int :=
  max 0 (2 * scaledDeficit object threshold dischargeScale envelope centre -
    (dischargeScale : Int) *
      (windowIncidences object threshold envelope windowSupport centre : Int))

/-- **The non-window half-credit covers the remaining demand.**

`½I_N = c − ½I_W ≥ D_B − ½I_W`, and the demand is that quantity truncated at
zero, so the available non-window credit is at least `D_N`.  This is the second
half of `lem:typeB-hybrid-incidence-budget`. -/
theorem nonWindowCredit_ge_demand (object : FiniteObject.{u})
    (threshold dischargeScale : Nat)
    (envelope windowSupport : Finset object.Vertex) (centre : object.Vertex)
    (baseline : 3 ≤ threshold)
    (slack : object.degree centre + 1 ≤ dischargeScale * threshold) :
    nonWindowDemand object threshold dischargeScale envelope windowSupport
        centre ≤
      (dischargeScale : Int) *
        (nonWindowIncidences object threshold envelope windowSupport centre :
          Int) := by
  have pays :=
    hybridCapacity_pays object threshold dischargeScale envelope windowSupport
      centre baseline slack
  have nonneg : (0 : Int) ≤ (dischargeScale : Int) *
      (nonWindowIncidences object threshold envelope windowSupport centre :
        Int) :=
    mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
  rw [nonWindowDemand, max_le_iff]
  refine ⟨nonneg, ?_⟩
  linarith [pays]

/-! ## `prop:fan-closed-port-typeB-routing` (a) and (b) -/

/-- **`r` fan-closed ports make the deficit positive.**

(a) is the count: the ports' vertices are cubic-closed neighbours, so `c ≥ r`;
that is the caller's, since which ports the profile records is fan data.  (b) is
this arithmetic: at `r ≥ 2` the deficit is at least `2 − (δ − (k+1)α)`, which the
registered slack makes positive — the manuscript's
`D_B ≥ r − (11−k)/4 ≥ (k−3)/4 > 0`. -/
theorem positive_deficit_of_two_le_closedCount (object : FiniteObject.{u})
    (threshold dischargeScale : Nat) (envelope : Finset object.Vertex)
    (centre : object.Vertex)
    (two_le : 2 ≤ closedCount object threshold envelope centre)
    (high : threshold < object.degree centre)
    (slack : dischargeScale * threshold <
      2 * dischargeScale + (threshold + 2)) :
    0 < scaledDeficit object threshold dischargeScale envelope centre := by
  have countInt : (2 : Int) ≤ (closedCount object threshold envelope centre :
      Int) := by exact_mod_cast two_le
  have degreeInt : ((threshold : Int) + 1) ≤ (object.degree centre : Int) := by
    exact_mod_cast high
  have slackInt : (dischargeScale : Int) * (threshold : Int) <
      2 * (dischargeScale : Int) + ((threshold : Int) + 2) := by
    exact_mod_cast slack
  have scaleNonneg : (0 : Int) ≤ (dischargeScale : Int) := Int.natCast_nonneg _
  rw [scaledDeficit]
  nlinarith [mul_le_mul_of_nonneg_left countInt scaleNonneg]

end Hypostructure.Graph.TypeBHybridIncidence
