import Hypostructure.Graph.SupportComponents
import Hypostructure.Graph.BoundaryDemand
import Hypostructure.Core.CeilSqrt

/-!
# The canonical support decomposition and net-charge localization

`def:canonical-decomp` decomposes a region into the connected components of the
graph it induces and assigns every ambient surplus unit to the piece that
carries it.  `def:net-charge` measures a piece by

  `N₀(X) = def⁺(X) − σ(X) − |V(X)|/s`,

with `s` the registered discharge scale (the manuscript's `4`).  Both
subtractions are signed, so the definition is *not* a `Nat`; what the
accounting ever compares is the sign of `N₀`, and that comparison is the
subtraction-free integer test

  `N₀(X) < 0  ⟺  s·def⁺(X) < |V(X)| + s·σ(X)`,

which is `NegativeNetCharge` below.  Nothing here rounds, and no numeral is
written: `s` is a parameter, as are the baseline threshold and the region.

`lem:netcharge-superadd` is the exactness of the decomposition: the three
quantities the charge is built from — vertex count, positive deficiency, and
assigned surplus — each add up over the components.  The vertex count and the
surplus add because the components partition the region; the *deficiency* adds
because a component is a connected component, so a vertex has the same
neighbours inside its component as inside the whole region.  That last clause
is the only mathematical content of the lemma, and it is exactly the
manuscript's `d_{X_i}(u) = d_R(u)`.

`prop:negative-net-charge` is its contrapositive: a region whose own charge is
negative has a *connected* piece whose charge is negative.  This is where the
argument stops being global.
-/

namespace Hypostructure.Graph

open scoped BigOperators

universe u

namespace FiniteObject

/-! ## The canonical decomposition -/

/-- **`def:canonical-decomp` (i).**  The connected components of the graph a
region induces, as a duplicate-free index.  The ordering is
`SupportComponents.Connected.order`'s own deterministic tie-break; nothing
below depends on it, because every statement here is a sum over the whole
index. -/
noncomputable def canonicalPieces (object : FiniteObject.{u})
    (support : Finset object.Vertex) :
    Finset (SupportComponents.Connected.Component object support) := by
  classical
  exact (SupportComponents.Connected.order object support).toFinset

theorem mem_canonicalPieces (object : FiniteObject.{u})
    (support : Finset object.Vertex)
    {piece : SupportComponents.Connected.Component object support} :
    piece ∈ object.canonicalPieces support ↔
      piece ∈ SupportComponents.Connected.order object support := by
  classical
  simp [canonicalPieces]

/-- The vertex set of one piece. -/
noncomputable abbrev pieceSupport (object : FiniteObject.{u})
    (support : Finset object.Vertex)
    (piece : SupportComponents.Connected.Component object support) :
    Finset object.Vertex :=
  SupportComponents.Connected.members object support piece

theorem pieceSupport_subset (object : FiniteObject.{u})
    (support : Finset object.Vertex)
    (piece : SupportComponents.Connected.Component object support) :
    object.pieceSupport support piece ⊆ support := by
  intro vertex inside
  exact ((SupportComponents.Connected.mem_members_iff object support piece
    vertex).mp inside).1

/-- **The pieces partition the region.**  Every vertex of the region lies in
exactly one piece, so any vertex-local count sums over the pieces to its value
on the region.  This is the single combinatorial fact
`lem:netcharge-superadd` is assembled from. -/
theorem sum_canonicalPieces (object : FiniteObject.{u})
    (support : Finset object.Vertex) (weight : object.Vertex → Nat) :
    ∑ piece ∈ object.canonicalPieces support,
        ∑ vertex ∈ object.pieceSupport support piece, weight vertex =
      ∑ vertex ∈ support, weight vertex := by
  classical
  have cover : (object.canonicalPieces support).biUnion
      (object.pieceSupport support) = support := by
    ext vertex
    rw [Finset.mem_biUnion]
    constructor
    · rintro ⟨piece, _present, inside⟩
      exact object.pieceSupport_subset support piece inside
    · intro inside
      obtain ⟨piece, present, member⟩ :=
        (SupportComponents.Connected.mem_support_iff_mem_component object support
          vertex).mp inside
      exact ⟨piece, (object.mem_canonicalPieces support).mpr present, member⟩
  have disjoint :
      ((object.canonicalPieces support : Finset _) : Set _).PairwiseDisjoint
        (object.pieceSupport support) := by
    intro left _ right _ different
    exact SupportComponents.Connected.disjoint_members object support different
  rw [← Finset.sum_biUnion disjoint, cover]

/-- `Σ_i |V(X_i)| = |R|`. -/
theorem sum_pieceSupport_card (object : FiniteObject.{u})
    (support : Finset object.Vertex) :
    ∑ piece ∈ object.canonicalPieces support,
        (object.pieceSupport support piece).card = support.card := by
  have base := object.sum_canonicalPieces support (fun _ => 1)
  simpa only [Finset.sum_const, smul_eq_mul, mul_one] using base

/-- `Σ_i σ(X_i) = σ(R)`: the assigned surplus credit of
`def:canonical-decomp` (ii).  Every surplus unit belongs to the unique piece
containing its carrier, so the assignment is the partition itself. -/
theorem sum_ambientSurplus_canonicalPieces (object : FiniteObject.{u})
    (support : Finset object.Vertex) (threshold : Nat) :
    ∑ piece ∈ object.canonicalPieces support,
        object.ambientSurplus (object.pieceSupport support piece) threshold =
      object.ambientSurplus support threshold :=
  object.sum_canonicalPieces support (fun vertex => object.degree vertex - threshold)

/-- **`d_{X_i}(u) = d_R(u)`.**  Inside a connected component, a vertex's
neighbours in the component are exactly its neighbours in the whole region: a
neighbour that stays in the region is joined to it by an edge of the induced
graph, so it lies in the same component. -/
theorem internalDegree_pieceSupport (object : FiniteObject.{u})
    (support : Finset object.Vertex)
    (piece : SupportComponents.Connected.Component object support)
    {vertex : object.Vertex}
    (inside : vertex ∈ object.pieceSupport support piece) :
    object.internalDegree (object.pieceSupport support piece) vertex =
      object.internalDegree support vertex := by
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  classical
  refine congrArg Finset.card (Finset.Subset.antisymm ?_ ?_)
  · exact Finset.inter_subset_inter_left
      (object.pieceSupport_subset support piece)
  · intro neighbour member
    rw [Finset.mem_inter] at member ⊢
    refine ⟨member.1, ?_⟩
    exact SupportComponents.Connected.neighbor_mem_vertices object support piece
      inside member.2 (SimpleGraph.mem_neighborFinset _ _ _ |>.mp member.1)

/-- `Σ_i def⁺(X_i) = def⁺(R)`.  The manuscript's "the positive deficiencies add
exactly", with its reason: the components are components. -/
theorem sum_positiveDeficiency_canonicalPieces (object : FiniteObject.{u})
    (support : Finset object.Vertex) (threshold : Nat) :
    ∑ piece ∈ object.canonicalPieces support,
        object.positiveDeficiency (object.pieceSupport support piece) threshold =
      object.positiveDeficiency support threshold := by
  classical
  have pointwise : ∀ piece ∈ object.canonicalPieces support,
      object.positiveDeficiency (object.pieceSupport support piece) threshold =
        ∑ vertex ∈ object.pieceSupport support piece,
          (threshold - object.internalDegree support vertex) :=
    fun piece _ => Finset.sum_congr rfl fun vertex inside => by
      rw [object.internalDegree_pieceSupport support piece inside]
  rw [Finset.sum_congr rfl pointwise]
  exact object.sum_canonicalPieces support
    (fun vertex => threshold - object.internalDegree support vertex)

/-! ## Net charge -/

/-- **`def:net-charge`, negative side.**  `N₀(X) < 0`, written without
subtraction: `s·def⁺(X) < |V(X)| + s·σ(X)`.  Multiplying the manuscript's
`def⁺(X) − σ(X) − |V(X)|/s < 0` by the positive `s` and moving both negative
terms across is exactly this, and it is an integer comparison, so no rounding
is introduced by the `1/s`. -/
def NegativeNetCharge (object : FiniteObject.{u})
    (support : Finset object.Vertex) (threshold dischargeScale : Nat) : Prop :=
  dischargeScale * object.positiveDeficiency support threshold <
    support.card + dischargeScale * object.ambientSurplus support threshold

/-- **`def:net-charge`, nonnegative side.**  `N₀(X) ≥ 0`, the exact negation of
`NegativeNetCharge`. -/
def NonNegativeNetCharge (object : FiniteObject.{u})
    (support : Finset object.Vertex) (threshold dischargeScale : Nat) : Prop :=
  support.card + dischargeScale * object.ambientSurplus support threshold ≤
    dischargeScale * object.positiveDeficiency support threshold

theorem not_negativeNetCharge_iff (object : FiniteObject.{u})
    (support : Finset object.Vertex) (threshold dischargeScale : Nat) :
    ¬ object.NegativeNetCharge support threshold dischargeScale ↔
      object.NonNegativeNetCharge support threshold dischargeScale :=
  Nat.not_lt

/-- **The exact finite net-cap implication.**

Suppose the positive deficiency of a support is paid by a boundary capacity
after adding a common debit, and suppose that capacity is strictly below the
support size after both sides are scaled and the same debit is restored.  Then
the support has negative net charge.

For the packed-window remainder, instantiate

* `debit = 2 * (order - 1) * packing.card`,
* `capacity = threshold * (order * packing.card) + slack`.

The first hypothesis is the exact finite form of `lem:stub-positive`; the
second is the cleared-denominator form of the strict quarter-cap.  The proof is
only multiplication and cancellation, so no asymptotic notation or rounding
enters. -/
theorem negativeNetCharge_of_stubSupply_of_strictCap
    (object : FiniteObject.{u}) (support : Finset object.Vertex)
    (threshold dischargeScale debit capacity : Nat)
    (stubSupply :
      object.positiveDeficiency support threshold + debit ≤ capacity)
    (strictCap :
      dischargeScale * capacity < dischargeScale * debit + support.card) :
    object.NegativeNetCharge support threshold dischargeScale := by
  have scaled := Nat.mul_le_mul_left dischargeScale stubSupply
  rw [Nat.mul_add] at scaled
  unfold NegativeNetCharge
  omega

/-- The residual window cost after the boundary debit and the remainder-card
contribution are moved across the scaled net-charge inequality. -/
def netCapWindowCost (threshold dischargeScale windowOrder : Nat) : Nat :=
  dischargeScale * (threshold * windowOrder - 2 * (windowOrder - 1)) + windowOrder

/-- A uniform scale absorbing the density rounding and the `O(√n)` surplus. -/
def netCapErrorScale
    (threshold dischargeScale windowOrder windowRate surplusScale : Nat) : Nat :=
  4 * (netCapWindowCost threshold dischargeScale windowOrder + windowRate * dischargeScale) *
    surplusScale

/-- The exact finite predicate used for the manuscript's phrase "for all
sufficiently large `n`" at the net-cap node. -/
def SufficientlyLargeForNetCap
    (threshold dischargeScale windowOrder windowRate surplusScale size : Nat) : Prop :=
  let cost := netCapWindowCost threshold dischargeScale windowOrder
  let errorScale := netCapErrorScale threshold dischargeScale windowOrder windowRate surplusScale
  2 * cost * threshold ≤ Nat.log2 size ∧
    (2 * errorScale) * (2 * errorScale) ≤ size ∧
      2 * errorScale < size

/-- A symbolic uniform cutoff; no order table is evaluated. -/
def netCapCutoff
    (threshold dischargeScale windowOrder windowRate surplusScale : Nat) : Nat :=
  let cost := netCapWindowCost threshold dischargeScale windowOrder
  let errorScale := netCapErrorScale threshold dischargeScale windowOrder windowRate surplusScale
  max (2 ^ (2 * cost * threshold))
    (max ((2 * errorScale) * (2 * errorScale)) (2 * errorScale + 1))

theorem sufficientlyLargeForNetCap_of_cutoff
    (threshold dischargeScale windowOrder windowRate surplusScale size : Nat)
    (large : netCapCutoff threshold dischargeScale windowOrder windowRate surplusScale ≤ size) :
    SufficientlyLargeForNetCap threshold dischargeScale windowOrder windowRate surplusScale size := by
  let cost := netCapWindowCost threshold dischargeScale windowOrder
  let errorScale := netCapErrorScale threshold dischargeScale windowOrder windowRate surplusScale
  have powerLe : 2 ^ (2 * cost * threshold) ≤ size :=
    le_trans (le_max_left _ _) large
  have sizeNe : size ≠ 0 := by
    have powerPos : 0 < 2 ^ (2 * cost * threshold) := pow_pos (by decide) _
    omega
  have logLarge : 2 * cost * threshold ≤ Nat.log2 size := by
    rw [Nat.log2_eq_log_two, Nat.le_log_iff_pow_le (by decide) sizeNe]
    exact powerLe
  have squareLe : (2 * errorScale) * (2 * errorScale) ≤ size :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) large
  have pastError : 2 * errorScale < size := by
    have successorLe : 2 * errorScale + 1 ≤ size :=
      le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) large
    omega
  exact ⟨logLarge, squareLe, pastError⟩

/-- The exact arithmetic content of the paper's asymptotic net-cap step. -/
theorem strictCap_of_densityCap_of_sufficientlyLarge
    (threshold dischargeScale windowOrder windowRate surplusScale size packingCard supportCard : Nat)
    (windowOrderPos : 0 < windowOrder)
    (thresholdPos : 0 < threshold)
    (debitLe : 2 * (windowOrder - 1) ≤ threshold * windowOrder)
    (rateSlack :
      netCapWindowCost threshold dischargeScale windowOrder * threshold < 2 * windowRate)
    (large :
      SufficientlyLargeForNetCap threshold dischargeScale windowOrder windowRate surplusScale size)
    (densityCap :
      2 * (windowRate * Nat.log2 size * packingCard) ≤
        (Nat.log2 size + 1) * (threshold * size + surplusScale * Core.ceilSqrt size))
    (supportCardIdentity : windowOrder * packingCard + supportCard = size) :
    dischargeScale *
          (threshold * (windowOrder * packingCard) + surplusScale * Core.ceilSqrt size) <
      dischargeScale * (2 * (windowOrder - 1) * packingCard) + supportCard := by
  let cost := netCapWindowCost threshold dischargeScale windowOrder
  let errorScale := netCapErrorScale threshold dischargeScale windowOrder windowRate surplusScale
  let logarithm := Nat.log2 size
  let root := Core.ceilSqrt size
  have large' :
      2 * cost * threshold ≤ logarithm ∧
        (2 * errorScale) * (2 * errorScale) ≤ size ∧
          2 * errorScale < size := by
    simpa [SufficientlyLargeForNetCap, cost, errorScale, logarithm] using large
  have costPos : 0 < cost := by
    dsimp [cost, netCapWindowCost]
    omega
  have logLarge : 2 * cost * threshold ≤ logarithm := large'.1
  have logarithmPos : 0 < logarithm := by
    nlinarith
  have rateGrowth : cost * threshold * logarithm + logarithm ≤ 2 * windowRate * logarithm := by
    have := Nat.mul_le_mul_right logarithm (Nat.succ_le_of_lt rateSlack)
    nlinarith
  have gapReserve :
      2 * (cost * threshold * (logarithm + 1)) + logarithm ≤
        2 * (2 * windowRate * logarithm) := by
    nlinarith [rateGrowth, logLarge]
  have gapAtSize := Nat.mul_le_mul_right size gapReserve
  have rootBound := Core.mul_ceilSqrt_le (2 * errorScale) 1 size (by simpa using large'.2.1)
  have rootSmall : errorScale * root < size := by
    dsimp [root] at rootBound ⊢
    nlinarith [rootBound, large'.2.2]
  have errorBound :
      cost * (logarithm + 1) * (surplusScale * root) +
          2 * windowRate * logarithm * (dischargeScale * surplusScale * root) ≤
        2 * logarithm * (cost + windowRate * dischargeScale) * surplusScale * root := by
    have successorLe : logarithm + 1 ≤ 2 * logarithm := by omega
    have first :
        cost * (logarithm + 1) * (surplusScale * root) ≤
          cost * (2 * logarithm) * (surplusScale * root) := by
      gcongr
    calc
      cost * (logarithm + 1) * (surplusScale * root) +
            2 * windowRate * logarithm * (dischargeScale * surplusScale * root) ≤
          cost * (2 * logarithm) * (surplusScale * root) +
            2 * windowRate * logarithm * (dischargeScale * surplusScale * root) :=
        Nat.add_le_add_right first _
      _ = 2 * logarithm * (cost + windowRate * dischargeScale) * surplusScale * root := by ring
  have errorStrict :
      2 *
            (cost * (logarithm + 1) * (surplusScale * root) +
              2 * windowRate * logarithm * (dischargeScale * surplusScale * root)) <
        logarithm * size := by
    have multiplied : logarithm * (errorScale * root) < logarithm * size :=
      (Nat.mul_lt_mul_left logarithmPos).2 rootSmall
    dsimp [errorScale, netCapErrorScale] at multiplied
    nlinarith [errorBound, multiplied]
  have densityScaled := Nat.mul_le_mul_left (2 * cost) densityCap
  have scaledMargin :
      4 * windowRate * logarithm *
            (cost * packingCard + dischargeScale * surplusScale * root) <
        4 * windowRate * logarithm * size := by
    change 2 * cost * (2 * (windowRate * logarithm * packingCard)) ≤
      2 * cost * ((logarithm + 1) * (threshold * size + surplusScale * root)) at densityScaled
    nlinarith [densityScaled, gapAtSize, errorStrict]
  have margin : cost * packingCard + dischargeScale * surplusScale * root < size := by
    have factorPos : 0 < 4 * windowRate * logarithm := by
      have ratePos : 0 < windowRate := by nlinarith
      positivity
    exact (Nat.mul_lt_mul_left factorPos).mp scaledMargin
  have split : threshold * windowOrder =
      2 * (windowOrder - 1) + (threshold * windowOrder - 2 * (windowOrder - 1)) := by
    omega
  have residualMargin :
      dischargeScale *
          ((threshold * windowOrder - 2 * (windowOrder - 1)) * packingCard +
            surplusScale * root) < supportCard := by
    dsimp [cost, netCapWindowCost] at margin
    rw [← supportCardIdentity] at margin
    have expand :
        (dischargeScale * (threshold * windowOrder - 2 * (windowOrder - 1)) + windowOrder) *
              packingCard + dischargeScale * surplusScale * root =
          windowOrder * packingCard +
            dischargeScale *
              ((threshold * windowOrder - 2 * (windowOrder - 1)) * packingCard +
                surplusScale * root) := by ring
    rw [expand] at margin
    exact Nat.lt_of_add_lt_add_left margin
  have capacityDecomp :
      threshold * (windowOrder * packingCard) =
        2 * (windowOrder - 1) * packingCard +
          (threshold * windowOrder - 2 * (windowOrder - 1)) * packingCard := by
    calc
      threshold * (windowOrder * packingCard) = (threshold * windowOrder) * packingCard := by ring
      _ = (2 * (windowOrder - 1) +
            (threshold * windowOrder - 2 * (windowOrder - 1))) * packingCard :=
        congrArg (fun value => value * packingCard) split
      _ = 2 * (windowOrder - 1) * packingCard +
            (threshold * windowOrder - 2 * (windowOrder - 1)) * packingCard := by ring
  calc
    dischargeScale *
          (threshold * (windowOrder * packingCard) + surplusScale * Core.ceilSqrt size) =
        dischargeScale * (2 * (windowOrder - 1) * packingCard) +
          dischargeScale *
            ((threshold * windowOrder - 2 * (windowOrder - 1)) * packingCard +
              surplusScale * root) := by
                dsimp [root]
                rw [capacityDecomp]
                ring
    _ < dischargeScale * (2 * (windowOrder - 1) * packingCard) + supportCard :=
      Nat.add_lt_add_left residualMargin _

/-- Stub supply and the eventual density margin imply negative net charge. -/
theorem negativeNetCharge_of_stubSupply_of_densityCap_of_sufficientlyLarge
    (object : FiniteObject.{u}) (support : Finset object.Vertex)
    (threshold dischargeScale windowOrder windowRate surplusScale size packingCard : Nat)
    (windowOrderPos : 0 < windowOrder)
    (thresholdPos : 0 < threshold)
    (debitLe : 2 * (windowOrder - 1) ≤ threshold * windowOrder)
    (rateSlack :
      netCapWindowCost threshold dischargeScale windowOrder * threshold < 2 * windowRate)
    (large :
      SufficientlyLargeForNetCap threshold dischargeScale windowOrder windowRate surplusScale size)
    (densityCap :
      2 * (windowRate * Nat.log2 size * packingCard) ≤
        (Nat.log2 size + 1) * (threshold * size + surplusScale * Core.ceilSqrt size))
    (supportCardIdentity : windowOrder * packingCard + support.card = size)
    (stubSupply :
      object.positiveDeficiency support threshold +
          2 * (windowOrder - 1) * packingCard ≤
        threshold * (windowOrder * packingCard) + surplusScale * Core.ceilSqrt size) :
    object.NegativeNetCharge support threshold dischargeScale := by
  apply object.negativeNetCharge_of_stubSupply_of_strictCap support threshold dischargeScale
    (2 * (windowOrder - 1) * packingCard)
    (threshold * (windowOrder * packingCard) + surplusScale * Core.ceilSqrt size) stubSupply
  exact strictCap_of_densityCap_of_sufficientlyLarge threshold dischargeScale windowOrder
    windowRate surplusScale size packingCard support.card windowOrderPos thresholdPos debitLe
    rateSlack large densityCap supportCardIdentity

/-- **`lem:netcharge-superadd`.**  The net charge of a region is the sum of the
net charges of its connected pieces.  Stated in the subtraction-free form the
comparison actually uses: if every piece is nonnegative then so is the region.

The manuscript's display `Σ_i N₀(X_i) = def⁺(R) − σ(R) − ¼|R|` is the three
exact sums above; this is that identity's only consumed consequence, and
stating it this way keeps every quantity a `Nat`. -/
theorem nonNegativeNetCharge_of_forall_pieces (object : FiniteObject.{u})
    (support : Finset object.Vertex) (threshold dischargeScale : Nat)
    (pieces : ∀ piece ∈ object.canonicalPieces support,
      object.NonNegativeNetCharge (object.pieceSupport support piece) threshold
        dischargeScale) :
    object.NonNegativeNetCharge support threshold dischargeScale := by
  classical
  have summed :
      ∑ piece ∈ object.canonicalPieces support,
          ((object.pieceSupport support piece).card +
            dischargeScale * object.ambientSurplus
              (object.pieceSupport support piece) threshold) ≤
        ∑ piece ∈ object.canonicalPieces support,
          dischargeScale * object.positiveDeficiency
            (object.pieceSupport support piece) threshold :=
    Finset.sum_le_sum pieces
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    object.sum_pieceSupport_card support,
    object.sum_ambientSurplus_canonicalPieces support threshold,
    object.sum_positiveDeficiency_canonicalPieces support threshold] at summed
  exact summed

/-- **`prop:negative-net-charge`, with the canonical index retained.**  A
region of negative net charge has one of its actual canonical connected
components of negative net charge.  Retaining the component is essential for
later refinements: its vertex support can be recovered definitionally, whereas
an arbitrary connected subset cannot be promoted back to the canonical
decomposition. -/
theorem exists_canonicalPiece_negativeNetCharge (object : FiniteObject.{u})
    (support : Finset object.Vertex) (threshold dischargeScale : Nat)
    (negative : object.NegativeNetCharge support threshold dischargeScale) :
    ∃ piece ∈ object.canonicalPieces support,
      object.NegativeNetCharge (object.pieceSupport support piece) threshold
        dischargeScale := by
  classical
  by_contra none
  push Not at none
  exact (Nat.not_le_of_lt negative)
    (object.nonNegativeNetCharge_of_forall_pieces support threshold
      dischargeScale fun piece present =>
        (object.not_negativeNetCharge_iff
          (object.pieceSupport support piece) threshold dischargeScale).mp
            (none piece present))

/-- **`prop:negative-net-charge`.**  A region of negative net charge has a
connected piece of negative net charge.

The manuscript's proof verbatim: if every piece were nonnegative their sum
could not be negative.  What the statement returns is a *connected* subset of
the region — `SupportComponents.Connected.ConnectedOn` is the walk-based
connectivity of `def:admissible`'s "connected remainder piece", and the piece
is nonempty because it is a component of the order. -/
theorem exists_connected_negativeNetCharge (object : FiniteObject.{u})
    (support : Finset object.Vertex) (threshold dischargeScale : Nat)
    (negative : object.NegativeNetCharge support threshold dischargeScale) :
    ∃ piece : Finset object.Vertex,
      piece ⊆ support ∧
        SupportComponents.Connected.ConnectedOn object piece ∧
        object.NegativeNetCharge piece threshold dischargeScale := by
  obtain ⟨piece, present, pieceNegative⟩ :=
    object.exists_canonicalPiece_negativeNetCharge support threshold
      dischargeScale negative
  exact ⟨object.pieceSupport support piece,
    object.pieceSupport_subset support piece,
    SupportComponents.Connected.connectedOn_of_mem_order object support
      ((object.mem_canonicalPieces support).mp present),
    pieceNegative⟩

end FiniteObject

end Hypostructure.Graph
