import Hypostructure.Graph.HighCentrePorts

/-!
# Cubic-closed fan neighbours and the closed-neighbour deficit

`def:typeB-multiclosed-residual`.  A marked Type B fan at a centre `h` counts its
*cubic-closed* neighbours: those `u ∈ N(h)` sitting exactly at the baseline whose
two non-`h` incidences are both assigned to the fan envelope.  Writing
`k = d_G(h)` and `c` for that count, the **closed-neighbour deficit** is

  `D_B = c − (δ − (k+1)·α)`

at the registered discharge scale `α = 1/s`, and the fan is *certificate-closed*
when `D_B ≤ 0`.  At the manuscript's `δ = 3` and `α = 1/4` the subtrahend is
`(11 − k)/4`, so `D_B = c − (11−k)/4`: the deficit whose positivity is the whole
subject of the Type B bridge.

## Everything is a scaled integer

`D_B` is rational, and nothing below rounds it.  Every quantity is carried at the
scale `s`, so the deficit appears as the integer

  `s·D_B = s·c − s·δ + (k+1)`,

which is `scaledDeficit`.  Certificate-closedness is `scaledDeficit ≤ 0`, an
integer comparison equivalent to `D_B ≤ 0` because `s > 0`.  The reciprocal never
appears, and neither `3`, `4` nor `11` is written anywhere: the baseline is
`threshold` and the scale is `dischargeScale`.

Nothing here is specialized to a manuscript.
-/

namespace Hypostructure.Graph.TypeBFanIncidence

open Hypostructure

universe u

variable {object : FiniteObject.{u}}

open scoped Classical

/-! ## `def:typeB-multiclosed-residual`: cubic-closed neighbours -/

/-- **A cubic-closed neighbour of the fan centre.**

`u ∈ N(h)` is *cubic* -- at the baseline exactly -- and *closed*: both of its
non-`h` incidences land in the assigned fan envelope.  The envelope is a
parameter, because which vertices the marked fan assigns is fan data and not a
property of the graph. -/
def IsCubicClosed (object : FiniteObject.{u}) (threshold : Nat)
    (envelope : Finset object.Vertex) (centre owner : object.Vertex) : Prop :=
  object.graph.Adj centre owner ∧ object.degree owner = threshold ∧
    ∀ other : object.Vertex, object.graph.Adj owner other → other ≠ centre →
      other ∈ envelope

/-- The cubic-closed neighbours of the centre, as a finset of `N(h)`. -/
noncomputable def closedNeighbours (object : FiniteObject.{u}) (threshold : Nat)
    (envelope : Finset object.Vertex) (centre : object.Vertex) :
    Finset object.Vertex :=
  (object.orderedNeighbors centre).toFinset.filter
    (IsCubicClosed object threshold envelope centre)

/-- **`c(𝔉)`**, the cubic-closed neighbour count. -/
noncomputable def closedCount (object : FiniteObject.{u}) (threshold : Nat)
    (envelope : Finset object.Vertex) (centre : object.Vertex) : Nat :=
  (closedNeighbours object threshold envelope centre).card

theorem mem_closedNeighbours_iff {threshold : Nat}
    {envelope : Finset object.Vertex} {centre owner : object.Vertex} :
    owner ∈ closedNeighbours object threshold envelope centre ↔
      IsCubicClosed object threshold envelope centre owner := by
  classical
  simp only [closedNeighbours, Finset.mem_filter, List.mem_toFinset,
    object.mem_orderedNeighbors_iff]
  exact ⟨fun ⟨_adjacent, closed⟩ => closed,
    fun closed => ⟨closed.1, closed⟩⟩

theorem closedNeighbours_subset (object : FiniteObject.{u}) (threshold : Nat)
    (envelope : Finset object.Vertex) (centre : object.Vertex) :
    closedNeighbours object threshold envelope centre ⊆
      (object.orderedNeighbors centre).toFinset := by
  classical
  exact Finset.filter_subset _ _

/-- **`c ≤ k`.**  A cubic-closed neighbour is a neighbour, so the count is
bounded by the centre's degree.  This is the upper half of `[79]`'s profile. -/
theorem closedCount_le_degree (object : FiniteObject.{u}) (threshold : Nat)
    (envelope : Finset object.Vertex) (centre : object.Vertex) :
    closedCount object threshold envelope centre ≤ object.degree centre := by
  have counted : (closedNeighbours object threshold envelope centre).card ≤
      (object.orderedNeighbors centre).toFinset.card :=
    Finset.card_le_card (closedNeighbours_subset object threshold envelope centre)
  rw [List.toFinset_card_of_nodup (object.orderedNeighbors_nodup centre),
    object.orderedNeighbors_length centre] at counted
  exact counted

/-! ## The closed-neighbour deficit -/

/-- **`s·D_B`**, the closed-neighbour deficit at the discharge scale.

`D_B = c − (δ − (k+1)·α)` with `α = 1/s`, multiplied through by `s`.  Carried in
`ℤ` because the deficit is genuinely signed: its sign is the certificate-closed
test. -/
noncomputable def scaledDeficit (object : FiniteObject.{u})
    (threshold dischargeScale : Nat) (envelope : Finset object.Vertex)
    (centre : object.Vertex) : Int :=
  (dischargeScale : Int) * (closedCount object threshold envelope centre : Int) -
      (dischargeScale : Int) * (threshold : Int) +
    ((object.degree centre : Int) + 1)

/-- **`def:typeB-multiclosed-residual`, certificate-closed.**  `D_B ≤ 0`. -/
def IsCertificateClosed (object : FiniteObject.{u})
    (threshold dischargeScale : Nat) (envelope : Finset object.Vertex)
    (centre : object.Vertex) : Prop :=
  scaledDeficit object threshold dischargeScale envelope centre ≤ 0

/-- **A positive-deficit fan is exactly a fan that is not certificate-closed.**

The two alternatives of the Type B local ledger are complementary by
construction, which is why no node has to offer a third. -/
theorem not_isCertificateClosed_iff (object : FiniteObject.{u})
    (threshold dischargeScale : Nat) (envelope : Finset object.Vertex)
    (centre : object.Vertex) :
    ¬ IsCertificateClosed object threshold dischargeScale envelope centre ↔
      0 < scaledDeficit object threshold dischargeScale envelope centre := by
  simp [IsCertificateClosed]

/-! ## `[79]`: the profile of a centre one above the baseline -/

/-- **The centre surplus of a degree-`δ+1` centre is one.** -/
theorem surplus_eq_one {threshold : Nat} {centre : object.Vertex}
    (degree : object.degree centre = threshold + 1) :
    object.degree centre - threshold = 1 := by omega

/-- **`[79]`, the degree-four fan profile.**

At a high centre sitting exactly one above the baseline: the centre surplus is
`1`, the cubic-closed count is at most the degree, and the deficit is
`s·c − s·δ + (δ + 2)`.  At the manuscript's `δ = 3`, `s = 4` and `k = 4` those
three readings are its *centre surplus `1`, `0 ≤ c ≤ 4`, `D_B = c − 7/4*`; the
`7/4` is `(δ − (k+1)/s)` evaluated, never written.

The lower and upper bounds on the deficit are the same three quantities read at
`c = 0` and at `c = k`, which is where `[81]`'s `c ≤ 1` / `c ≥ 2` split gets its
range. -/
theorem degreeFourProfile (object : FiniteObject.{u})
    (threshold dischargeScale : Nat) (envelope : Finset object.Vertex)
    {centre : object.Vertex}
    (degree : object.degree centre = threshold + 1) :
    object.degree centre - threshold = 1 ∧
      closedCount object threshold envelope centre ≤ threshold + 1 ∧
      scaledDeficit object threshold dischargeScale envelope centre =
          (dischargeScale : Int) *
              (closedCount object threshold envelope centre : Int) -
            (dischargeScale : Int) * (threshold : Int) + ((threshold : Int) + 2) ∧
        (- (dischargeScale : Int) * (threshold : Int) + ((threshold : Int) + 2) ≤
            scaledDeficit object threshold dischargeScale envelope centre ∧
          scaledDeficit object threshold dischargeScale envelope centre ≤
            (dischargeScale : Int) + ((threshold : Int) + 2)) := by
  have counted : closedCount object threshold envelope centre ≤ threshold + 1 := by
    have bound := closedCount_le_degree object threshold envelope centre
    omega
  refine ⟨surplus_eq_one degree, counted, ?_, ?_, ?_⟩
  · rw [scaledDeficit, degree]
    push_cast
    ring
  · rw [scaledDeficit, degree]
    have nonneg :
        (0 : Int) ≤ (dischargeScale : Int) *
          (closedCount object threshold envelope centre : Int) :=
      mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
    push_cast
    linarith [nonneg]
  · rw [scaledDeficit, degree]
    have capped :
        (dischargeScale : Int) *
            (closedCount object threshold envelope centre : Int) ≤
          (dischargeScale : Int) * ((threshold : Int) + 1) := by
      refine mul_le_mul_of_nonneg_left ?_ (Int.natCast_nonneg _)
      exact_mod_cast counted
    push_cast at capped ⊢
    nlinarith [capped]

end Hypostructure.Graph.TypeBFanIncidence
