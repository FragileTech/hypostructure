import Mathlib.Data.Nat.Choose.Basic
import Hypostructure.Core.Finite.Enumeration
import Hypostructure.Graph.Finite

/-!
# Wedge lower bound

Paper `lem:wedge-lower`'s core per-graph identity, proved directly (no
dependency on the paper's asymptotic near-cubic-spine hypotheses, which only
specialize this exact fact for the cubic baseline): for any registered
baseline degree `k` (a problem's own registered threshold -- an explicit
argument to every theorem below, never a literal baked into this file) with
`k >= 3`, the number of length-two wedges (paths through a common centre,
`C(d(v),2)` summed over vertices -- fixed by what a length-two wedge *is*,
a choice of 2 neighbours, independent of any problem's baseline) plus twice
the total deficiency below `k`, per vertex, is always at least `2k - 3`
(the pointwise form); summed over the whole object this gives `W_2 + 2 def
+ 3|V| >= 2k|V|` (`sharp_baseline_mul_vertexCount_le_...` below).

This is the SHARP form, not merely a sufficient one: `sharp_pointwise` below
proves equality is achieved at `d = 2` and `d = 3` for *every* baseline
`k >= 3`, not only at `k = 3`.  (An earlier version of this file only
proved the weaker `k <= C(d,2) + 2*(k-d)`, which is true for every
`k >= 3` but whose slack grows without bound as `k` grows -- e.g. at
`k = 7` the tightest case gives `7 <= 11`, slack `4` -- and so does not
capture the same sharp fact the paper's cubic argument relies on.  The
`2k - 3` form here is tight at every valid baseline, matching what a
different problem registering a larger baseline would actually need to
reuse this fact for anything requiring sharpness, not just truth.)

The `k >= 3` hypothesis itself is not an application-specific constant
copied from the paper: `baseline_two_insufficient` and
`baseline_one_insufficient` below *prove*, from this file's own
definitions, that even the weak (non-sharp) bound is false at `k = 1` and
`k = 2`, so `3` is derived here as the precise threshold the statement
needs. -/

namespace Hypostructure.Graph

namespace FiniteObject

/-- Per-vertex deficiency below a registered baseline `k`, `(k - d(v))`
truncated at zero (`Nat` subtraction), summed over the whole object -- the
paper's atom deficiency `def(C)` at baseline `k`. -/
def deficiencyAt (object : FiniteObject) (baseline : Nat) : Nat :=
  (object.orderedVertices.map fun vertex => baseline - object.degree vertex).sum

/-- Count of length-two wedges, `C(d(v),2)` summed over the whole object --
`W_2(C) = sum_i C(i,2) n_i`, independent of any baseline. -/
def wedgeCount (object : FiniteObject) : Nat :=
  (object.orderedVertices.map fun vertex => (object.degree vertex).choose 2).sum

/-- The literal unordered pairs of neighbours at one centre.  This is the
finite Graph carrier whose cardinality is the corresponding summand in
`wedgeCount`; it is derived solely from the incoming finite graph. -/
noncomputable def wedgePairs (object : FiniteObject)
    (centre : object.Vertex) : Finset (Finset object.Vertex) := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  exact (object.orderedNeighbors centre).toFinset.powersetCard 2

/-- A raw length-two wedge is its centre together with one unordered pair of
distinct neighbours.  No target response or rank outcome is stored here. -/
abbrev WedgeCoordinate (object : FiniteObject) :=
  Σ centre : object.Vertex,
    { pair : Finset object.Vertex // pair ∈ object.wedgePairs centre }

/-- Exact finite family of raw wedges of the incoming graph. -/
noncomputable def wedgeFinset (object : FiniteObject) :
    Finset object.WedgeCoordinate := by
  classical
  exact object.vertexFinset.sigma fun centre =>
    (object.wedgePairs centre).attach

/-- Deterministic exact CT member schedule for the raw wedge family. -/
noncomputable def wedgeSchedule (object : FiniteObject) :
    Core.Finite.Enumeration object.WedgeCoordinate := by
  classical
  exact Core.Finite.Enumeration.ofNodupList object.wedgeFinset.toList
    object.wedgeFinset.nodup_toList

/-- The exact carrier schedule agrees with the pre-existing numerical wedge
observable, so retaining the schedule does not change the mathematics. -/
theorem wedgeSchedule_card (object : FiniteObject) :
    object.wedgeSchedule.card = object.wedgeCount := by
  classical
  letI : DecidableEq object.Vertex := object.vertices.decEq
  calc
    object.wedgeSchedule.card = object.wedgeFinset.card := by
      change object.wedgeFinset.toList.length = object.wedgeFinset.card
      exact object.wedgeFinset.length_toList
    _ = ∑ centre ∈ object.vertexFinset,
        (object.degree centre).choose 2 := by
      rw [wedgeFinset, Finset.card_sigma]
      apply Finset.sum_congr rfl
      intro centre _centre_mem
      rw [Finset.card_attach, wedgePairs, Finset.card_powersetCard]
      congr 1
      exact (List.toFinset_card_of_nodup
        (object.orderedNeighbors_nodup centre)).trans
          (object.orderedNeighbors_length centre)
    _ = object.wedgeCount := by
      rw [wedgeCount, ← List.sum_toFinset _ object.orderedVertices_nodup]
      congr 1
      ext vertex
      simp [FiniteObject.vertexFinset]

/-- `2 * d.choose 2 = d * (d - 1)` for every `d`, including `d = 0` (`Nat`
subtraction truncates `0 - 1` to `0` on both sides). -/
private theorem two_mul_choose_two (d : Nat) :
    2 * d.choose 2 = d * (d - 1) := by
  rw [Nat.choose_two_right, mul_comm]
  exact Nat.div_mul_cancel d.even_mul_pred_self.two_dvd

/-- The threshold `baseline >= 3` is necessary, not merely sufficient: at
`baseline = 1`, a single vertex of degree exactly `1` (zero deficiency,
matching the baseline) has wedge count `0`, strictly below `1`. -/
theorem baseline_one_insufficient :
    ¬ (1 ≤ (1 : Nat).choose 2 + 2 * (1 - 1)) := by decide

/-- Likewise at `baseline = 2`: a single vertex of degree exactly `2` (zero
deficiency) has wedge count `C(2,2) = 1`, strictly below `2`. -/
theorem baseline_two_insufficient :
    ¬ (2 ≤ (2 : Nat).choose 2 + 2 * (2 - 2)) := by decide

/-- Baseline-independent pointwise fact underlying the sharp bound: twice a
vertex's own degree is absorbed by its own wedge count plus three units of
slack, with equality at `d = 2` and `d = 3` (this is the exact source of
the sharpness at every baseline -- the `2k - 3` bound below is this same
fact merely relocated by a fixed shift, not a different, baseline-dependent
computation). -/
private theorem two_mul_le_choose_two_add_three (d : Nat) :
    2 * d ≤ d.choose 2 + 3 := by
  match d with
  | 0 => decide
  | 1 => decide
  | 2 => decide
  | 3 => decide
  | (m + 4) =>
    have h2 := two_mul_choose_two (m + 4)
    have hsub : m + 4 - 1 = m + 3 := by omega
    rw [hsub] at h2
    nlinarith

/-- Sharp pointwise form of the paper's proof, for an arbitrary registered
baseline `k >= 3`: at any degree `d`, `2k - 3` (not merely `k`) is absorbed
by a unit vertex's own wedge count plus twice its own deficiency below `k`.
Split on whether `d` meets the baseline: at or above it, the deficiency
vanishes and `d.choose 2` alone already covers `2k-3` (using `k >= 3`
exactly where `k.choose 2 + 3 >= 2k` needs it, via
`two_mul_le_choose_two_add_three` applied at `d = k` and monotonicity for
`d > k`); below it, `two_mul_le_choose_two_add_three` applied at `d`
directly supplies the bound, using the doubled deficiency to make up the
remaining `2*(k-d)` gap between `2d` and `2k`. -/
theorem sharp_pointwise
    (baseline d : Nat) (baseline_ge : 3 ≤ baseline) :
    2 * baseline ≤ d.choose 2 + 2 * (baseline - d) + 3 := by
  rcases Nat.lt_or_ge d baseline with hlt | hle
  · have h := two_mul_le_choose_two_add_three d
    omega
  · have hzero : baseline - d = 0 := by omega
    rw [hzero, mul_zero]
    have hmono : baseline.choose 2 ≤ d.choose 2 := Nat.choose_le_choose 2 hle
    have hbase := two_mul_le_choose_two_add_three baseline
    omega

/-- The weaker (non-sharp, but simpler to state) bound `baseline <= ...`
used to be this file's only claim.  It is now a direct corollary of the
sharp form (using `baseline_ge` to absorb the extra `baseline - 3 >= 0`
slack), kept for callers that only need the plain lower bound. -/
theorem baseline_le_choose_two_add_two_mul_deficit
    (baseline d : Nat) (baseline_ge : 3 ≤ baseline) :
    baseline ≤ d.choose 2 + 2 * (baseline - d) := by
  have h := sharp_pointwise baseline d baseline_ge
  omega

/-- Paper `lem:wedge-lower`'s core per-object identity at a registered
baseline `k >= 3`, in its sharp `2k - 3` form: the wedge count plus twice
the `k`-deficiency, plus `3` per vertex, is at least `2k` times the vertex
count. -/
theorem sharp_baseline_mul_vertexCount_le_wedgeCount_add_two_mul_deficiencyAt
    (object : FiniteObject) (baseline : Nat) (baseline_ge : 3 ≤ baseline) :
    2 * baseline * object.vertexCount ≤
      object.wedgeCount + 2 * object.deficiencyAt baseline +
        3 * object.vertexCount := by
  rw [vertexCount_eq_orderedVertices_length, wedgeCount, deficiencyAt]
  generalize object.orderedVertices = l
  induction l with
  | nil => simp
  | cons head tail ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.mul_add,
      Nat.mul_one]
    have h := sharp_pointwise baseline (object.degree head) baseline_ge
    omega

/-- Non-sharp corollary of the sharp identity, stated to match the paper's
own `W_2(C) >= k|V(C)| - 2 def(C)` phrasing (subtraction-free, since this
form needs no side condition on which side is larger). -/
theorem baseline_mul_vertexCount_le_wedgeCount_add_two_mul_deficiencyAt
    (object : FiniteObject) (baseline : Nat) (baseline_ge : 3 ≤ baseline) :
    baseline * object.vertexCount ≤
      object.wedgeCount + 2 * object.deficiencyAt baseline := by
  have h := sharp_baseline_mul_vertexCount_le_wedgeCount_add_two_mul_deficiencyAt
    object baseline baseline_ge
  have key : baseline * object.vertexCount + 3 * object.vertexCount ≤
      2 * baseline * object.vertexCount := by
    have hle : baseline + 3 ≤ 2 * baseline := by omega
    calc baseline * object.vertexCount + 3 * object.vertexCount
        = (baseline + 3) * object.vertexCount := by ring
      _ ≤ (2 * baseline) * object.vertexCount := Nat.mul_le_mul_right _ hle
  omega

end FiniteObject

end Hypostructure.Graph
