import Hypostructure.Core.Residual.Query
import Hypostructure.Core.Strategy.FiniteBarrierEnumerationSemantics

/-!
# Finite density budget semantics

The problem/domain boundary contributes only the represented ambient-state
capacity.  Packing cardinality and finite-barrier output remain execution
facts exported by sealed Strategies through Core's typed ledger queries.

The surviving *cap* alternative of the multiplicative comparison exports a
query-only ledger entry of its own, `CapLedger`, mirroring the overflow
alternative's `ColdBranchAggregation.OverflowLedger`.  It lives here, beside
the inert registration and away from the CT machinery, so that a downstream
Strategy can name the surviving cap without importing CT14.
-/

namespace Hypostructure.Core.Strategy.FiniteDensityBudget

open Hypostructure.Core.Residual

universe u uStage uNew

/-- Inert domain presentation for the represented ambient state space. -/
structure Registration (Residual : Type u) where
  ambientCapacity : Residual → Nat
  ambientCapacity_pos : ∀ residual, 0 < ambientCapacity residual

/-- **Query-only view of the exact surviving finite-density cap entry.**

The complementary-terminal mirror of
`ColdBranchAggregation.OverflowLedger`: where that one retains the strict
overflow of the retained state demand over the represented capacity, this one
retains the literal cap that the surviving alternative certified.

Three of the four fields are the very queries the density comparison was run
on -- the retained packing cardinality, the finite-barrier `Summary`, and the
represented ambient capacity -- so the fourth states the comparison in the
producer's own coordinates and nothing is reconstructed from the residual. -/
structure CapLedger (Stage : Type uStage) where
  packingCount : Query Stage (fun _ => Nat)
  barrierSummary : Query Stage
    (fun _ => FiniteBarrierEnumeration.Summary)
  ambientCapacity : Query Stage (fun _ => Nat)
  cap : Query Stage fun stage =>
    (barrierSummary.read stage).safeProduct ^ packingCount.read stage ≤
      (barrierSummary.read stage).flatProduct ^ packingCount.read stage *
        ambientCapacity.read stage
  /-- The exact entropy-form cap derived from the retained CT14 comparison.
  This is published as a query so downstream Strategies can consume the
  density fact without unfolding the predecessor or replaying CT14. -/
  entropyCap : Query Stage fun stage =>
    2 ^ ((barrierSummary.read stage).binaryRateFloor *
      packingCount.read stage) ≤ ambientCapacity.read stage
  /-- The represented ambient state space is nonempty.  This is the density
  registration's own `ambientCapacity_pos`, forwarded rather than reproved --
  for the graph presentation it is `skeletonBudget_pos`, the statement that the
  residual object's own edge count is an admissible edge count on its own
  vertex set. -/
  ambientCapacity_pos : Query Stage fun stage =>
    0 < ambientCapacity.read stage
  /-- The compared barrier `Summary` is the one Core derived by `ofRows`, so
  its `binaryRateFloor` is a genuine `log₂` of its own aggregation columns and
  not a free field.  Produced at the barrier node and transported here by the
  compiler through `FiniteBarrierEnumeration.RateLedger`. -/
  barrierDerived : Query Stage fun stage =>
    FiniteBarrierEnumeration.Summary.Derived (barrierSummary.read stage)
  /-- The compared barrier `Summary`'s flat column -- the denominator of the
  flatness ratio `log₂(W/F)` -- is nonvanishing, as proved and published by the
  sealed barrier strategy. -/
  barrierFlatPositive : Query Stage fun stage =>
    0 < (barrierSummary.read stage).flatProduct
  /-- **`def:near-cubic-spine`, retained on this node's own ledger.**  The
  node-`[19]` `scaleThresholdDichotomy`'s at-or-below branch load, carried
  forward rather than re-derived: `degreeSurplusLoad` is that branch's own
  `load` at the active object and `degreeSurplusThreshold` its own `table`
  value, both already fixed at the branch that produced this node. -/
  degreeSurplusLoad : Query Stage fun _ => Nat
  degreeSurplusThreshold : Query Stage fun _ => Nat
  /-- The node-`[19]` at-or-below comparison itself, i.e. `def:near-cubic-spine`
  read off the retained branch payload -- never re-derived, never assumed. -/
  nearCubic : Query Stage fun stage =>
    degreeSurplusLoad.read stage ≤ degreeSurplusThreshold.read stage

namespace CapLedger

def comap (ledger : CapLedger Stage) (project : NewStage → Stage) :
    CapLedger NewStage where
  packingCount := ledger.packingCount.comap project
  barrierSummary := ledger.barrierSummary.comap project
  ambientCapacity := ledger.ambientCapacity.comap project
  cap := ledger.cap.comap project
  entropyCap := ledger.entropyCap.comap project
  ambientCapacity_pos := ledger.ambientCapacity_pos.comap project
  barrierDerived := ledger.barrierDerived.comap project
  barrierFlatPositive := ledger.barrierFlatPositive.comap project
  degreeSurplusLoad := ledger.degreeSurplusLoad.comap project
  degreeSurplusThreshold := ledger.degreeSurplusThreshold.comap project
  nearCubic := ledger.nearCubic.comap project

def preserve {Added : Stage → Type uNew} (ledger : CapLedger Stage) :
    CapLedger (Ledger.Extension Stage Added) :=
  ledger.comap Ledger.Extension.previous

def preserveProp {Added : Stage → Prop} (ledger : CapLedger Stage) :
    CapLedger (Ledger.Extension Stage Added) :=
  ledger.comap Ledger.Extension.previous

/-- **The entropy form of the surviving density cap, read off the ledger.**

`cap` is a comparison of two products.  Taking `log₂` of it is the
manuscript's `[22]`--`[24]` comparison

  `rate · packingCount ≤ log₂ (ambient capacity)`,

and this is that statement in exact `Nat` form, with no rounding and no `o(·)`
term: `2 ^ (rate · packingCount) ≤ ambientCapacity`.

`rate` is not a numeral and is not chosen here.  It is whatever per-package
rate the ledger's own barrier `Summary` certifies through the first
hypothesis -- for a package declared at every separated dyadic scale of the
residual object that is the registered table's rate times the object's scale
count, so the left side really is `c_hot · log₂ n · p₁₃` bits and it grows
with the residual.

This is the same statement as
`Profile.CapResidual.two_pow_rate_mul_packingCount_le_ambientCapacity`, stated
on the retained ledger entry rather than on the CT14 residual, so a consumer
several ledger extensions below the producing node can still read it. -/
theorem two_pow_rate_mul_packingCount_le_ambientCapacity
    (ledger : CapLedger Stage) (stage : Stage) {rate : Nat}
    (rateFloor :
      2 ^ rate * (ledger.barrierSummary.read stage).flatProduct ≤
        (ledger.barrierSummary.read stage).safeProduct)
    (flatPositive :
      0 < (ledger.barrierSummary.read stage).flatProduct) :
    2 ^ (rate * ledger.packingCount.read stage) ≤
      ledger.ambientCapacity.read stage := by
  have capExact := ledger.cap.read stage
  set packing := ledger.packingCount.read stage with packingDef
  set flat := (ledger.barrierSummary.read stage).flatProduct with flatDef
  set safe := (ledger.barrierSummary.read stage).safeProduct with safeDef
  have raised : (2 ^ rate * flat) ^ packing ≤ safe ^ packing :=
    Nat.pow_le_pow_left rateFloor _
  rw [mul_pow, ← pow_mul] at raised
  have chain : 2 ^ (rate * packing) * flat ^ packing ≤
      flat ^ packing * ledger.ambientCapacity.read stage :=
    le_trans raised capExact
  rw [mul_comm (flat ^ packing)] at chain
  exact Nat.le_of_mul_le_mul_right chain (Nat.pow_pos flatPositive)

/-- **`prop:p13-density` on the surviving branch, with no hypothesis left.**

  `2 ^ (binaryRateFloor · packingCount) ≤ ambientCapacity`.

This is `two_pow_rate_mul_packingCount_le_ambientCapacity` with `rate`
instantiated at the one rate the retained ledger itself names -- the derived
barrier table's own `binaryRateFloor` -- and with both of that theorem's
premises discharged from the ledger instead of assumed:

* the rate floor is `Summary.Derived.two_pow_binaryRateFloor_mul_flatProduct_le_or_eq_zero`,
  which is unconditional because `ofRows` sets `binaryRateFloor := 0` exactly on
  the tables that certify no rate;
* the degenerate alternative is closed by `ambientCapacity_pos`, since a zero
  rate demands only `1 ≤ ambientCapacity`.

Read on the multi-scale window package of `lem:p13-window-package`, the
exponent is the scale-free flatness cost `c₁₃ = log₂(∏W / ∏F)` times the
object's own dyadic scale count times `p₁₃`, and the right-hand side is the
labelled skeleton budget `binom(binom(n,2), m)` -- the manuscript's
`(c₁₃ - o(1)) p₁₃ log₂ n ≤ (3/2) n log₂ n + o(n log n)` in exact `Nat` form.
No numeral, no rounding, and no `o(·)` term enters, and every symbol is a read
from the stage this ledger is indexed by. -/
theorem two_pow_binaryRateFloor_mul_packingCount_le_ambientCapacity
    (ledger : CapLedger Stage) (stage : Stage) :
    2 ^ ((ledger.barrierSummary.read stage).binaryRateFloor *
          ledger.packingCount.read stage) ≤
      ledger.ambientCapacity.read stage := by
  rcases (ledger.barrierDerived.read
      stage).two_pow_binaryRateFloor_mul_flatProduct_le_or_eq_zero with
    rateFloor | rateZero
  · exact ledger.two_pow_rate_mul_packingCount_le_ambientCapacity stage
      rateFloor (ledger.barrierFlatPositive.read stage)
  · rw [rateZero, Nat.zero_mul, pow_zero]
    exact ledger.ambientCapacity_pos.read stage

/-- **The rate ceiling of the compared barrier table, read off the density
ledger.**  `binaryRateFloor` under-reports the table's true flatness cost by
strictly less than one bit, and the two rates stay distinct: the floor is what
`two_pow_binaryRateFloor_mul_packingCount_le_ambientCapacity` spends, the
ceiling `binaryRateFloor + 1` is what the table can be charged with.  They
coincide only when `safeProduct / flatProduct` is an exact power of two, which
the registered `P₁₃` window table's `2 ^ 118.10858…` is not. -/
theorem safeProduct_le_two_pow_succ_binaryRateFloor_mul_flatProduct
    (ledger : CapLedger Stage) (stage : Stage) :
    (ledger.barrierSummary.read stage).safeProduct ≤
      2 ^ ((ledger.barrierSummary.read stage).binaryRateFloor + 1) *
        (ledger.barrierSummary.read stage).flatProduct :=
  (ledger.barrierDerived.read
      stage).safeProduct_le_two_pow_succ_binaryRateFloor_mul_flatProduct
    (ledger.barrierFlatPositive.read stage)

end CapLedger

end Hypostructure.Core.Strategy.FiniteDensityBudget
