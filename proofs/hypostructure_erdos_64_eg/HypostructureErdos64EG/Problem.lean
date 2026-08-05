import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Paths
import Hypostructure.Graph.MinimumDegreeCycleTarget
import Hypostructure.Graph.ReceiverLoad
import Hypostructure.Graph.SameTokenBlockerRoles
import Hypostructure.Graph.Strategy.SpineRun
import Hypostructure.Core.CeilSqrt
import Hypostructure.Core.DyadicLength
import HypostructureErdos64EG.WindowAlgebra
import HypostructureErdos64EG.FiniteChecks.P13Barrier.Table

/-!
# Erdős problem 64: the problem, its target, and its registered data

This is the whole application boundary.  It declares the public statement, one
Core problem, one Core target, and the one record of registered data the
framework's entry spine reads.  It contains no theorem about the proof, no
strategy, no executor, no ledger operation, and no DAG.

Everything the framework needs that is *specific to this problem* enters
through `spineData` below: the baseline degree, the accepted cycle lengths, the
window order, the external closure law, the surplus threshold, and the barrier
rate.  Each is either a presentation parameter or a projection of an already
registered object -- the external theorem of `WindowAlgebra.lean`, or the
audited finite table of `FiniteChecks/P13Barrier`.  The framework reads them
from here; nothing in `Hypostructure.Graph` or `Hypostructure.Core` names this
problem.
-/

namespace HypostructureErdos64EG

open Hypostructure

universe u

/-! ## The public statement

Pinned verbatim against the right-hand side of `Erdos64.erdos_64` in Google
DeepMind's `formal-conjectures`, at
`FormalConjectures/ErdosProblems/64.lean`:

> theorem erdos_64 :
>     answer(..) ↔ ∀ (V : Type*) (G : SimpleGraph V) [Fintype V]
>         [DecidableRel G.Adj],
>         G.minDegree ≥ 3 → ∃ (k : ℕ) (v : V) (c : G.Walk v v),
>             k ≥ 2 ∧ c.IsCycle ∧ c.length = 2^k

(the upstream declaration's own placeholder is elided above so that this file
contains no unfinished-proof token; it is `answer(_)` in the source).

The statement below is that right-hand side, binder for binder.  It stays in
Mathlib's `SimpleGraph` vocabulary: the application bridges its packed finite
graph to this proposition rather than replacing the public proposition with an
application-specific one. -/

/-- Official mathematical proposition for Erdős Problem 64. -/
def OfficialStatement : Prop :=
  ∀ (V : Type*) (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj],
    G.minDegree ≥ 3 →
      ∃ (k : Nat) (v : V) (c : G.Walk v v),
        k ≥ 2 ∧ c.IsCycle ∧ c.length = 2 ^ k

/-! ## The problem presentation -/

/-- Receiver/load parameters are part of the problem presentation.  They are
not strategy-local constants: Core carries them in `Problem.presentation`.

`remainderEntropyThresholdDenominator := 10` is the manuscript's own two-budget
threshold: node [50] asks `η(R) ≥ (1/10)·log₂ n` for the per-vertex skeleton
entropy of `def:remainder-entropy`, and `prop:two-budget` splits its branches
on exactly that comparison.  It is a proof-design threshold chosen by the
argument, not a quantity measured from a graph, so it is declared here with the
other presentation parameters. -/
def erdosReceiverLoadProfile :
    Graph.ReceiverLoad.LoadCapacityProfile where
  baselineDegree := 3
  loadMultiplier := 4
  remainderEntropyThresholdDenominator := 10
  dischargeRate_gt := by norm_num
  dischargeRate_le := by norm_num

/-- The sole baseline hypothesis in the official theorem, with its threshold
read from the registered problem presentation. -/
abbrev Baseline (object : Graph.FiniteObject.{u}) : Prop :=
  Graph.MinimumDegreeAtLeast erdosReceiverLoadProfile.baselineDegree object

def BranchState (_object : Graph.FiniteObject.{u}) : Type := Unit

/-- The minimal domain-neutral problem registration for Problem 64. -/
abbrev problem : Core.Problem :=
  Graph.problemWithPresentation Baseline BranchState
    Graph.ReceiverLoad.LoadCapacityProfile erdosReceiverLoadProfile

/-! The accepted cycle lengths are the framework's executable dyadic length
family; the manuscript's `2^k`, `k ≥ 2` is that predicate at every occurrence
below. -/
export Hypostructure.Core.DyadicLength (PowerOfTwoLength powerOfTwoLength_iff)

/-- A packed graph realizes the target when it has an accepted Mathlib cycle. -/
def Target (object : Graph.FiniteObject.{u}) : Prop :=
  Graph.HasCycleWithLength PowerOfTwoLength object

/-- The single public target contract.  Its `Statement` is the pinned
`OfficialStatement` and its `Predicate` is `Target`; both bridge directions are
the framework's. -/
def target : Core.Target problem :=
  Graph.minimumDegreeCycleTarget erdosReceiverLoadProfile.baselineDegree
    BranchState
    Graph.ReceiverLoad.LoadCapacityProfile erdosReceiverLoadProfile
    PowerOfTwoLength (fun exponent => exponent ≥ 2) (fun exponent => 2 ^ exponent)
    powerOfTwoLength_iff

/-! ## The registered scale threshold

`C_sp` of node `[19]`.  The manuscript fixes it as one more than the uniform
homogeneous-token cap of `cor:homogeneous-same-token-caps-close`, so that the
successor absorbs the additive one in the routed bound `1 + √(M₀ n)` that the
non-near-cubic branch supplies.  Both factors are read: the cap from the
framework's role alphabet at this problem's own baseline degree, and the scale
from the framework's `⌈√n⌉`. -/

/-- `C_sp`, one more than the uniform homogeneous-token cap at the registered
baseline degree. -/
def surplusScaleCoefficient : Nat :=
  Graph.SameTokenBlockerRoles.homogeneousTokenCap
      erdosReceiverLoadProfile.baselineDegree + 1


/-! ## The registered curvature-rank allowance

Node `[32]` is the only comparison of the spine whose manuscript form still
carries an asymptotic term, `o(W₂)`, after the exact substitutions of nodes
`[29]`--`[30]`.  Like the scale threshold above, it is registered here rather
than written at the node. -/

/-- **Not yet pinned.**  The manuscript's `o(W₂)` at node `[32]`, registered as
the zero allowance.

Node `[32]` is not among the ported rows: no fact the entry spine commits
mentions `rankDefect`, and the two keys whose statements do -- the node-`[32]`
rank-drop and full-rank arms -- are not produced by `Spine.run`.  So this value
is a placeholder that nothing currently proved depends on, and the node-`[32]`
port must replace it with the allowance the manuscript's estimate supplies
before either arm is committed. -/
def nodeThirtyTwoRankAllowance (_wedgeSupply : Nat) : Nat := 0

/-! ## The registered curvature coordinate cost

`c_Ω` of nodes `[48]` and `[53]` is registered directly in `spineData` below.
`lem:curv-enum` computes it as `log₂(543958/111286)` by the same direct finite
enumeration the window rate comes from: `543958` is the number of locally safe
wedges `(S, A, T)` with `C₁(S,A) = C₁(A,T) = 1`, and `111286` is its
curvature-flat subfamily.  Those two counts are the audited barrier table's own
certified safe and flat counts at the length-`1` connector pair, so the cost is
read off the table rather than copied out of the manuscript. -/

/-! ## The registered data of the entry spine

Every number the spine compares comes from this record.  No row writes one. -/

/-- **The data this problem registers with the framework's entry spine.**

`freeForcesTarget` is the Hegde--Sandeep--Shashank theorem of
`WindowAlgebra.lean` at this problem's own threshold and length predicate, and
`windowRate` is the audited barrier table's own derived rate.  Both are inputs
of this problem, supplied here; the framework holds neither. -/
noncomputable def spineData : Graph.Strategy.Spine.Data.{u} where
  threshold := erdosReceiverLoadProfile.baselineDegree
  three_le_threshold := by norm_num [erdosReceiverLoadProfile]
  LengthOK := PowerOfTwoLength
  windowOrder := inducedPathOrder
  windowOrder_pos := by norm_num [inducedPathOrder]
  freeForcesTarget := fun object baseline free =>
    externalHasCycleWithLength
      (fun _length witness => Core.DyadicLength.powerOfTwoLength_of_exists witness)
      (by norm_num [externalMinimumDegree, erdosReceiverLoadProfile])
      object baseline free
  surplusScale := surplusScaleCoefficient
  windowRate := FiniteChecks.P13Barrier.windowRate
  rankDefect := nodeThirtyTwoRankAllowance
  -- `c_Ω`, as the natural number the spine multiplies by: the framework's
  -- `binaryRowRateFloor` of the audited barrier table's length-`1` connector
  -- row, which rounds *down*, so the forced cost node `[48]` states is no
  -- larger than the real one.  It is a projection of the audited counts, not a
  -- numeral: nothing downstream has a table parameter to fill.
  curvatureCost :=
    Hypostructure.Core.Finite.CertifiedTableAggregation.binaryRowRateFloor
      FiniteChecks.P13Barrier.certifiedTable
      ⟨(⟨1, by norm_num⟩, ⟨1, by norm_num⟩), by norm_num⟩
  -- Node `[50]`'s `10` and node `[58]`'s `4`, both already carried by the
  -- registered receiver/load presentation: the manuscript's two-budget
  -- threshold denominator and its discharge scale.
  entropyDenominator :=
    erdosReceiverLoadProfile.remainderEntropyThresholdDenominator
  entropyDenominator_pos := by norm_num [erdosReceiverLoadProfile]
  dischargeScale := erdosReceiverLoadProfile.loadMultiplier
  dischargeScale_pos := by norm_num [erdosReceiverLoadProfile]
  -- The manuscript's "for all sufficiently large `n`" of
  -- `prop:negative-net-charge`, as a binary exponent.  It is a presentation
  -- choice, like the two-budget denominator and the discharge scale; the two
  -- obligations below are what make it a *valid* one, and both are decided on
  -- the registered numbers rather than restated as numerals here.
  largeOrderExponent := 56
  largeOrderExponent_pos := by norm_num
  -- `τ_win < ¼` cleared of denominators.  Every factor is registered -- the
  -- baseline, the window order, the discharge scale, the order exponent, and
  -- the audited table's own rate -- so the comparison is decided, not written.
  netChargeRate := by native_decide
  -- The registered order is past the square of the coefficient the net-charge
  -- collision carries against the surplus.  `Data.surplusThreshold_sublinear`
  -- derives `σ(G) = O(√n) = o(n)` from this; no decimal or intermediate
  -- product is spelled anywhere.
  largeOrder_dominates_surplus := by native_decide
  -- `def:declared-coordinate-signature` at this problem's own window order.
  -- The signature is "fixed once and for all" in the manuscript, so the
  -- framework registers it once, complete: all thirty-two generating kinds of
  -- clauses (D1)--(D7), with (D8) as its own closure.  The bounded active
  -- interface is derived from the order -- the manuscript's additive `30` is
  -- `2·13 + 2·2`, "the two `P₁₃`-window interfaces and the two boundary stubs"
  -- -- so nothing is spelled here and this problem supplies only its order.
  coldSignature := Graph.ColdCorridor.declaredSignature inducedPathOrder
    (by norm_num [inducedPathOrder])
  coldSignature_windowOrder := rfl

end HypostructureErdos64EG
