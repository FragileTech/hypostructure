import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Paths
import Hypostructure.Graph.MinimumDegreeCycleTarget
import Hypostructure.Graph.ReceiverLoad
import Hypostructure.Graph.SameTokenBlockerRoles
import Hypostructure.Graph.Strategy.SpineVocabulary
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
non-near-cubic branch supplies.  The cap is computed from the cardinality of
the manuscript's complete routing-label alphabet at this presentation's
baseline degree and window order; the scale is the framework's `⌈√n⌉`. -/

/-- `C_sp`, one more than the uniform homogeneous-token cap at the registered
seven-coordinate routing-label alphabet. -/
def surplusScaleCoefficient : Nat :=
  let threshold := erdosReceiverLoadProfile.baselineDegree
  let order := inducedPathOrder
  Graph.SameTokenBlockerRoles.homogeneousTokenCap
      (Fintype.card Graph.SameTokenBlockerRoles.Role *
        Fintype.card Graph.SameTokenBlockerRoles.TokenSubtype * 2 *
        (Fintype.card Graph.SameTokenRoutingGerms.PortStatus *
          Fintype.card Graph.SameTokenRoutingGerms.PortStatus) *
        ((threshold ^ threshold) * (threshold ^ threshold)) *
        (2 ^ order) * 2) + 1


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

set_option maxRecDepth 4096 in
/-- The single presentation value read by the generic spine.  Its mathematical
fields are either problem constants or proofs derived directly from those
constants; there is no application-owned executor, router, or proof ledger. -/
noncomputable def spineData : Graph.Strategy.Spine.Data.{u} where
  threshold := erdosReceiverLoadProfile.baselineDegree
  threshold_eq_three := by norm_num [erdosReceiverLoadProfile]
  three_le_threshold := by norm_num [erdosReceiverLoadProfile]
  LengthOK := PowerOfTwoLength
  lengthOK_iff_powerOfTwo := fun _length => Iff.rfl
  windowOrder := inducedPathOrder
  windowOrder_pos := by norm_num [inducedPathOrder]
  labelCount := WindowAlgebra.labels_enumeration.1
  labelSizeDistribution := by
    rw [WindowAlgebra.labels_enumeration.2]
    rfl
  freeForcesTarget := fun object baseline free =>
    externalHasCycleWithLength
      (fun _length witness => Core.DyadicLength.powerOfTwoLength_of_exists witness)
      (by norm_num [externalMinimumDegree, erdosReceiverLoadProfile])
      object baseline free
  quadrilateralAccepted := Core.DyadicLength.powerOfTwoLength_four
  degenerateClosureRejected := by decide
  fanCapSlack := by
    simpa [erdosReceiverLoadProfile] using WindowAlgebra.fanPackingCap_succ_le
  highCentreDeficitSlack := by norm_num [erdosReceiverLoadProfile]
  joinSlack := by norm_num [erdosReceiverLoadProfile, inducedPathOrder]
  routingLabelBound :=
    Fintype.card Graph.SameTokenBlockerRoles.Role *
      Fintype.card Graph.SameTokenBlockerRoles.TokenSubtype * 2 *
      (Fintype.card Graph.SameTokenRoutingGerms.PortStatus *
        Fintype.card Graph.SameTokenRoutingGerms.PortStatus) *
      ((erdosReceiverLoadProfile.baselineDegree ^
          erdosReceiverLoadProfile.baselineDegree) *
        (erdosReceiverLoadProfile.baselineDegree ^
          erdosReceiverLoadProfile.baselineDegree)) *
      (2 ^ inducedPathOrder) * 2
  routingLabelBound_eq := by
    rw [Graph.SameTokenRoutingGerms.card_routingLabel]
    simp only [Fintype.card_fun, Fintype.card_fin,
      Graph.WindowCurvature.Label]
    norm_num [erdosReceiverLoadProfile, inducedPathOrder]
  roleSafety := by
    rw [Graph.TokenLoad.quadraticSafetyScale,
      Graph.SameTokenBlockerRoles.sameTokenRoleBound,
      Graph.SameTokenBlockerRoles.card_role,
      Graph.SameTokenBlockerRoles.card_blockerKind,
      Graph.SameTokenBlockerRoles.card_tokenSubtype]
    norm_num
  surplusScale := surplusScaleCoefficient
  baselineDeficitSafety := by
    have statusCard :
        Fintype.card Graph.SameTokenRoutingGerms.PortStatus = 2 := by
      decide
    norm_num [Graph.baselineDeficitCoefficient, surplusScaleCoefficient,
      Graph.SameTokenBlockerRoles.homogeneousTokenCap,
      Graph.SameTokenBlockerRoles.homogeneousCapCharge,
      Graph.SameTokenBlockerRoles.geometricPatternBound,
      Graph.SameTokenBlockerRoles.sameTokenRoleBound,
      Graph.SameTokenBlockerRoles.card_role,
      Graph.SameTokenBlockerRoles.card_blockerKind,
      Graph.SameTokenBlockerRoles.card_tokenSubtype,
      statusCard, erdosReceiverLoadProfile, inducedPathOrder]
  windowRate := FiniteChecks.P13Barrier.windowRate
  windowBarrier :=
    { size := FiniteChecks.P13Barrier.labelCount
      profile := FiniteChecks.P13Barrier.semanticProfile
      Length := Fin 15
      lengthValue := fun length => length.1
      relation := fun length =>
        FiniteChecks.P13Barrier.semanticRelation length.1
      Index := FiniteChecks.P13Barrier.AcceptedPair
      indexFintype := inferInstance
      table := FiniteChecks.P13Barrier.certifiedTable
      flatPositive := by native_decide
      improves := by native_decide }
  windowBarrierLabel := FiniteChecks.P13Barrier.barrierLabel
  windowBarrierLabel_mem := FiniteChecks.P13Barrier.barrierLabel_mem
  windowBarrierLabel_injective :=
    FiniteChecks.P13Barrier.barrierLabel_injective
  windowBarrierLabel_surjective :=
    FiniteChecks.P13Barrier.barrierLabel_surjective
  windowBarrier_left_semantic := FiniteChecks.P13Barrier.leftRow_eq_safe
  windowBarrier_right_semantic := FiniteChecks.P13Barrier.rightRow_eq_safe
  windowBarrier_sum_semantic := FiniteChecks.P13Barrier.sumRow_eq_safe
  windowRate_eq_barrier := rfl
  separatedScaleCount := Nat.log2
  separatedScaleCount_le := fun _size => le_refl _
  separatedScaleCount_eq_log2 := fun _size => rfl
  netCapRateSlack := by
    rw [FiniteChecks.P13Barrier.windowRate_eq]
    norm_num [Graph.FiniteObject.netCapWindowCost, erdosReceiverLoadProfile,
      inducedPathOrder]
  curvatureCost :=
    Hypostructure.Core.Finite.CertifiedTableAggregation.binaryRowRateFloor
      FiniteChecks.P13Barrier.certifiedTable
      ⟨(⟨1, by norm_num⟩, ⟨1, by norm_num⟩), by norm_num⟩
  curvatureBarrierRow :=
    ⟨(⟨1, by norm_num⟩, ⟨1, by norm_num⟩), by norm_num⟩
  curvatureCost_eq_barrierRow := rfl
  entropyDenominator :=
    erdosReceiverLoadProfile.remainderEntropyThresholdDenominator
  entropyDenominator_pos := by norm_num [erdosReceiverLoadProfile]
  dischargeScale := erdosReceiverLoadProfile.loadMultiplier
  dischargeScale_pos := by norm_num [erdosReceiverLoadProfile]
  bridgeMassFactor := 8
  bridgeMassSlack := by norm_num [erdosReceiverLoadProfile]
  bridgeDeletionSlack := by norm_num [erdosReceiverLoadProfile]


end HypostructureErdos64EG
