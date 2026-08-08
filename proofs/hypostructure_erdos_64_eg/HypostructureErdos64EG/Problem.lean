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

-- The concrete routing label is a deeply nested product.  This affects only
-- elaboration depth in this problem module; no memory or heartbeat limit is
-- changed.
set_option maxRecDepth 100000

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

/-- The boundary-profile alphabet declared by this presentation. -/
abbrev SpineBoundaryProfile : Type :=
  Fin erdosReceiverLoadProfile.baselineDegree →
    Fin erdosReceiverLoadProfile.baselineDegree

/-- `Q_geom` as the product of the seven declared factor cardinalities.  This
is the paper's routed alphabet count without an executable product `Fintype`. -/
def spineRoutingLabelCard : Nat :=
  Fintype.card Graph.SameTokenBlockerRoles.Role *
    Fintype.card Graph.SameTokenBlockerRoles.TokenSubtype * 2 *
    (Fintype.card Graph.SameTokenRoutingGerms.PortStatus *
      Fintype.card Graph.SameTokenRoutingGerms.PortStatus) *
    ((3 ^ 3) * (3 ^ 3)) * (2 ^ 13) * 2

/-- The registered structural product is exactly the cardinality of the
paper's routed seven-coordinate label type. -/
lemma spineRoutingLabel_card_eq :
    Fintype.card (Graph.SameTokenRoutingGerms.RoutingLabel SpineBoundaryProfile
      (Graph.WindowCurvature.Label inducedPathOrder)) = spineRoutingLabelCard := by
  rw [Graph.SameTokenRoutingGerms.card_routingLabel]
  unfold spineRoutingLabelCard SpineBoundaryProfile
  simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool,
    Graph.WindowCurvature.Label]
  norm_num [erdosReceiverLoadProfile, inducedPathOrder]

/-- A conservative arithmetic bound for the registered structural product. -/
lemma spineRoutingLabelCard_le : spineRoutingLabelCard ≤ 2 ^ 35 := by
  have status : Fintype.card Graph.SameTokenRoutingGerms.PortStatus = 2 := by
    decide
  unfold spineRoutingLabelCard
  rw [Graph.SameTokenBlockerRoles.card_role,
    Graph.SameTokenBlockerRoles.card_blockerKind,
    Graph.SameTokenBlockerRoles.card_tokenSubtype, status]
  norm_num

/-- Generic arithmetic absorption of a routing-cardinality bound into the
paper's homogeneous-cap formula. -/
lemma homogeneousCap_formula_le (q : Nat) (qBound : q ≤ 2 ^ 35) :
    Graph.SameTokenBlockerRoles.sameTokenRoleBound *
      (((q + 1) - 1) * (2 * (q + 1) - 3)) ≤ 2 ^ 78 := by
  rw [Graph.SameTokenBlockerRoles.sameTokenRoleBound,
    Graph.SameTokenBlockerRoles.card_role,
    Graph.SameTokenBlockerRoles.card_blockerKind,
    Graph.SameTokenBlockerRoles.card_tokenSubtype]
  have second : 2 * (q + 1) - 3 ≤ 2 * q := by omega
  have first : q + 1 - 1 = q := by omega
  rw [first]
  calc
    36 * (q * (2 * (q + 1) - 3)) ≤ 36 * (q * (2 * q)) :=
      Nat.mul_le_mul_left 36 (Nat.mul_le_mul_left q second)
    _ ≤ 36 * ((2 ^ 35) * (2 * (2 ^ 35))) := by
      exact Nat.mul_le_mul_left 36
        (Nat.mul_le_mul qBound (Nat.mul_le_mul_left 2 qBound))
    _ ≤ 2 ^ 78 := by norm_num

/-- The routed homogeneous cap is bounded without evaluating `Fintype.card` of
the routing-label product. -/
lemma registeredHomogeneousCap_le :
    Graph.Strategy.Spine.registeredHomogeneousCap spineRoutingLabelCard ≤
      2 ^ 78 := by
  unfold Graph.Strategy.Spine.registeredHomogeneousCap
  unfold Graph.SameTokenBlockerRoles.homogeneousTokenCap
  unfold Graph.SameTokenBlockerRoles.homogeneousCapCharge
  unfold Graph.SameTokenBlockerRoles.geometricPatternBound
  apply homogeneousCap_formula_le
  exact spineRoutingLabelCard_le

/-- The manuscript's registered baseline surplus scale is small independently
of the routed geometric alphabet. -/
lemma surplusScaleCoefficient_le : surplusScaleCoefficient ≤ 2 ^ 10 := by
  norm_num [surplusScaleCoefficient, erdosReceiverLoadProfile,
    Graph.SameTokenBlockerRoles.homogeneousTokenCap,
    Graph.SameTokenBlockerRoles.geometricPatternBound,
    Graph.SameTokenBlockerRoles.homogeneousCapCharge,
    Graph.SameTokenBlockerRoles.sameTokenRoleBound,
    Graph.SameTokenBlockerRoles.card_role]

/-- A conservative bound for `C_sp`, derived from the routed cap and the
registered surplus scale without computing either finite alphabet. -/
lemma registeredSpineScale_le :
    Graph.Strategy.Spine.registeredSpineScale spineRoutingLabelCard
      erdosReceiverLoadProfile.baselineDegree
      surplusScaleCoefficient ≤ 2 ^ 85 := by
  change 2 * (1 + 2 *
      (Graph.Strategy.Spine.registeredHomogeneousCap spineRoutingLabelCard)) +
    (2 * surplusScaleCoefficient +
      2 * (Graph.Strategy.Spine.registeredHomogeneousCap
        spineRoutingLabelCard) *
        (3 * (erdosReceiverLoadProfile.baselineDegree - 1) + 2)) ≤ 2 ^ 85
  have cap := registeredHomogeneousCap_le
  have surplus := surplusScaleCoefficient_le
  norm_num [erdosReceiverLoadProfile] at *
  omega

/-- The registered rate has the strict margin needed by the paper's
net-charge comparison at the chosen sufficiently-large exponent. -/
lemma registeredNetChargeRate :
    (erdosReceiverLoadProfile.loadMultiplier *
        (erdosReceiverLoadProfile.baselineDegree * inducedPathOrder -
          2 * (inducedPathOrder - 1)) + inducedPathOrder) * (512 + 1) *
        erdosReceiverLoadProfile.baselineDegree <
      2 * FiniteChecks.P13Barrier.windowRate * 512 := by
  rw [FiniteChecks.P13Barrier.windowRate_eq]
  norm_num [erdosReceiverLoadProfile, inducedPathOrder]

/-- The registered order is past the square of the exact surplus coefficient.
The proof uses only the structural bound on `C_sp`; it never evaluates the
routed homogeneous cap. -/
lemma registeredLargeOrder_dominates_surplus :
    4 * (((erdosReceiverLoadProfile.loadMultiplier *
            (erdosReceiverLoadProfile.baselineDegree * inducedPathOrder -
              2 * (inducedPathOrder - 1)) + inducedPathOrder) * (512 + 1) +
          2 * FiniteChecks.P13Barrier.windowRate * 512 *
            erdosReceiverLoadProfile.loadMultiplier) *
        (Graph.Strategy.Spine.registeredSpineScale spineRoutingLabelCard
          erdosReceiverLoadProfile.baselineDegree
          surplusScaleCoefficient)) *
      (((erdosReceiverLoadProfile.loadMultiplier *
            (erdosReceiverLoadProfile.baselineDegree * inducedPathOrder -
              2 * (inducedPathOrder - 1)) + inducedPathOrder) * (512 + 1) +
          2 * FiniteChecks.P13Barrier.windowRate * 512 *
            erdosReceiverLoadProfile.loadMultiplier) *
        (Graph.Strategy.Spine.registeredSpineScale spineRoutingLabelCard
          erdosReceiverLoadProfile.baselineDegree
          surplusScaleCoefficient)) ≤ 2 ^ 512 := by
  let scale := Graph.Strategy.Spine.registeredSpineScale spineRoutingLabelCard
    erdosReceiverLoadProfile.baselineDegree
    surplusScaleCoefficient
  have scaleBound : scale ≤ 2 ^ 85 := by
    simpa [scale] using registeredSpineScale_le
  rw [FiniteChecks.P13Barrier.windowRate_eq]
  change 4 * (520777 * scale) * (520777 * scale) ≤ 2 ^ 512
  have coefficientBound : 520777 ≤ 2 ^ 19 := by norm_num
  have productBound : 520777 * scale ≤ 2 ^ 104 := by
    calc
      520777 * scale ≤ (2 ^ 19) * (2 ^ 85) :=
        Nat.mul_le_mul coefficientBound scaleBound
      _ = 2 ^ 104 := by rw [← pow_add]
  calc
    4 * (520777 * scale) * (520777 * scale)
        ≤ 4 * (2 ^ 104) * (2 ^ 104) := by gcongr
    _ = 2 ^ 210 := by norm_num [← pow_add]
    _ ≤ 2 ^ 512 := Nat.pow_le_pow_right (n := 2) (by norm_num) (by norm_num)

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
  -- The quadrilateral the high-centre normal form excludes: `4 = 2 ^ 2` is a
  -- power-of-two length, so it is one of this problem's accepted cycles.
  quadrilateralAccepted := Core.DyadicLength.powerOfTwoLength_four
  -- The degenerate closure `lem:labels` never counts: `2 = 2 ^ 1` is below the
  -- exponent floor of this problem's accepted lengths, so a single attachment
  -- counted twice closes nothing.
  degenerateClosureRejected := by decide
  -- The marked-fan slack the local Type B fan ledger spends: the label algebra's
  -- own packing number at the registered order leaves the closed-neighbour
  -- deficit nonnegative slack against this problem's discharge scale.  The value
  -- is computed once, in `WindowAlgebra.fanPackingCap_succ_le`; nothing here
  -- writes the manuscript's `8`.
  fanCapSlack := by
    simpa [erdosReceiverLoadProfile] using WindowAlgebra.fanPackingCap_succ_le
  -- `prop:fan-closed-port-typeB-routing` (b) at the smallest high-centre degree:
  -- the manuscript's `12 < 13`, decided on the registered numbers.
  highCentreDeficitSlack := by norm_num [erdosReceiverLoadProfile]
  -- `lem:capacity-token-supply`'s `15 ≤ 2·13`, decided on the registered
  -- baseline and the registered window order.
  joinSlack := by norm_num [erdosReceiverLoadProfile, inducedPathOrder]
  -- `def:same-token-routing-germs`' routing-label alphabet, at this
  -- presentation's own two declared coordinates.  The boundary-degree profile of
  -- a *bounded* port support is a degree function on at most `δ` boundary
  -- vertices taking values below `δ` -- `T(p) = {a_p, b_p, x(p)}` is the
  -- registered baseline's own size -- and the `P₁₃` label is the window's own
  -- `order`-bit label code.  The five remaining coordinates are the framework's
  -- own finite alphabets, so `Q_geom` is certified against `Fintype.card` of
  -- the tuple while its arithmetic uses the structural factor product above.
  -- Only the boundary-degree profile alphabet is registered: the `P₁₃` label is
  -- the labelling's own `Graph.WindowCurvature.Label inducedPathOrder`, derived
  -- from the window order this record already registers.  The profile of a
  -- *bounded* port support `T(p) = {a_p, b_p, x(p)}` is a degree function on at
  -- most `δ` boundary vertices taking values below `δ`.
  BoundaryProfile := SpineBoundaryProfile
  boundaryProfileFintype := inferInstance
  boundaryProfileInhabited :=
    ⟨fun _ => ⟨0, by norm_num [erdosReceiverLoadProfile]⟩⟩
  routingLabelBound := spineRoutingLabelCard
  routingLabelBound_eq := spineRoutingLabel_card_eq.symm
  -- The universal quadratic absorption coefficient is covered by this
  -- problem's declared same-token role alphabet.  Both finite cardinalities
  -- are derived from the constructor lists in `SameTokenBlockerRoles`; the
  -- framework does not assume a hardcoded role lower bound.
  roleSafety := by
    rw [Graph.TokenLoad.quadraticSafetyScale,
      Graph.SameTokenBlockerRoles.sameTokenRoleBound,
      Graph.SameTokenBlockerRoles.card_role,
      Graph.SameTokenBlockerRoles.card_blockerKind,
      Graph.SameTokenBlockerRoles.card_tokenSubtype]
    norm_num
  surplusScale := surplusScaleCoefficient
  windowRate := FiniteChecks.P13Barrier.windowRate
  -- `lem:p13-window-package`'s selected dyadic scales.  The manuscript writes
  -- `⌊log₂ n⌋ − O(1)`; this presentation registers no discard, so the selection
  -- is the object's own dyadic scale count.  The `O(1)` remains available to a
  -- refinement that needs it -- `separatedScaleCount_le` and
  -- `separatedScaleReach` are exactly what a nonzero discard has to satisfy.
  separatedScaleCount := Nat.log2
  separatedScaleCount_le := fun _size => le_refl _
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
  -- obligations below are what make it a *valid* one, and both are proved from
  -- the registered numbers rather than computed by unfolding the routed cap.
  largeOrderExponent := 512
  largeOrderExponent_pos := by norm_num
  -- With no discard the reach is the registered exponent lying below the
  -- object's own scale count, which is what `2 ^ k ≤ n` says.
  separatedScaleReach := by
    intro size large
    have reach : 512 ≤ Nat.log2 size := by
      have monotone := Nat.log_mono_right (b := 2) large
      rw [Nat.log_pow (by norm_num)] at monotone
      simpa [Nat.log2_eq_log_two] using monotone
    calc 512 * (Nat.log2 size + 1)
        = 512 * Nat.log2 size + 512 := by
          ring
      _ ≤ 512 * Nat.log2 size + Nat.log2 size :=
          Nat.add_le_add_left reach _
      _ = (512 + 1) * Nat.log2 size := by ring
  -- `τ_win < ¼` cleared of denominators.  Every factor is registered -- the
  -- baseline, the window order, the discharge scale, the order exponent, and
  -- the audited table's own rate -- so the comparison is decided, not written.
  netChargeRate := registeredNetChargeRate
  -- The registered order is past the square of the coefficient the net-charge
  -- collision carries against the surplus.  `Data.surplusThreshold_sublinear`
  -- derives `σ(G) = O(√n) = o(n)` from this; no decimal or intermediate
  -- product is spelled anywhere.
  largeOrder_dominates_surplus := registeredLargeOrder_dominates_surplus
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
  -- `lem:typeB-bridge-deficit-bound`'s factor.  The manuscript charges each
  -- Type B bridge residual at `No_-(X) ≤ 8 Σ_{h}(d_G(h) − 3)` and remarks that
  -- the estimate "is equivalent to `27k ≥ 85`, and holds for every `k ≥ 4`", so
  -- the factor is a round choice above a floor rather than a forced value.  It
  -- is a presentation constant of this manuscript, registered here in the same
  -- way as the order exponent above.
  bridgeMassFactor := 8
  -- `27k ≥ 85` at the registered baseline and discharge scale: `3 + 2 + 4 ≤ 32`.
  -- Decided on the registered numbers, not restated as a numeral.
  bridgeMassSlack := by norm_num [erdosReceiverLoadProfile]

end HypostructureErdos64EG
