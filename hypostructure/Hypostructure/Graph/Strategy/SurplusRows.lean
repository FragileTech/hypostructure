import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.SparsePortActivation
import Hypostructure.Graph.PrimitiveCarrier
import Hypostructure.Graph.SparsePairLedger
import Hypostructure.Graph.SameTokenBlockerRoles
import Hypostructure.Graph.SparseEntropySandwich
import Hypostructure.Graph.CapacityTokenAssignment
import Hypostructure.Graph.SparseUpperEnvelope
import Hypostructure.Graph.ObjectCapacityLedger
import Hypostructure.Graph.Induced
import Hypostructure.Graph.Contracts.SurplusPair.BlockerRoute
import Hypostructure.Graph.Contracts.SurplusPair.Activation
import Hypostructure.Graph.Contracts.SurplusPair.PairSchedule

/-!
# The sparse surplus branch: the activation rows

Nodes `[126]`--`[128]` of the non-near-cubic branch, the arm node `[19]` sends
an object whose degree surplus exceeds the registered scale threshold.

Each row is one atomic Strategy over the one canonical `ExactLedger`.  A row
reads its prerequisites by exact semantic key through sealed `FactInputs`,
proves the manuscript's statement about the residual's own object, and commits
exactly that statement.  Nothing is transported outside the ledger and no row
names a producer or an execution position.

* `sparseSlackSurplusRow` is `lem:sparse-slack-surplus`.  The manuscript's two
  displays, `σ(G) = n − 6 − 2λ` and `m = (3/2)n + (1/2)σ(G)`, are one identity
  cleared of division and of the `λ = 2n − 3 − m` abbreviation: `2m = δn + σ(G)`
  at the registered baseline.  It is an identity of the surplus observable's own
  definition once the handshake bound `δn ≤ 2m` is available, and that bound is
  the standing baseline read off the residual.
* `activeSurplusFamilyRow` is `lem:sparse-excess-port-extraction` together with
  the family statement of `lem:surviving-active-family`: the excess selector has
  exactly `σ(G)` members, and each of them is a port whose centre is strictly
  above the baseline, whose endpoint sits exactly at it, and which therefore
  carries exactly `δ − 1` shoulders.  The endpoint's degree is node `[10]`'s
  independence spent, not re-proved: the row reads the committed
  slack-independence fact.
* `sparsePortActivationRow` is `lem:sparse-port-activation` clauses (a)--(d).
  Clause (b) is the return path `R_p ⊆ G − c(p)x(p)`, which `lem:bridgeless` --
  the edge contraction of `Graph/Contraction.lean` -- supplies from the same
  minimality and avoidance; clause (c) is the suppression witness `Q_p`, which
  minimality and avoidance supply through `TightVertexSuppression`; clause (d)
  is the triangle of a triangular port.
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-! ## Node `[126]`: the sparse slack identity -/

/-- `lem:sparse-slack-surplus`, cleared of division: `2m = δn + σ(G)`.

The manuscript writes `m = (3/2)n + (1/2)σ(G)` and, with `λ = 2n − 3 − m`,
`σ(G) = n − 6 − 2λ`; substituting the abbreviation turns the second display into
the first, and doubling the first is the exact `Nat` identity committed here.
The only input is the standing baseline, which the executor reads off the
residual rather than from a fact. -/
@[reducible] noncomputable def sparseSlackSurplusRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.sparseSlackSurplus
    { Requires := []
      Produces := [K .sparseSlackSurplus]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .sparseSlackSurplus)
        ⟨Graph.Contracts.SurplusPair.sparseSlackSurplus_of_baseline inputs.current.baseline⟩
        .nil)

/-! ## Node `[127]`: the excess selector and its count -/

/-- `lem:sparse-excess-port-extraction`, and with it the family half of
`lem:surviving-active-family`.

`|𝒫_exc| = σ(G)` is the count of the excess selector; the per-port clauses are
the manuscript's *"the vertex `h` has degree at least `4`, the vertex `x` has
degree `3`, and `N_G(x) = {h, a_p, b_p}`"*, stated at the registered baseline as
`δ < d(c(p))`, `d(x(p)) = δ`, and `|s(p)| = δ − 1`.

Node `[10]`'s independence is consumed, not re-proved: it is the committed
slack-independence fact, and it is exactly what forces a port's endpoint down to
the baseline. -/
@[reducible] noncomputable def activeSurplusFamilyRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.activeSurplusFamily
    { Requires := [K .slackIndependent]
      Produces := [K .activeSurplusFamily]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .activeSurplusFamily)
        ⟨Graph.Contracts.SurplusPair.activeSurplusFamily_of_slackIndependent inputs.current.baseline
          (inputs.get (K .slackIndependent)).down⟩
        .nil)

/-! ## Node `[128]`: port activation -/

/-- `lem:sparse-port-activation`, clauses (a)--(d).

At a selected port whose endpoint carries a shoulder *pair* -- which at the
manuscript's `δ = 3` is every selected port, by the previous row's `|s(p)| =
δ − 1` -- the two cases of the lemma are:

* the port is *open*, and the row reads the already published single-port
  suppression witness through `FactInputs.get`.  That witness is the simple
  shoulder-to-shoulder path `Q_p ⊆ G − x(p)` whose restored length is accepted,
  namely the manuscript's `2^{j(p)} − 1` with `j(p) ≥ 2` at the registered
  accepted set;
* the port is *triangular*, and the triangle `x a_p b_p x` is present.

Clause (a) is the shoulder pair itself, which is the row's own hypothesis at
each port.  Clause (b) is the return path `R_p ⊆ G − c(p)x(p)`: the port's own
edge is not a bridge, because contracting it gives a strictly smaller object
still meeting the baseline, and minimality and avoidance close it exactly as
they close the suppression.  Its first edge after `x(p)` is a shoulder. -/
@[reducible] noncomputable def sparsePortActivationRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.sparsePortActivation
    { Requires := [K .selection, K .singleOpenPortSuppressionWitness]
      Produces := [K .sparsePortActivation]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .sparsePortActivation)
        ⟨Graph.Contracts.SurplusPair.sparsePortActivation_of_selection inputs.current.baseline
          (inputs.get (K .selection)).down
          (inputs.get (K .singleOpenPortSuppressionWitness)).down⟩
        .nil)

/-- The completed active family, read only from the three incoming facts. -/
@[reducible] noncomputable def activeSurplusDemandsRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.activeSurplusDemands
    { Requires := [K .sparseSurplusSurvivor, K .activeSurplusFamily, K .sparsePortActivation]
      Produces := [K .activeSurplusDemands]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .activeSurplusDemands)
        ⟨Graph.Contracts.SurplusPair.activeSurplusDemands_of_activation data.threshold_eq_three
          (inputs.get (K .activeSurplusFamily)).down
          (inputs.get (K .sparsePortActivation)).down⟩
        .nil)

/-! ## Node `[129]`: the active family and baseline demand -/

/-- `def:baseline-spine-demand` on the literal sparse-surplus survivor.

The family is not an empty or numerically supplied coordinate carrier.  It is
the clause-(D8) family of labelled Boolean quotient images of the full-support
clause-(D2) return-data profile.  Its cardinality is the cubic-baseline exponent
computed from the current object and the registered baseline.  A functional
quotient that identified two of these declared coordinates would localize to
exactly one of the paper's replacement or delocalization exits, both excluded
by the incoming survivor fact.  The row publishes the stronger realization the
paper requires: every Boolean response word is read from an actual labelled
graph in the current fixed-edge stratum.  Its exponent is the largest uniform
cubic-baseline rate supplied by the current sparse envelope, and the resulting
deficit is bounded linearly using the registered coefficient inequality. -/
@[reducible] noncomputable def baselineSpineDemandRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.baselineSpineDemand
    { Requires := [K .activeSurplusDemands, K .sparseSurplusSurvivor, K .surplusAbove, K .noProperBaseline, K .tightEndpoint]
      Produces := [K .baselineSpineDemand]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .baselineSpineDemand)
        ⟨Graph.Contracts.SurplusPair.baselineSpineDemand_of_survivor inputs.current.baseline
          (inputs.get (K .activeSurplusDemands)).down
          (inputs.get (K .sparseSurplusSurvivor)).down
          (inputs.get (K .surplusAbove)).down
          (inputs.get (K .noProperBaseline)).down
          (inputs.get (K .tightEndpoint)).down
          data.three_le_threshold data.baselineDeficitSafety⟩
        .nil)

/-! ## Node `[132]`: route the dependent pair family -/

/-- Node `[130]`, canonical pair split "blocker-free?": exact case analysis on
the dependent predicate.  The independent arm is its literal negation. -/
noncomputable def pairResponseIndependenceDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous : ExactLedger (Input BranchState Presentation presentation data)
      current known)
    (independentFresh : K .independentPairFamily ∉ known)
    (dependentFresh : K .dependentPairFamily ∉ known) :
    Decision (K .independentPairFamily) (K .dependentPairFamily) previous := by
  classical
  exact Decision.run previous (K .independentPairFamily) (K .dependentPairFamily)
    `Hypostructure.Graph.Strategy.Spine.pairResponseIndependenceDichotomy
    (if blocked : Holds BranchState Presentation presentation data
        .dependentPairFamily current.object then
      .inr ⟨blocked⟩
    else
      .inl ⟨blocked⟩)
    independentFresh dependentFresh

/-! ## Node `[131]`: mixed sparse-spine dependence -/

/-- `lem:mixed-sparse-spine-dependence` on the literal independent residual of
`[130]`.  The concrete spine family and active pair schedule are read from the
same incoming ledger; the four-case circuit proof is published as one exact
semantic fact. -/
@[reducible] noncomputable def mixedSparseSpineDependenceRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.mixedSparseSpineDependence
    { Requires := [K .baselineSpineDemand]
      Produces := [K .mixedSparseSpineDependence]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .mixedSparseSpineDependence)
        ⟨Graph.Contracts.SurplusPair.mixedSparseSpineDependence_of_baseline
          (inputs.get (K .baselineSpineDemand)).down⟩
        .nil)

/-- `lem:exact-cubic-baseline-budget` at the current residual's order and
registered baseline.  The result is the manuscript's two-sided estimate with
logarithms cleared, published from the literal `[131]` residual. -/
@[reducible] noncomputable def exactCubicBaselineBudgetRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.exactCubicBaselineBudget
    { Requires := []
      Produces := [K .exactCubicBaselineBudget]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .exactCubicBaselineBudget)
        ⟨Graph.Contracts.SurplusPair.exactCubicBaselineBudget_of_threshold data.three_le_threshold⟩
        .nil)

/-- `lem:incremental-skeleton-room` at the current object's edge count.  Both
the binomial-room estimate and `s ≤ σ/2+1` are stored with logarithms and
division cleared. -/
@[reducible] noncomputable def incrementalSkeletonRoomRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.incrementalSkeletonRoom
    { Requires := []
      Produces := [K .incrementalSkeletonRoom]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .incrementalSkeletonRoom)
        ⟨Graph.Contracts.SurplusPair.incrementalSkeletonRoom_of_baseline inputs.current.baseline
          data.three_le_threshold⟩
        .nil)

/-- `lem:skeleton-dominates` at the current residual's exact edge stratum.
The fixed-edge labelled skeleton count and the canonical-state pigeonhole are
proved inside this executor and published on the same exact ledger. -/
@[reducible] noncomputable def skeletonDominatesRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.skeletonDominates
    { Requires := []
      Produces := [K .skeletonDominates]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .skeletonDominates)
        ⟨Graph.Contracts.SurplusPair.skeletonDominates_of_object⟩
        .nil)

/-- Node `[132]`, blocked-pair routing "exit or canonical blocker?": exact case
analysis on the sparse-exit predicate of `def:named-surplus-exits`.  The exit
arm closes at `[133]`; the blocker arm is its literal negation. -/
noncomputable def blockedPairRoutingDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous : ExactLedger (Input BranchState Presentation presentation data)
      current known)
    (exitFresh : K .sparsePairExit ∉ known)
    (noExitFresh : K .blockedPairNoExit ∉ known) :
    Decision (K .sparsePairExit) (K .blockedPairNoExit) previous := by
  classical
  exact Decision.run previous (K .sparsePairExit) (K .blockedPairNoExit)
    `Hypostructure.Graph.Strategy.Spine.blockedPairRoutingDichotomy
    (if exit : Holds BranchState Presentation presentation data
        .sparsePairExit current.object then
      .inl ⟨exit⟩
    else
      .inr ⟨exit⟩)
    exitFresh noExitFresh

/-- Node `[132]`, blocker arm (`lem:sparse-pair-dependence-exit`): with no
sparse exit, the blocked pair of `[130]` carries its canonical blocker
`Φ_can(π) = min_≺ Blk(π)`. -/
@[reducible] noncomputable def canonicalBlockerRouteRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.canonicalBlockerRoute
    { Requires := [K .blockedPairNoExit, K .dependentPairFamily]
      Produces := [K .canonicalBlockerRoute]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .canonicalBlockerRoute)
        ⟨Graph.Contracts.SurplusPair.canonicalBlockerRoute_of_noExit
          (inputs.get (K .blockedPairNoExit)).down
          (inputs.get (K .dependentPairFamily)).down⟩
        .nil)

/-! ## Node `[134]`: canonical blocker ledger -/

/-- The canonical blocker ledger on the literal blocker residual of `[132]`.
The executor reconstructs the paper's full finite blocker set: clauses
(a)--(c) from the two demands' active data, clauses (d)--(e) from every actual
minimal failed determination, and clause (f) from every actual compatible
suppression chord set.  It then publishes the blocked/free partition and the
canonical-fibre no-overcount identities. -/
@[reducible] noncomputable def canonicalPairLedgerRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.canonicalPairLedger
    { Requires := [K .canonicalBlockerRoute]
      Produces := [K .canonicalPairLedger]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .canonicalPairLedger)
        ⟨Graph.Contracts.SurplusPair.canonicalPairLedger_of_blockerRoute inputs.current.baseline
          (inputs.get (K .canonicalBlockerRoute)).down⟩
        .nil)

/-! ## Node `[135]`: exact window-join pressure -/

@[reducible] noncomputable def exactWindowJoinPressureRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.exactWindowJoinPressure
    { Requires := [K .maximalPacking, K .noProperBaseline, K .tightEndpoint, K .surplusAbove]
      Produces := [K .sparseUpperEnvelope]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .sparseUpperEnvelope)
        ⟨Graph.Contracts.SurplusPair.sparseUpperEnvelope_of_packing inputs.current.baseline
          (inputs.get (K .maximalPacking)).down
          (inputs.get (K .noProperBaseline)).down
          (inputs.get (K .tightEndpoint)).down
          (inputs.get (K .surplusAbove)).down
          data.three_le_threshold⟩
        .nil)

/-! ## Node `[136]`: capacity-token ledger -/

@[reducible] noncomputable def capacityTokenLedgerRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.capacityTokenLedger
    { Requires := [K .canonicalPairLedger, K .sparseUpperEnvelope, K .noProperBaseline,
        K .selection]
      Produces := [K .capacityTokenLedger]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .capacityTokenLedger)
        ⟨Graph.Contracts.SurplusPair.capacityTokenLedger_of_pairLedger inputs.current.baseline
          (inputs.get (K .canonicalPairLedger)).down
          (inputs.get (K .sparseUpperEnvelope)).down
          (inputs.get (K .noProperBaseline)).down
          (inputs.get (K .selection)).down.1
          data.three_le_threshold data.joinSlack⟩
        .nil)

end Hypostructure.Graph.Strategy.Spine
