import Hypostructure.Graph.Strategy.SpineRows
import Hypostructure.Graph.SparsePortActivation
import Hypostructure.Graph.PrimitiveCarrier
import Hypostructure.Graph.SparsePairLedger
import Hypostructure.Graph.SameTokenBlockerRoles
import Hypostructure.Graph.SparseEntropySandwich
import Hypostructure.Graph.CapacityTokenAssignment

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
variable [FactSystem (Input BranchState Presentation presentation data)]

/-! ## Node `[126]`: the sparse slack identity -/

/-- `lem:sparse-slack-surplus`, cleared of division: `2m = δn + σ(G)`.

The manuscript writes `m = (3/2)n + (1/2)σ(G)` and, with `λ = 2n − 3 − m`,
`σ(G) = n − 6 − 2λ`; substituting the abbreviation turns the second display into
the first, and doubling the first is the exact `Nat` identity committed here.
The only input is the standing baseline, which the executor reads off the
residual rather than from a fact. -/
@[reducible] noncomputable def sparseSlackSurplusRow
    (sparseSlackSurplus :
      FactKey (Input BranchState Presentation presentation data))
    (encode : (input : Input BranchState Presentation presentation data) →
      (2 * input.object.edgeCount =
        data.threshold * input.object.vertexCount +
          input.object.degreeSurplus data.threshold) →
      sparseSlackSurplus.At input) :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.sparseSlackSurplus
    (sourceFreeManifest sparseSlackSurplus)
    (fun inputs =>
      let handshake : data.threshold * inputs.current.object.vertexCount ≤
          2 * inputs.current.object.edgeCount :=
        Graph.baselineDegree_mul_vertexCount_le_two_mul_edgeCount
          inputs.current.object data.threshold fun vertex =>
            le_trans inputs.current.baseline
              (inputs.current.object.minDegree_le_degree vertex)
      .cons (key := sparseSlackSurplus)
        (encode inputs.current (by
          unfold Graph.FiniteObject.degreeSurplus
          omega))
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
@[reducible] noncomputable def activeSurplusFamilyRow
    (slackIndependent activeSurplusFamily :
      FactKey (Input BranchState Presentation presentation data))
    (distinct : slackIndependent ≠ activeSurplusFamily)
    (independentOf : (input : Input BranchState Presentation presentation data) →
      slackIndependent.At input →
      ∀ left right : input.object.Vertex,
        data.threshold < input.object.degree left →
        data.threshold < input.object.degree right →
        ¬ input.object.graph.Adj left right)
    (encode : (input : Input BranchState Presentation presentation data) →
      ((input.object.excessPorts data.threshold).card =
          input.object.degreeSurplus data.threshold ∧
        ∀ pair : input.object.Vertex × input.object.Vertex,
          ∀ member : pair ∈ input.object.excessPorts data.threshold,
            data.threshold < input.object.degree pair.1 ∧
              input.object.degree pair.2 = data.threshold ∧
              (input.object.surplusPortOfMem member).shoulders.card =
                data.threshold - 1) →
      activeSurplusFamily.At input) :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.activeSurplusFamily
    (rowManifest slackIndependent activeSurplusFamily distinct)
    (fun inputs =>
      let object := inputs.current.object
      let baseline : ∀ vertex : object.Vertex,
          data.threshold ≤ object.degree vertex :=
        fun vertex => le_trans inputs.current.baseline
          (object.minDegree_le_degree vertex)
      let independent := independentOf inputs.current (inputs.get slackIndependent)
      .cons (key := activeSurplusFamily)
        (encode inputs.current
          ⟨object.card_excessPorts baseline, fun _pair member =>
            ⟨Graph.FiniteObject.centre_high_of_mem_excessPorts member,
              (object.surplusPortOfMem member).endpoint_degree_eq baseline
                independent,
              (object.surplusPortOfMem member).card_shoulders baseline
                independent⟩⟩)
        .nil)

/-! ## Node `[128]`: port activation -/

/-- `lem:sparse-port-activation`, clauses (a)--(d).

At a selected port whose endpoint carries a shoulder *pair* -- which at the
manuscript's `δ = 3` is every selected port, by the previous row's `|s(p)| =
δ − 1` -- the two cases of the lemma are:

* the port is *open*, and suppressing its endpoint gives a strictly smaller
  object meeting the baseline; minimality supplies an accepted cycle there,
  avoidance forces it through the inserted shoulder chord, and the
  reconstruction returns the simple shoulder-to-shoulder path `Q_p ⊆ G − x(p)`
  whose restored length is accepted.  That is the manuscript's `2^{j(p)} − 1`
  with `j(p) ≥ 2`, at whatever accepted set is registered;
* the port is *triangular*, and the triangle `x a_p b_p x` is present.

Clause (a) is the shoulder pair itself, which is the row's own hypothesis at
each port.  Clause (b) is the return path `R_p ⊆ G − c(p)x(p)`: the port's own
edge is not a bridge, because contracting it gives a strictly smaller object
still meeting the baseline, and minimality and avoidance close it exactly as
they close the suppression.  Its first edge after `x(p)` is a shoulder. -/
@[reducible] noncomputable def sparsePortActivationRow
    (selection sparsePortActivation :
      FactKey (Input BranchState Presentation presentation data))
    (distinct : selection ≠ sparsePortActivation)
    (avoidsOf : (input : Input BranchState Presentation presentation data) →
      selection.At input →
      ¬ Graph.HasCycleWithLength data.LengthOK input.object)
    (minimalOf : (input : Input BranchState Presentation presentation data) →
      selection.At input →
      ∀ smaller : Graph.FiniteObject.{u},
        smaller.LexicographicallySmaller input.object →
        data.threshold ≤ smaller.minDegree →
        Graph.HasCycleWithLength data.LengthOK smaller)
    (encode : (input : Input BranchState Presentation presentation data) →
      (∀ pair : input.object.Vertex × input.object.Vertex,
        ∀ member : pair ∈ input.object.excessPorts data.threshold,
          ∀ left right : input.object.Vertex,
            (∀ vertex : input.object.Vertex,
              vertex ∈ (input.object.surplusPortOfMem member).shoulders ↔
                (vertex = left ∨ vertex = right)) →
            left ≠ right →
            Nonempty (Graph.FiniteObject.SurplusPort.PortReturn
                input.object pair.1 pair.2 left right) ∧
              (¬ input.object.graph.Adj left right →
                Nonempty (Graph.FiniteObject.SurplusPort.OpenPortWitness
                  input.object data.LengthOK pair.2 left right)) ∧
              (input.object.graph.Adj left right →
                input.object.graph.Adj pair.2 left ∧
                  input.object.graph.Adj left right ∧
                  input.object.graph.Adj right pair.2)) →
      sparsePortActivation.At input) :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.sparsePortActivation
    (rowManifest selection sparsePortActivation distinct)
    (fun inputs =>
      let object := inputs.current.object
      let fact := inputs.get selection
      let avoids := avoidsOf inputs.current fact
      let minimal := minimalOf inputs.current fact
      .cons (key := sparsePortActivation)
        (encode inputs.current fun _pair member left right shoulders distinct =>
          ⟨(object.surplusPortOfMem member).portReturn_of_minimal
              shoulders inputs.current.baseline avoids minimal,
            fun openPort =>
              (object.surplusPortOfMem member).openPortWitness_of_minimal
                shoulders distinct openPort inputs.current.baseline avoids
                minimal,
            fun adjacent =>
              (object.surplusPortOfMem member).triangle_of_shoulders_adj
                (shoulders left |>.2 (Or.inl rfl))
                (shoulders right |>.2 (Or.inr rfl)) adjacent⟩)
        .nil)

/-! ## Node `[129]`: the baseline spine demand -/

/-- `def:baseline-spine-demand` with `lem:exact-cubic-baseline-budget`,
`lem:incremental-skeleton-room` and `def:spine-lower-bound-deficits`.

The manuscript fixes `N = C(n,2)`, `m₀ = ⌈(3/2)n⌉` and `B₀(n) = log₂ C(N,m₀)`,
calls a family `ℐ_spine` of declared target coordinates a baseline spine demand
with deficit `E_spine(n)` when it is independently target-testable and
`|ℐ_spine| ≥ B₀(n) − E_spine(n)`, evaluates `B₀(n) = (3/2)n log₂ n + O(n)`,
bounds the room a larger edge count buys by `s·log₂ n`, and records three
lower-bound packages whose deficits are admissible `E_spine`.

Every display is committed with the logarithms cleared, so the branch carries
exact `Nat` inequalities rather than asymptotic ones:

* `C(N,m₀+s) ≤ C(N,m₀)·n^s` and that estimate spent at the object's own edge
  count;
* `(n−1)^{m₀} ≤ C(N,m₀)·(2(δ+1))^{m₀} ≤ C(N,m₀)·(2n)^{m₀}·…`, i.e. both halves
  of `lem:exact-cubic-baseline-budget`, whose logarithms are `B₀(n) =
  (δ/2)n log₂ n + O(n)`.  The lower half carries the manuscript's own
  nonemptiness hypothesis `2m₀ ≤ N`, without which the baseline stratum is
  empty and `B₀(n)` is unbounded below;
* `def:baseline-spine-demand` at every family of declared target coordinates the
  branch may present, with `E_spine(n) = spineDeficit` -- this node's own
  *output*, computed from the object's order and the package's lower bound,
  never a constant carried in;
* `def:spine-lower-bound-deficits`' three packages, at the registered window
  rate, entropy denominator and curvature cost, with their deficits ordered.

`m₀ = ⌈δn/2⌉` is the least edge count a `δ`-regular object can carry, so the
only thing consumed is the registered baseline's own `2 ≤ δ`, which
`three_le_threshold` supplies.  The row reads no fact: every statement is a
theorem about the residual object's own counting observables and the registered
rates, and declaring a prerequisite it does not read would claim a dependency it
does not have. -/
@[reducible] noncomputable def baselineSpineDemandRow
    (baselineSpineDemand :
      FactKey (Input BranchState Presentation presentation data))
    (encode : (input : Input BranchState Presentation presentation data) →
      ((∀ increment : Nat,
          Graph.cubicBaselineEdgeCount input.object.vertexCount
              data.threshold + increment ≤ 2 * input.object.vertexCount - 2 →
          (input.object.vertexCount.choose 2).choose
              (Graph.cubicBaselineEdgeCount input.object.vertexCount
                data.threshold + increment) ≤
            (input.object.vertexCount.choose 2).choose
                (Graph.cubicBaselineEdgeCount input.object.vertexCount
                  data.threshold) *
              input.object.vertexCount ^ increment) ∧
        (Graph.cubicBaselineEdgeCount input.object.vertexCount
              data.threshold ≤ input.object.edgeCount →
          Graph.skeletonBudget input.object ≤
            Graph.cubicBaselineBudget input.object.vertexCount
                data.threshold *
              input.object.vertexCount ^
                (input.object.edgeCount -
                  Graph.cubicBaselineEdgeCount input.object.vertexCount
                    data.threshold)) ∧
        (Graph.cubicBaselineBudget input.object.vertexCount data.threshold ≤
            (2 * input.object.vertexCount) ^
              Graph.cubicBaselineEdgeCount input.object.vertexCount
                data.threshold ∧
          (2 * Graph.cubicBaselineEdgeCount input.object.vertexCount
                data.threshold ≤ input.object.vertexCount.choose 2 →
            (input.object.vertexCount - 1) ^
                Graph.cubicBaselineEdgeCount input.object.vertexCount
                  data.threshold ≤
              Graph.cubicBaselineBudget input.object.vertexCount
                  data.threshold *
                (2 * (data.threshold + 1)) ^
                  Graph.cubicBaselineEdgeCount input.object.vertexCount
                    data.threshold)) ∧
        (∀ Coordinate : Type u, ∀ family : Finset Coordinate,
          ∀ system : Core.TargetRank.QuotientSystem.{u, u + 1} Coordinate
              family,
            ∀ lowerBound : Nat,
              system.Survives ↑family →
              lowerBound ≤ family.card →
              Graph.IsBaselineSpineDemand system input.object.vertexCount
                data.threshold
                (Graph.spineDeficit input.object.vertexCount data.threshold
                  lowerBound)) ∧
        (∀ packing remainder scaleCount : Nat,
          Graph.spineDeficit input.object.vertexCount data.threshold
              (Graph.curvaturePackageBound data.windowRate packing scaleCount
                remainder data.entropyDenominator data.curvatureCost) ≤
            Graph.spineDeficit input.object.vertexCount data.threshold
              (Graph.highEntropyPackageBound data.windowRate packing scaleCount
                remainder data.entropyDenominator) ∧
          Graph.spineDeficit input.object.vertexCount data.threshold
              (Graph.highEntropyPackageBound data.windowRate packing scaleCount
                remainder data.entropyDenominator) ≤
            Graph.spineDeficit input.object.vertexCount data.threshold
              (Graph.windowPackageBound data.windowRate packing scaleCount))) →
      baselineSpineDemand.At input) :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.baselineSpineDemand
    (sourceFreeManifest baselineSpineDemand)
    (fun inputs =>
      let baseline : 2 ≤ data.threshold :=
        le_trans (by omega) data.three_le_threshold
      let order := inputs.current.object.vertexCount
      .cons (key := baselineSpineDemand)
        (encode inputs.current
          ⟨fun increment _envelope =>
              Graph.incremental_skeleton_room order baseline increment,
            fun above =>
              Graph.skeletonBudget_le_cubicBaselineBudget_mul_pow
                inputs.current.object baseline above,
            ⟨Graph.cubicBaselineBudget_le_pow order baseline,
              fun room => Graph.pow_pred_le_cubicBaselineBudget_mul order room⟩,
            fun _Coordinate _family system lowerBound testable supply =>
              Graph.isBaselineSpineDemand_of_package system order baseline
                lowerBound testable supply,
            fun packing remainder scaleCount =>
              ⟨Graph.spineDeficit_le_of_le order data.threshold
                  (Graph.highEntropyPackageBound_le_curvaturePackageBound
                    data.windowRate packing scaleCount remainder
                    data.entropyDenominator data.curvatureCost),
                Graph.spineDeficit_le_of_le order data.threshold
                  (Graph.windowPackageBound_le_highEntropyPackageBound
                    data.windowRate packing scaleCount remainder
                    data.entropyDenominator)⟩⟩)
        .nil)

/-! ## Nodes `[130]`--`[134]`: the canonical pair-response ledger -/

/-- `def:sparse-pair-response`, `def:surplus-blockers`, `def:canonical-blocker-ledger`,
`lem:sparse-pair-dependence-exit`, `prop:sparse-pair-independence-dichotomy`,
`prop:sparse-entropy-sandwich` and its blocked refinement.

`Π(𝒜₀) = C(𝒜₀,2)` is the unordered pairs of the active family, and its count is
`C(σ(G),2)` because `|𝒜₀| = σ(G)` — the same `card_excessPorts` the previous row
committed, spent again rather than assumed.

Everything else is committed at an arbitrary `DemandActivation`, the canonical
data `def:active-surplus-demands` equips a selected port with, in the concrete
form the six clauses read: `T(p) ∪ Γ(p)`, `R_p`, `{a_p, b_p, x(p)}`, and the
obstruction families the dependence analysis hands back.  At that activation:

* `def:sparse-pair-response` is built — `X_π` is the minimum connected superset
  of `T(p) ∪ Γ(p) ∪ T(q) ∪ Γ(q)` selected canonically, `∂X_π` is its literal cut
  boundary, `r_π` is the (D7) declared coordinate labelled `π` and supported on
  `X_π`, and the pair family carries one coordinate per pair;
* `def:surplus-blockers` is instantiated — a pair is blocked exactly when it
  carries one of the six concrete blocker *objects*, which is the definition's
  own closing paragraph, so `Π_blk` is the manuscript's set and not the set of a
  quantified relation;
* `def:canonical-blocker-ledger`'s two identities are read at that set: the split
  `|Π_blk| + |Π_free| = |Π(𝒜₀)|` and the no-overcount
  `|Π_blk| = Σ_B μ(B)`, where `Φ_can` is the first clause of
  `def:canonical-sparse-blocker-order` that applies;
* `lem:sparse-pair-dependence-exit` and `lem:mixed-sparse-spine-dependence` are
  committed in the form the manuscript's three consumers use: at an object that
  survives the sparse surplus exits and admits no proper-support replacement, a
  rank-reducing attempted determination exhibits the blocker of type (d) or (e)
  as concrete separated realizations;
* `prop:sparse-pair-independence-dichotomy` is the admissible reading of the
  same: the declared family attains full target rank;
* `prop:sparse-entropy-sandwich-with-blockers` and `prop:sparse-entropy-sandwich`
  are the entropy sandwich with the logarithms cleared, and
  `cor:sparse-pair-entropy-saturation` is its `ℐ_spine = ∅` reading.

The dependence and sandwich clauses are committed as implications from their own
hypotheses — survival, replacement-freeness, the entropy count and the baseline
demand — which is the discipline `def:baseline-spine-demand` is already stated
in and the same one the next row's sparse-envelope bound uses.  Nothing supplies
a callback: every hypothesis is a statement the branch either already carries or
is about to derive. -/
@[reducible] noncomputable def canonicalPairLedgerRow
    (activeSurplusFamily canonicalPairLedger :
      FactKey (Input BranchState Presentation presentation data))
    (distinct : activeSurplusFamily ≠ canonicalPairLedger)
    (encode : (input : Input BranchState Presentation presentation data) →
      ((input.object.portPairSchedule data.threshold).card =
          (input.object.degreeSurplus data.threshold).choose 2 ∧
        (∀ Coordinate Chord : Type u,
          ∀ activation :
            Graph.FiniteObject.DemandActivation input.object Coordinate Chord,
            -- `def:canonical-blocker-ledger` at `def:surplus-blockers`' own set.
            ((activation.chargedPairs data.threshold).card +
                  (activation.freePairs data.threshold).card =
                (input.object.portPairSchedule data.threshold).card ∧
              (activation.chargedPairs data.threshold).card =
                Graph.SameTokenBlockerRoles.canonicalBlockerOrder.toFinset.sum
                  (activation.multiplicity data.threshold) ∧
              ∀ pair : Finset (input.object.Vertex × input.object.Vertex),
                (∃ kind, activation.Blocks kind pair) ↔
                  (activation.blockers pair).Nonempty) ∧
            -- `def:sparse-pair-response`.
            (∀ pair : Finset (input.object.Vertex × input.object.Vertex),
              ∀ support : Finset input.object.Vertex,
                activation.pairSupport pair = some support →
                  activation.pairSeed pair ⊆ support ∧
                    Graph.SupportComponents.Connected.ConnectedOn input.object
                      support ∧
                    (∀ other : Finset input.object.Vertex,
                      activation.pairSeed pair ⊆ other →
                      Graph.SupportComponents.Connected.ConnectedOn input.object
                        other → support.card ≤ other.card) ∧
                    ∀ vertex : input.object.Vertex,
                      vertex ∈
                          Graph.FiniteObject.DemandActivation.pairBoundary
                            input.object support ↔
                        vertex ∈ support ∧
                          ∃ neighbor, input.object.graph.Adj vertex neighbor ∧
                            neighbor ∉ support) ∧
            ∀ family : Finset (Finset (input.object.Vertex × input.object.Vertex)),
              (activation.pairFamily family).card = family.card) ∧
        -- `lem:sparse-pair-dependence-exit`, `lem:mixed-sparse-spine-dependence`
        -- and `prop:sparse-pair-independence-dichotomy`.
        (∀ Coordinate : Type u, ∀ family : Finset Coordinate,
          ∀ coordinateSupport : Coordinate → Finset input.object.Vertex,
            Graph.SurvivesSparseExits
                (Graph.MinimumDegreeAtLeast data.threshold)
                (Graph.HasCycleWithLength data.LengthOK) data.LengthOK
                input.object →
            (∀ support : Finset input.object.Vertex,
              ¬ Graph.Strategy.InterfaceReplacement.ReplacementSupport
                (Graph.MinimumDegreeAtLeast data.threshold)
                (Graph.HasCycleWithLength data.LengthOK) input.object support) →
            (∀ attempt :
                Graph.AttemptedQuotient
                  (Graph.MinimumDegreeAtLeast data.threshold)
                  (Graph.HasCycleWithLength data.LengthOK) input.object family
                  coordinateSupport,
                ¬ Set.InjOn attempt.label ↑family →
                  (∃ left right, attempt.Identifies left right ∧
                      left.boundaryDegreeProfile ≠ right.boundaryDegreeProfile) ∨
                    (∃ left right, attempt.Identifies left right ∧
                      Graph.Response.TargetDefect
                        (Graph.HasCycleWithLength data.LengthOK) left right)) ∧
              Core.TargetRank.targetRank
                  (Graph.FiniteObject.declaredQuotientSystem
                    (Graph.MinimumDegreeAtLeast data.threshold)
                    (Graph.HasCycleWithLength data.LengthOK) input.object family
                    coordinateSupport) =
                family.card) ∧
        -- `prop:sparse-entropy-sandwich`, its blocked refinement, and
        -- `cor:sparse-pair-entropy-saturation`.
        (∀ spineCount freeCount deficit : Nat,
          Graph.cubicBaselineEdgeCount input.object.vertexCount data.threshold ≤
            input.object.edgeCount →
          2 ^ (spineCount + freeCount) ≤ Graph.skeletonBudget input.object →
          Graph.cubicBaselineBudget input.object.vertexCount data.threshold ≤
            2 ^ (spineCount + deficit) →
          2 ^ freeCount ≤
            2 ^ deficit *
              input.object.vertexCount ^
                (input.object.edgeCount -
                  Graph.cubicBaselineEdgeCount input.object.vertexCount
                    data.threshold)) ∧
        (2 ^ (input.object.portPairSchedule data.threshold).card ≤
            Graph.skeletonBudget input.object →
          2 ^ ((input.object.degreeSurplus data.threshold).choose 2) ≤
            Graph.skeletonBudget input.object)) →
      canonicalPairLedger.At input) :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.canonicalPairLedger
    (rowManifest activeSurplusFamily canonicalPairLedger distinct)
    (fun inputs =>
      let object := inputs.current.object
      let baseline : ∀ vertex : object.Vertex,
          data.threshold ≤ object.degree vertex :=
        fun vertex => le_trans inputs.current.baseline
          (object.minDegree_le_degree vertex)
      let two_le : 2 ≤ data.threshold := le_trans (by omega) data.three_le_threshold
      -- The schedule is read at the family the ledger already carries.
      let _family := inputs.get activeSurplusFamily
      .cons (key := canonicalPairLedger)
        (encode inputs.current
          ⟨Graph.FiniteObject.card_portPairSchedule baseline,
            fun _Coordinate _Chord activation =>
              ⟨⟨activation.card_chargedPairs_add_card_freePairs data.threshold,
                  activation.card_chargedPairs_eq_sum_multiplicity data.threshold,
                  fun pair => activation.exists_blocks_iff_blockers_nonempty pair⟩,
                fun _pair _support selected =>
                  ⟨(Graph.FiniteObject.DemandActivation.pairSupport_mem_candidates
                      selected).1,
                    (Graph.FiniteObject.DemandActivation.pairSupport_mem_candidates
                      selected).2,
                    fun _other contains connected =>
                      Graph.FiniteObject.DemandActivation.pairSupport_card_le
                        selected contains connected,
                    fun vertex =>
                      Graph.FiniteObject.DemandActivation.mem_pairBoundary_iff
                        object _ vertex⟩,
                fun family => activation.card_pairFamily family⟩,
            fun _Coordinate _family _coordinateSupport survives noReplacement =>
              ⟨fun attempt reducing =>
                  Graph.blockerSeparation_of_reducing survives noReplacement
                    attempt reducing,
                Graph.targetRank_eq_card_of_exitFree survives noReplacement⟩,
            fun _spineCount _freeCount _deficit above entropy demand =>
              Graph.entropySandwich object two_le above entropy demand,
            fun entropy =>
              (Graph.FiniteObject.card_portPairSchedule baseline) ▸ entropy⟩)
        .nil)

/-! ## Nodes `[134]`--`[136]`: the capacity-token ledger -/

/-- `def:primitive-sparse-blocker-carrier` with `lem:primitive-carrier-supply`,
`def:capacity-token-ledger` with `lem:capacity-token-supply` and
`lem:token-ledger-no-overcount`, and `def:same-token-patterns`.

The carrier `𝔘_sp(G) = V(G) ⊔ I_E(G) ⊔ 𝒫_exc` is built from the object's own
data, and its supply is committed in both of the manuscript's forms: the
identity `|𝔘_sp(G)| = n + 2m + σ(G)`, and the display `≤ 6n` on the sparse upper
envelope `m ≤ 2n − 2`, which is committed as an implication because the envelope
is a hypothesis the manuscript carries into the estimate rather than a property
of every object.

The token universe is the manuscript's three-summand
`𝔗_cap = 𝔗_prim ⊔ 𝔗_R ⊔ 𝔗_W`: the primitive carrier, the remainder surplus units
`{(v,j) : v ∈ R, 1 ≤ j ≤ d_G(v) − δ}`, and the window--remainder and cross-window
incidence families of the packing.  `lem:capacity-token-supply` is committed in
its exact form `|𝔗_cap| + 2(order−1)p = |𝔘_sp(G)| + δ·order·p + σ(G)` — the
manuscript's `|𝔗_cap| = |𝔘_sp(G)| + 15p₁₃ + σ(G)` — and its displayed bound
`|𝔗_cap| ≤ 8n + σ(G)` as an implication from the same envelope and the registered
join comparison.

`Θ_cap` is the four-case charge, built from the pair's canonical blocker
`Φ_can(π)`, that blocker's declared support and its primitive carrier `κ`.  It
lands in `𝔗_cap`, and `lem:token-ledger-no-overcount` is the blocker ledger's own
fibre identity read at that charge — the same
`card_chargedPairs_eq_sum_multiplicity`, not a second implementation — together
with the clause that makes the identity read at the whole blocked family.
`def:same-token-patterns`' fibre graph `H_t` is the charge's own fibre, a simple
graph on `𝒜₀` with `e(H_t) = ℓ_cap(t)`.

The statement is quantified over exactly two things the branch does not fix: a
maximal packing of induced windows, and the declared coordinate and shoulder-chord
presentation of `def:declared-coordinate-signature`. -/
@[reducible] noncomputable def capacityTokenLedgerRow
    (canonicalPairLedger capacityTokenLedger :
      FactKey (Input BranchState Presentation presentation data))
    (distinct : canonicalPairLedger ≠ capacityTokenLedger)
    (encode : (input : Input BranchState Presentation presentation data) →
      (((input.object.primitiveCarrier data.threshold).card =
            input.object.vertexCount + 2 * input.object.edgeCount +
              input.object.degreeSurplus data.threshold ∧
          (input.object.edgeCount + 2 ≤ 2 * input.object.vertexCount →
            (input.object.primitiveCarrier data.threshold).card ≤
              6 * input.object.vertexCount)) ∧
        Graph.FiniteObject.CapacityTokenLedgerStatement input.object
          data.threshold data.windowOrder) →
      capacityTokenLedger.At input) :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.capacityTokenLedger
    (rowManifest canonicalPairLedger capacityTokenLedger distinct)
    (fun inputs =>
      let object := inputs.current.object
      let baseline : ∀ vertex : object.Vertex,
          data.threshold ≤ object.degree vertex :=
        fun vertex => le_trans inputs.current.baseline
          (object.minDegree_le_degree vertex)
      let handshake : data.threshold * object.vertexCount ≤
          2 * object.edgeCount :=
        Graph.baselineDegree_mul_vertexCount_le_two_mul_edgeCount object
          data.threshold baseline
      -- The demands the token map charges are the pair ledger's own schedule.
      let _schedule := inputs.get canonicalPairLedger
      .cons (key := capacityTokenLedger)
        (encode inputs.current
          ⟨⟨object.card_primitiveCarrier baseline,
            fun envelope =>
              object.card_primitiveCarrier_le baseline data.three_le_threshold
                handshake envelope⟩,
            Graph.FiniteObject.capacityTokenLedgerStatement object baseline
              data.three_le_threshold data.windowOrder_pos handshake⟩)
        .nil)

end Hypostructure.Graph.Strategy.Spine
