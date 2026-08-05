import Hypostructure.Graph.Strategy.SpineRows
import Hypostructure.Graph.SparsePortActivation

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
* `sparsePortActivationRow` is `lem:sparse-port-activation` clauses (a), (c) and
  (d).  Clause (c) is the suppression witness `Q_p`, which minimality and
  avoidance supply through `TightVertexSuppression`; clause (d) is the triangle
  of a triangular port.  Clause (b), the return path `R_p ⊆ G − c(p)x(p)`, is
  *not* committed here: it rests on `lem:bridgeless`, which the framework does
  not yet carry.
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

/-- `lem:sparse-port-activation`, clauses (a), (c) and (d).

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
each port.  Clause (b) -- the return path `R_p` in `G − c(p)x(p)` -- rests on
`lem:bridgeless` and is not committed. -/
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
          ⟨fun openPort =>
              (object.surplusPortOfMem member).openPortWitness_of_minimal
                shoulders distinct openPort inputs.current.baseline avoids
                minimal,
            fun adjacent =>
              (object.surplusPortOfMem member).triangle_of_shoulders_adj
                (shoulders left |>.2 (Or.inl rfl))
                (shoulders right |>.2 (Or.inr rfl)) adjacent⟩)
        .nil)

/-! ## Node `[129]`: the baseline spine demand -/

/-- `def:baseline-spine-demand`'s common baseline, with
`lem:incremental-skeleton-room`.

The manuscript fixes `N = C(n,2)`, `m₀ = ⌈(3/2)n⌉` and `B₀(n) = log₂ C(N,m₀)`,
and bounds the room a larger edge count buys by `s·log₂ n`.  Both displays are
committed with the logarithms cleared -- `C(N,m₀+s) ≤ C(N,m₀)·n^s` -- so the
branch carries the estimate as an exact `Nat` inequality rather than an
asymptotic one; the second output is that estimate spent at the object's own
edge count.

`m₀ = ⌈δn/2⌉` is the least edge count a `δ`-regular object can carry, so the
only thing consumed is the registered baseline's own `2 ≤ δ`, which
`three_le_threshold` supplies.  The row reads no fact: both statements are
theorems about the object's two counting observables, and declaring a
prerequisite it does not read would claim a dependency it does not have. -/
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
                    data.threshold))) →
      baselineSpineDemand.At input) :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.baselineSpineDemand
    (sourceFreeManifest baselineSpineDemand)
    (fun inputs =>
      let baseline : 2 ≤ data.threshold :=
        le_trans (by omega) data.three_le_threshold
      .cons (key := baselineSpineDemand)
        (encode inputs.current
          ⟨fun increment _envelope =>
              Graph.incremental_skeleton_room inputs.current.object.vertexCount
                baseline increment,
            fun above =>
              Graph.skeletonBudget_le_cubicBaselineBudget_mul_pow
                inputs.current.object baseline above⟩)
        .nil)

end Hypostructure.Graph.Strategy.Spine
