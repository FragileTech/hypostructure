import Hypostructure.Graph.Strategy.SurplusRows
import Hypostructure.Graph.Strategy.HomogeneousBottleneckRows
import Hypostructure.Graph.Strategy.SpineRun

/-!
# The sparse surplus branch, run

Nodes `[126]`--`[136]`, on the arm node `[19]` sends an object whose degree
surplus exceeds the registered scale threshold.  The rows of `SurplusRows` are
each quantified over the keys they consume and produce; this module installs
them at the spine's own vocabulary and runs them in the manuscript's order
against the one canonical `ExactLedger`, over the literal ledger the entry
spine leaves at `Spine.Result.surplusAbove`.

Every prerequisite is discharged by instance resolution against the incoming
index: node `[127]` does not elaborate before node `[10]`'s slack-independence
entry, and node `[128]` does not elaborate before the node-`[1]`--`[4]`
selection entry.  Nothing is carried between rows but the residual and the
ledger, and no row names a producer or an execution position.

Node `[125]` is the *survivor* of the five sparse surplus exits of
`def:named-surplus-exits`.  Those exits are not yet branch alternatives of this
block -- exit `(e)` has no live support -- so this module runs the six rows
that do not depend on exit-freeness, and the arm it produces is the activation
data itself.  `lem:surviving-active-family`'s cardinality is committed;
its *"not removed by an exit"* clause is not.
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-! ## The rows, at the spine's own keys

Every schema bridge below is the identity on `PLift`: the spine's value at a
sparse-surplus key *is* the manuscript statement, so nothing is re-encoded. -/

/-- Node `[126]`: the sparse slack identity. -/
@[reducible] noncomputable def sparseSlackSurplus :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  sparseSlackSurplusRow (K .sparseSlackSurplus) (fun _input value => ⟨value⟩)

/-- Node `[127]`: the excess selector, its count, and the port structure. -/
@[reducible] noncomputable def activeSurplusFamily :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  activeSurplusFamilyRow (K .slackIndependent) (K .activeSurplusFamily)
    (by simp) (fun _input fact => fact.down) (fun _input value => ⟨value⟩)

/-- Node `[128]`: port activation.

The selection entry supplies both halves the suppression witness needs: the
object's own avoidance and its own minimality.  The minimality clause is read
at the registered progress, which is the canonical lexicographic one, so it is
exactly the raw hypothesis `TightVertexSuppression` asks for. -/
@[reducible] noncomputable def sparsePortActivation :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  sparsePortActivationRow (K .selection) (K .sparsePortActivation) (by simp)
    (fun _input fact => fact.down.1)
    (fun _input fact smaller lexicographic baseline =>
      fact.down.2 smaller lexicographic baseline)
    (fun _input value => ⟨value⟩)

/-- Node `[129]`: the common cubic baseline and the room above it. -/
@[reducible] noncomputable def baselineSpineDemand :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  baselineSpineDemandRow (K .baselineSpineDemand) (fun _input value => ⟨value⟩)

/-- Nodes `[130]`--`[134]`: the pair schedule and the canonical blocker
ledger. -/
@[reducible] noncomputable def canonicalPairLedger :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  canonicalPairLedgerRow (K .activeSurplusFamily) (K .canonicalPairLedger)
    (by simp) (fun _input value => ⟨value⟩)

/-- Nodes `[134]`--`[136]`: the primitive carrier supply and the capacity-token
ledger. -/
@[reducible] noncomputable def capacityTokenLedger :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  capacityTokenLedgerRow (K .canonicalPairLedger) (K .capacityTokenLedger)
    (by simp) (fun _input value => ⟨value⟩)

/-- Nodes `[137]`--`[143]`: the coupled high-load test with its role split and
the near-cubic surplus estimate.

Three keys are read and all three are spent: node `[130]`'s pair count converts
the lower-bound package bound, node `[136]`'s capacity-token ledger witnesses the
high-load display, and node `[129]`'s package ordering supplies the deficit the
estimate is stated at. -/
@[reducible] noncomputable def coupledFibrePressure :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  coupledFibrePressureRow (K .canonicalPairLedger) (K .capacityTokenLedger)
    (K .baselineSpineDemand) (K .roleFibrePartition) (K .fibrePressure)
    (K .spineSurplusEstimate)
    (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
    (fun _input fact => fact.down.1)
    (fun _input fact => fact.down.2)
    (fun _input fact => fact.down.2.2.2.2)
    (fun _input value => ⟨value⟩) (fun _input value => ⟨value⟩)
    (fun _input value => ⟨value⟩)

/-- Nodes `[140]`, `[142]`, `[143]`: the three geometric class audits. -/
@[reducible] noncomputable def bottleneckClassification :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  bottleneckClassificationRow (K .canonicalPairLedger)
    (K .bottleneckClassification) (by simp)
    (fun _input fact => fact.down.1) (fun _input value => ⟨value⟩)

/-- Node `[144]`: the homogeneous bottleneck. -/
@[reducible] noncomputable def homogeneousBottleneck :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  homogeneousBottleneckRow (K .canonicalPairLedger) (K .homogeneousBottleneck)
    (by simp) (fun _input fact => fact.down.1) (fun _input value => ⟨value⟩)

/-- Node `[125]`: the selected object survives the five sparse surplus exits.
Derived from the selection entry; every later node of the block reads it. -/
@[reducible] noncomputable def sparseSurplusSurvivor :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  sparseSurplusSurvivorRow (K .selection) (K .uncompressible)
    (K .sparseSurplusSurvivor) (by simp) (by simp)
    (fun _input fact => fact.down.1)
    (fun _input fact smaller lexicographic baseline =>
      fact.down.2 smaller lexicographic baseline)
    (fun _input fact => fact.down)
    (fun _input value => ⟨value⟩)

/-- Node `[125]`, continued: `def:active-surplus-demands` with
`lem:surviving-active-family`.  Every input is a fact the branch already
carries. -/
@[reducible] noncomputable def activeSurplusDemands :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  activeSurplusDemandsRow (K .sparseSurplusSurvivor) (K .activeSurplusFamily)
    (K .sparsePortActivation) (K .activeSurplusDemands)
    (by simp) (by simp) (by simp) (by simp)
    (fun _input fact => fact.down)
    (fun _input fact => fact.down.1)
    (fun _input fact pair member left right shoulders distinct =>
      fact.down pair member left right shoulders distinct)
    (fun _input value => ⟨value⟩)

/-! ## The block, run -/

/-- The key index a branch carries after nodes `[126]`--`[137]`, before the
node-`[137]` branch. -/
abbrev sparseActivationKeys
    (known : FactKeys (Input BranchState Presentation presentation data)) :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .roleFibrePartition :: K .fibrePressure :: K .spineSurplusEstimate ::
    K .capacityTokenLedger :: K .canonicalPairLedger :: K .baselineSpineDemand ::
    K .activeSurplusDemands :: K .sparseSurplusSurvivor ::
    K .sparsePortActivation :: K .activeSurplusFamily ::
    K .sparseSlackSurplus :: known

/-- The near-cubic arm's index: the block's facts plus
`prop:single-graph-sparse-pressure-routing` (a).  The geometric audits are
absent, so nothing downstream of `[138]` can read an overload that did not
occur. -/
abbrev nearCubicKeys
    (known : FactKeys (Input BranchState Presentation presentation data)) :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .sparsePressureNearCubic :: sparseActivationKeys known

/-- The overload arm's index: the block's facts, the forced role-homogeneous
pattern of `prop:single-graph-sparse-pressure-routing` (b), and the three
geometric class audits `[140]`, `[142]`, `[143]` with `[144]` that read it. -/
abbrev overloadKeys
    (known : FactKeys (Input BranchState Presentation presentation data)) :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .homogeneousBottleneck :: K .bottleneckClassification ::
    K .sparsePressureOverload :: sparseActivationKeys known

/-- **The exit of the sparse activation block.**

Two constructors, one per arm of `prop:single-graph-sparse-pressure-routing`:
either the geometric caps hold and the branch routes to node `[138]` carrying
`σ(G) ≤ R_L(n)` and the surplus estimate, or some role fibre overloads and the
branch carries the forced role-homogeneous pattern into the three geometric
class audits.  The arm not taken is not in the taken arm's index. -/
inductive SurplusResult
    (selected : Input BranchState Presentation presentation data)
    (known : FactKeys (Input BranchState Presentation presentation data)) where
  | nearCubic
      (history : ExactLedger (Input BranchState Presentation presentation data)
        selected (nearCubicKeys known))
  | overloaded
      (history : ExactLedger (Input BranchState Presentation presentation data)
        selected (overloadKeys known))

/-- **Nodes `[126]`--`[144]`, run.**

The eleven fact-only rows are composed by `AtomicCT.run`, which appends each
row's declared productions to the incoming index while retaining the literal
ancestry.  Every freshness side condition is decided on the vocabulary's own
finite `Key`. -/
noncomputable def runSparseActivation
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    [FactKeys.Has (K (data := data) .selection) known]
    [FactKeys.Has (K (data := data) .slackIndependent) known]
    [FactKeys.Has (K (data := data) .uncompressible) known]
    (history : ExactLedger (Input BranchState Presentation presentation data)
      current known)
    (slackFresh : K (data := data) .sparseSlackSurplus ∉ known)
    (familyFresh : K (data := data) .activeSurplusFamily ∉ known)
    (activationFresh : K (data := data) .sparsePortActivation ∉ known)
    (survivorFresh : K (data := data) .sparseSurplusSurvivor ∉ known)
    (demandsFresh : K (data := data) .activeSurplusDemands ∉ known)
    (demandFresh : K (data := data) .baselineSpineDemand ∉ known)
    (pairFresh : K (data := data) .canonicalPairLedger ∉ known)
    (tokenFresh : K (data := data) .capacityTokenLedger ∉ known)
    (partitionFresh : K (data := data) .roleFibrePartition ∉ known)
    (pressureFresh : K (data := data) .fibrePressure ∉ known)
    (estimateFresh : K (data := data) .spineSurplusEstimate ∉ known)
    (nearCubicFresh : K (data := data) .sparsePressureNearCubic ∉ known)
    (overloadFresh : K (data := data) .sparsePressureOverload ∉ known)
    (classificationFresh : K (data := data) .bottleneckClassification ∉ known)
    (bottleneckFresh : K (data := data) .homogeneousBottleneck ∉ known) :
    SurplusResult current known := by
  classical
  have afterSlack :=
    (sparseSlackSurplus (data := data)).run history (by
      intro key isNew isOld
      simp only [List.mem_singleton] at isNew
      subst isNew
      revert isOld
      simp [slackFresh])
  have afterFamily :=
    (activeSurplusFamily (data := data)).run afterSlack (by
      intro key isNew isOld
      simp only [List.mem_singleton] at isNew
      subst isNew
      revert isOld
      simp [familyFresh])
  have afterActivation :=
    (sparsePortActivation (data := data)).run afterFamily (by
      intro key isNew isOld
      simp only [List.mem_singleton] at isNew
      subst isNew
      revert isOld
      simp [activationFresh])
  have afterSurvivor :=
    (sparseSurplusSurvivor (data := data)).run afterActivation (by
      intro key isNew isOld
      simp only [List.mem_singleton] at isNew
      subst isNew
      revert isOld
      simp [survivorFresh])
  have afterDemands :=
    (activeSurplusDemands (data := data)).run afterSurvivor (by
      intro key isNew isOld
      simp only [List.mem_singleton] at isNew
      subst isNew
      revert isOld
      simp [demandsFresh])
  have afterDemand :=
    (baselineSpineDemand (data := data)).run afterDemands (by
      intro key isNew isOld
      simp only [List.mem_singleton] at isNew
      subst isNew
      revert isOld
      simp [demandFresh])
  have afterPairs :=
    (canonicalPairLedger (data := data)).run afterDemand (by
      intro key isNew isOld
      simp only [List.mem_singleton] at isNew
      subst isNew
      revert isOld
      simp [pairFresh])
  have afterTokens :=
    (capacityTokenLedger (data := data)).run afterPairs (by
      intro key isNew isOld
      simp only [List.mem_singleton] at isNew
      subst isNew
      revert isOld
      simp [tokenFresh])
  have afterPressure :=
    (coupledFibrePressure (data := data)).run afterTokens (by
      intro key isNew isOld
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil,
        or_false] at isNew
      rcases isNew with rfl | rfl | rfl <;> revert isOld <;>
        simp [partitionFresh, pressureFresh, estimateFresh])
  -- Node `[137]`: `prop:single-graph-sparse-pressure-routing`.
  match sparsePressureDichotomy afterPressure (K .sparsePressureNearCubic)
      (K .sparsePressureOverload) (fun value => ⟨value⟩) (fun value => ⟨value⟩)
      (by simp [nearCubicFresh]) (by simp [overloadFresh]) with
  | .left nearCubicHistory => exact .nearCubic nearCubicHistory
  | .right overloadHistory =>
      have afterClassification :=
        (bottleneckClassification (data := data)).run overloadHistory (by
          intro key isNew isOld
          simp only [List.mem_singleton] at isNew
          subst isNew
          revert isOld
          simp [classificationFresh])
      have afterBottleneck :=
        (homogeneousBottleneck (data := data)).run afterClassification (by
          intro key isNew isOld
          simp only [List.mem_singleton] at isNew
          subst isNew
          revert isOld
          simp [bottleneckFresh])
      exact .overloaded afterBottleneck

/-- **The sparse surplus branch, entered from the entry spine's own exit.**

The predecessor is the literal ledger of `Spine.Result.surplusAbove`: node
`[19]`'s above arm, indexed by the nine facts that branch established.  Both
prerequisites -- the selection entry and node `[10]`'s slack independence -- are
in that index, so the block elaborates against it and nothing is re-selected or
re-proved. -/
noncomputable def runSurplusBranch
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected (surplusAboveKeys (BranchState := BranchState)
        (presentation := presentation) (data := data))) :
    SurplusResult selected
      (surplusAboveKeys (BranchState := BranchState)
        (presentation := presentation) (data := data)) :=
  runSparseActivation history (by simp) (by simp) (by simp) (by simp) (by simp)
    (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
    (by simp) (by simp) (by simp)

end Hypostructure.Graph.Strategy.Spine
