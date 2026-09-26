import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.NamedSurplusExits
import Hypostructure.Graph.SparsePressureLedger
import Hypostructure.Graph.GluedCrossingCycle
import Hypostructure.Graph.Strategy.HomogeneousBottleneckRows.Basic
import Hypostructure.Graph.SparseUpperEnvelope

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-- Node `[137]`, second production: `lem:capacity-token-high-load` with
`cor:forced-homogeneous-same-token-scale` and the two sharp budgets, at the
same certified ledger whose count was just accepted. -/
@[reducible] noncomputable def fibrePressureRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.fibrePressure
    { Requires := [K .roleFibrePartition]
      Produces := [K .fibrePressure]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .fibrePressure)
        (show Value BranchState Presentation presentation data
            .fibrePressure inputs.current from
          ⟨by
            obtain ⟨active, presentation, activationEq, certified,
                _partition⟩ :=
              (inputs.get (K .roleFibrePartition)).down
            let ledger := certified.ledger
            obtain ⟨token, tokenMem, role, display, roleBound, forced,
                pattern⟩ := ledger.presented.exists_forced_pattern
            exact ⟨active, presentation, activationEq, certified, token, role,
              tokenMem, display, roleBound, forced, pattern⟩⟩)
        .nil)

/-- Node `[137]`, the coupled excess test `D_all > 0?` of
`prop:single-graph-sparse-pressure-routing`, decided by exact case analysis on
the overload predicate.  The near-cubic arm is its literal negation; node
`[138]` derives the surplus estimate from it. -/
noncomputable def coupledExcessDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous : ExactLedger (Input BranchState Presentation presentation data)
      current known)
    (nearCubicFresh : K .sparsePressureNearCubic ∉ known)
    (overloadFresh : K .sparsePressureOverload ∉ known) :
    Decision (K .sparsePressureNearCubic) (K .sparsePressureOverload) previous := by
  classical
  exact Decision.run previous (K .sparsePressureNearCubic) (K .sparsePressureOverload)
    `Hypostructure.Graph.Strategy.Spine.coupledExcessDichotomy
    (if overload : Holds BranchState Presentation presentation data
        .sparsePressureOverload current.object then
      .inr ⟨overload⟩
    else
      .inl ⟨overload⟩)
    nearCubicFresh overloadFresh

/-- Node `[144]`, the dichotomy of `thm:homogeneous-overload-geometric-closure`
as the proof of `prop:nonnear-cubic-sharp-overload-routing` applies it: either
the three fixed homogeneous caps `L_W = L_R = L_P = L_geom` fail, or they hold.
The split is exact classical case analysis on the caps predicate; neither arm
derives anything.  On the failing arm the bottleneck pattern already published
by the geometric audit `[140]`/`[142]`/`[143]` is on the same ledger and is read
there by `lem:same-token-bottleneck-routing`; the caps arm goes to `[138]`. -/
noncomputable def homogeneousBottleneckDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous : ExactLedger (Input BranchState Presentation presentation data)
      current known)
    (failFresh : K .homogeneousCapsFail ∉ known)
    (capsFresh : K .homogeneousCapsHold ∉ known) :
    Decision (K .homogeneousCapsFail) (K .homogeneousCapsHold) previous :=
  Decision.run previous (K .homogeneousCapsFail) (K .homogeneousCapsHold)
    `Hypostructure.Graph.Strategy.Spine.homogeneousBottleneckDichotomy
    (Classical.choice (show Nonempty
        ((K .homogeneousCapsFail).At current ⊕
          (K .homogeneousCapsHold).At current) from by
      classical
      letI := data.boundaryProfileFintype
      by_cases caps : Holds BranchState Presentation presentation data
          .homogeneousCapsHold current.object
      · exact ⟨.inr ⟨caps⟩⟩
      · exact ⟨.inl ⟨caps⟩⟩))
    failFresh capsFresh

end Hypostructure.Graph.Strategy.Spine
