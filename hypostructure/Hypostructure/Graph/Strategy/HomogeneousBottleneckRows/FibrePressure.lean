import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.NamedSurplusExits
import Hypostructure.Graph.SparsePressureLedger
import Hypostructure.Graph.GluedCrossingCycle
import Hypostructure.Graph.Strategy.HomogeneousBottleneckRows.Basic
import Hypostructure.Graph.SparseUpperEnvelope
import Hypostructure.Graph.Contracts.SurplusPair.Pressure
import Hypostructure.Graph.Contracts.SurplusPair.OverloadClass

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
        ⟨Graph.Contracts.SurplusPair.fibrePressure_of_partition (inputs.get (K .roleFibrePartition)).down⟩
        .nil)

/-- Node `[137]`, the coupled excess test `D_all > 0?` of
`prop:single-graph-sparse-pressure-routing`, at G's canonical certified
capacity-token ledger: exact case analysis on the overload predicate at that
ledger.  The near-cubic arm is its literal negation at the same ledger; node
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
      .inl ⟨fun capacity certified selected positive =>
        overload ⟨capacity, certified, selected, positive⟩⟩)
    nearCubicFresh overloadFresh

/-- Node `[144]`, the dichotomy of `thm:homogeneous-overload-geometric-closure`
as the proof of `prop:nonnear-cubic-sharp-overload-routing` applies it, at G's
canonical certified ledger -- the ledger whose overloading token the geometric
audit `[140]`/`[142]`/`[143]` just read (its predecessor key): either the three
fixed homogeneous caps `L_W = L_R = L_P = L_geom` fail at that ledger, or they
hold there.  On the failing arm the audited pattern is read by
`lem:same-token-bottleneck-routing`; the caps arm goes to `[138]`. -/
noncomputable def homogeneousBottleneckDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous : ExactLedger (Input BranchState Presentation presentation data)
      current known)
    [FactKeys.Has (K .homogeneousBottleneckPattern) known]
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
      obtain ⟨overload, _pattern, overloadSelected, _patternSelected, _spec⟩ :=
        (previous.get (K .homogeneousBottleneckPattern)).down
      have ledgerSelected :=
        (Graph.Contracts.SurplusPair.canonicalOverload_selected
          overloadSelected).1
      by_cases caps : Graph.HomogeneousCapsHoldAt overload.1.2.ledger
          (Graph.SameTokenRoutingGerms.RoutingLabel data.BoundaryProfile
            (Graph.WindowCurvature.Label data.windowOrder))
      · exact ⟨.inr ⟨overload.1.1, overload.1.2, ledgerSelected, caps⟩⟩
      · exact ⟨.inl ⟨overload.1.1, overload.1.2, ledgerSelected, caps⟩⟩))
    failFresh capsFresh

end Hypostructure.Graph.Strategy.Spine
