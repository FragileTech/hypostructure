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
`prop:single-graph-sparse-pressure-routing`, on the blocked branch: it reads
its predecessor `K .fibrePressure` (the high-load display at G's canonical
certified capacity-token ledger), and splits `D_all > 0` at exactly that one
ledger.  The near-cubic arm is the literal negation at the same ledger; node
`[138]` derives the surplus estimate from it. -/
noncomputable def coupledExcessDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous : ExactLedger (Input BranchState Presentation presentation data)
      current known)
    [FactKeys.Has (K .fibrePressure) known]
    (nearCubicFresh : K .sparsePressureNearCubic ∉ known)
    (overloadFresh : K .sparsePressureOverload ∉ known) :
    Decision (K .sparsePressureNearCubic) (K .sparsePressureOverload) previous :=
  Decision.run previous (K .sparsePressureNearCubic) (K .sparsePressureOverload)
    `Hypostructure.Graph.Strategy.Spine.coupledExcessDichotomy
    (Classical.choice (show Nonempty
        ((K .sparsePressureNearCubic).At current ⊕
          (K .sparsePressureOverload).At current) from by
      obtain ⟨capacity, certified, selected, _pressure⟩ :=
        (previous.get (K .fibrePressure)).down
      by_cases overload : 0 < sparseCoupledExcess data.toParameters certified
      · exact ⟨.inr ⟨capacity, certified, selected, overload⟩⟩
      · refine ⟨.inl ⟨fun capacity' certified' selected' positive => ?_⟩⟩
        have same := Option.some.inj (selected'.symm.trans selected)
        cases same
        exact overload positive))
    nearCubicFresh overloadFresh

/-- Node `[137]` on the blocker-free branch: the same coupled excess test
`D_all > 0?` at G's canonical certified ledger, reached from `[131]`'s "count
holds: free pairs" edge; it reads that predecessor `K .freePairEntropySandwich`.
The two arms are the overload predicate at the canonical ledger and its
literal negation (registered: both arms close by `[138]`). -/
noncomputable def freePairCoupledExcessDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous : ExactLedger (Input BranchState Presentation presentation data)
      current known)
    [FactKeys.Has (K .freePairEntropySandwich) known]
    (nearCubicFresh : K .sparsePressureNearCubic ∉ known)
    (overloadFresh : K .sparsePressureOverload ∉ known) :
    Decision (K .sparsePressureNearCubic) (K .sparsePressureOverload) previous := by
  classical
  exact Decision.run previous (K .sparsePressureNearCubic) (K .sparsePressureOverload)
    `Hypostructure.Graph.Strategy.Spine.freePairCoupledExcessDichotomy
    (Classical.choice (show Nonempty
        ((K .sparsePressureNearCubic).At current ⊕
          (K .sparsePressureOverload).At current) from by
      have _count := (previous.get (K .freePairEntropySandwich)).down
      by_cases overload : Holds BranchState Presentation presentation data
          .sparsePressureOverload current.object
      · exact ⟨.inr ⟨overload⟩⟩
      · exact ⟨.inl ⟨fun capacity certified selected positive =>
          overload ⟨capacity, certified, selected, positive⟩⟩⟩))
    nearCubicFresh overloadFresh

/-- Node `[144]`, the dichotomy of `thm:homogeneous-overload-geometric-closure`
as the proof of `prop:nonnear-cubic-sharp-overload-routing` applies it, at G's
canonical certified ledger -- the ledger whose overloading token the geometric
audit `[140]`/`[142]`/`[143]` just read (its predecessor key): either the three
fixed homogeneous caps `L_W = L_R = L_P = L_geom` fail at that ledger, or they
hold there.  On the failing arm the audited pattern is read by
`lem:same-token-bottleneck-routing`; the caps arm goes to `[138]`.

This is the paper's order (diagram tex 1238-1252: the audits `[140]`/`[142]`/
`[143]` feed `[144]` "Type B handoff or capped route?", whose capped arm goes to
`[138]`).  On that order the caps arm is unreachable: the audit's pattern at
the overloading token refutes the caps at the same ledger
(`Contracts.SurplusPair.not_homogeneousCapsHold_of_pattern`).  It is a paper
error, registered in `lean-vs-paper-discrepancies.md#paper-errors`; the arm is
kept as the paper draws it. -/
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
