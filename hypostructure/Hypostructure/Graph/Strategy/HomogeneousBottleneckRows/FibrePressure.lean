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
`prop:single-graph-sparse-pressure-routing`, on the certified ledger produced
immediately above: either it respects the geometric cap and gives `[138]`, or
its positive coupled excess selects one of `[140]`, `[142]`, `[143]`. -/
noncomputable def coupledExcessDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous : ExactLedger (Input BranchState Presentation presentation data)
      current known)
    [FactKeys.Has (K .fibrePressure) known]
    [FactKeys.Has (K .surplusAbove) known]
    (nearCubicFresh : K .sparsePressureNearCubic ∉ known)
    (overloadFresh : K .sparsePressureOverload ∉ known) :
    Decision (K .sparsePressureNearCubic) (K .sparsePressureOverload) previous := by
  classical
  exact Decision.run previous (K .sparsePressureNearCubic) (K .sparsePressureOverload)
    `Hypostructure.Graph.Strategy.Spine.coupledExcessDichotomy
    (Classical.choice (show Nonempty
        ((K .sparsePressureNearCubic).At current ⊕
          (K .sparsePressureOverload).At current) from by
      obtain ⟨active, presentation, activationEq, certified, _token, _role,
          _tokenMem, _display, _roleBound, _forced, _pattern⟩ :=
        (previous.get (K .fibrePressure)).down
      have above : data.surplusThreshold current.object.vertexCount <
          current.object.degreeSurplus data.threshold :=
        (previous.get (K .surplusAbove)).down
      let ledger := certified.ledger
      let patternBound := fun _ : Graph.SameTokenBlockerRoles.TokenClass =>
        Graph.SameTokenBlockerRoles.geometricPatternBound data.routingLabelBound
      rcases Nat.eq_zero_or_pos (ledger.presented.coupledExcess
          ledger.presented.tokenClass patternBound) with balanced | overload
      · have capped : Graph.SparsePressureCappedAt certified
            data.routingLabelBound := by
          exact ledger.presented.demand_le_sparsePressureBound
            ledger.presented.tokenClass patternBound
            (Graph.SameTokenBlockerRoles.homogeneousTokenCap
              data.routingLabelBound)
            (current.object.capacityTokenSupply data.threshold)
            (fun _ => Nat.le_refl _) ledger.tokens_card_le balanced
        exact ⟨.inl ⟨by
          have sizePos : 0 < current.object.vertexCount :=
            current.object.vertexCount_pos_of_degreeSurplus_pos
              (lt_of_le_of_lt (Nat.zero_le _) above)
          have safety := data.quadraticSafetyScale_le_spineScale
          have estimate := Graph.surplus_le_scale_of_capped presentation certified
            data.routingLabelBound capped sizePos safety
          change current.object.degreeSurplus data.threshold ≤
            data.spineScale * Core.ceilSqrt current.object.vertexCount
          exact estimate⟩⟩
      · exact ⟨.inr ⟨by
          obtain ⟨token, tokenMem, role, excess, pattern⟩ :=
            ledger.presented.exists_overloaded_roleFibre
              ledger.presented.tokenClass patternBound
          exact ⟨active, presentation, activationEq, certified, token, role,
            tokenMem, trivial, overload, excess, pattern⟩⟩⟩))
    nearCubicFresh overloadFresh

/-- Node `[141]`: classify the concrete overload witness, already known to be
outside the window-incidence class, according to whether its token lies in the
remainder-surplus class; the residual is otherwise primitive. -/
noncomputable def remainderOverloadClassDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous : ExactLedger (Input BranchState Presentation presentation data)
      current known)
    [FactKeys.Has (K .windowClassAbsent) known]
    (remainderFresh : K .remainderClassOverload ∉ known)
    (primitiveFresh : K .remainderClassAbsent ∉ known) :
    Decision (K .remainderClassOverload) (K .remainderClassAbsent) previous :=
  Decision.run previous (K .remainderClassOverload) (K .remainderClassAbsent)
    `Hypostructure.Graph.Strategy.Spine.remainderOverloadClassDichotomy
    (Classical.choice (show Nonempty
        ((K .remainderClassOverload).At current ⊕
          (K .remainderClassAbsent).At current) from by
      obtain ⟨active, declared, activationEq, certified, token, role, tokenMem,
        outside, rest⟩ := (previous.get (K .windowClassAbsent)).down
      let ledger := certified.ledger
      cases classified : ledger.presented.tokenClass token with
      | windowIncidence => exact absurd classified outside
      | remainderSurplus =>
          exact ⟨.inl ⟨active, declared, activationEq, certified, token, role,
            tokenMem, classified, rest⟩⟩
      | primitiveCarrier =>
          exact ⟨.inr ⟨active, declared, activationEq, certified, token, role,
            tokenMem, classified, rest⟩⟩))
    remainderFresh primitiveFresh

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
