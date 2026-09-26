import Hypostructure.Graph.Statements.SurplusPair
import Hypostructure.Graph.SparsePressureLedger
import Hypostructure.Graph.SparseUpperEnvelope

/-!
# Contract lemmas: node `[138]`'s surplus estimate

`cor:spine-lower-bound-surplus-estimates` in its three uses on the strict
branch: at the free-pair sandwich of `[131]`, at a capped certified capacity
ledger (`[137]`'s no arm), and at the fixed homogeneous caps (`[144]`'s caps
arm).  Each conclusion is `σ(G) ≤ C_sp ⌈√n⌉` with the registered `C_sp`; the
generic quadratic absorption is `Graph.surplus_le_scale_of_capped` /
`Graph.surplus_le_scale_of_pairSandwich`, and its safety coefficient is the
explicit hypothesis `safety`.
-/

namespace Hypostructure.Graph.Contracts.SurplusPair

open Hypostructure
open Hypostructure.Graph.Strategy.Spine

universe u

variable {data : Parameters} {object : Graph.FiniteObject.{u}}

/-- A strict surplus above the registered scale threshold is positive, so the
object is nonempty. -/
theorem vertexCount_pos_of_surplusAbove
    (above : data.surplusThreshold object.vertexCount <
      object.degreeSurplus data.threshold) :
    0 < object.vertexCount :=
  object.vertexCount_pos_of_degreeSurplus_pos
    (lt_of_le_of_lt (Nat.zero_le _) above)

/-- `[138]` at a certified capacity ledger respecting the geometric cap. -/
theorem spineSurplusEstimate_of_capped
    (capacity : Graph.CapacityPresentation object data.threshold data.windowOrder)
    (certified : Graph.CertifiedObjectCapacityLedger object data.threshold
      data.windowOrder data.surplusScale capacity)
    (capped : Graph.SparsePressureCappedAt certified data.routingLabelBound)
    (above : data.surplusThreshold object.vertexCount <
      object.degreeSurplus data.threshold)
    (safety : Graph.TokenLoad.quadraticSafetyScale ≤ data.spineScale) :
    SpineSurplusEstimateStatement data object :=
  Graph.surplus_le_scale_of_capped capacity certified data.routingLabelBound
    capped (vertexCount_pos_of_surplusAbove above) safety

/-- `[138]` at the free-pair entropy sandwich of `[131]`: with the sparse slack
identity `2m = δn + σ(G)` and a strict surplus, the realized full-pair count
gives `σ(G) ≤ C_sp ⌈√n⌉`. -/
theorem spineSurplusEstimate_of_pairSandwich
    (sandwich : FreePairEntropySandwichStatement data object)
    (slack : SparseSlackSurplusStatement data object)
    (above : data.surplusThreshold object.vertexCount <
      object.degreeSurplus data.threshold)
    (threeLe : 3 ≤ data.threshold)
    (safety : Graph.TokenLoad.quadraticSafetyScale ≤ data.spineScale) :
    SpineSurplusEstimateStatement data object := by
  obtain ⟨_Coordinate, family, _coordinateSupport, _survives, _realization,
    demand, deficitLe, entropy, _sandwich⟩ := sandwich
  have aboveEdges : Graph.cubicBaselineEdgeCount object.vertexCount
      data.threshold ≤ object.edgeCount := by
    unfold Graph.cubicBaselineEdgeCount
    change 2 * object.edgeCount = _ at slack
    omega
  have slackLe : object.edgeCount - Graph.cubicBaselineEdgeCount
      object.vertexCount data.threshold ≤ object.degreeSurplus data.threshold := by
    unfold Graph.cubicBaselineEdgeCount
    change 2 * object.edgeCount = _ at slack
    omega
  exact Graph.surplus_le_scale_of_pairSandwich object
    (Graph.SameTokenBlockerRoles.homogeneousTokenCap data.routingLabelBound)
    (le_trans (by norm_num) threeLe) aboveEdges family.card
    (Graph.spineDeficit object.vertexCount data.threshold family.card) demand
    deficitLe slackLe entropy (vertexCount_pos_of_surplusAbove above) safety

/-- `[138]` on `[137]`'s no arm: no capacity ledger of the object has positive
coupled excess, so the object's own certified ledger (from
`lem:capacity-token-high-load`) is capped and the estimate follows. -/
theorem spineSurplusEstimate_of_notOverloaded
    (notOverloaded : SparsePressureNearCubicStatement data object)
    (pressure : FibrePressureSchema data object)
    (above : data.surplusThreshold object.vertexCount <
      object.degreeSurplus data.threshold)
    (safety : Graph.TokenLoad.quadraticSafetyScale ≤ data.spineScale) :
    SpineSurplusEstimateStatement data object := by
  classical
  obtain ⟨active, capacity, activationEq, certified, _token, _role,
      _tokenMem, _display, _roleBound, _forced, _pattern⟩ := pressure
  let ledger := certified.ledger
  let patternBound := fun _ : Graph.SameTokenBlockerRoles.TokenClass =>
    Graph.SameTokenBlockerRoles.geometricPatternBound data.routingLabelBound
  rcases Nat.eq_zero_or_pos (ledger.presented.coupledExcess
      ledger.presented.tokenClass patternBound) with balanced | overload
  · exact spineSurplusEstimate_of_capped capacity certified
      (ledger.presented.demand_le_sparsePressureBound
        ledger.presented.tokenClass patternBound
        (Graph.SameTokenBlockerRoles.homogeneousTokenCap data.routingLabelBound)
        (object.capacityTokenSupply data.threshold)
        (fun _ => Nat.le_refl _) ledger.tokens_card_le balanced)
      above safety
  · obtain ⟨token, tokenMem, role, excess, pattern⟩ :=
      ledger.presented.exists_overloaded_roleFibre
        ledger.presented.tokenClass patternBound
    exact (notOverloaded ⟨active, capacity, activationEq, certified, token,
      role, tokenMem, trivial, overload, excess, pattern⟩).elim

/-- `[138]` on `[144]`'s caps arm: `cor:homogeneous-same-token-caps-close` at
the object's certified capacity ledger (from `lem:capacity-token-high-load`)
is the sparse-pressure cap at `M₀ = Cap_hom(L_geom)`, since the counted
routing-label alphabet has exactly `routingLabelBound` letters. -/
theorem spineSurplusEstimate_of_capsClose
    (close : HomogeneousBottleneckStatement data object)
    (pressure : FibrePressureSchema data object)
    (above : data.surplusThreshold object.vertexCount <
      object.degreeSurplus data.threshold)
    (labelCount : data.routingLabelBound = Fintype.card
      (Graph.SameTokenRoutingGerms.RoutingLabel data.BoundaryProfile
        (Graph.WindowCurvature.Label data.windowOrder)))
    (safety : Graph.TokenLoad.quadraticSafetyScale ≤ data.spineScale) :
    SpineSurplusEstimateStatement data object := by
  obtain ⟨_active, capacity, _activationEq, certified, _token, _role,
      _tokenMem, _display, _roleBound, _forced, _pattern⟩ := pressure
  obtain ⟨_loads, _blocked, surplus, _edges⟩ := close capacity certified.ledger
  have patternEq :
      Graph.SameTokenRoutingGerms.patternBound
          (Graph.SameTokenRoutingGerms.RoutingLabel data.BoundaryProfile
            (Graph.WindowCurvature.Label data.windowOrder)) =
        Graph.SameTokenBlockerRoles.geometricPatternBound
          data.routingLabelBound := by
    unfold Graph.SameTokenRoutingGerms.patternBound
      Graph.SameTokenRoutingGerms.labelBound
      Graph.SameTokenBlockerRoles.geometricPatternBound
    rw [labelCount]
  rw [patternEq] at surplus
  exact spineSurplusEstimate_of_capped capacity certified surplus above safety

end Hypostructure.Graph.Contracts.SurplusPair
