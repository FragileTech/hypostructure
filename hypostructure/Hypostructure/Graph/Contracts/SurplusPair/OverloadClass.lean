import Hypostructure.Graph.Statements.SurplusPair
import Hypostructure.Graph.NamedSurplusExits
import Hypostructure.Graph.SparsePressureLedger
import Hypostructure.Graph.GluedCrossingCycle

/-!
# Contract lemmas: the token-class tests `[139]`, `[141]` and the geometric
audits `[140]`, `[142]`, `[143]`

The overload of `[137]` is classified by the class of its token, read off the
token.  Whatever class selects the overload, its role fibre is large enough to
carry a role-homogeneous same-token `L_geom`-matching or `L_geom`-star
(`lem:same-token-matching-star`), and every endpoint of every pattern edge has
its declared same-root connector configuration: one geometric audit, stated
once for an arbitrary class selector.
-/

namespace Hypostructure.Graph.Contracts.SurplusPair

open Hypostructure
open Hypostructure.Graph.Strategy.Spine

universe u

variable {data : Parameters} {object : Graph.FiniteObject.{u}}

/-- Node `[143]`'s entry: an overload whose token is in neither `𝔗_W` nor
`𝔗_R` has its token in `𝔗_prim`. -/
theorem primitiveClassOverload_of_classesAbsent
    (overload : SparsePressureOverloadSchema data object)
    (windowAbsent : WindowClassAbsentStatement data object)
    (remainderAbsent : RemainderClassAbsentStatement data object) :
    PrimitiveClassOverloadStatement data object := by
  obtain ⟨active, capacity, activationEq, certified, token, role, tokenMem,
    _selected, rest⟩ := overload
  cases classified : certified.ledger.presented.tokenClass token with
  | windowIncidence =>
      exact (windowAbsent ⟨active, capacity, activationEq, certified, token,
        role, tokenMem, classified, rest⟩).elim
  | remainderSurplus =>
      exact (remainderAbsent ⟨active, capacity, activationEq, certified, token,
        role, tokenMem, classified, rest⟩).elim
  | primitiveCarrier =>
      exact ⟨active, capacity, activationEq, certified, token, role, tokenMem,
        classified, rest⟩

/-- Nodes `[140]`, `[142]`, `[143]`: the geometric audit of an overload whose
token class satisfies `Selects`.  Its positive role-fibre excess makes the role
fibre exceed `(L_geom - 1)(2 L_geom - 3)`, so it carries an `L_geom`-matching or
`L_geom`-star, and on the object's connected vertex set every endpoint of
every pattern edge has its declared same-root connector configuration. -/
theorem homogeneousBottleneckPattern_of_overloadAtClass
    {Selects : Graph.SameTokenBlockerRoles.TokenClass → Prop}
    (overload : ∃ active : Graph.ActiveSurplusDemands
        (Graph.MinimumDegreeAtLeast data.threshold)
        (Graph.HasCycleWithLength data.LengthOK) data.LengthOK object
        data.threshold,
      ∃ capacity : Graph.CapacityPresentation object data.threshold
          data.windowOrder,
        capacity.activation =
            (Graph.recordSparsePairDEBlockers
              (Baseline := Graph.MinimumDegreeAtLeast data.threshold)
              (LengthOK := data.LengthOK)
              (Graph.pairResponseActivation active)
              (object.portPairSchedule data.threshold)) ∧
          Graph.OverloadAtClass object data.threshold data.windowOrder
            data.surplusScale data.routingLabelBound capacity Selects)
    (capacityLedger : CapacityTokenLedgerStatement data object)
    (labelCount : data.routingLabelBound = Fintype.card
      (Graph.SameTokenRoutingGerms.RoutingLabel data.BoundaryProfile
        (Graph.WindowCurvature.Label data.windowOrder))) :
    HomogeneousBottleneckPatternSchema data object := by
  classical
  letI := data.boundaryProfileFintype
  obtain ⟨active, declared, activationEq, certified, token, role,
      tokenMem, _selected, positive, absorbs, quantitativePattern⟩ := overload
  have connectedOn :
      Graph.SupportComponents.Connected.ConnectedOn object object.vertexFinset :=
    capacityLedger.choose_spec.choose_spec.2.2.2.2
  let ledger := certified.ledger
  have productPositive :
      0 < Graph.SameTokenBlockerRoles.sameTokenRoleBound *
        ledger.presented.tokens.card *
        ledger.presented.roleFibreExcess ledger.presented.tokenClass
          (fun _ => Graph.SameTokenBlockerRoles.geometricPatternBound
            data.routingLabelBound) token role :=
    positive.trans_le absorbs
  have excessPositive :
      0 < ledger.presented.roleFibreExcess ledger.presented.tokenClass
        (fun _ => Graph.SameTokenBlockerRoles.geometricPatternBound
          data.routingLabelBound) token role := by
    by_contra notPositive
    have zero : ledger.presented.roleFibreExcess
        ledger.presented.tokenClass
        (fun _ => Graph.SameTokenBlockerRoles.geometricPatternBound
          data.routingLabelBound) token role = 0 :=
      Nat.eq_zero_of_not_pos notPositive
    simp [zero] at productPositive
  have large :
      (Graph.SameTokenBlockerRoles.geometricPatternBound
          data.routingLabelBound - 1) *
          (2 * Graph.SameTokenBlockerRoles.geometricPatternBound
            data.routingLabelBound - 3) <
        (ledger.presented.roleFibre token role).card := by
    unfold Graph.CapacityTokenLedger.roleFibreExcess at excessPositive
    exact Nat.sub_pos_iff_lt.mp excessPositive
  have structured := Graph.PatternFamily.exists_matching_or_star_of_lt_card
    (ledger.presented.roleFibre token role)
    (Graph.SameTokenBlockerRoles.geometricPatternBound
      data.routingLabelBound)
    (by simp [Graph.SameTokenBlockerRoles.geometricPatternBound])
    (ledger.presented.pairs_roleFibre token role) large
  have configurations :
      ∀ pair ∈ ledger.presented.roleFibre token role,
        ∃ responseSupport : Finset object.Vertex,
          declared.activation.pairSupport pair = some responseSupport ∧
            ∀ demand ∈ pair,
              ∃ configuration :
                  Graph.SameTokenRoutingGerms.RoutingConfiguration
                    object
                    (declared.sameTokenRoutingSupport token pair)
                    (Graph.CapacityPresentation.tokenSupport token)
                    (declared.activation.localBuffer demand),
                configuration.path.head? =
                  some (Graph.CapacityPresentation.tokenRoot token) ∧
                  configuration.path.getLast? = some demand.2 := by
    intro pair pairFibre
    have pairTokenFibre : pair ∈ ledger.presented.fibre token :=
      Graph.PatternFamily.roleFibre_subset _ _ _ pairFibre
    have pairSchedule :
        pair ∈ object.portPairSchedule data.threshold :=
      ledger.presented.fibre_subset token pairTokenFibre
    have pairSubset :
        pair ⊆ object.excessPorts data.threshold :=
      object.subset_excessPorts_of_mem_portPairSchedule
        data.threshold pairSchedule
    have charge :
        Graph.FiniteObject.capacityCharge declared.activation
            declared.carrier data.threshold declared.packing pair =
          some token := by
      have labelled := (Finset.mem_filter.mp pairTokenFibre).2
      change Graph.CanonicalFibreLedger.canonicalLabel
          declared.tokenOrder declared.Eligible pair = some token at labelled
      have charged : declared.Eligible token pair :=
        Graph.CanonicalFibreLedger.applies_canonicalLabel labelled
      exact charged
    exact Graph.CapacityPresentation.exists_sameRootRoutingConfigurationFamily_of_charge
        active declared
        activationEq pairSubset connectedOn charge
  refine ⟨active, declared, activationEq, certified, token, role,
    tokenMem, positive, absorbs, quantitativePattern,
    ledger.presented.tokenClass token, rfl,
    Graph.CapacityPresentation.tokenRoot token, rfl, ?_⟩
  rcases structured with
      ⟨matching, matchingSubset, matchingShape, matchingLarge⟩ |
      ⟨centre, star, starSubset, starShape, starLarge⟩
  · refine Or.inl ⟨matching, matchingSubset, matchingShape, ?_, ?_⟩
    · change Fintype.card
          (Graph.SameTokenRoutingGerms.RoutingLabel data.BoundaryProfile
            (Graph.WindowCurvature.Label data.windowOrder)) + 1 ≤
        matching.card
      rw [← labelCount]
      simpa only [Graph.SameTokenBlockerRoles.geometricPatternBound] using
        matchingLarge
    · intro pair pairMem
      exact configurations pair (matchingSubset pairMem)
  · refine Or.inr ⟨centre, star, starSubset, starShape, ?_, ?_⟩
    · change Fintype.card
          (Graph.SameTokenRoutingGerms.RoutingLabel data.BoundaryProfile
            (Graph.WindowCurvature.Label data.windowOrder)) + 1 ≤
        star.card
      rw [← labelCount]
      simpa only [Graph.SameTokenBlockerRoles.geometricPatternBound] using
        starLarge
    · intro pair pairMem
      exact configurations pair (starSubset pairMem)

end Hypostructure.Graph.Contracts.SurplusPair
