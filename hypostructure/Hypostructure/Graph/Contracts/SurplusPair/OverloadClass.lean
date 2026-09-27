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

/-- The canonical overload of G is read off its canonical ledger and the
canonical token and role at that ledger. -/
theorem canonicalOverload_eq_some
    {capacity : SurplusCapacity data object}
    {certified : SurplusCertified data object capacity}
    {token : certified.ledger.presented.Token}
    {role : Graph.SameTokenBlockerRoles.Role}
    (ledgerSelected : canonicalCertifiedCapacityData data object =
      some ⟨capacity, certified⟩)
    (tokenSelected : canonicalOverloadTokenAt data object certified =
      some (token, role)) :
    canonicalOverload data object = some ⟨⟨capacity, certified⟩, (token, role)⟩ := by
  unfold canonicalOverload
  rw [ledgerSelected, Option.bind_some]
  simp only
  rw [tokenSelected, Option.map_some]

/-- The canonical overload of G, when it exists, is the canonical token and
role at G's canonical ledger. -/
theorem canonicalOverload_selected
    {overload : (ledger : (capacity : SurplusCapacity data object) ×
        SurplusCertified data object capacity) ×
      (ledger.2.ledger.presented.Token × Graph.SameTokenBlockerRoles.Role)}
    (selected : canonicalOverload data object = some overload) :
    canonicalCertifiedCapacityData data object = some overload.1 ∧
      canonicalOverloadTokenAt data object overload.1.2 = some overload.2 := by
  unfold canonicalOverload at selected
  cases ledgerSelected : canonicalCertifiedCapacityData data object with
  | none => simp [ledgerSelected] at selected
  | some ledger =>
    rw [ledgerSelected, Option.bind_some] at selected
    cases tokenSelected : canonicalOverloadTokenAt data object ledger.2 with
    | none => simp [tokenSelected] at selected
    | some choice =>
      rw [tokenSelected, Option.map_some, Option.some.injEq] at selected
      subst selected
      exact ⟨rfl, tokenSelected⟩

/-- Node `[137]`, overload arm, `prop:single-graph-sparse-pressure-routing`
(b) with `cor:coupled-single-graph-overload-budget`: positive coupled excess
at G's canonical ledger exhibits an overloaded role fibre
(`exists_overloaded_roleFibre`), so the canonical overloading token of G
exists and has a class. -/
theorem canonicalOverloadClass_of_overload
    (overload : SparsePressureOverloadSchema data object) :
    ∃ value, canonicalOverloadClass data object = some value := by
  classical
  obtain ⟨capacity, certified, ledgerSelected, positive⟩ := overload
  obtain ⟨token, tokenMem, role, excess, pattern⟩ :=
    certified.ledger.presented.exists_overloaded_roleFibre
      certified.ledger.presented.tokenClass
      (fun _ => Graph.SameTokenBlockerRoles.geometricPatternBound
        data.routingLabelBound)
  obtain ⟨chosenToken, chosenRole, tokenSelected, _spec⟩ :=
    canonicalOverloadTokenAt_spec data object certified
      ⟨token, role, tokenMem, positive, excess, pattern⟩
  refine ⟨certified.ledger.presented.tokenClass chosenToken, ?_⟩
  unfold canonicalOverloadClass
  rw [canonicalOverload_eq_some ledgerSelected tokenSelected, Option.map_some]

/-- Node `[143]`'s entry: the class of G's overloading token is neither
`𝔗_W` (node `[139]` no arm) nor `𝔗_R` (node `[141]` no arm), so it is
`𝔗_prim`. -/
theorem primitiveClassOverload_of_classesAbsent
    (windowAbsent : WindowClassAbsentStatement data object)
    (remainderAbsent : RemainderClassAbsentStatement data object) :
    PrimitiveClassOverloadStatement data object := by
  obtain ⟨value, classified, notWindow⟩ := windowAbsent
  obtain ⟨value', classified', notRemainder⟩ := remainderAbsent
  have same : value' = value :=
    Option.some.inj (classified'.symm.trans classified)
  subst same
  change canonicalOverloadClass data object = some .primitiveCarrier
  cases value' with
  | windowIncidence => exact (notWindow rfl).elim
  | remainderSurplus => exact (notRemainder rfl).elim
  | primitiveCarrier => exact classified

set_option maxHeartbeats 1000000 in
/-- Nodes `[140]`, `[142]`, `[143]`: the geometric audit of G's overloading
token, whatever its class.  Its positive role-fibre excess makes the role
fibre exceed `(L_geom - 1)(2 L_geom - 3)`, so it carries an `L_geom`-matching
or `L_geom`-star, and on G's connected vertex set (node `[136]`) every endpoint
of every pattern edge has its declared same-root connector configuration.  The
node publishes the canonical such pattern of G. -/
theorem homogeneousBottleneckPattern_of_class
    {value : Graph.SameTokenBlockerRoles.TokenClass}
    (classified : canonicalOverloadClass data object = some value)
    (capacityLedger : CapacityTokenLedgerStatement data object)
    (labelCount : data.routingLabelBound = Fintype.card
      (Graph.SameTokenRoutingGerms.RoutingLabel data.BoundaryProfile
        (Graph.WindowCurvature.Label data.windowOrder))) :
    HomogeneousBottleneckPatternSchema data object := by
  classical
  letI := data.boundaryProfileFintype
  obtain ⟨overload, overloadSelected⟩ :
      ∃ overload, canonicalOverload data object = some overload := by
    unfold canonicalOverloadClass at classified
    cases selected : canonicalOverload data object with
    | none => simp [selected] at classified
    | some overload => exact ⟨overload, rfl⟩
  obtain ⟨ledgerSelected, tokenSelected⟩ := canonicalOverload_selected overloadSelected
  obtain ⟨⟨declared, certified⟩, token, role⟩ := overload
  obtain ⟨tokenMem, positive, absorbs, _quantitativePattern⟩ :=
    canonicalOverloadTokenAt_spec_of_eq_some data object tokenSelected
  -- Node `[136]`'s presentation of G, with its connectedness.
  obtain ⟨capacity, capacitySelected, capacitySpec⟩ := capacityLedger
  have sameCapacity : capacity = declared :=
    Option.some.inj (capacitySelected.symm.trans
      ((canonicalCertifiedCapacityData_eq_some_iff data object declared
        certified).1 ledgerSelected).1)
  subst sameCapacity
  obtain ⟨⟨active, activationEq⟩, _primitiveEq, _primitiveLe, _concrete,
      connectedOn, _packingEq⟩ := capacitySpec
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
          capacity.activation.pairSupport pair = some responseSupport ∧
            ∀ demand ∈ pair,
              ∃ configuration :
                  Graph.SameTokenRoutingGerms.RoutingConfiguration
                    object
                    (capacity.sameTokenRoutingSupport token pair)
                    (Graph.CapacityPresentation.tokenSupport token)
                    (capacity.activation.localBuffer demand),
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
        Graph.FiniteObject.capacityCharge capacity.activation
            capacity.carrier data.threshold capacity.packing pair =
          some token := by
      have labelled := (Finset.mem_filter.mp pairTokenFibre).2
      change Graph.CanonicalFibreLedger.canonicalLabel
          capacity.tokenOrder capacity.Eligible pair = some token at labelled
      have charged : capacity.Eligible token pair :=
        Graph.CanonicalFibreLedger.applies_canonicalLabel labelled
      exact charged
    exact Graph.CapacityPresentation.exists_sameRootRoutingConfigurationFamily_of_charge
        active capacity
        activationEq pairSubset connectedOn charge
  have boundEq : Graph.SameTokenRoutingGerms.patternBound
        (SurplusRoutingLabel data) =
      Graph.SameTokenBlockerRoles.geometricPatternBound data.routingLabelBound := by
    change Fintype.card
        (Graph.SameTokenRoutingGerms.RoutingLabel data.BoundaryProfile
          (Graph.WindowCurvature.Label data.windowOrder)) + 1 = _
    rw [← labelCount]
    rfl
  have exists_ : ∃ pattern,
      HomogeneousPatternSpec data object certified token role pattern := by
    rcases structured with
        ⟨matching, matchingSubset, matchingShape, matchingLarge⟩ |
        ⟨centre, star, starSubset, starShape, starLarge⟩
    · refine ⟨matching, matchingSubset, Or.inl matchingShape, ?_, ?_⟩
      · rw [boundEq]
        exact matchingLarge
      · intro pair pairMem
        exact configurations pair (matchingSubset pairMem)
    · refine ⟨star, starSubset, Or.inr ⟨centre, starShape⟩, ?_, ?_⟩
      · rw [boundEq]
        exact starLarge
      · intro pair pairMem
        exact configurations pair (starSubset pairMem)
  obtain ⟨pattern, patternSelected, patternSpec⟩ :=
    canonicalHomogeneousPatternAt_spec data object certified token role exists_
  exact ⟨⟨⟨capacity, certified⟩, (token, role)⟩, pattern, overloadSelected,
    patternSelected, patternSpec⟩

/-- **The `[144]` caps arm is unreachable after the audits** (paper error at
`[144]`, `thm:homogeneous-overload-geometric-closure` with the diagram order
tex 1238-1252).  The geometric audit `[140]`/`[142]`/`[143]` publishes a
role-homogeneous same-token pattern of size at least `L_geom` in the role
fibre of G's overloading token at G's canonical certified ledger; the fixed
caps at that same ledger say no token carries such a pattern.  So the caps
test of `[144]`, drawn after the audits, has only its failing arm. -/
theorem not_homogeneousCapsHold_of_pattern
    (pattern : HomogeneousBottleneckPatternSchema data object)
    (caps : HomogeneousCapsHoldStatement data object) : False := by
  obtain ⟨⟨⟨capacity, certified⟩, token, role⟩, pat, overloadSelected,
    _patternSelected, spec⟩ := pattern
  obtain ⟨ledgerSelected, tokenSelected⟩ :=
    canonicalOverload_selected overloadSelected
  obtain ⟨capacity', certified', ledgerSelected', capsAt⟩ := caps
  rw [ledgerSelected] at ledgerSelected'
  cases ledgerSelected'
  have tokenMem :=
    (canonicalOverloadTokenAt_spec_of_eq_some data object tokenSelected).1
  obtain ⟨subset, shape, large, _⟩ := spec
  rcases shape with matching | ⟨centre, star⟩
  · exact capsAt.1 _ tokenMem _ ⟨pat, subset, matching, large⟩
  · exact capsAt.2 _ tokenMem _ ⟨centre, pat, subset, star, large⟩

end Hypostructure.Graph.Contracts.SurplusPair
