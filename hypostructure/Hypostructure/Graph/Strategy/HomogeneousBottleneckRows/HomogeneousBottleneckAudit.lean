import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.NamedSurplusExits
import Hypostructure.Graph.SparsePressureLedger
import Hypostructure.Graph.GluedCrossingCycle
import Hypostructure.Graph.Strategy.HomogeneousBottleneckRows.Basic

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-- Nodes `[140]`, `[142]`, `[143]`: the geometric audit of the overload
selected at `[137]` and classified by `[139]`/`[141]`.  One row, run after each
class arm: it reads the concrete overload witness on the incoming ledger, whose
role-fibre excess is positive, so the role fibre exceeds
`(L_geom - 1)(2 L_geom - 3)` and carries an `L_geom`-matching or `L_geom`-star
(`lem:same-token-matching-star`); every endpoint of every pattern edge then has
its declared same-root connector configuration.  The source class recorded in
the fact is the token's own class, read off the token.  This is the only
derivation of the bottleneck pattern consumed by `[144]`. -/
@[reducible] noncomputable def homogeneousBottleneckAuditRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.homogeneousBottleneckAudit
    { Requires := [K .sparsePressureOverload, K .capacityTokenLedger]
      Produces := [K .homogeneousBottleneckPattern]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .homogeneousBottleneckPattern)
        (show Value BranchState Presentation presentation data
            .homogeneousBottleneckPattern inputs.current from ⟨by
          classical
          letI := data.boundaryProfileFintype
          obtain ⟨active, declared, activationEq, certified, token, role,
              tokenMem, _selected, positive, absorbs, quantitativePattern⟩ :=
            (inputs.get (K .sparsePressureOverload)).down
          have connectedOn :
              Graph.SupportComponents.Connected.ConnectedOn
                inputs.current.object inputs.current.object.vertexFinset :=
            (inputs.get (K .capacityTokenLedger)).down.choose_spec.choose_spec.2.2.2.2
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
                ∃ responseSupport : Finset inputs.current.object.Vertex,
                  declared.activation.pairSupport pair = some responseSupport ∧
                    ∀ demand ∈ pair,
                      ∃ configuration :
                          Graph.SameTokenRoutingGerms.RoutingConfiguration
                            inputs.current.object
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
                pair ∈ inputs.current.object.portPairSchedule data.threshold :=
              ledger.presented.fibre_subset token pairTokenFibre
            have pairSubset :
                pair ⊆ inputs.current.object.excessPorts data.threshold :=
              inputs.current.object.subset_excessPorts_of_mem_portPairSchedule
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
              rw [← data.routingLabelBound_eq]
              simpa only [Graph.SameTokenBlockerRoles.geometricPatternBound] using
                matchingLarge
            · intro pair pairMem
              exact configurations pair (matchingSubset pairMem)
          · refine Or.inr ⟨centre, star, starSubset, starShape, ?_, ?_⟩
            · change Fintype.card
                  (Graph.SameTokenRoutingGerms.RoutingLabel data.BoundaryProfile
                    (Graph.WindowCurvature.Label data.windowOrder)) + 1 ≤
                star.card
              rw [← data.routingLabelBound_eq]
              simpa only [Graph.SameTokenBlockerRoles.geometricPatternBound] using
                starLarge
            · intro pair pairMem
              exact configurations pair (starSubset pairMem)⟩)
        .nil)

end Hypostructure.Graph.Strategy.Spine
