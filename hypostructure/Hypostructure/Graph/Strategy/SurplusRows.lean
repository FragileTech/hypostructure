import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.SparsePortActivation
import Hypostructure.Graph.PrimitiveCarrier
import Hypostructure.Graph.SparsePairLedger
import Hypostructure.Graph.SameTokenBlockerRoles
import Hypostructure.Graph.SparseEntropySandwich
import Hypostructure.Graph.CapacityTokenAssignment
import Hypostructure.Graph.SparseUpperEnvelope
import Hypostructure.Graph.ObjectCapacityLedger
import Hypostructure.Graph.Induced

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
* `sparsePortActivationRow` is `lem:sparse-port-activation` clauses (a)--(d).
  Clause (b) is the return path `R_p ⊆ G − c(p)x(p)`, which `lem:bridgeless` --
  the edge contraction of `Graph/Contraction.lean` -- supplies from the same
  minimality and avoidance; clause (c) is the suppression witness `Q_p`, which
  minimality and avoidance supply through `TightVertexSuppression`; clause (d)
  is the triangle of a triangular port.
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-! ## Node `[126]`: the sparse slack identity -/

/-- `lem:sparse-slack-surplus`, cleared of division: `2m = δn + σ(G)`.

The manuscript writes `m = (3/2)n + (1/2)σ(G)` and, with `λ = 2n − 3 − m`,
`σ(G) = n − 6 − 2λ`; substituting the abbreviation turns the second display into
the first, and doubling the first is the exact `Nat` identity committed here.
The only input is the standing baseline, which the executor reads off the
residual rather than from a fact. -/
@[reducible] noncomputable def sparseSlackSurplusRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.sparseSlackSurplus
    { Requires := []
      Produces := [K .sparseSlackSurplus]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let handshake : data.threshold * inputs.current.object.vertexCount ≤
          2 * inputs.current.object.edgeCount :=
        Graph.baselineDegree_mul_vertexCount_le_two_mul_edgeCount
          inputs.current.object data.threshold fun vertex =>
            le_trans inputs.current.baseline
              (inputs.current.object.minDegree_le_degree vertex)
      .cons (key := K .sparseSlackSurplus)
        (show Value BranchState Presentation presentation data
            .sparseSlackSurplus inputs.current from
          ⟨by
            simp only [Holds]
            unfold Graph.FiniteObject.degreeSurplus
            omega⟩)
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
@[reducible] noncomputable def activeSurplusFamilyRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.activeSurplusFamily
    { Requires := [K .slackIndependent]
      Produces := [K .activeSurplusFamily]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let object := inputs.current.object
      let baseline : ∀ vertex : object.Vertex,
          data.threshold ≤ object.degree vertex :=
        fun vertex => le_trans inputs.current.baseline
          (object.minDegree_le_degree vertex)
      let independent := (inputs.get (K .slackIndependent)).down
      .cons (key := K .activeSurplusFamily)
        (show Value BranchState Presentation presentation data
            .activeSurplusFamily inputs.current from
          ⟨⟨object.card_excessPorts baseline, fun _pair member =>
            ⟨Graph.FiniteObject.centre_high_of_mem_excessPorts member,
              (object.surplusPortOfMem member).endpoint_degree_eq baseline
                independent,
              (object.surplusPortOfMem member).card_shoulders baseline
                independent⟩⟩⟩)
        .nil)

/-! ## Node `[128]`: port activation -/

/-- `lem:sparse-port-activation`, clauses (a)--(d).

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
each port.  Clause (b) is the return path `R_p ⊆ G − c(p)x(p)`: the port's own
edge is not a bridge, because contracting it gives a strictly smaller object
still meeting the baseline, and minimality and avoidance close it exactly as
they close the suppression.  Its first edge after `x(p)` is a shoulder. -/
@[reducible] noncomputable def sparsePortActivationRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.sparsePortActivation
    { Requires := [K .selection]
      Produces := [K .sparsePortActivation]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let object := inputs.current.object
      let fact := (inputs.get (K .selection)).down
      let avoids := fact.1
      let minimal := fact.2
      .cons (key := K .sparsePortActivation)
        (show Value BranchState Presentation presentation data
            .sparsePortActivation inputs.current from
          ⟨fun _pair member left right shoulders distinct =>
          ⟨(object.surplusPortOfMem member).portReturn_of_minimal
              shoulders inputs.current.baseline avoids minimal,
            fun openPort =>
              (object.surplusPortOfMem member).openPortWitness_of_minimal
                shoulders distinct openPort inputs.current.baseline avoids
                minimal,
            fun adjacent =>
              (object.surplusPortOfMem member).triangle_of_shoulders_adj
                (shoulders left |>.2 (Or.inl rfl))
                (shoulders right |>.2 (Or.inr rfl)) adjacent⟩
          ⟩)
        .nil)

/-- The completed active family, read only from the three incoming facts. -/
@[reducible] noncomputable def activeSurplusDemandsRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.activeSurplusDemands
    { Requires := [K .sparseSurplusSurvivor, K .activeSurplusFamily,
        K .sparsePortActivation]
      Produces := [K .activeSurplusDemands]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .activeSurplusDemands)
        (show Value BranchState Presentation presentation data
            .activeSurplusDemands inputs.current from
          ⟨Graph.surviving_active_family
            (inputs.get (K .sparseSurplusSurvivor)).down
            (inputs.get (K .activeSurplusFamily)).down.1
            (by
              classical
              intro pair member
              have cardAt :=
                (inputs.get (K .activeSurplusFamily)).down.2 pair member |>.2.2
              have cardTwo :
                  (inputs.current.object.surplusPortOfMem member).shoulders.card = 2 := by
                simpa [data.threshold_eq_three] using cardAt
              obtain ⟨left, right, distinct, description⟩ :=
                Finset.card_eq_two.mp cardTwo
              refine ⟨left, right, ?_, distinct⟩
              intro vertex
              rw [description]
              simp)
            (inputs.get (K .sparsePortActivation)).down⟩)
        .nil)

/-! ## Node `[129]`: the active family and baseline demand -/

/-- `def:baseline-spine-demand` on the literal sparse-surplus survivor.

The family is not an empty or numerically supplied coordinate carrier.  The
strict-surplus fact makes the selected excess-port family nonempty; the row
chooses one of those actual demands and uses its declared response support for
the baseline coordinates.  Their cardinality is the cubic-baseline exponent
computed from the current object and the registered baseline.  A functional
quotient that identified two of these declared coordinates would localize to
exactly one of the paper's replacement or delocalization exits, both excluded
by the incoming survivor fact.  Thus the family is independently target
testable, its canonical deficit is zero, and the required linear deficit bound
is derived rather than registered. -/
@[reducible] noncomputable def baselineSpineDemandRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.baselineSpineDemand
    { Requires := [K .activeSurplusDemands, K .sparseSurplusSurvivor,
        K .surplusAbove]
      Produces := [K .baselineSpineDemand]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .baselineSpineDemand)
        (show Value BranchState Presentation presentation data
            .baselineSpineDemand inputs.current from
          ⟨by
            classical
            simp only [Holds]
            let object := inputs.current.object
            let active := (inputs.get (K .activeSurplusDemands)).down
            let survivor := (inputs.get (K .sparseSurplusSurvivor)).down
            have surplusPositive :
                0 < object.degreeSurplus data.threshold :=
              lt_of_le_of_lt (Nat.zero_le _)
                (inputs.get (K .surplusAbove)).down
            have activeNonempty :
                (object.excessPorts data.threshold).Nonempty := by
              apply Finset.card_pos.mp
              rw [active.count]
              exact surplusPositive
            let demand := activeNonempty.choose
            let activation := Graph.pairResponseActivation active
            let support := activation.declaredSupport demand
            let bits := Graph.cubicBaselineExponent object.vertexCount
              data.threshold
            let Coordinate := Graph.DeclaredSignature.Coordinate object.Vertex
              (ULift.{u} (Fin bits))
            let family : Finset Coordinate :=
              Finset.univ.image fun bit =>
                Graph.DeclaredSignature.Coordinate.base
                  .sparseSurplus bit support
            let coordinateSupport : Coordinate → Finset object.Vertex :=
              Graph.DeclaredSignature.Coordinate.support
            have familyCard : family.card = bits := by
              rw [Finset.card_image_iff.mpr]
              · simp [Fintype.card_ulift]
              · intro left _ right _ equality
                injection equality
            refine ⟨active, Coordinate, family, coordinateSupport, ?_, ?_, ?_⟩
            · intro declared _functional
              by_contra reducing
              rcases declared.localize reducing with replacement |
                ⟨representative, smaller, baseline, transfer⟩
              · exact survivor
                  (.compression declared.support replacement)
              · exact survivor
                  (.delocalization representative smaller baseline transfer)
            · rw [familyCard]
              exact
                Graph.cubicBaselineBudget_le_two_pow_add_spineDeficit
                  object.vertexCount
                  (le_trans (by omega) data.three_le_threshold) bits
            · rw [familyCard]
              change Graph.spineDeficit object.vertexCount data.threshold bits ≤
                data.surplusScale * object.vertexCount
              simp [bits, Graph.spineDeficit]⟩)
        .nil)

/-! ## Node `[132]`: route the dependent pair family -/

/-- Node `[130]`: construct the full response family from the active-family
fact on the literal `[129]` ledger, then retain exactly the paper's independent
or dependent arm. -/
noncomputable def pairResponseIndependenceDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous : ExactLedger (Input BranchState Presentation presentation data)
      current known)
    [FactKeys.Has (K .activeSurplusDemands) known]
    (independentFresh : K .independentPairFamily ∉ known)
    (dependentFresh : K .dependentPairFamily ∉ known) :
    Decision (K .independentPairFamily) (K .dependentPairFamily) previous :=
  Decision.run previous (K .independentPairFamily) (K .dependentPairFamily)
    `Hypostructure.Graph.Strategy.Spine.pairResponseIndependenceDichotomy
    (Classical.choice (show Nonempty
        ((K .independentPairFamily).At current ⊕
          (K .dependentPairFamily).At current) from by
      let active := (previous.get (K .activeSurplusDemands)).down
      let activation := Graph.pairResponseActivation active
      let pairs := current.object.portPairSchedule data.threshold
      let family := activation.pairFamily pairs
      let coordinateSupport : current.object.PairCoordinate →
          Finset current.object.Vertex := by
        letI := current.object.vertices.decEq
        exact Graph.DeclaredSignature.Coordinate.support
      by_cases independent : ∀ attempt : Graph.AttemptedQuotient
          (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) current.object family
          coordinateSupport,
          attempt.toRankQuotient.FunctionalOn ↑family →
            Set.InjOn attempt.label ↑family
      · exact ⟨.inl ⟨active, independent⟩⟩
      · push_neg at independent
        exact ⟨.inr ⟨active, independent⟩⟩))
    independentFresh dependentFresh

/-! ## Node `[131]`: mixed sparse-spine dependence -/

/-- `lem:mixed-sparse-spine-dependence` on the literal independent residual of
`[130]`.  The concrete spine family and active pair schedule are read from the
same incoming ledger; the four-case circuit proof is published as one exact
semantic fact. -/
@[reducible] noncomputable def mixedSparseSpineDependenceRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.mixedSparseSpineDependence
    { Requires := [K .baselineSpineDemand]
      Produces := [K .mixedSparseSpineDependence]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .mixedSparseSpineDependence)
        (show Value BranchState Presentation presentation data
            .mixedSparseSpineDependence inputs.current from
          ⟨by
            obtain ⟨active, Coordinate, family, coordinateSupport, survives,
                demand, deficitBound⟩ :=
              (inputs.get (K .baselineSpineDemand)).down
            refine ⟨active, Coordinate, family, coordinateSupport, survives,
              demand, deficitBound, ?_⟩
            dsimp only
            intro notIndependent
            classical
            let object := inputs.current.object
            let activation := Graph.pairResponseActivation active
            let pairs := object.portPairSchedule data.threshold
            let pairFamily := activation.pairFamily pairs
            let mixedFamily : Finset (Sum Coordinate object.PairCoordinate) :=
              family.image Sum.inl ∪ pairFamily.image Sum.inr
            let mixedSupport : Sum Coordinate object.PairCoordinate →
                Finset object.Vertex :=
              Sum.elim coordinateSupport (by
                letI := object.vertices.decEq
                exact Graph.DeclaredSignature.Coordinate.support)
            push Not at notIndependent
            obtain ⟨attempt, functional, reducing⟩ := notIndependent
            change ¬ Set.InjOn attempt.label ↑mixedFamily at reducing
            let quotient : Core.TargetRank.RankQuotient.{u, u + 1}
                (Sum Coordinate object.PairCoordinate) :=
              attempt.toRankQuotient
            change quotient.FunctionalOn ↑mixedFamily at functional
            let candidates :
                Finset (Finset (Sum Coordinate object.PairCoordinate)) :=
              mixedFamily.powerset.filter fun independent =>
                Set.InjOn attempt.label ↑independent
            have candidatesNonempty : candidates.Nonempty := by
              refine ⟨∅, ?_⟩
              simp [candidates]
            obtain ⟨independent, independentMember, maximum⟩ :=
              Finset.exists_mem_eq_sup candidates candidatesNonempty Finset.card
            have independentFacts : independent ⊆ mixedFamily ∧
                Set.InjOn attempt.label ↑independent := by
              simpa [candidates] using independentMember
            obtain ⟨coordinate, coordinateMember, coordinateOutside⟩ :
                ∃ coordinate ∈ mixedFamily, coordinate ∉ independent := by
              by_contra absent
              push Not at absent
              have equal : independent = mixedFamily :=
                Finset.Subset.antisymm independentFacts.1 absent
              apply reducing
              rw [← equal]
              exact independentFacts.2
            let candidate := insert coordinate independent
            have candidateSubset : candidate ⊆ mixedFamily := by
              intro member membership
              simp only [candidate, Finset.mem_insert] at membership
              rcases membership with rfl | membership
              · exact coordinateMember
              · exact independentFacts.1 membership
            have candidateNotInjective :
                ¬ Set.InjOn attempt.label ↑candidate := by
              intro candidateInjective
              have candidateMember : candidate ∈ candidates := by
                simp only [candidates, Finset.mem_filter,
                  Finset.mem_powerset]
                exact ⟨candidateSubset, candidateInjective⟩
              have bound := Finset.le_sup (f := Finset.card) candidateMember
              rw [maximum] at bound
              have larger : independent.card < candidate.card := by
                simp [candidate, coordinateOutside]
              omega
            have independentInjective :
                quotient.LabelInjectiveOn ↑independent :=
              independentFacts.2
            have candidateReducing :
                ¬ quotient.LabelInjectiveOn ↑candidate :=
              candidateNotInjective
            obtain ⟨determiners, finite, determinersSubset, determines⟩ :=
              functional independentFacts.1 coordinateMember coordinateOutside
                independentInjective (by
                  simpa [candidate] using candidateReducing)
            let certificates :
                Finset (Finset (Sum Coordinate object.PairCoordinate)) :=
              finite.toFinset.powerset.filter fun certificate =>
                quotient.Determines coordinate ↑certificate
            have certificatesNonempty : certificates.Nonempty := by
              refine ⟨finite.toFinset, ?_⟩
              simp [certificates, determines]
            obtain ⟨minimalDeterminers, minimal⟩ :=
              certificates.exists_minimal certificatesNonempty
            have minimalFacts : minimalDeterminers ⊆ finite.toFinset ∧
                quotient.Determines coordinate ↑minimalDeterminers := by
              simpa [certificates] using minimal.1
            have _inclusionMinimal : ∀ candidate ⊆ minimalDeterminers,
                quotient.Determines coordinate ↑candidate →
                  minimalDeterminers ⊆ candidate := by
              intro candidate candidateSubset candidateDetermines
              apply minimal.2
              · simp only [certificates, Finset.mem_filter,
                  Finset.mem_powerset]
                exact ⟨candidateSubset.trans minimalFacts.1,
                  candidateDetermines⟩
              · exact candidateSubset
            have _circuit : (↑minimalDeterminers : Set _) ⊆
                (↑mixedFamily : Set
                  (Sum Coordinate object.PairCoordinate)) ∧
                Set.Finite (↑minimalDeterminers : Set
                  (Sum Coordinate object.PairCoordinate)) ∧
                  coordinate ∉ minimalDeterminers ∧
                    quotient.Determines coordinate ↑minimalDeterminers := by
              refine ⟨?_, minimalDeterminers.finite_toSet, ?_, minimalFacts.2⟩
              · intro member membership
                exact independentFacts.1
                  (determinersSubset (by simpa using minimalFacts.1 membership))
              · intro coordinateInDeterminers
                exact coordinateOutside
                  (determinersSubset (by
                    apply minimalFacts.1 at coordinateInDeterminers
                    simpa using coordinateInDeterminers))
            have pair_of_mem (pairCoordinate : object.PairCoordinate)
                (membership : Sum.inr pairCoordinate ∈ mixedFamily) :
                ∃ pair ∈ pairs,
                  Graph.FiniteObject.DemandActivation.pairCoordinate pair
                      ((activation.pairSupport pair).getD ∅) = pairCoordinate := by
              change Sum.inr pairCoordinate ∈
                family.image Sum.inl ∪ pairFamily.image Sum.inr at membership
              rcases Finset.mem_union.mp membership with spineMem | pairMem
              · obtain ⟨spine, _, impossible⟩ := Finset.mem_image.mp spineMem
                cases impossible
              · obtain ⟨candidate, candidateMem, candidateEq⟩ :=
                  Finset.mem_image.mp pairMem
                injection candidateEq with candidateEq
                subst pairCoordinate
                change candidate ∈ activation.pairFamily pairs at candidateMem
                rw [Graph.FiniteObject.DemandActivation.pairFamily] at candidateMem
                exact Finset.mem_image.mp candidateMem
            -- The determination is an admissible rank quotient
            -- (`lem:target-rank-circuit`), so it is fibrewise and
            -- context-universal (`lem:degree-profile-fibres`,
            -- `lem:context-universality`); `def:admissible-rank-quotient`'s
            -- representative clauses leave the two remaining alternatives:
            -- a target-complete compression of a proper support (exit (c), and
            -- for a pair coordinate the blocker of type (e)) or a strictly
            -- smaller closed representative (exit (d)).
            rcases attempt.localize reducing with replacement |
                ⟨representative, smaller, baseline, transfer⟩
            · cases coordinate with
              | inl spine =>
                  exact Or.inl (.compression attempt.support replacement)
              | inr pairCoordinate =>
                  obtain ⟨pair, pairMem, pairEq⟩ :=
                    pair_of_mem pairCoordinate coordinateMember
                  subst pairCoordinate
                  exact Or.inr
                    ⟨pair, pairMem, attempt.toAttempt, Or.inr (Or.inr replacement)⟩
            · exact Or.inl
                (.delocalization representative smaller baseline transfer)⟩)
        .nil)

/-- `lem:exact-cubic-baseline-budget` at the current residual's order and
registered baseline.  The result is the manuscript's two-sided estimate with
logarithms cleared, published from the literal `[131]` residual. -/
@[reducible] noncomputable def exactCubicBaselineBudgetRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.exactCubicBaselineBudget
    { Requires := []
      Produces := [K .exactCubicBaselineBudget]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .exactCubicBaselineBudget)
        (show Value BranchState Presentation presentation data
            .exactCubicBaselineBudget inputs.current from
          ⟨by
            have two_le_threshold : 2 ≤ data.threshold :=
              le_trans (by norm_num) data.three_le_threshold
            constructor
            · exact Graph.cubicBaselineBudget_le_pow
                inputs.current.object.vertexCount two_le_threshold
            · intro room
              exact Graph.pow_pred_le_cubicBaselineBudget_mul
                inputs.current.object.vertexCount room⟩)
        .nil)

/-- `lem:incremental-skeleton-room` at the current object's edge count.  Both
the binomial-room estimate and `s ≤ σ/2+1` are stored with logarithms and
division cleared. -/
@[reducible] noncomputable def incrementalSkeletonRoomRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.incrementalSkeletonRoom
    { Requires := []
      Produces := [K .incrementalSkeletonRoom]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .incrementalSkeletonRoom)
        (show Value BranchState Presentation presentation data
            .incrementalSkeletonRoom inputs.current from
          ⟨by
            let object := inputs.current.object
            have two_le_threshold : 2 ≤ data.threshold :=
              le_trans (by norm_num) data.three_le_threshold
            have handshake : data.threshold * object.vertexCount ≤
                2 * object.edgeCount :=
              Graph.baselineDegree_mul_vertexCount_le_two_mul_edgeCount
                object data.threshold fun vertex =>
                  le_trans inputs.current.baseline
                    (object.minDegree_le_degree vertex)
            have above : Graph.cubicBaselineEdgeCount object.vertexCount
                data.threshold ≤ object.edgeCount :=
              Graph.cubicBaselineEdgeCount_le_edgeCount_of_handshake
                object data.threshold handshake
            constructor
            · exact Graph.skeletonBudget_le_cubicBaselineBudget_mul_pow
                object two_le_threshold above
            · have lower : data.threshold * object.vertexCount ≤
                  2 * Graph.cubicBaselineEdgeCount object.vertexCount
                    data.threshold := by
                unfold Graph.cubicBaselineEdgeCount
                omega
              change 2 * (object.edgeCount -
                  Graph.cubicBaselineEdgeCount object.vertexCount
                    data.threshold) ≤
                (2 * object.edgeCount -
                  data.threshold * object.vertexCount) + 2
              omega⟩)
        .nil)

/-- `lem:skeleton-dominates` at the current residual's exact edge stratum.
The fixed-edge labelled skeleton count and the canonical-state pigeonhole are
proved inside this executor and published on the same exact ledger. -/
@[reducible] noncomputable def skeletonDominatesRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.skeletonDominates
    { Requires := []
      Produces := [K .skeletonDominates]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .skeletonDominates)
        (show Value BranchState Presentation presentation data
            .skeletonDominates inputs.current from
          ⟨by
            let object := inputs.current.object
            have count : Nat.card
                (Graph.PackedWindowRealization.Skeleton
                  object.vertexCount object.edgeCount) =
                Graph.skeletonBudget object := by
              simpa [Graph.skeletonBudget, Graph.edgeStratumCount] using
                Graph.PackedWindowRealization.card_skeleton
                  object.vertexCount object.edgeCount
            refine ⟨count, ?_⟩
            intro State stateOf
            have realized :=
              Core.FiniteEntropy.card_range_le_card_ambient stateOf
            exact realized.trans_eq count⟩)
        .nil)

/-- `lem:sparse-pair-dependence-exit` on the literal residual produced by
node `[130]`.  The attempted quotient and its failure of injectivity are read
from that residual's exact ledger.  The two conclusions are distinct decision
arms, and `Decision.run` preserves the complete incoming ancestry on either
arm. -/
noncomputable def blockedPairRoutingDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous : ExactLedger (Input BranchState Presentation presentation data)
      current known)
    [FactKeys.Has (K .dependentPairFamily) known]
    (exitFresh : K .sparsePairExit ∉ known)
    (blockerFresh : K .canonicalBlockerRoute ∉ known) :
    Decision (K .sparsePairExit) (K .canonicalBlockerRoute) previous :=
  Decision.run previous (K .sparsePairExit) (K .canonicalBlockerRoute)
    `Hypostructure.Graph.Strategy.Spine.blockedPairRoutingDichotomy
    (Classical.choice (show Nonempty
        ((K .sparsePairExit).At current ⊕
          (K .canonicalBlockerRoute).At current) from by
      obtain ⟨active, attempt, functional, reducing⟩ :=
        (previous.get (K .dependentPairFamily)).down
      let activation := Graph.pairResponseActivation active
      let pairs := current.object.portPairSchedule data.threshold
      rcases Graph.sparsePairDependence_exit_or_blocker activation pairs
          attempt reducing functional with exit | blocker
      · exact ⟨.inl ⟨exit⟩⟩
      · exact ⟨.inr ⟨active, blocker⟩⟩))
    exitFresh blockerFresh

/-! ## Node `[134]`: canonical blocker ledger -/

/-- The canonical blocker ledger on the literal blocker residual of `[132]`.
The executor reconstructs the paper's full finite blocker set: clauses
(a)--(c) from the two demands' active data, clauses (d)--(e) from every actual
minimal failed determination, and clause (f) from every actual compatible
suppression chord set.  It then publishes the blocked/free partition and the
canonical-fibre no-overcount identities. -/
@[reducible] noncomputable def canonicalPairLedgerRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.canonicalPairLedger
    { Requires := [K .canonicalBlockerRoute]
      Produces := [K .canonicalPairLedger]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .canonicalPairLedger)
        (show Value BranchState Presentation presentation data
            .canonicalPairLedger inputs.current from
          ⟨by
            obtain ⟨active, certificate⟩ :=
              (inputs.get (K .canonicalBlockerRoute)).down
            let activation := Graph.pairResponseActivation active
            let pairs := inputs.current.object.portPairSchedule data.threshold
            let recorded := Graph.recordSparsePairDEBlockers
              (Baseline := Graph.MinimumDegreeAtLeast data.threshold)
              (LengthOK := data.LengthOK) activation pairs
            have baseline : ∀ vertex : inputs.current.object.Vertex,
                data.threshold ≤ inputs.current.object.degree vertex :=
              fun vertex => le_trans inputs.current.baseline
                (inputs.current.object.minDegree_le_degree vertex)
            refine ⟨active, certificate, rfl, ?_, ?_, ?_, ?_, ?_⟩
            · exact inputs.current.object.card_portPairSchedule baseline
            · simpa [recorded] using
                recorded.card_blockedPairs_add_card_unblockedPairs data.threshold
            · exact recorded.card_canonicalIncidenceLedger data.threshold
            · exact recorded.card_blockedPairs_eq_sum_blockerMultiplicity
                data.threshold
            · exact Graph.recordedSparsePairDEBlocker_nonempty activation pairs
                certificate⟩)
        .nil)

/-! ## Node `[135]`: exact window-join pressure -/

@[reducible] noncomputable def exactWindowJoinPressureRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.exactWindowJoinPressure
    { Requires := [K .maximalPacking, K .noProperBaseline,
        K .tightEndpoint, K .surplusAbove]
      Produces := [K .sparseUpperEnvelope]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .sparseUpperEnvelope)
        (show Value BranchState Presentation presentation data
            .sparseUpperEnvelope inputs.current from
          ⟨by
            have baseline : ∀ vertex : inputs.current.object.Vertex,
                data.threshold ≤ inputs.current.object.degree vertex :=
              fun vertex => le_trans inputs.current.baseline
                (inputs.current.object.minDegree_le_degree vertex)
            have surplusPositive :
                0 < inputs.current.object.degreeSurplus data.threshold :=
              lt_of_le_of_lt (Nat.zero_le _)
                (inputs.get (K .surplusAbove)).down
            have edgePositive : 0 < inputs.current.object.edgeCount :=
              inputs.current.object.edgeCount_pos_of_degreeSurplus_pos
                surplusPositive
            have envelope := inputs.current.object.edgeCount_add_two_le
              data.three_le_threshold
              (inputs.get (K .noProperBaseline)).down
              (inputs.get (K .tightEndpoint)).down edgePositive
            obtain ⟨_, packing, valid, maximal, _⟩ :=
              (inputs.get (K .maximalPacking)).down
            exact ⟨envelope, packing, valid, maximal,
              inputs.current.object.exact_window_join_identity valid baseline⟩⟩)
        .nil)

/-! ## Node `[136]`: capacity-token ledger -/

@[reducible] noncomputable def capacityTokenLedgerRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.capacityTokenLedger
    { Requires := [K .canonicalPairLedger, K .sparseUpperEnvelope,
        K .noProperBaseline]
      Produces := [K .capacityTokenLedger]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .capacityTokenLedger)
        (show Value BranchState Presentation presentation data
            .capacityTokenLedger inputs.current from
          PLift.up (by
            obtain ⟨active, certificate, _pairsEq, scheduleCard,
                _partition, _incidence, _multiplicity, _blocked⟩ :=
              (inputs.get (K .canonicalPairLedger)).down
            obtain ⟨envelope, packing, valid, maximal, _joinIdentity⟩ :=
              (inputs.get (K .sparseUpperEnvelope)).down
            let activation := Graph.recordSparsePairDEBlockers
              (Baseline := Graph.MinimumDegreeAtLeast data.threshold)
              (LengthOK := data.LengthOK)
              (Graph.pairResponseActivation active)
              (inputs.current.object.portPairSchedule data.threshold)
            have pairCard : certificate.choose.card = 2 :=
              Graph.card_of_mem_portPairSchedule inputs.current.object data.threshold
                certificate.choose_spec.1
            have pairNonempty : certificate.choose.Nonempty :=
              Finset.card_pos.mp (by omega : 0 < certificate.choose.card)
            let port := pairNonempty.choose
            letI : Nonempty inputs.current.object.Vertex := ⟨port.1⟩
            have graphConnected : inputs.current.object.graph.Connected := by
              classical
              let root : inputs.current.object.Vertex := port.1
              let support : Finset inputs.current.object.Vertex :=
                inputs.current.object.vertexFinset.filter fun vertex =>
                  inputs.current.object.graph.connectedComponentMk vertex =
                    inputs.current.object.graph.connectedComponentMk root
              by_contra disconnected
              have rootMem : root ∈ support := by
                simp [support]
              have supportCardLt : support.card < inputs.current.object.vertexCount := by
                have notAllReachable :
                    ¬ ∀ vertex : inputs.current.object.Vertex,
                      inputs.current.object.graph.Reachable root vertex := by
                  intro allReachable
                  apply disconnected
                  exact inputs.current.object.graph.connected_iff_exists_forall_reachable.mpr
                    ⟨root, allReachable⟩
                push Not at notAllReachable
                rcases notAllReachable with ⟨outside, unreachable⟩
                have outsideNotMem : outside ∉ support := by
                  simp only [support, Finset.mem_filter,
                    inputs.current.object.mem_vertexFinset, true_and,
                    SimpleGraph.ConnectedComponent.eq]
                  exact fun reachable => unreachable reachable.symm
                have strict : support ⊂ inputs.current.object.vertexFinset := by
                  refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
                  · intro vertex _
                    exact inputs.current.object.mem_vertexFinset vertex
                  · intro equal
                    exact outsideNotMem
                      (equal ▸ inputs.current.object.mem_vertexFinset outside)
                simpa only [inputs.current.object.card_vertexFinset] using
                  Finset.card_lt_card strict
              let component : Graph.ProperSubgraph inputs.current.object :=
                Graph.ProperSubgraph.ofInducedSupport inputs.current.object support
                  supportCardLt
              letI : Nonempty component.value.Vertex := ⟨⟨root, rootMem⟩⟩
              have neighborSubset
                  (vertex : component.value.Vertex) :
                  inputs.current.object.graph.neighborSet vertex.1 ⊆
                    (support : Set inputs.current.object.Vertex) := by
                intro neighbor adjacent
                change neighbor ∈ support
                simp only [support, Finset.mem_filter,
                  inputs.current.object.mem_vertexFinset, true_and,
                  SimpleGraph.ConnectedComponent.eq]
                exact (show inputs.current.object.graph.Adj vertex.1 neighbor from
                  adjacent).reachable.symm.trans (by
                    simpa only [support, Finset.mem_filter,
                      inputs.current.object.mem_vertexFinset, true_and,
                      SimpleGraph.ConnectedComponent.eq] using vertex.2)
              have componentMinimumDegree :
                  data.threshold ≤ component.value.minDegree := by
                apply component.value.le_minDegree_of_forall_le_degree data.threshold
                intro vertex
                rw [show component.value.degree vertex =
                    inputs.current.object.degree vertex.1 from
                  inputs.current.object.degree_induce_of_neighborSet_subset
                    support vertex (neighborSubset vertex)]
                exact inputs.current.baseline.trans
                  (inputs.current.object.minDegree_le_degree vertex.1)
              exact (inputs.get (K .noProperBaseline)).down component
                componentMinimumDegree
            have connectedOn :
                Graph.SupportComponents.Connected.ConnectedOn
                  inputs.current.object inputs.current.object.vertexFinset := by
              letI := inputs.current.object.vertices.decEq
              constructor
              · exact ⟨port.1, inputs.current.object.mem_vertexFinset _⟩
              · intro left right _ _
                obtain ⟨walk⟩ := graphConnected.preconnected left right
                let path := walk.toPath
                exact ⟨path, path.isPath, fun vertex _ =>
                  inputs.current.object.mem_vertexFinset vertex⟩
            letI : DecidableEq inputs.current.object.Vertex := Classical.decEq _
            have pairCoordinateNonempty
                (pair : Finset
                  (inputs.current.object.Vertex × inputs.current.object.Vertex)) :
                (Graph.DeclaredSignature.Coordinate.support
                  (Graph.FiniteObject.DemandActivation.pairCoordinate pair
                    (((Graph.pairResponseActivation active).pairSupport pair).getD
                      ∅))).Nonempty := by
              have pairSupportSome :=
                Graph.FiniteObject.DemandActivation.pairSupport_isSome_of_connected
                  (Graph.pairResponseActivation active) pair connectedOn
              obtain ⟨pairSupport, pairSupportEq⟩ :=
                Option.isSome_iff_exists.mp pairSupportSome
              have pairSupportNonempty : pairSupport.Nonempty :=
                (Graph.FiniteObject.DemandActivation.pairSupport_mem_candidates
                  pairSupportEq).2.1
              change (((Graph.pairResponseActivation active).pairSupport pair).getD
                ∅).Nonempty
              rw [pairSupportEq]
              exact pairSupportNonempty
            let presentation : inputs.current.object.CarrierPresentation
                inputs.current.object.PairCoordinate
                (inputs.current.object.Vertex ×
                  inputs.current.object.Vertex) := {
              coordinateSupport := by
                letI := inputs.current.object.vertices.decEq
                exact Graph.DeclaredSignature.Coordinate.support
              chordEnds := Graph.pairResponseChordEnds active
              chordPort := id }
            have carried : ∀ pair ∈
                inputs.current.object.portPairSchedule data.threshold,
                ∀ blocker ∈ activation.blockers pair,
                  (Graph.FiniteObject.Blocker.carrier inputs.current.object
                    data.threshold presentation.coordinateSupport
                    presentation.chordPort blocker).isSome := by
              classical
              intro pair _pairMem blocker blockerMem
              cases blocker with
              | sharedDeclaredSupport item =>
                  cases item <;> rfl
              | sharedReturnSupport item =>
                  cases item <;> rfl
              | sharedLocalBuffer _ => rfl
              | boundaryProfile coordinate =>
                  have coordinateMem :
                      coordinate ∈ activation.profileObstructions pair := by
                    simpa [Graph.FiniteObject.DemandActivation.blockers] using
                      blockerMem
                  have coordinateEq : coordinate =
                      Graph.FiniteObject.DemandActivation.pairCoordinate pair
                        (((Graph.pairResponseActivation active).pairSupport pair).getD
                          ∅) := by
                    simp only [activation, Graph.recordSparsePairDEBlockers] at coordinateMem
                    split at coordinateMem
                    · simpa using coordinateMem
                    · simp at coordinateMem
                  subst coordinate
                  rw [Graph.FiniteObject.Blocker.carrier]
                  simp only [Option.isSome_map, List.isSome_head?]
                  exact List.ne_nil_of_mem (by
                    simpa [presentation] using
                      (pairCoordinateNonempty pair).choose_spec)
              | targetResponse coordinate =>
                  have coordinateMem :
                      coordinate ∈ activation.responseObstructions pair := by
                    simpa [Graph.FiniteObject.DemandActivation.blockers] using
                      blockerMem
                  have coordinateEq : coordinate =
                      Graph.FiniteObject.DemandActivation.pairCoordinate pair
                        (((Graph.pairResponseActivation active).pairSupport pair).getD
                          ∅) := by
                    simp only [activation, Graph.recordSparsePairDEBlockers] at coordinateMem
                    split at coordinateMem
                    · simpa using coordinateMem
                    · simp at coordinateMem
                  subst coordinate
                  rw [Graph.FiniteObject.Blocker.carrier]
                  simp only [Option.isSome_map, List.isSome_head?]
                  exact List.ne_nil_of_mem (by
                    simpa [presentation] using
                      (pairCoordinateNonempty pair).choose_spec)
              | arithmeticChordSet chords =>
                  have chordMem :
                      chords ∈ activation.chordObstructions pair := by
                    simpa [Graph.FiniteObject.DemandActivation.blockers] using
                      blockerMem
                  change chords ∈ (Graph.pairResponseActivation active).chordObstructions pair at chordMem
                  simp only [Graph.pairResponseActivation] at chordMem
                  have chordFacts := List.mem_filter.mp chordMem
                  have orderedFacts := List.mem_filter.mp chordFacts.1
                  have powersetMember : chords ∈
                      (inputs.current.object.excessPorts data.threshold).powerset :=
                    of_decide_eq_true orderedFacts.2
                  have chordSubset :
                      chords ⊆ inputs.current.object.excessPorts data.threshold :=
                    Finset.mem_powerset.mp powersetMember
                  have obstruction :
                      Graph.SparsePairSuppressionChordObstruction active pair
                        chords :=
                    of_decide_eq_true chordFacts.2
                  obtain ⟨_pairSubset, family, suppressionCertificate,
                      _familyPorts, _chordEnds, usedChords⟩ := obstruction
                  have avoids : ¬ Graph.HasCycleWithLength data.LengthOK
                      inputs.current.object := by
                    intro cycle
                    exact active.survives (.dyadic cycle)
                  have usedNonempty :=
                    family.usedChords_nonempty_of_avoids avoids
                      suppressionCertificate
                  have chordsNonempty : chords.Nonempty := by
                    let portOf := fun index : family.Index =>
                      ((family.configuration index).center,
                        (family.configuration index).vertex)
                    have imageNonempty :
                        (family.usedChords suppressionCertificate.walk).image
                          portOf |>.Nonempty :=
                      usedNonempty.image portOf
                    have imageEq :
                        (family.usedChords suppressionCertificate.walk).image
                          portOf = chords := by
                      simpa only [portOf] using usedChords
                    rw [← imageEq]
                    exact imageNonempty
                  have chosenInIntersection : chordsNonempty.choose ∈
                      (chords.image presentation.chordPort) ∩
                        inputs.current.object.excessPorts data.threshold := by
                    refine Finset.mem_inter.mpr ⟨?_,
                      chordSubset chordsNonempty.choose_spec⟩
                    simpa [presentation] using
                      (Finset.mem_image_of_mem presentation.chordPort
                        chordsNonempty.choose_spec)
                  rw [Graph.FiniteObject.Blocker.carrier]
                  simp only [Option.isSome_map, List.isSome_head?]
                  exact List.ne_nil_of_mem (by
                    simpa using chosenInIntersection)
            have baseline : ∀ vertex : inputs.current.object.Vertex,
                data.threshold ≤ inputs.current.object.degree vertex :=
              fun vertex => le_trans inputs.current.baseline
                (inputs.current.object.minDegree_le_degree vertex)
            have handshake : data.threshold * inputs.current.object.vertexCount ≤
                2 * inputs.current.object.edgeCount :=
              Graph.baselineDegree_mul_vertexCount_le_two_mul_edgeCount
                inputs.current.object data.threshold baseline
            let accounting : Graph.CapacityPresentation inputs.current.object
                data.threshold data.windowOrder := {
              activation := activation
              carrierComplete := carried
              packing := packing
              packingValid := valid
              packingMaximal := maximal }
            have concrete : Graph.FiniteObject.ConcreteCapacityTokenLedgerStatement
                inputs.current.object data.threshold data.windowOrder activation
                presentation packing := by
              refine ⟨inputs.current.object.card_capacityTokens_add_internalMass
                  valid baseline, ?_, ?_, ?_, ?_, ?_⟩
              · exact inputs.current.object.card_capacityTokens_le valid baseline
                  data.three_le_threshold handshake envelope data.windowOrder_pos
                  data.joinSlack
              · intro pair token charged
                exact Graph.FiniteObject.capacityCharge_mem_capacityTokens
                  activation presentation data.threshold packing charged
              · rw [← Graph.FiniteObject.capacityTokenOrder_toFinset
                    (object := inputs.current.object) (threshold := data.threshold)
                    (packing := packing)]
                exact Graph.FiniteObject.card_chargedPairs_eq_sum_load
                  activation presentation data.threshold packing
              · exact ⟨carried,
                  Graph.FiniteObject.chargedPairs_eq_blockedPairs
                    activation presentation data.threshold packing carried⟩
              · have rolePartition : ∀ token :
                    Graph.FiniteObject.CapacityToken inputs.current.object,
                    (Graph.FiniteObject.tokenFibre activation presentation
                      data.threshold packing token).card =
                      ∑ role : Graph.SameTokenBlockerRoles.Role,
                        (Graph.FiniteObject.tokenRoleFibre activation presentation
                          data.threshold packing token role).card :=
                    fun token =>
                      Graph.FiniteObject.card_tokenFibre_eq_sum_roleFibre
                        activation presentation data.threshold packing token
                refine ⟨rolePartition, ?_, ?_⟩
                · rw [← Graph.FiniteObject.chargedPairs_eq_blockedPairs
                      activation presentation data.threshold packing carried]
                  rw [← Graph.FiniteObject.capacityTokenOrder_toFinset
                    (object := inputs.current.object) (threshold := data.threshold)
                    (packing := packing)]
                  rw [Graph.FiniteObject.card_chargedPairs_eq_sum_load
                    activation presentation data.threshold packing]
                  apply Finset.sum_congr rfl
                  intro token _tokenMem
                  exact rolePartition token
                · intro token
                  exact ⟨Graph.FiniteObject.tokenFibre_subset activation presentation
                      data.threshold packing token,
                    fun pair member =>
                      Graph.FiniteObject.card_of_mem_tokenFibre activation presentation
                        data.threshold packing member,
                    Graph.FiniteObject.card_tokenFibre_eq_pairMultiplicity activation
                      presentation data.threshold packing token⟩
            refine ⟨active, accounting, ?_,
              inputs.current.object.card_primitiveCarrier baseline,
              inputs.current.object.card_primitiveCarrier_le baseline
                data.three_le_threshold handshake envelope, ?_, connectedOn⟩
            · rfl
            change Graph.FiniteObject.ConcreteCapacityTokenLedgerStatement
              inputs.current.object data.threshold data.windowOrder activation
                presentation packing
            exact concrete))
        .nil)

end Hypostructure.Graph.Strategy.Spine
