import Hypostructure.Graph.Strategy.SpineRows
import Hypostructure.Graph.ObjectCapacityLedger
import Hypostructure.Graph.SameTokenBottleneckRouting
import Hypostructure.Graph.NamedSurplusExits
import Hypostructure.Graph.SparseUpperEnvelope

/-!
# The sparse surplus branch: the three homogeneous-bottleneck rows

Nodes `[137]`--`[143]` and `[144]`, as atomic Strategies over the entry spine's
residual domain.

Each row reads node `[130]`'s committed pair count `|Π(𝒜₀)| = C(σ(G),2)` by
exact key, and commits one of the four statements
`Graph.CapacityTokenLedger` writes out: the role-fibre partition, the coupled
high-load display with its forced role-homogeneous pattern, the three geometric
class audits, and `cor:homogeneous-same-token-caps-close`.  The statements are
named there rather than here so that the residual domain's value schema and the
row that proves it are the same text.

The ledger is not rebuilt.  `Π_blk`, `Π_free` and `ℓ_cap(t)` are
`Graph.CanonicalFibreLedger`'s `assigned`, `unassigned` and `multiplicity` --
the single implementation nodes `[130]`--`[136]` already use -- and
`lem:token-ledger-no-overcount` is that module's
`card_assigned_eq_sum_multiplicity`, read rather than restated.  A pair is a
two-element `Finset` of selected ports, which is
`FiniteObject.portPairSchedule`'s own representation.

## Where the data comes from

Nothing is quantified over a presentation nobody built.  Node `[136]` commits
`Graph.ObjectCapacityLedger` -- the token universe `𝔗_cap`, the assignment
`Θ_cap`, node `[130]`'s pair count, `lem:capacity-token-supply`'s
`|𝔗_cap| ≤ 8n + σ(G)` and the free-side entropy sandwich -- and node `[137]`
reads that commitment by exact key.  The lower-bound package ordering of
`def:spine-lower-bound-deficits` is read from node `[129]`, and node `[130]`'s
pair count is read from the canonical pair ledger.  Every key in a manifest is
consumed by the executor, and every production is derived from what was read.
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}
variable [FactSystem (Input BranchState Presentation presentation data)]

/-! ## Nodes `[137]`--`[143]`: the coupled homogeneous fibre pressure

`lem:capacity-token-high-load` is the coupled single-graph high-load test:

  `C(s,2) ≤ E_spine(n) + ((1/2)σ(G) + 1)log₂ n + L_max|𝔗_cap|`,

proved from the canonical ledger's own split `Π(𝒜₀) = Π_free ⊔ Π_blk`, the
entropy sandwich on the free part, and `lem:token-ledger-no-overcount` on the
charged part.  All three token classes are evaluated against the one committed
ledger, which is what makes the test coupled.

The three productions are the three things the manuscript reads off that ledger
before it branches.

* `roleFibrePartition` is `lem:exact-surplus-pair-charge-partition` with
  `thm:sharp-classwise-homogeneous-token-budget` (a)--(c) and
  `thm:sharp-surplus-overload-audit` (b)--(c): the exact decomposition of
  `C(𝒜₀,2)` into the free side and the class/token/role fibres, the class and
  subtype splits of `|Π_blk| ≥ N_*(G)`, the supplies, and the classwise cap.
* `fibrePressure` is `lem:capacity-token-high-load` with
  `cor:forced-homogeneous-same-token-scale`,
  `thm:sharp-classwise-homogeneous-token-budget` (e) and
  `thm:sharp-surplus-overload-audit` (d), stated *at the object's own* capacity
  ledger.  It is existential in that ledger, so it is unprovable without node
  `[136]`'s commitment, which the executor reads and spends.
* `spineSurplusEstimate` is `cor:spine-lower-bound-surplus-estimates`: node
  `[129]`'s ordering of the three lower-bound packages, composed with node
  `[130]`'s pair count, turns a package bound on the pair schedule into the
  surplus estimate the near-cubic route carries.

Both reads are spent: the pair count converts the package bound and the token
ledger witnesses the high-load display. -/
@[reducible] noncomputable def coupledFibrePressureRow
    (canonicalPairLedger capacityTokenLedger
      roleFibrePartition fibrePressure :
      FactKey (Input BranchState Presentation presentation data))
    (pairNeToken : canonicalPairLedger ≠ capacityTokenLedger)
    (partitionNePressure : roleFibrePartition ≠ fibrePressure)
    (pairCountOf : (input : Input BranchState Presentation presentation data) →
      canonicalPairLedger.At input →
      (input.object.portPairSchedule data.threshold).card =
        (input.object.degreeSurplus data.threshold).choose 2)
    (tokenLedgerOf : (input : Input BranchState Presentation presentation data) →
      capacityTokenLedger.At input →
      ∀ declared : Graph.CapacityPresentation input.object data.windowOrder,
        Nonempty (Graph.ObjectCapacityLedger input.object data.threshold
          data.windowOrder declared))
    (encodePartition : (input : Input BranchState Presentation presentation data) →
      Graph.RoleFibrePartitionStatement input.object data.threshold
        data.windowOrder →
      roleFibrePartition.At input)
    (encodePressure : (input : Input BranchState Presentation presentation data) →
      Graph.FibrePressureStatement input.object data.threshold
        data.windowOrder →
      fibrePressure.At input) :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.coupledFibrePressure
    { Requires := [canonicalPairLedger, capacityTokenLedger]
      Produces := [roleFibrePartition, fibrePressure]
      requiresUnique := by simp [pairNeToken]
      producesUnique := by simp [partitionNePressure]
      producesNonempty := by simp }
    (fun inputs =>
      let object := inputs.current.object
      -- Node `[130]`'s count and node `[136]`'s ledger.
      let _pairCount := pairCountOf inputs.current (inputs.get canonicalPairLedger)
      let existing := tokenLedgerOf inputs.current (inputs.get capacityTokenLedger)
      .cons (key := roleFibrePartition)
        (encodePartition inputs.current
          (Graph.roleFibrePartitionStatement object data.threshold
            data.windowOrder))
        (.cons (key := fibrePressure)
          (encodePressure inputs.current
            (Graph.fibrePressureStatement object data.threshold data.windowOrder
              existing))
          .nil))

/-! ## Node `[137]`: the branch

`prop:single-graph-sparse-pressure-routing` is exhaustive: either every capacity
ledger of the object respects the geometric caps of
`thm:homogeneous-overload-geometric-closure` -- and then
`cor:coupled-single-graph-overload-budget` and
`cor:numerical-single-graph-budget` give `σ(G) ≤ R_L(n)`, the near-cubic route
`[138]` -- or `D_all > 0`, and
`cor:quantified-homogeneous-class-overload` forces a role-homogeneous same-token
matching or star whose token class selects `[140]`, `[142]` or `[143]`.

This is a `Decision`, not a fact-only row: the arm not taken is absent from the
taken branch's key index, so the geometric audits cannot read the near-cubic
bound and the near-cubic route cannot read an overload that did not occur.  The
test is `SparsePressureCapped` itself, a property of the object; no graph
remains at `[137]` because the two arms are the two cases of the excluded middle
on it. -/
noncomputable def sparsePressureDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous :
      ExactLedger (Input BranchState Presentation presentation data)
        current known)
    (sparsePressureNearCubic sparsePressureOverload :
      FactKey (Input BranchState Presentation presentation data))
    (encodeNearCubic :
      Graph.SparsePressureCapped current.object data.threshold
        data.windowOrder →
      sparsePressureNearCubic.At current)
    (encodeOverload :
      Graph.SparsePressureOverloadStatement current.object data.threshold
        data.windowOrder →
      sparsePressureOverload.At current)
    (nearCubicFresh : sparsePressureNearCubic ∉ known)
    (overloadFresh : sparsePressureOverload ∉ known) :
    Decision sparsePressureNearCubic sparsePressureOverload previous := by
  classical
  refine Decision.run previous sparsePressureNearCubic sparsePressureOverload
    `Hypostructure.Graph.Strategy.Spine.sparsePressureRouting ?_ nearCubicFresh
    overloadFresh
  exact
    if capped : Graph.SparsePressureCapped current.object data.threshold
        data.windowOrder then
      .inl (encodeNearCubic capped)
    else
      .inr (encodeOverload
        ((Graph.sparsePressureRouting current.object data.threshold
          data.windowOrder).resolve_left
          capped))

/-- The one arithmetic bridge used by both near-cubic exits `[138]` and
`[144]`.  All graph-specific data is already inside the certified ledger. -/
theorem certifiedDegreeSurplus_le_spineScale
    (object : Graph.FiniteObject.{u})
    (certified : Σ declared : Graph.CapacityPresentation object data.windowOrder,
      Graph.CertifiedObjectCapacityLedger object data.threshold
        data.windowOrder data.surplusScale declared)
    (sizePos : 0 < object.vertexCount)
    (pressure : object.degreeSurplus data.threshold ≤
      1 + 2 * data.homogeneousCap +
        Nat.sqrt (2 * certified.2.ledger.entropyBudget +
          2 * (data.homogeneousCap * object.capacityTokenSupply data.threshold))) :
    object.degreeSurplus data.threshold ≤
      data.spineScale * Core.ceilSqrt object.vertexCount := by
  have safety : Graph.TokenLoad.quadraticSafetyScale ≤
      2 * (1 + 2 * data.homogeneousCap) +
        (2 * data.surplusScale +
          2 * data.homogeneousCap * (3 * (data.threshold - 1) + 2)) :=
    le_trans data.quadraticSafetyScale_le_twiceAdditive
      (Nat.le_add_right _ _)
  have bound := certified.2.degreeSurplus_le_mul_ceilSqrt sizePos
    data.homogeneousCap safety pressure
  simpa [Data.spineScale, registeredSpineScale, Data.homogeneousCap,
    registeredHomogeneousCap, Data.capacityTokenScale] using bound

/-- Node `[138]`: turn node `[137]`'s capped pressure into the paper's actual
`σ(G) ≤ C_sp⌈√n⌉`, reading the concrete node-`[129]`/`[131]` certified
capacity ledger. -/
@[reducible] noncomputable def spineSurplusEstimateRow
    (sparsePressureNearCubic capacityTokenLedger surplusAbove
      spineSurplusEstimate :
      FactKey (Input BranchState Presentation presentation data))
    (nearNeLedger : sparsePressureNearCubic ≠ capacityTokenLedger)
    (nearNeAbove : sparsePressureNearCubic ≠ surplusAbove)
    (ledgerNeAbove : capacityTokenLedger ≠ surplusAbove)
    (nearOf : (input : Input BranchState Presentation presentation data) →
      sparsePressureNearCubic.At input →
      Graph.SparsePressureCapped input.object data.threshold data.windowOrder)
    (certifiedOf : (input : Input BranchState Presentation presentation data) →
      capacityTokenLedger.At input →
      Nonempty (Σ declared : Graph.CapacityPresentation input.object data.windowOrder,
        Graph.CertifiedObjectCapacityLedger input.object data.threshold
          data.windowOrder data.surplusScale declared))
    (aboveOf : (input : Input BranchState Presentation presentation data) →
      surplusAbove.At input →
      data.surplusThreshold input.object.vertexCount <
        input.object.degreeSurplus data.threshold)
    (encode : (input : Input BranchState Presentation presentation data) →
      input.object.degreeSurplus data.threshold ≤
        data.spineScale * Core.ceilSqrt input.object.vertexCount →
      spineSurplusEstimate.At input) :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.spineSurplusEstimate
    { Requires := [sparsePressureNearCubic, capacityTokenLedger, surplusAbove]
      Produces := [spineSurplusEstimate]
      requiresUnique := by simp [nearNeLedger, nearNeAbove, ledgerNeAbove]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let object := inputs.current.object
      let capped := nearOf inputs.current (inputs.get sparsePressureNearCubic)
      let certified := (certifiedOf inputs.current
        (inputs.get capacityTokenLedger)).some
      let above := aboveOf inputs.current (inputs.get surplusAbove)
      let positive : 0 < object.degreeSurplus data.threshold :=
        Nat.lt_of_le_of_lt (Nat.zero_le _) above
      let sizePos : 0 < object.vertexCount :=
        object.vertexCount_pos_of_degreeSurplus_pos positive
      let pressure := capped certified.1 certified.2.ledger
        (Fintype.card (Graph.SameTokenRoutingGerms.RoutingLabel
          data.BoundaryProfile (Graph.WindowCurvature.Label data.windowOrder)))
      let normalized : object.degreeSurplus data.threshold ≤
          1 + 2 * data.homogeneousCap +
            Nat.sqrt (2 * certified.2.ledger.entropyBudget +
              2 * (data.homogeneousCap *
                object.capacityTokenSupply data.threshold)) := by
        simpa [Graph.CapacityTokenLedger.sparsePressureBound,
          Data.homogeneousCap, registeredHomogeneousCap,
          Graph.SameTokenBlockerRoles.homogeneousTokenCap,
          Graph.SameTokenBlockerRoles.geometricPatternBound,
          Graph.SameTokenRoutingGerms.patternBound,
          Graph.SameTokenRoutingGerms.labelBound] using pressure
      let bound := certifiedDegreeSurplus_le_spineScale object certified
        sizePos normalized
      .cons (key := spineSurplusEstimate) (encode inputs.current bound) .nil)

/-! ## Nodes `[139]` and `[141]`: the class dispatch

`prop:single-graph-sparse-pressure-routing` (b): "according to the class of the
token, `G` is routed to node `[140]`, `[142]`, or `[143]`."  The manuscript draws
that as two binary tests -- `[139]` "token in `𝔗_W`?" and `[141]` "token in
`𝔗_R`?" -- and they are two `Decision`s here for the same reason node `[137]` is
one: the arm not taken is absent from the taken arm's key index, so the
window-incidence audit cannot read a remainder-surplus verdict and neither can
read the other's.

Each test is the excluded middle on a property of the object, so no fact is
consumed to decide it and nothing is assumed to make the split exhaustive.
What the two negative arms are *for* is node `[143]`: `class(t)` has three
values, so failing both tests is the primitive-carrier case, and that is derived
at `[143]` from the two negative facts rather than declared here. -/

/-- **Node `[139]`**: is the overloading token of node `[137]` in `𝔗_W`? -/
noncomputable def windowClassDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous :
      ExactLedger (Input BranchState Presentation presentation data)
        current known)
    (windowClassOverload windowClassAbsent :
      FactKey (Input BranchState Presentation presentation data))
    (encodeOverload :
      Graph.SparsePressureOverloadInClass current.object data.threshold
        data.windowOrder .windowIncidence →
      windowClassOverload.At current)
    (encodeAbsent :
      (¬ Graph.SparsePressureOverloadInClass current.object data.threshold
        data.windowOrder .windowIncidence) →
      windowClassAbsent.At current)
    (overloadFresh : windowClassOverload ∉ known)
    (absentFresh : windowClassAbsent ∉ known) :
    Decision windowClassOverload windowClassAbsent previous := by
  classical
  refine Decision.run previous windowClassOverload windowClassAbsent
    `Hypostructure.Graph.Strategy.Spine.windowClassDichotomy ?_ overloadFresh
    absentFresh
  exact
    if inClass : Graph.SparsePressureOverloadInClass current.object data.threshold
        data.windowOrder .windowIncidence then
      .inl (encodeOverload inClass)
    else
      .inr (encodeAbsent inClass)

/-- **Node `[141]`**: is it in `𝔗_R`? -/
noncomputable def remainderClassDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous :
      ExactLedger (Input BranchState Presentation presentation data)
        current known)
    (remainderClassOverload remainderClassAbsent :
      FactKey (Input BranchState Presentation presentation data))
    (encodeOverload :
      Graph.SparsePressureOverloadInClass current.object data.threshold
        data.windowOrder .remainderSurplus →
      remainderClassOverload.At current)
    (encodeAbsent :
      (¬ Graph.SparsePressureOverloadInClass current.object data.threshold
        data.windowOrder .remainderSurplus) →
      remainderClassAbsent.At current)
    (overloadFresh : remainderClassOverload ∉ known)
    (absentFresh : remainderClassAbsent ∉ known) :
    Decision remainderClassOverload remainderClassAbsent previous := by
  classical
  refine Decision.run previous remainderClassOverload remainderClassAbsent
    `Hypostructure.Graph.Strategy.Spine.remainderClassDichotomy ?_ overloadFresh
    absentFresh
  exact
    if inClass : Graph.SparsePressureOverloadInClass current.object data.threshold
        data.windowOrder .remainderSurplus then
      .inl (encodeOverload inClass)
    else
      .inr (encodeAbsent inClass)

/-! ## Nodes `[140]`, `[142]`, `[143]`: the three geometric class audits

`def:homogeneous-token-charge` fixes what a token may carry without a
role-homogeneous pattern:

  `Cap_hom(L) = Q_st(L−1)(2L−3)`,

"the uniform token load allowed by charging each of the at most `Q_st` role
fibres separately when no role-homogeneous same-token `L`-matching or `L`-star
occurs at that token".  The audit commits its contrapositive at the manuscript's
own fixed cap `L_geom = Q_geom + 1`, where `Q_geom` is the *counted* cardinality
of `def:same-token-routing-germs`' routing-label alphabet, so nothing supplies
the bound as a parameter.

The audit is stated at the object's own `Graph.ObjectCapacityLedger`, which node
`[136]` commits at every declared presentation, so it is a verdict about the
branch's object rather than an implication about a token universe nobody built.
It is committed together with `cor:quantitative-homogeneous-overload`, the
forced pattern scale `K_hom(G) ≥ ψ(N_*(G)/(Q_st(8n+σ(G))))` cleared of division,
which is what makes the audit quantitative.

`Requires := []` is the honest declaration: both productions are theorems about
the object, and an unread key would claim a dependency the executor does not
have.  What places the audit at its class is the DAG -- the arm of `[139]` or
`[141]` it runs on carries that class's verdict -- not a hypothesis inside it. -/
@[reducible] noncomputable def classAuditRow
    (value : Graph.SameTokenBlockerRoles.TokenClass)
    (classAudit quantitativeOverload :
      FactKey (Input BranchState Presentation presentation data))
    (distinct : classAudit ≠ quantitativeOverload)
    (encodeAudit : (input : Input BranchState Presentation presentation data) →
      Graph.ClassAuditStatement input.object data.threshold data.windowOrder
        (Graph.SameTokenRoutingGerms.RoutingLabel data.BoundaryProfile
          (Graph.WindowCurvature.Label data.windowOrder)) value →
      classAudit.At input)
    (encodeScale : (input : Input BranchState Presentation presentation data) →
      Graph.QuantitativeOverloadStatement input.object data.threshold
        data.windowOrder →
      quantitativeOverload.At input) :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.classAudit
    { Requires := []
      Produces := [classAudit, quantitativeOverload]
      requiresUnique := by simp
      producesUnique := by simp [distinct]
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := classAudit)
        (encodeAudit inputs.current
          (Graph.classAuditStatement inputs.current.object data.threshold
            data.windowOrder (Graph.SameTokenRoutingGerms.RoutingLabel data.BoundaryProfile
          (Graph.WindowCurvature.Label data.windowOrder)) value))
        (.cons (key := quantitativeOverload)
          (encodeScale inputs.current
            (Graph.quantitativeOverloadStatement inputs.current.object
              data.threshold data.windowOrder))
          .nil))

/-- **Node `[143]`, the primitive-carrier audit.**

The fall-through case, and the only one of the three that owes a derivation of
its own class verdict.  `class(t)` has three values, so node `[137]`'s overload
together with the two negative arms of `[139]` and `[141]` puts the overloading
token in `𝔗_prim`; all three are read by exact key and all three are spent by
`Graph.overloadClassExhaustive`.  The audit itself and the quantitative scale are
the same two theorems the other two arms commit. -/
@[reducible] noncomputable def primitiveCarrierAuditRow
    (sparsePressureOverload windowClassAbsent remainderClassAbsent
      primitiveClassOverload primitiveCarrierAudit quantitativeOverload :
      FactKey (Input BranchState Presentation presentation data))
    (overloadNeWindow : sparsePressureOverload ≠ windowClassAbsent)
    (overloadNeRemainder : sparsePressureOverload ≠ remainderClassAbsent)
    (windowNeRemainder : windowClassAbsent ≠ remainderClassAbsent)
    (verdictNeAudit : primitiveClassOverload ≠ primitiveCarrierAudit)
    (verdictNeScale : primitiveClassOverload ≠ quantitativeOverload)
    (auditNeScale : primitiveCarrierAudit ≠ quantitativeOverload)
    (overloadOf : (input : Input BranchState Presentation presentation data) →
      sparsePressureOverload.At input →
      Graph.SparsePressureOverloadStatement input.object data.threshold
        data.windowOrder)
    (windowAbsentOf : (input : Input BranchState Presentation presentation data) →
      windowClassAbsent.At input →
      ¬ Graph.SparsePressureOverloadInClass input.object data.threshold
        data.windowOrder .windowIncidence)
    (remainderAbsentOf :
      (input : Input BranchState Presentation presentation data) →
      remainderClassAbsent.At input →
      ¬ Graph.SparsePressureOverloadInClass input.object data.threshold
        data.windowOrder .remainderSurplus)
    (encodeVerdict : (input : Input BranchState Presentation presentation data) →
      Graph.SparsePressureOverloadInClass input.object data.threshold
        data.windowOrder .primitiveCarrier →
      primitiveClassOverload.At input)
    (encodeAudit : (input : Input BranchState Presentation presentation data) →
      Graph.ClassAuditStatement input.object data.threshold data.windowOrder
        (Graph.SameTokenRoutingGerms.RoutingLabel data.BoundaryProfile
          (Graph.WindowCurvature.Label data.windowOrder)) .primitiveCarrier →
      primitiveCarrierAudit.At input)
    (encodeScale : (input : Input BranchState Presentation presentation data) →
      Graph.QuantitativeOverloadStatement input.object data.threshold
        data.windowOrder →
      quantitativeOverload.At input) :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.primitiveCarrierAudit
    { Requires :=
        [sparsePressureOverload, windowClassAbsent, remainderClassAbsent]
      Produces :=
        [primitiveClassOverload, primitiveCarrierAudit, quantitativeOverload]
      requiresUnique := by
        simp [overloadNeWindow, overloadNeRemainder, windowNeRemainder]
      producesUnique := by
        simp [verdictNeAudit, verdictNeScale, auditNeScale]
      producesNonempty := by simp }
    (fun inputs =>
      let object := inputs.current.object
      let overload := overloadOf inputs.current (inputs.get sparsePressureOverload)
      let windowAbsent :=
        windowAbsentOf inputs.current (inputs.get windowClassAbsent)
      let remainderAbsent :=
        remainderAbsentOf inputs.current (inputs.get remainderClassAbsent)
      .cons (key := primitiveClassOverload)
        (encodeVerdict inputs.current
          (Graph.overloadClassExhaustive object data.threshold data.windowOrder
            overload windowAbsent remainderAbsent))
        (.cons (key := primitiveCarrierAudit)
          (encodeAudit inputs.current
            (Graph.classAuditStatement object data.threshold data.windowOrder
              (Graph.SameTokenRoutingGerms.RoutingLabel data.BoundaryProfile
          (Graph.WindowCurvature.Label data.windowOrder)) .primitiveCarrier))
          (.cons (key := quantitativeOverload)
            (encodeScale inputs.current
              (Graph.quantitativeOverloadStatement object data.threshold
                data.windowOrder))
            .nil)))

/-! ## Node `[144]`: the homogeneous bottleneck, and the close of the branch

`thm:homogeneous-overload-geometric-closure` has two assertions.  The first is
`lem:same-token-bottleneck-routing`: every role-homogeneous same-token
`L_geom`-matching or `L_geom`-star realizes a sparse surplus exit or a decorated
Type B handoff fan envelope.  The second is that on the subbranch where neither
survives, the three fixed caps `L_W = L_R = L_P = L_geom` hold, and then
`cor:homogeneous-same-token-caps-close` gives `σ(G) = O(√n)` and
`lem:sparse-slack-surplus` turns that into `m = (3/2)n + O(√n)`.

`prop:nonnear-cubic-sharp-overload-routing` is the outcome: *"(a) `G` satisfies
the near-cubic spine estimate; (b) a sparse surplus exit occurs; or (c) a
role-homogeneous same-token bottleneck produces decorated Type B fan data and is
routed to the Type B fan ledger."*

That is a branch, and it is one here.  `homogeneousCapsDichotomy` decides the
subbranch hypothesis itself — a property of the object, so the split is the
excluded middle and nothing is assumed to make it exhaustive.  Its caps arm runs
`homogeneousBottleneckRow`, which closes the branch with (a).  Its bottleneck
arm carries the pattern, and `Graph.SameTokenRoutingGerms.bottleneckRouting`
reads that pattern's separated routing germs as (b) or (c): absorbed at the
first separator is the manuscript's quotient, compression and delocalization
exits, and surviving gives `d_G(z) ≥ 4` and admissible decorated Type B fan
data.  Splitting the bottleneck arm further into (b) and (c) needs the germs of
`Z(π;t,r)` themselves, which are declared data of
`def:declared-coordinate-signature` and not built by this branch, so the arm
carries the bottleneck and the routing lemma is what the Type B ledger reads it
with. -/

/-- **Node `[144]`'s test**: do the fixed homogeneous caps hold? -/
noncomputable def homogeneousCapsDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous :
      ExactLedger (Input BranchState Presentation presentation data)
        current known)
    (homogeneousCapsHold homogeneousBottleneckPattern :
      FactKey (Input BranchState Presentation presentation data))
    (encodeCaps :
      Graph.HomogeneousCapsHold current.object data.threshold data.windowOrder
        (Graph.SameTokenRoutingGerms.RoutingLabel data.BoundaryProfile
          (Graph.WindowCurvature.Label data.windowOrder)) →
      homogeneousCapsHold.At current)
    (encodePattern :
      (¬ Graph.HomogeneousCapsHold current.object data.threshold
        data.windowOrder (Graph.SameTokenRoutingGerms.RoutingLabel data.BoundaryProfile
          (Graph.WindowCurvature.Label data.windowOrder))) →
      homogeneousBottleneckPattern.At current)
    (capsFresh : homogeneousCapsHold ∉ known)
    (patternFresh : homogeneousBottleneckPattern ∉ known) :
    Decision homogeneousCapsHold homogeneousBottleneckPattern previous := by
  classical
  refine Decision.run previous homogeneousCapsHold homogeneousBottleneckPattern
    `Hypostructure.Graph.Strategy.Spine.homogeneousCapsRouting ?_ capsFresh
    patternFresh
  exact
    if caps : Graph.HomogeneousCapsHold current.object data.threshold
        data.windowOrder (Graph.SameTokenRoutingGerms.RoutingLabel data.BoundaryProfile
          (Graph.WindowCurvature.Label data.windowOrder)) then
      .inl (encodeCaps caps)
    else
      -- The bottleneck arm carries `lem:same-token-bottleneck-routing` at it:
      -- the pattern, and the exit-or-Type-B reading of its routed germs.
      .inr (encodePattern caps)

/-- **Node `[144]`, the near-cubic close.**

`cor:homogeneous-same-token-caps-close` at the object's own capacity-token
ledger.  Both reads are spent: the caps arm's own fact discharges clauses (a),
(b), (c) — they are *facts a predecessor established*, not hypotheses of a
committed implication — and node `[126]`'s `lem:sparse-slack-surplus` turns the
surplus bound into the edge-count half `m = (3/2)n + O(√n)`.

`M₀ = Cap_hom(L_geom)` is the counted routing-label alphabet's own cap charge
and the token supply is `lem:capacity-token-supply`'s, carried by the ledger, so
neither is a parameter of the committed statement. -/
@[reducible] noncomputable def homogeneousBottleneckRow
    (homogeneousCapsHold sparseSlackSurplus homogeneousBottleneck :
      FactKey (Input BranchState Presentation presentation data))
    (capsNeSlack : homogeneousCapsHold ≠ sparseSlackSurplus)
    (capsOf : (input : Input BranchState Presentation presentation data) →
      homogeneousCapsHold.At input →
      Graph.HomogeneousCapsHold input.object data.threshold data.windowOrder
        (Graph.SameTokenRoutingGerms.RoutingLabel data.BoundaryProfile
          (Graph.WindowCurvature.Label data.windowOrder)))
    (slackOf : (input : Input BranchState Presentation presentation data) →
      sparseSlackSurplus.At input →
      2 * input.object.edgeCount =
        data.threshold * input.object.vertexCount +
          input.object.degreeSurplus data.threshold)
    (encode : (input : Input BranchState Presentation presentation data) →
      Graph.HomogeneousCapsCloseStatement input.object data.threshold
        data.windowOrder (Graph.SameTokenRoutingGerms.RoutingLabel data.BoundaryProfile
          (Graph.WindowCurvature.Label data.windowOrder)) →
      homogeneousBottleneck.At input) :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.homogeneousBottleneck
    { Requires := [homogeneousCapsHold, sparseSlackSurplus]
      Produces := [homogeneousBottleneck]
      requiresUnique := by simp [capsNeSlack]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let caps := capsOf inputs.current (inputs.get homogeneousCapsHold)
      let slack := slackOf inputs.current (inputs.get sparseSlackSurplus)
      .cons (key := homogeneousBottleneck)
        (encode inputs.current
          (Graph.homogeneousCapsCloseStatement inputs.current.object caps slack))
        .nil)

/-- Node `[144]` spends its concrete cap-close pressure against the same
certified node-`[129]`/`[131]` ledger and commits `σ(G) ≤ C_sp⌈√n⌉`. -/
@[reducible] noncomputable def homogeneousSpineSurplusEstimateRow
    (homogeneousBottleneck capacityTokenLedger surplusAbove
      spineSurplusEstimate :
      FactKey (Input BranchState Presentation presentation data))
    (closeNeLedger : homogeneousBottleneck ≠ capacityTokenLedger)
    (closeNeAbove : homogeneousBottleneck ≠ surplusAbove)
    (ledgerNeAbove : capacityTokenLedger ≠ surplusAbove)
    (closeOf : (input : Input BranchState Presentation presentation data) →
      homogeneousBottleneck.At input →
      Graph.HomogeneousCapsCloseStatement input.object data.threshold
        data.windowOrder (Graph.SameTokenRoutingGerms.RoutingLabel
          data.BoundaryProfile (Graph.WindowCurvature.Label data.windowOrder)))
    (certifiedOf : (input : Input BranchState Presentation presentation data) →
      capacityTokenLedger.At input →
      Nonempty (Σ declared : Graph.CapacityPresentation input.object data.windowOrder,
        Graph.CertifiedObjectCapacityLedger input.object data.threshold
          data.windowOrder data.surplusScale declared))
    (aboveOf : (input : Input BranchState Presentation presentation data) →
      surplusAbove.At input →
      data.surplusThreshold input.object.vertexCount <
        input.object.degreeSurplus data.threshold)
    (encode : (input : Input BranchState Presentation presentation data) →
      input.object.degreeSurplus data.threshold ≤
        data.spineScale * Core.ceilSqrt input.object.vertexCount →
      spineSurplusEstimate.At input) :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.homogeneousSpineSurplusEstimate
    { Requires := [homogeneousBottleneck, capacityTokenLedger, surplusAbove]
      Produces := [spineSurplusEstimate]
      requiresUnique := by simp [closeNeLedger, closeNeAbove, ledgerNeAbove]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let object := inputs.current.object
      let close := closeOf inputs.current (inputs.get homogeneousBottleneck)
      let certified := (certifiedOf inputs.current
        (inputs.get capacityTokenLedger)).some
      let above := aboveOf inputs.current (inputs.get surplusAbove)
      let sizePos := object.vertexCount_pos_of_degreeSurplus_pos
        (Nat.lt_of_le_of_lt (Nat.zero_le _) above)
      let pressure := (close certified.1 certified.2.ledger).2.2.1
      .cons (key := spineSurplusEstimate)
        (encode inputs.current
          (certifiedDegreeSurplus_le_spineScale object certified sizePos pressure))
        .nil)

/-- **Node `[144]`, the bottleneck arm's own fact.**

`thm:homogeneous-overload-geometric-closure`'s **first** assertion, which is
`lem:same-token-bottleneck-routing` at every declared routed bottleneck of the
object: the identification at the first separator is absorbed -- the quotient,
compression and delocalization readings of `def:named-surplus-exits` -- or the
separator survives, `d_G(z) ≥ 4`, and its separated tails are admissible
decorated Type B handoff fan data.

Both reads are spent and neither is assumed.  The node-`[1]`--`[4]` selection
entry supplies the object's own avoidance, which is the envelope's
`dyadicSafe`; and node `[11]`--`[14]`'s `cor:uncompressible` entry supplies the
hereditary uncompressibility the admissibility clause asks for -- *at the
ledger's own predicate*, so nothing is re-derived and nothing is parameterised
into triviality. -/
@[reducible] noncomputable def bottleneckRoutingRow
    (selection uncompressible sparseSurplusSurvivor bottleneckRouting :
      FactKey (Input BranchState Presentation presentation data))
    (distinct : selection ≠ uncompressible)
    (selectionNeSurvivor : selection ≠ sparseSurplusSurvivor)
    (uncompressibleNeSurvivor : uncompressible ≠ sparseSurplusSurvivor)
    (survivesOf : (input : Input BranchState Presentation presentation data) →
      sparseSurplusSurvivor.At input →
      Graph.SurvivesSparseExits (Graph.MinimumDegreeAtLeast data.threshold)
        (Graph.HasCycleWithLength data.LengthOK) data.LengthOK input.object)
    (avoidsOf : (input : Input BranchState Presentation presentation data) →
      selection.At input →
      ¬ Graph.HasCycleWithLength data.LengthOK input.object)
    (uncompressibleOf :
      (input : Input BranchState Presentation presentation data) →
      uncompressible.At input →
      ∀ piece : Finset input.object.Vertex,
        ¬ Graph.Strategy.InterfaceReplacement.CompressibleSupport
          (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) input.object piece)
    (encode : (input : Input BranchState Presentation presentation data) →
      (Graph.BottleneckRoutingStatement input.object
          (Graph.MinimumDegreeAtLeast data.threshold) data.LengthOK
          data.windowOrder ∧
        Graph.TypeBHandoffStatement input.object
          (Graph.MinimumDegreeAtLeast data.threshold) data.LengthOK
          data.windowOrder) →
      bottleneckRouting.At input) :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.bottleneckRouting
    { Requires := [selection, uncompressible, sparseSurplusSurvivor]
      Produces := [bottleneckRouting]
      requiresUnique := by
        simp [distinct, selectionNeSurvivor, uncompressibleNeSurvivor]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let avoids := avoidsOf inputs.current (inputs.get selection)
      let uncompressed := uncompressibleOf inputs.current
        (inputs.get uncompressible)
      let survives := survivesOf inputs.current (inputs.get sparseSurplusSurvivor)
      .cons (key := bottleneckRouting)
        (encode inputs.current
          ⟨Graph.bottleneckRoutingStatement inputs.current.object avoids
            uncompressed,
            Graph.typeBHandoffStatement inputs.current.object survives avoids
              uncompressed⟩)
        .nil)

/-! ## Node `[125]`: the survivor of the sparse surplus exits

`def:named-surplus-exits`' standing hypothesis, *derived*.

The manuscript's branch is entered by a graph that "survives the sparse surplus
exits", and every later node of the block reads that hypothesis.  It is not an
assumption here: a selected minimal counterexample survives, and every clause is
refuted by a fact the branch already carries.

* (a) the direct dyadic contradiction is the selection's own avoidance;
* (b) a target-defective quotient is refuted by
  `DeclaredQuotient.targetComplete_of_identified` -- an admissible quotient's
  identified pieces share a boundary-degree profile and are context-equivalent;
* (c) a *target-complete* compression is `CompressibleSupport`, and its absence
  is exactly node `[11]`--`[14]`'s `cor:uncompressible` entry, read by key
  rather than re-derived;
* (d) a strictly smaller representative meeting the baseline has an accepted
  cycle by minimality, and the delocalization coordinate transfers it back;
* (e) `lem:suppressed-family-critical-cycle` expands an accepted cycle of
  `G/𝒬` into a simple cycle of `G` of length `2^j + |𝒮|`, so accepting that
  length would be an accepted cycle of `G`.

The manifest lists the two keys the executor reads and nothing else. -/
@[reducible] noncomputable def sparseSurplusSurvivorRow
    (selection uncompressible sparseSurplusSurvivor :
      FactKey (Input BranchState Presentation presentation data))
    (distinctRequired : selection ≠ uncompressible)
    (survivorFresh : sparseSurplusSurvivor ≠ selection)
    (avoidsOf : (input : Input BranchState Presentation presentation data) →
      selection.At input →
      ¬ Graph.HasCycleWithLength data.LengthOK input.object)
    (minimalOf : (input : Input BranchState Presentation presentation data) →
      selection.At input →
      ∀ smaller : Graph.FiniteObject.{u},
        (progress BranchState Presentation presentation data).Smaller
          smaller input.object →
        Graph.MinimumDegreeAtLeast data.threshold smaller →
        Graph.HasCycleWithLength data.LengthOK smaller)
    (uncompressibleOf : (input : Input BranchState Presentation presentation data) →
      uncompressible.At input →
      ∀ support : Finset input.object.Vertex,
        ¬ Graph.Strategy.InterfaceReplacement.CompressibleSupport
          (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) input.object support)
    (encode : (input : Input BranchState Presentation presentation data) →
      (Graph.SurvivesSparseExits (Graph.MinimumDegreeAtLeast data.threshold)
            (Graph.HasCycleWithLength data.LengthOK) data.LengthOK
            input.object ∧
        ∀ support : Finset input.object.Vertex,
          ¬ Graph.Strategy.InterfaceReplacement.ReplacementSupport
            (Graph.MinimumDegreeAtLeast data.threshold)
            (Graph.HasCycleWithLength data.LengthOK) input.object support) →
      sparseSurplusSurvivor.At input) :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.sparseSurplusSurvivor
    { Requires := [selection, uncompressible]
      Produces := [sparseSurplusSurvivor]
      requiresUnique := by simp [distinctRequired]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let fact := inputs.get selection
      .cons (key := sparseSurplusSurvivor)
        (encode inputs.current
          ⟨Graph.survives_of_selection (avoidsOf inputs.current fact)
              (minimalOf inputs.current fact)
              (uncompressibleOf inputs.current (inputs.get uncompressible)),
            -- `lem:replacement` at the same selection: a proper-support
            -- replacement is the global barrier reading node `[45]`--`[46]`
            -- refutes, and its two halves are the selection's own.
            fun _support replacement =>
              not_globalBarrierReading (BranchState := BranchState)
                (Presentation := Presentation) (presentation := presentation)
                (data := data) inputs.current.baseline
                inputs.current.branchState (avoidsOf inputs.current fact)
                (minimalOf inputs.current fact) (Or.inl replacement)⟩)
        .nil)

/-! ## Node `[125]`, continued: the active surplus family

`def:active-surplus-demands` and `lem:surviving-active-family`.

> An *active surplus demand* is a selected surplus port `p ∈ 𝒫_exc` equipped
> with the canonical data `T(p)`, `R_p`, `Γ(p)`, and not already removed by a
> sparse surplus exit.
>
> If `G` survives the sparse surplus exits, then `𝒜₀ := 𝒫_exc` is a finite
> family of active surplus demands and `|𝒜₀| = σ(G)`.

Exit-freeness is a property of the object rather than of one port: the
manuscript's "survives" clause quantifies over every selected demand, every
selected pair, and every baseline spine coordinate at once.

Every input is a fact the branch already carries -- the survivor of `[125]`, the
count of `[127]`, and clause (b) of `[128]` -- so this row proves nothing again;
it commits the family those three facts *are*. -/
@[reducible] noncomputable def activeSurplusDemandsRow
    (sparseSurplusSurvivor activeSurplusFamily sparsePortActivation
      activeSurplusDemands :
      FactKey (Input BranchState Presentation presentation data))
    (survivorNeFamily : sparseSurplusSurvivor ≠ activeSurplusFamily)
    (survivorNeActivation : sparseSurplusSurvivor ≠ sparsePortActivation)
    (familyNeActivation : activeSurplusFamily ≠ sparsePortActivation)
    (demandsFresh : activeSurplusDemands ≠ sparseSurplusSurvivor)
    (survivesOf : (input : Input BranchState Presentation presentation data) →
      sparseSurplusSurvivor.At input →
      Graph.SurvivesSparseExits (Graph.MinimumDegreeAtLeast data.threshold)
        (Graph.HasCycleWithLength data.LengthOK) data.LengthOK input.object)
    (countOf : (input : Input BranchState Presentation presentation data) →
      activeSurplusFamily.At input →
      (input.object.excessPorts data.threshold).card =
        input.object.degreeSurplus data.threshold)
    (activatedOf : (input : Input BranchState Presentation presentation data) →
      sparsePortActivation.At input →
      ∀ pair : input.object.Vertex × input.object.Vertex,
        ∀ member : pair ∈ input.object.excessPorts data.threshold,
          ∀ left right : input.object.Vertex,
            (∀ vertex : input.object.Vertex,
              vertex ∈ (input.object.surplusPortOfMem member).shoulders ↔
                (vertex = left ∨ vertex = right)) →
            left ≠ right →
            Nonempty (Graph.FiniteObject.SurplusPort.PortReturn
                input.object pair.1 pair.2 left right) ∧
              (¬ input.object.graph.Adj left right →
                Nonempty (Graph.FiniteObject.SurplusPort.OpenPortWitness
                  input.object data.LengthOK pair.2 left right)) ∧
              (input.object.graph.Adj left right →
                input.object.graph.Adj pair.2 left ∧
                  input.object.graph.Adj left right ∧
                  input.object.graph.Adj right pair.2))
    (encode : (input : Input BranchState Presentation presentation data) →
      Graph.ActiveSurplusDemands (Graph.MinimumDegreeAtLeast data.threshold)
        (Graph.HasCycleWithLength data.LengthOK) data.LengthOK input.object
        data.threshold →
      activeSurplusDemands.At input) :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.activeSurplusDemands
    { Requires := [sparseSurplusSurvivor, activeSurplusFamily,
        sparsePortActivation]
      Produces := [activeSurplusDemands]
      requiresUnique := by
        simp [survivorNeFamily, survivorNeActivation, familyNeActivation]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := activeSurplusDemands)
        (encode inputs.current
          (Graph.surviving_active_family
            (survivesOf inputs.current (inputs.get sparseSurplusSurvivor))
            (countOf inputs.current (inputs.get activeSurplusFamily))
            (activatedOf inputs.current (inputs.get sparsePortActivation))))
        .nil)

end Hypostructure.Graph.Strategy.Spine
