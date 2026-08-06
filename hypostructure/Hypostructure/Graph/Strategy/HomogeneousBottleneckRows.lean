import Hypostructure.Graph.Strategy.SpineRows
import Hypostructure.Graph.ObjectCapacityLedger
import Hypostructure.Graph.NamedSurplusExits

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
    (canonicalPairLedger capacityTokenLedger baselineSpineDemand
      roleFibrePartition fibrePressure spineSurplusEstimate :
      FactKey (Input BranchState Presentation presentation data))
    (pairNeToken : canonicalPairLedger ≠ capacityTokenLedger)
    (pairNeDemand : canonicalPairLedger ≠ baselineSpineDemand)
    (tokenNeDemand : capacityTokenLedger ≠ baselineSpineDemand)
    (partitionNePressure : roleFibrePartition ≠ fibrePressure)
    (partitionNeEstimate : roleFibrePartition ≠ spineSurplusEstimate)
    (pressureNeEstimate : fibrePressure ≠ spineSurplusEstimate)
    (pairCountOf : (input : Input BranchState Presentation presentation data) →
      canonicalPairLedger.At input →
      (input.object.portPairSchedule data.threshold).card =
        (input.object.degreeSurplus data.threshold).choose 2)
    (tokenLedgerOf : (input : Input BranchState Presentation presentation data) →
      capacityTokenLedger.At input →
      Nonempty (Graph.ObjectCapacityLedger input.object data.threshold))
    (packageOrderOf : (input : Input BranchState Presentation presentation data) →
      baselineSpineDemand.At input →
      ∀ packing remainder scaleCount : Nat,
        Graph.spineDeficit input.object.vertexCount data.threshold
            (Graph.curvaturePackageBound data.windowRate packing scaleCount
              remainder data.entropyDenominator data.curvatureCost) ≤
          Graph.spineDeficit input.object.vertexCount data.threshold
            (Graph.highEntropyPackageBound data.windowRate packing scaleCount
              remainder data.entropyDenominator) ∧
        Graph.spineDeficit input.object.vertexCount data.threshold
            (Graph.highEntropyPackageBound data.windowRate packing scaleCount
              remainder data.entropyDenominator) ≤
          Graph.spineDeficit input.object.vertexCount data.threshold
            (Graph.windowPackageBound data.windowRate packing scaleCount))
    (encodePartition : (input : Input BranchState Presentation presentation data) →
      Graph.RoleFibrePartitionStatement input.object data.threshold →
      roleFibrePartition.At input)
    (encodePressure : (input : Input BranchState Presentation presentation data) →
      Graph.FibrePressureStatement input.object data.threshold →
      fibrePressure.At input)
    (encodeEstimate : (input : Input BranchState Presentation presentation data) →
      (∀ packing remainder scaleCount : Nat,
        (input.object.portPairSchedule data.threshold).card ≤
            Graph.spineDeficit input.object.vertexCount data.threshold
              (Graph.curvaturePackageBound data.windowRate packing scaleCount
                remainder data.entropyDenominator data.curvatureCost) →
          input.object.degreeSurplus data.threshold ≤
            1 + Nat.sqrt (2 * Graph.spineDeficit input.object.vertexCount
              data.threshold
              (Graph.windowPackageBound data.windowRate packing scaleCount))) →
      spineSurplusEstimate.At input) :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.coupledFibrePressure
    { Requires := [canonicalPairLedger, capacityTokenLedger, baselineSpineDemand]
      Produces := [roleFibrePartition, fibrePressure, spineSurplusEstimate]
      requiresUnique := by simp [pairNeToken, pairNeDemand, tokenNeDemand]
      producesUnique := by
        simp [partitionNePressure, partitionNeEstimate, pressureNeEstimate]
      producesNonempty := by simp }
    (fun inputs =>
      let object := inputs.current.object
      -- Node `[130]`'s count, node `[136]`'s ledger, node `[129]`'s ordering.
      let pairCount := pairCountOf inputs.current (inputs.get canonicalPairLedger)
      let existing := tokenLedgerOf inputs.current (inputs.get capacityTokenLedger)
      let ordering := packageOrderOf inputs.current (inputs.get baselineSpineDemand)
      .cons (key := roleFibrePartition)
        (encodePartition inputs.current
          (Graph.roleFibrePartitionStatement object data.threshold))
        (.cons (key := fibrePressure)
          (encodePressure inputs.current
            (Graph.fibrePressureStatement object data.threshold existing))
          (.cons (key := spineSurplusEstimate)
            (encodeEstimate inputs.current
              (fun packing remainder scaleCount budget =>
                Graph.surplus_le_of_package object data.threshold _
                  (le_trans (pairCount ▸ budget)
                    (le_trans (ordering packing remainder scaleCount).1
                      (ordering packing remainder scaleCount).2))))
            .nil)))

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
      Graph.SparsePressureCapped current.object data.threshold →
      sparsePressureNearCubic.At current)
    (encodeOverload :
      Graph.SparsePressureOverloadStatement current.object data.threshold →
      sparsePressureOverload.At current)
    (nearCubicFresh : sparsePressureNearCubic ∉ known)
    (overloadFresh : sparsePressureOverload ∉ known) :
    Decision sparsePressureNearCubic sparsePressureOverload previous := by
  classical
  refine Decision.run previous sparsePressureNearCubic sparsePressureOverload
    `Hypostructure.Graph.Strategy.Spine.sparsePressureRouting ?_ nearCubicFresh
    overloadFresh
  exact
    if capped : Graph.SparsePressureCapped current.object data.threshold then
      .inl (encodeNearCubic capped)
    else
      .inr (encodeOverload
        ((Graph.sparsePressureRouting current.object data.threshold).resolve_left
          capped))

/-! ## Nodes `[140]`, `[142]`, `[143]`: the three geometric class audits

`def:homogeneous-token-charge` fixes what a class may carry without a
role-homogeneous pattern:

  `Cap_hom(L) = Q_st(L−1)(2L−3)`,

"the uniform token load allowed by charging each of the at most `Q_st` role
fibres separately when no role-homogeneous same-token `L`-matching or `L`-star
occurs at that token".  The row commits the contrapositive, which is what the
audits produce.  The three audits are one statement because the class bound is a
function of `class(t)` and the ledger is one presentation. -/
@[reducible] noncomputable def bottleneckClassificationRow
    (canonicalPairLedger bottleneckClassification :
      FactKey (Input BranchState Presentation presentation data))
    (distinct : canonicalPairLedger ≠ bottleneckClassification)
    (pairCountOf : (input : Input BranchState Presentation presentation data) →
      canonicalPairLedger.At input →
      (input.object.portPairSchedule data.threshold).card =
        (input.object.degreeSurplus data.threshold).choose 2)
    (encode : (input : Input BranchState Presentation presentation data) →
      Graph.BottleneckClassificationStatement input.object data.threshold →
      bottleneckClassification.At input) :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.bottleneckClassification
    (rowManifest canonicalPairLedger bottleneckClassification distinct)
    (fun inputs =>
      let _read := pairCountOf inputs.current (inputs.get canonicalPairLedger)
      .cons (key := bottleneckClassification)
        (encode inputs.current
          (Graph.bottleneckClassificationStatement inputs.current.object
            data.threshold))
        .nil)

/-! ## Node `[144]`: the homogeneous bottleneck

`cor:homogeneous-same-token-caps-close`.  Its hypotheses are clauses (a), (b),
(c) -- no token in `𝔗_W`, `𝔗_R` or `𝔗_prim` supports a role-homogeneous
same-token `L_W`-, `L_R`- or `L_P`-matching or star -- and its proof forms
`M₀ := max{Cap_hom(L_W), Cap_hom(L_R), Cap_hom(L_P)}`, bounds every token load
by it through the role-fibre partition and `lem:same-token-matching-star`, sums
the canonical ledger's own identity to `|Π_blk| ≤ M₀|𝔗_cap|`, and invokes
`thm:tokenized-surplus-accounting-closure` to conclude `σ(G) = O(√n)`.

The closure is exact rather than asymptotic:

  `σ(G) ≤ 1 + 2M₀ + ⌊√(2·E + 2·M₀·scale)⌋`,

which at `scale = 8n` and `E ≤ C_E n + ((1/2)σ+1)log₂ n` is the manuscript's
`σ(G) = O(√n)` with the implicit constant written out.

`thm:homogeneous-overload-geometric-closure`'s own contribution -- that
`L_W = L_R = L_P = L_geom` may be taken once sparse exits are absent and every
decorated Type B handoff has been routed to the Type B fan ledger -- is the
branch structure that discharges these hypotheses, not part of this
implication; `lem:same-token-bottleneck-routing` and
`def:same-token-routing-germs` supply it and are not implemented. -/
@[reducible] noncomputable def homogeneousBottleneckRow
    (canonicalPairLedger homogeneousBottleneck :
      FactKey (Input BranchState Presentation presentation data))
    (distinct : canonicalPairLedger ≠ homogeneousBottleneck)
    (pairCountOf : (input : Input BranchState Presentation presentation data) →
      canonicalPairLedger.At input →
      (input.object.portPairSchedule data.threshold).card =
        (input.object.degreeSurplus data.threshold).choose 2)
    (encode : (input : Input BranchState Presentation presentation data) →
      Graph.HomogeneousBottleneckStatement input.object data.threshold →
      homogeneousBottleneck.At input) :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.homogeneousBottleneck
    (rowManifest canonicalPairLedger homogeneousBottleneck distinct)
    (fun inputs =>
      let _read := pairCountOf inputs.current (inputs.get canonicalPairLedger)
      .cons (key := homogeneousBottleneck)
        (encode inputs.current
          (Graph.homogeneousBottleneckStatement inputs.current.object data.threshold))
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
      Graph.SurvivesSparseExits (Graph.MinimumDegreeAtLeast data.threshold)
        (Graph.HasCycleWithLength data.LengthOK) data.LengthOK input.object →
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
          (Graph.survives_of_selection (avoidsOf inputs.current fact)
            (minimalOf inputs.current fact)
            (uncompressibleOf inputs.current (inputs.get uncompressible))))
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
