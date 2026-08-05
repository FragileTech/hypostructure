import Hypostructure.Graph.Strategy.SpineVocabulary

/-!
# The minimum-degree cycle spine: entry rows

Each row is one atomic Strategy.  A row reads its prerequisites by exact
semantic key through sealed `FactInputs`, proves the manuscript's statement,
and commits exactly that statement.  No row names a producer, a predecessor
depth, or an execution position, and no row transports anything outside the one
canonical `ExactLedger`.

Every row is quantified over the residual domain's fact system and over the
keys it consumes and produces, so the same executor runs after any canonical
branch cursor whose index carries its requirements.  A caller supplies the
schema bridges (`decode`/`encode`) that say which of its semantic keys carries
which manuscript statement; the mathematics below is the manuscript's own.
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-- The residual domain of a minimum-degree cycle spine. -/
abbrev Input (BranchState : Graph.FiniteObject.{u} → Type v)
    (Presentation : Type) (presentation : Presentation) (data : Data.{u}) :=
  Core.Strategy.ProblemInput
    (problem BranchState Presentation presentation data)

variable [FactSystem (Input BranchState Presentation presentation data)]

/-- **The selected context, as the ledger records it.**

Nodes `[11]` onwards call framework theorems that are stated against a
`MinimalCounterexampleContext`.  This rebuilds that context from the residual
and the selection *fact* — its two components are exactly the context's
`avoids` and its minimality kernel — so a later row consumes the committed
fact rather than re-selecting, re-deriving, or re-quantifying over the ambient
graph.  Nothing is proved here; this is the reading of one ledger entry. -/
def contextOfSelection
    (input : Input BranchState Presentation presentation data)
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK input.object)
    (minimal : ∀ smaller : Graph.FiniteObject.{u},
      (progress BranchState Presentation presentation data).Smaller
        smaller input.object →
      Graph.MinimumDegreeAtLeast data.threshold smaller →
      Graph.HasCycleWithLength data.LengthOK smaller) :
    Core.MinimalCounterexampleContext
      (problem BranchState Presentation presentation data)
      (Graph.HasCycleWithLength data.LengthOK)
      (progress BranchState Presentation presentation data) where
  G := input.object
  baseline := input.baseline
  state := input.branchState
  avoids := avoids
  minimal := minimal

/-- The manifest shape shared by every one-in/one-out spine row. -/
abbrev rowManifest
    (required produced :
      FactKey (Input BranchState Presentation presentation data))
    (distinct : required ≠ produced) :
    FactManifest (Input BranchState Presentation presentation data) where
  Requires := [required]
  Produces := [produced]
  requiresUnique := by simp
  producesUnique := by simp
  producesNonempty := by simp

/-! ## Nodes `[5]`--`[7]`: the return-set form of target avoidance

`lem:return-equivalence` says a graph has an accepted cycle exactly when some
oriented edge admits a simple return of the shifted length.  The selected
object avoids the target, so no oriented edge does: the return-length set is
disjoint from the shifted accepted set everywhere.

The equivalence is `Graph.not_hasCycleWithLength_iff_returnLengthSets_disjoint`.
This row does not restate or re-prove it; it transports the selection's own
avoidance through it. -/
@[reducible] noncomputable def returnAvoidanceRow
    (selection returnAvoidance :
      FactKey (Input BranchState Presentation presentation data))
    (distinct : selection ≠ returnAvoidance)
    (avoidsOf : (input : Input BranchState Presentation presentation data) →
      selection.At input → ¬ Graph.HasCycleWithLength data.LengthOK input.object)
    (encode : (input : Input BranchState Presentation presentation data) →
      (∀ dart : input.object.graph.Dart,
        Disjoint (Graph.returnLengthSet input.object dart)
          (Graph.shiftedAcceptedSet data.LengthOK)) →
      returnAvoidance.At input) :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.returnAvoidance
    (rowManifest selection returnAvoidance distinct)
    (fun inputs =>
      .cons (key := returnAvoidance)
        (encode inputs.current
          ((Graph.not_hasCycleWithLength_iff_returnLengthSets_disjoint data.LengthOK
              inputs.current.object).mp
            (avoidsOf inputs.current (inputs.get selection))))
        .nil)

/-! ## Node `[8]`: no proper subgraph satisfies the baseline

`lem:no-proper-core`.  A proper subgraph is strictly smaller in the registered
order, so minimality forces it to have an accepted cycle; but every cycle of a
proper subgraph is a cycle of the ambient graph
(`Graph.cycleProperSubgraphTargetMonotone`), which the selected object does not
have.  So no proper subgraph satisfies the baseline. -/
@[reducible] noncomputable def noProperBaselineRow
    (selection noProperBaseline :
      FactKey (Input BranchState Presentation presentation data))
    (distinct : selection ≠ noProperBaseline)
    (avoidsOf : (input : Input BranchState Presentation presentation data) →
      selection.At input → ¬ Graph.HasCycleWithLength data.LengthOK input.object)
    (minimalOf : (input : Input BranchState Presentation presentation data) →
      selection.At input →
      ∀ smaller : Graph.FiniteObject.{u},
        smaller.LexicographicallySmaller input.object →
        Graph.MinimumDegreeAtLeast data.threshold smaller →
        Graph.HasCycleWithLength data.LengthOK smaller)
    (encode : (input : Input BranchState Presentation presentation data) →
      (∀ subgraph : Graph.ProperSubgraph input.object,
        ¬ Graph.MinimumDegreeAtLeast data.threshold subgraph.value) →
      noProperBaseline.At input) :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.noProperBaseline
    (rowManifest selection noProperBaseline distinct)
    (fun inputs =>
      let fact := inputs.get selection
      .cons (key := noProperBaseline)
        (encode inputs.current fun subgraph baseline =>
          avoidsOf inputs.current fact
            ((Graph.cycleProperSubgraphTargetMonotone data.LengthOK).map subgraph
              (minimalOf inputs.current fact subgraph.value subgraph.decreases
                baseline)))
        .nil)

/-! ## Nodes `[9]`--`[10]`: deletion criticality

`lem:deletion-critical`.  If some oriented edge had *both* endpoints strictly
above the threshold, deleting it would preserve the baseline
(`Graph.DeletionCriticalityProfile.baseline_of_not_critical`, the profile's own
one-edge accounting) while producing a proper subgraph — which node `[8]` has
just excluded.  So every edge has an endpoint exactly at the threshold, and
"equivalently", as the manuscript puts it, the vertices strictly above the
threshold are pairwise nonadjacent.

Both clauses are derived here, and the second is derived from the first exactly
as the manuscript derives it.  Neither is registered. -/

/-- The two-output manifest of nodes `[9]`--`[10]`. -/
abbrev criticalityManifest
    (required tight slack :
      FactKey (Input BranchState Presentation presentation data))
    (tightFresh : tight ≠ required) (slackFresh : slack ≠ required)
    (distinct : tight ≠ slack) :
    FactManifest (Input BranchState Presentation presentation data) where
  Requires := [required]
  Produces := [tight, slack]
  requiresUnique := by simp
  producesUnique := by simp [distinct]
  producesNonempty := by simp

/-- **Nodes `[9]`--`[10]`.** -/
@[reducible] noncomputable def deletionCriticalityRow
    (noProperBaseline tightEndpoint slackIndependent :
      FactKey (Input BranchState Presentation presentation data))
    (tightFresh : tightEndpoint ≠ noProperBaseline)
    (slackFresh : slackIndependent ≠ noProperBaseline)
    (distinct : tightEndpoint ≠ slackIndependent)
    (excludes : (input : Input BranchState Presentation presentation data) →
      noProperBaseline.At input →
      ∀ subgraph : Graph.ProperSubgraph input.object,
        ¬ Graph.MinimumDegreeAtLeast data.threshold subgraph.value)
    (encodeTight :
      (input : Input BranchState Presentation presentation data) →
      (∀ dart : input.object.graph.Dart,
        input.object.degree dart.fst = data.threshold ∨
          input.object.degree dart.snd = data.threshold) →
      tightEndpoint.At input)
    (encodeSlack :
      (input : Input BranchState Presentation presentation data) →
      (∀ left right : input.object.Vertex,
        data.threshold < input.object.degree left →
        data.threshold < input.object.degree right →
        ¬ input.object.graph.Adj left right) →
      slackIndependent.At input) :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.deletionCriticality
    (criticalityManifest noProperBaseline tightEndpoint slackIndependent
      tightFresh slackFresh distinct)
    (fun inputs =>
      let object := inputs.current.object
      let profile := Graph.minimumDegreeDeletionCriticalityProfile data.threshold
      let noProper := excludes inputs.current (inputs.get noProperBaseline)
      -- Node `[9]`: an edge with two slack endpoints would survive deletion.
      let tight : ∀ dart : object.graph.Dart,
          object.degree dart.fst = data.threshold ∨
            object.degree dart.snd = data.threshold := by
        intro dart
        by_contra noncritical
        exact noProper (Graph.ProperSubgraph.deleteEdge object
            (object.edgeOfDart dart))
          (profile.baseline_of_not_critical inputs.current.baseline dart
            noncritical)
      .cons (key := tightEndpoint) (encodeTight inputs.current tight)
        (.cons (key := slackIndependent)
          -- Node `[10]`: two adjacent slack carriers would contradict `[9]`.
          (encodeSlack inputs.current fun left right leftSlack rightSlack
              adjacent =>
            match tight ⟨(left, right), adjacent⟩ with
            | .inl atThreshold => Nat.ne_of_lt' leftSlack atThreshold
            | .inr atThreshold => Nat.ne_of_lt' rightSlack atThreshold)
          .nil))

/-! ## Nodes `[11]`--`[14]`: interface replacement

`lem:replacement` and `cor:uncompressible`.  A target-complete compression of a
proper atom would produce a strictly smaller baseline object whose obstruction
profile is contained in the original's; minimality gives that object the target,
context-universality carries the target back through the shared outside
context, and the reconstruction is isomorphic to the selected object, which
avoids the target.

`Core.Strategy.InterfaceReplacement.Profile.strictReplacementImpossible` is that
argument, and it reads nothing but the selected context's `avoids` and
`target_of_smaller`.  This row therefore consumes the selection fact and
nothing else; no closure record, registration, or payload stands between the
fact and its consequence. -/
@[reducible] noncomputable def interfaceReplacementRow
    (T : Core.Target (problem BranchState Presentation presentation data))
    (targetInvariant : Core.TargetInvariant
      (Graph.isomorphismEquivalenceWithPresentation
        (Graph.MinimumDegreeAtLeast data.threshold) BranchState
        Presentation presentation
        (Graph.minimumDegreeAtLeast_isomorphismInvariant data.threshold))
      T.Predicate)
    (selection uncompressible :
      FactKey (Input BranchState Presentation presentation data))
    (distinct : selection ≠ uncompressible)
    (avoidsOf : (input : Input BranchState Presentation presentation data) →
      selection.At input → ¬ T.Predicate input.object)
    (minimalOf : (input : Input BranchState Presentation presentation data) →
      selection.At input →
      ∀ smaller : Graph.FiniteObject.{u},
        (progress BranchState Presentation presentation data).Smaller
          smaller input.object →
        Graph.MinimumDegreeAtLeast data.threshold smaller →
        T.Predicate smaller)
    (encode : (input : Input BranchState Presentation presentation data) →
      (∀ support : Finset input.object.Vertex,
        ¬ Graph.Strategy.InterfaceReplacement.CompressibleSupport
            (Graph.MinimumDegreeAtLeast data.threshold) T.Predicate
            input.object support) →
      uncompressible.At input) :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.interfaceReplacement
    (rowManifest selection uncompressible distinct)
    (fun inputs =>
      let fact := inputs.get selection
      -- The selected context, rebuilt from the committed fact rather than
      -- re-selected: its two components are exactly `avoids` and `minimal`.
      let context :
          Core.MinimalCounterexampleContext
            (problem BranchState Presentation presentation data) T.Predicate
            (progress BranchState Presentation presentation data) :=
        { G := inputs.current.object
          baseline := inputs.current.baseline
          state := inputs.current.branchState
          avoids := avoidsOf inputs.current fact
          minimal := minimalOf inputs.current fact }
      .cons (key := uncompressible)
        (encode inputs.current fun support =>
          Graph.Strategy.InterfaceReplacement.not_compressibleSupport
            (Graph.MinimumDegreeAtLeast data.threshold) BranchState
            (Graph.minimumDegreeAtLeast_isomorphismInvariant data.threshold)
            Presentation presentation T targetInvariant context support)
        .nil)

/-! ## Nodes `[15]`--`[17]`: the maximal induced-window packing

`cor:p13-exists` and the packing that follows it.  If the selected object had
no induced window of the registered order it would be window-free, and the
registered external law would give it an accepted cycle -- which node `[1]`
has excluded.  So some window is present, the packing number is positive, and
some vertex-disjoint family attains it.

Maximality is not assumed: `exists_mem_not_disjoint_of_card_eq` derives it from
attaining the maximum, because a window disjoint from every member could be
added.  The family itself never leaves this row -- what the ledger records is
the number, which is a function of the object, and the statement that a family
attains it. -/
@[reducible] noncomputable def obstructionPackingRow
    (selection maximalPacking :
      FactKey (Input BranchState Presentation presentation data))
    (distinct : selection ≠ maximalPacking)
    (avoidsOf : (input : Input BranchState Presentation presentation data) →
      selection.At input →
      ¬ Graph.HasCycleWithLength data.LengthOK input.object)
    (encode : (input : Input BranchState Presentation presentation data) →
      (0 < input.object.windowPackingNumber data.windowOrder ∧
        ∃ packing : Finset (Finset input.object.Vertex),
          input.object.IsWindowPacking data.windowOrder packing ∧
            packing.card =
              input.object.windowPackingNumber data.windowOrder ∧
            ∀ support : Finset input.object.Vertex,
              input.object.InducesWindow data.windowOrder support →
              ∃ member ∈ packing, ¬ Disjoint support member) →
      maximalPacking.At input) :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.obstructionPacking
    (rowManifest selection maximalPacking distinct)
    (fun inputs =>
      let object := inputs.current.object
      let avoids := avoidsOf inputs.current (inputs.get selection)
      -- `cor:p13-exists`: window-freeness would force the target.
      let carried : ∃ support : Finset object.Vertex,
          object.InducesWindow data.windowOrder support := by
        by_contra empty
        push Not at empty
        exact avoids
          (data.freeForcesTarget object inputs.current.baseline
            (Graph.FiniteObject.inducedPathFree_of_forall_not_inducesWindow
              object empty))
      let attaining := object.exists_windowPacking_card_eq data.windowOrder
      .cons (key := maximalPacking)
        (encode inputs.current (by
          obtain ⟨support, window⟩ := carried
          obtain ⟨packing, valid, attains⟩ := attaining
          exact ⟨object.windowPackingNumber_pos data.windowOrder_pos window,
            packing, valid, attains,
            fun other otherWindow =>
              object.exists_mem_not_disjoint_of_card_eq data.windowOrder_pos
                valid attains otherWindow⟩))
        .nil)

/-! ## Node `[18]`: the exact finite local algebra

`lem:labels`.  The legal labels of a window of the registered order are exactly
the ones the ascending code enumeration lists, and the two-step curvature
relation is decided on them.  Both are theorems about the registered order --
`legalCodeList_length` and `curvatureTwo_eq_true_iff` -- so the row states them
at `data.windowOrder` and never writes their values.  The manuscript's `399` is
the computed length of that list at the manuscript's own order. -/
@[reducible] noncomputable def localAlgebraRow
    (maximalPacking localAlgebra :
      FactKey (Input BranchState Presentation presentation data))
    (distinct : maximalPacking ≠ localAlgebra)
    (encode : (input : Input BranchState Presentation presentation data) →
      ((Graph.WindowCurvature.legalCodeList data.windowOrder).length =
          (Graph.WindowCurvature.Labels data.windowOrder).card ∧
        ∀ source middle target :
            Graph.WindowCurvature.Label data.windowOrder,
          Graph.WindowCurvature.curvatureTwo source middle target = true ↔
            Graph.WindowCurvature.Safe 1 source middle ∧
              Graph.WindowCurvature.Safe 1 middle target ∧
              ¬ Graph.WindowCurvature.Safe 2 source target) →
      localAlgebra.At input) :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.localAlgebra
    (rowManifest maximalPacking localAlgebra distinct)
    (fun inputs =>
      .cons (key := localAlgebra)
        (encode inputs.current
          ⟨Graph.WindowCurvature.legalCodeList_length data.windowOrder,
            fun source middle target =>
              Graph.WindowCurvature.curvatureTwo_eq_true_iff source middle
                target⟩)
        .nil)

/-! ## Node `[19]`: the surplus split

`def:surplus-ports` fixes `σ(G) = Σ_{h∈V_{≥δ+1}}(d(h)-δ)`, which on the standing
baseline is the object's own `degreeSurplus`; the diamond compares it against
the registered scale threshold at the object's own order.  The split is
exhaustive by trichotomy on `Nat`, and each arm commits a proved inequality, so
`def:near-cubic-spine` is *carried* on the surviving route rather than assumed
there.

This is a `Decision`, not a fact-only row: the arm not taken is absent from the
taken branch's key index, so no later row on either branch can read the other
alternative. -/
noncomputable def surplusDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous :
      ExactLedger (Input BranchState Presentation presentation data)
        current known)
    (surplusAbove surplusAtOrBelow :
      FactKey (Input BranchState Presentation presentation data))
    (encodeAbove :
      (data.surplusThreshold current.object.vertexCount <
        current.object.degreeSurplus data.threshold) →
      surplusAbove.At current)
    (encodeAtOrBelow :
      (current.object.degreeSurplus data.threshold ≤
        data.surplusThreshold current.object.vertexCount) →
      surplusAtOrBelow.At current)
    (aboveFresh : surplusAbove ∉ known)
    (belowFresh : surplusAtOrBelow ∉ known) :
    Decision surplusAbove surplusAtOrBelow previous :=
  Decision.run previous surplusAbove surplusAtOrBelow
    `Hypostructure.Graph.Strategy.Spine.scaleThresholdDichotomy
    (if above : data.surplusThreshold current.object.vertexCount <
        current.object.degreeSurplus data.threshold then
      .inl (encodeAbove above)
    else
      .inr (encodeAtOrBelow (Nat.le_of_not_lt above)))
    aboveFresh belowFresh

/-! ## Node `[21]`: the finite barrier enumeration

The registered barrier rate demands `2 ^ (rate · p)` distinguishable states of
the packing; `lem:skeleton-dominates` supplies the labelled skeleton budget
`C(C(n,2), m)` the object can pay from.  The comparison is exhaustive, so the
node is a `Decision` again.

The cap arm carries `lem:variable-edge-budget` with it: the budget the arm
retained is stable when the edge count is only known to lie in an admissible
family, because the exact stratum is one of the family's and the family's own
union bound dominates it (`sum_edgeStratumCount_le_variableEdgeBudget` is the
summed form of the same count).  That is what makes the retained cap survive
`rem:budget-robustness` rather than depending on the exact `m`. -/
noncomputable def barrierEnumerationDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous :
      ExactLedger (Input BranchState Presentation presentation data)
        current known)
    (barrierCap barrierOverflow :
      FactKey (Input BranchState Presentation presentation data))
    (encodeCap :
      (2 ^ (data.windowRate *
            current.object.windowPackingNumber data.windowOrder) ≤
          Graph.skeletonBudget current.object ∧
        ∀ family : Finset Nat, current.object.edgeCount ∈ family →
          Graph.skeletonBudget current.object ≤
            Graph.variableEdgeBudget current.object.vertexCount family) →
      barrierCap.At current)
    (encodeOverflow :
      (Graph.skeletonBudget current.object <
        2 ^ (data.windowRate *
          current.object.windowPackingNumber data.windowOrder)) →
      barrierOverflow.At current)
    (capFresh : barrierCap ∉ known)
    (overflowFresh : barrierOverflow ∉ known) :
    Decision barrierCap barrierOverflow previous :=
  -- `lem:variable-edge-budget` on the object's own counts.  It is proved once
  -- here and attached to the cap arm; the overflow arm never needs it.
  let stable : ∀ family : Finset Nat, current.object.edgeCount ∈ family →
      Graph.skeletonBudget current.object ≤
        Graph.variableEdgeBudget current.object.vertexCount family := by
    intro family member
    have dominated :
        Graph.edgeStratumCount current.object.vertexCount
            current.object.edgeCount ≤
          family.sup (Graph.edgeStratumCount current.object.vertexCount) :=
      Finset.le_sup member
    have positive : 0 < family.card :=
      Finset.card_pos.mpr ⟨current.object.edgeCount, member⟩
    exact le_trans dominated (Nat.le_mul_of_pos_left _ positive)
  Decision.run previous barrierCap barrierOverflow
    `Hypostructure.Graph.Strategy.Spine.finiteBarrierEnumeration
    (if overflow : Graph.skeletonBudget current.object <
        2 ^ (data.windowRate *
          current.object.windowPackingNumber data.windowOrder) then
      .inr (encodeOverflow overflow)
    else
      .inl (encodeCap ⟨Nat.le_of_not_lt overflow, stable⟩))
    capFresh overflowFresh

/-! ## Nodes `[22]`--`[24]`: the finite window-density budget

`prop:p13-density`.  The cap arm of node `[21]` retained
`2 ^ (rate · p) ≤ C(C(n,2), m)`; the at-or-below arm of node `[19]` retained
`σ(G) ≤ T(n)`; and the standing baseline gives `δ n ≤ 2m` by the handshake.
`Graph.two_mul_exponent_le_scale_mul_edgeBudget` spends the skeleton budget's
own `m !` against those three and returns the linear cap

  `2 · rate · p ≤ (log₂ n + 1) · (δ n + T(n))`,

which is the manuscript's `θ ≤ θ_win` in exact `Nat` form.  Every symbol is
read: `rate`, `δ`, and `T` from the registered `Data`, and `n`, `m`, `p` from
the object.  There is no `o(·)` term and no rounding. -/
@[reducible] noncomputable def densityBudgetRow
    (barrierCap surplusAtOrBelow densityCap :
      FactKey (Input BranchState Presentation presentation data))
    (distinctRequired : barrierCap ≠ surplusAtOrBelow)
    (capOf : (input : Input BranchState Presentation presentation data) →
      barrierCap.At input →
      2 ^ (data.windowRate * input.object.windowPackingNumber data.windowOrder)
        ≤ Graph.skeletonBudget input.object)
    (surplusOf : (input : Input BranchState Presentation presentation data) →
      surplusAtOrBelow.At input →
      input.object.degreeSurplus data.threshold ≤
        data.surplusThreshold input.object.vertexCount)
    (encode : (input : Input BranchState Presentation presentation data) →
      (2 * (data.windowRate *
          input.object.windowPackingNumber data.windowOrder) ≤
        (Graph.dyadicScaleCount input.object + 1) *
          (data.threshold * input.object.vertexCount +
            data.surplusThreshold input.object.vertexCount)) →
      densityCap.At input) :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.finiteDensityBudget
    { Requires := [barrierCap, surplusAtOrBelow]
      Produces := [densityCap]
      requiresUnique := by simp [distinctRequired]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let object := inputs.current.object
      -- The handshake half of `def:near-cubic-spine`, from the standing
      -- baseline rather than from a branch fact.
      let spine : data.threshold * object.vertexCount ≤ 2 * object.edgeCount :=
        Graph.baselineDegree_mul_vertexCount_le_two_mul_edgeCount object
          data.threshold fun vertex =>
            le_trans inputs.current.baseline (object.minDegree_le_degree vertex)
      .cons (key := densityCap)
        (encode inputs.current
          (Graph.two_mul_exponent_le_scale_mul_edgeBudget object
            (data.windowRate * object.windowPackingNumber data.windowOrder)
            data.threshold (data.surplusThreshold object.vertexCount)
            (capOf inputs.current (inputs.get barrierCap)) spine
            data.three_le_threshold
            (surplusOf inputs.current (inputs.get surplusAtOrBelow))))
        .nil)

/-! ## Nodes `[25]`--`[27]`: the packed-window remainder

`sec:remainder`.  With `W` the union of a maximal packing and `R = G − W`, the
manuscript asserts that `R` carries no induced window -- "since any such copy
would extend `𝒫`" -- and that no subgraph of `R` has minimum degree at least the
baseline.  The second is the cited external law applied at its own interface:
the induced closure of such a subgraph is still window-free, so it has an
accepted cycle, and a cycle of an induced subgraph is a cycle of the selected
object, which avoids the target.

The row quantifies over every maximal packing rather than naming one.  That is
what the manuscript's statement actually says, and it is also what the ledger
permits: a packing is data, and no fact can carry it.  The row's manifest
therefore lists `selection` alone -- the avoidance half of it is the only thing
the derivation consumes. -/
@[reducible] noncomputable def remainderNormalizationRow
    (selection remainderNormalized :
      FactKey (Input BranchState Presentation presentation data))
    (distinct : selection ≠ remainderNormalized)
    (avoidsOf : (input : Input BranchState Presentation presentation data) →
      selection.At input →
      ¬ Graph.HasCycleWithLength data.LengthOK input.object)
    (encode : (input : Input BranchState Presentation presentation data) →
      (∀ packing : Finset (Finset input.object.Vertex),
        input.object.IsWindowPacking data.windowOrder packing →
        (∀ window : Finset input.object.Vertex,
          input.object.InducesWindow data.windowOrder window →
          ∃ member ∈ packing, ¬ Disjoint window member) →
        ∀ support : Finset input.object.Vertex,
          support ⊆ input.object.remainderSupport packing →
          ¬ input.object.InducesWindow data.windowOrder support ∧
            ¬ Graph.MinimumDegreeAtLeast data.threshold
              (input.object.induce support)) →
      remainderNormalized.At input) :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.remainderNormalization
    (rowManifest selection remainderNormalized distinct)
    (fun inputs =>
      let object := inputs.current.object
      let avoids := avoidsOf inputs.current (inputs.get selection)
      .cons (key := remainderNormalized)
        (encode inputs.current
          (fun _packing _valid maximal support inside =>
            ⟨object.not_inducesWindow_of_subset_remainderSupport maximal inside,
              object.not_baseline_induce_of_subset_remainderSupport
                data.freeForcesTarget avoids maximal inside⟩))
        .nil)

/-! ## Nodes `[28]`--`[29]`: boundary-demand accounting

`def:deficiency-surplus` measures external degree demand by positive
deficiency, and `lem:surplus-aware-window-stub`'s first display bounds it by
the boundary incidences:

  `def⁺(R) ≤ e(R,W)`.

The manuscript's argument, verbatim: on the standing baseline every remainder
vertex already has ambient degree at least `δ`, so it is deficient *inside* `R`
only because some of its incidences leave.  Writing `d_G(v) = d_R(v) + e_v`
gives `max{0, δ − d_R(v)} ≤ e_v` pointwise; summing over `R` gives the claim.

No near-cubic hypothesis is used -- the manuscript is explicit that this half
needs none -- so the row consumes only the standing baseline, which it reads
off the residual rather than from a fact. -/
@[reducible] noncomputable def boundaryDemandRow
    (remainderNormalized boundaryDemand :
      FactKey (Input BranchState Presentation presentation data))
    (distinct : remainderNormalized ≠ boundaryDemand)
    (encode : (input : Input BranchState Presentation presentation data) →
      (∀ packing : Finset (Finset input.object.Vertex),
        input.object.IsWindowPacking data.windowOrder packing →
        input.object.positiveDeficiency
              (input.object.remainderSupport packing) data.threshold +
            2 * (data.windowOrder - 1) * packing.card ≤
          data.threshold * (data.windowOrder * packing.card) +
            input.object.ambientSurplus
              (Graph.FiniteObject.windowSupport packing) data.threshold) →
      boundaryDemand.At input) :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.boundaryDemand
    (rowManifest remainderNormalized boundaryDemand distinct)
    (fun inputs =>
      let object := inputs.current.object
      .cons (key := boundaryDemand)
        (encode inputs.current fun packing valid =>
          object.positiveDeficiency_add_internal_mass_le valid
            (fun vertex => le_trans inputs.current.baseline
              (object.minDegree_le_degree vertex)))
        .nil)

end Hypostructure.Graph.Strategy.Spine
