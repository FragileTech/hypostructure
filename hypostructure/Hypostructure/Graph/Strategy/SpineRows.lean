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

/-- The manifest shape of a row whose fact is a theorem about the registered
presentation alone, so it reads no prerequisite.  `Requires := []` is the honest
declaration: an unread key in `Requires` would claim a dependency the executor
does not have, and `FactInputs.get` is the only way a row may consume a fact. -/
abbrev sourceFreeManifest
    (produced : FactKey (Input BranchState Presentation presentation data)) :
    FactManifest (Input BranchState Presentation presentation data) where
  Requires := []
  Produces := [produced]
  requiresUnique := by simp
  producesUnique := by simp
  producesNonempty := by simp

/-- The manifest shape shared by every one-in/two-out spine row. -/
abbrev pairManifest
    (required first second :
      FactKey (Input BranchState Presentation presentation data))
    (firstFresh : first ≠ required) (secondFresh : second ≠ required)
    (distinct : first ≠ second) :
    FactManifest (Input BranchState Presentation presentation data) where
  Requires := [required]
  Produces := [first, second]
  requiresUnique := by simp
  producesUnique := by simp [distinct]
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
    (pairManifest noProperBaseline tightEndpoint slackIndependent
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
the computed length of that list at the manuscript's own order.

The row reads no fact.  Its statement quantifies over the registered window
order and ignores the residual object entirely -- `Holds .localAlgebra` takes
`_object` -- so there is no prerequisite to declare, and `Requires := []` says
exactly that.  An earlier revision declared `maximalPacking` as a requirement
and never called `FactInputs.get` on it: that claimed a dependency the executor
does not have, and used the manifest to express paper order, which the
composition in `SpineRun` already expresses. -/
@[reducible] noncomputable def localAlgebraRow
    (localAlgebra : FactKey (Input BranchState Presentation presentation data))
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
    (sourceFreeManifest localAlgebra)
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

`lem:p13-window-package`.  The registered barrier rate is a per-window cost
*per dyadic scale*, so the packing demands
`2 ^ (rate · scaleCount · p)` distinguishable states -- the manuscript's
`c₁₃ p₁₃ log₂ n` bits.  `lem:skeleton-dominates` supplies the labelled skeleton
budget `C(C(n,2), m)` the object can pay from.  The comparison is exhaustive,
so the node is a `Decision` again.

The scale factor is not decorative: without it the demand grows a whole
`log₂ n` slower than the manuscript's, and the cap node `[22]`--`[24]` derives
from it degrades to `θ ≲ 1.5·log₂ n / rate`, which bounds nothing as `n` grows.

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
      (2 ^ (data.windowRate * Graph.dyadicScaleCount current.object *
            current.object.windowPackingNumber data.windowOrder) ≤
          Graph.skeletonBudget current.object ∧
        ∀ family : Finset Nat, current.object.edgeCount ∈ family →
          Graph.skeletonBudget current.object ≤
            Graph.variableEdgeBudget current.object.vertexCount family) →
      barrierCap.At current)
    (encodeOverflow :
      (Graph.skeletonBudget current.object <
        2 ^ (data.windowRate * Graph.dyadicScaleCount current.object *
          current.object.windowPackingNumber data.windowOrder)) →
      barrierOverflow.At current)
    (capFresh : barrierCap ∉ known)
    (overflowFresh : barrierOverflow ∉ known) :
    Decision barrierCap barrierOverflow previous :=
  -- `lem:variable-edge-budget` / `rem:budget-robustness`, quoted from the
  -- framework module that owns the edge-stratum count.  The row states no
  -- combinatorics of its own.
  let stable : ∀ family : Finset Nat, current.object.edgeCount ∈ family →
      Graph.skeletonBudget current.object ≤
        Graph.variableEdgeBudget current.object.vertexCount family :=
    fun _family member =>
      Graph.skeletonBudget_le_variableEdgeBudget current.object member
  Decision.run previous barrierCap barrierOverflow
    `Hypostructure.Graph.Strategy.Spine.finiteBarrierEnumeration
    (if overflow : Graph.skeletonBudget current.object <
        2 ^ (data.windowRate * Graph.dyadicScaleCount current.object *
          current.object.windowPackingNumber data.windowOrder) then
      .inr (encodeOverflow overflow)
    else
      .inl (encodeCap ⟨Nat.le_of_not_lt overflow, stable⟩))
    capFresh overflowFresh

/-! ## Nodes `[22]`--`[24]`: the finite window-density budget

`prop:p13-density`.  The cap arm of node `[21]` retained
`2 ^ (rate · scaleCount · p) ≤ C(C(n,2), m)`; the at-or-below arm of node `[19]`
retained `σ(G) ≤ T(n)`; and the standing baseline gives `δ n ≤ 2m` by the
handshake.  `Graph.two_mul_exponent_le_scale_mul_edgeBudget` spends the skeleton
budget's own `m !` against those three and returns the linear cap

  `2 · rate · scaleCount · p ≤ (log₂ n + 1) · (δ n + T(n))`,

with `scaleCount = log₂ n`.  Dividing through, this is
`θ = p/n ≤ (δ/2)(1 + 1/log₂ n)/rate + O(T/n)`, converging to `δ/(2·rate)`: the
manuscript's `θ ≤ θ_win = 1.5/118.108581006…`, in exact `Nat` form.  Every
symbol is read: `rate`, `δ`, and `T` from the registered `Data`, and `n`, `m`,
`p` from the object.  The manuscript's `o(1)` is here the exact
`(log₂ n + 1)/log₂ n` factor together with the `T(n)` term; there is no
rounding and no asymptotic estimate inserted as data. -/
@[reducible] noncomputable def densityBudgetRow
    (barrierCap surplusAtOrBelow densityCap :
      FactKey (Input BranchState Presentation presentation data))
    (distinctRequired : barrierCap ≠ surplusAtOrBelow)
    (capOf : (input : Input BranchState Presentation presentation data) →
      barrierCap.At input →
      2 ^ (data.windowRate * Graph.dyadicScaleCount input.object *
          input.object.windowPackingNumber data.windowOrder)
        ≤ Graph.skeletonBudget input.object)
    (surplusOf : (input : Input BranchState Presentation presentation data) →
      surplusAtOrBelow.At input →
      input.object.degreeSurplus data.threshold ≤
        data.surplusThreshold input.object.vertexCount)
    (encode : (input : Input BranchState Presentation presentation data) →
      (2 * (data.windowRate * Graph.dyadicScaleCount input.object *
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
            (data.windowRate * Graph.dyadicScaleCount object *
              object.windowPackingNumber data.windowOrder)
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
    (remainderNormalized surplusAtOrBelow boundaryDemand stubSupply :
      FactKey (Input BranchState Presentation presentation data))
    (distinctRequired : remainderNormalized ≠ surplusAtOrBelow)
    (demandFresh : boundaryDemand ≠ remainderNormalized)
    (supplyFresh : stubSupply ≠ remainderNormalized)
    (distinctProduced : boundaryDemand ≠ stubSupply)
    (surplusOf : (input : Input BranchState Presentation presentation data) →
      surplusAtOrBelow.At input →
      input.object.degreeSurplus data.threshold ≤
        data.surplusThreshold input.object.vertexCount)
    (encodeDemand : (input : Input BranchState Presentation presentation data) →
      (∀ packing : Finset (Finset input.object.Vertex),
        input.object.IsWindowPacking data.windowOrder packing →
        input.object.positiveDeficiency
              (input.object.remainderSupport packing) data.threshold ≤
            input.object.boundaryIncidence
              (input.object.remainderSupport packing) ∧
          input.object.boundaryIncidence
                (input.object.remainderSupport packing) +
              2 * (data.windowOrder - 1) * packing.card ≤
            data.threshold * (data.windowOrder * packing.card) +
              input.object.ambientSurplus
                (Graph.FiniteObject.windowSupport packing) data.threshold) →
      boundaryDemand.At input)
    (encodeSupply : (input : Input BranchState Presentation presentation data) →
      (∀ packing : Finset (Finset input.object.Vertex),
        input.object.IsWindowPacking data.windowOrder packing →
        input.object.positiveDeficiency
              (input.object.remainderSupport packing) data.threshold +
            2 * (data.windowOrder - 1) * packing.card ≤
          data.threshold * (data.windowOrder * packing.card) +
            data.surplusThreshold input.object.vertexCount) →
      stubSupply.At input) :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.boundaryDemand
    { Requires := [remainderNormalized, surplusAtOrBelow]
      Produces := [boundaryDemand, stubSupply]
      requiresUnique := by simp [distinctRequired]
      producesUnique := by simp [distinctProduced]
      producesNonempty := by simp }
    (fun inputs =>
      -- The standing baseline, read off the residual rather than from a fact.
      let baseline : ∀ vertex : inputs.current.object.Vertex,
          data.threshold ≤ inputs.current.object.degree vertex :=
        fun vertex => le_trans inputs.current.baseline
          (inputs.current.object.minDegree_le_degree vertex)
      .cons (key := boundaryDemand)
        -- `lem:surplus-aware-window-stub`: the demand link and the capacity
        -- link, each at its own hypothesis and neither near-cubic.
        (encodeDemand inputs.current fun packing valid =>
          ⟨inputs.current.object.positiveDeficiency_le_boundaryIncidence
              (inputs.current.object.remainderSupport packing) data.threshold
              baseline,
            inputs.current.object.boundaryIncidence_add_internal_mass_le valid
              baseline⟩)
        (.cons (key := stubSupply)
          -- `lem:stub-positive`: the same chain with the object's own surplus,
          -- then the registered near-cubic ceiling spent against it.
          (encodeSupply inputs.current fun packing valid => by
            have stub :=
              inputs.current.object.positiveDeficiency_add_internal_mass_le_degreeSurplus
                valid baseline
            have ceiling :=
              surplusOf inputs.current (inputs.get surplusAtOrBelow)
            omega)
          .nil))

/-! ## Node `[30]`: the wedge lower bound

`lem:wedge-lower`.  A region `X` of the remainder carries
`W₂(X) = Σ_{v∈X} C(d_X(v), 2)` internal length-two wedges -- a wedge being a
choice of two distinct neighbours of a common centre inside `X` -- and the
manuscript's degree count bounds that below by the region's own size:

  `W₂(X) ≥ δ|X| − 2 def⁺(X)`,

committed subtraction-free.  The manuscript states it for a component `C` of
`R` and then sums over the components of `R`, using that `d_C = d_R` inside a
component.  The count is pointwise, so
`Graph.FiniteObject.baseline_mul_card_le_internalWedgeCount_add_two_mul_positiveDeficiency`
holds at *every* region, and both of the lemma's displayed inequalities are
instances of it: the componentwise one at a component, its sum at `R` itself.
No component decomposition is built, and none is needed to connect them.

The node exists for its "in particular", and that is the second output.
Substituting the boundary-demand ceiling of nodes `[28]`--`[29]` for `def⁺(R)`
turns the bound into the demand floor of the final collision -- invariant 28 --
which is why this row consumes `boundaryDemand`: the manuscript's own
`Requires` cell for `[30]` names `cor:stub-boundary-supply`.  Where the
manuscript substitutes the asymptotic `def⁺(R) ≤ (τ_win + o(1))|R|`, the row
substitutes the exact inequality the ledger actually carries, and the two
doubled terms of the conclusion are literally twice that inequality's two
sides.

`3 ≤ δ` is spent here a second time and for an unrelated reason: the skeleton
budget needed it as Stirling's `⌈e⌉`, and the wedge count needs it because a
vertex sitting exactly at the baseline contributes only `C(δ,2)`.
`baseline_one_insufficient` and `baseline_two_insufficient` prove it is the
exact threshold rather than a constant copied from a manuscript. -/
@[reducible] noncomputable def wedgeSupplyRow
    (boundaryDemand wedgeSupply curvatureDemandFloor :
      FactKey (Input BranchState Presentation presentation data))
    (supplyFresh : wedgeSupply ≠ boundaryDemand)
    (floorFresh : curvatureDemandFloor ≠ boundaryDemand)
    (distinct : wedgeSupply ≠ curvatureDemandFloor)
    (ceilingOf : (input : Input BranchState Presentation presentation data) →
      boundaryDemand.At input →
      ∀ packing : Finset (Finset input.object.Vertex),
        input.object.IsWindowPacking data.windowOrder packing →
        input.object.positiveDeficiency
              (input.object.remainderSupport packing) data.threshold +
            2 * (data.windowOrder - 1) * packing.card ≤
          data.threshold * (data.windowOrder * packing.card) +
            input.object.ambientSurplus
              (Graph.FiniteObject.windowSupport packing) data.threshold)
    (encodeSupply :
      (input : Input BranchState Presentation presentation data) →
      (∀ packing : Finset (Finset input.object.Vertex),
        input.object.IsWindowPacking data.windowOrder packing →
        ∀ support : Finset input.object.Vertex,
          support ⊆ input.object.remainderSupport packing →
          data.threshold * support.card ≤
            input.object.internalWedgeCount support +
              2 * input.object.positiveDeficiency support data.threshold) →
      wedgeSupply.At input)
    (encodeFloor :
      (input : Input BranchState Presentation presentation data) →
      (∀ packing : Finset (Finset input.object.Vertex),
        input.object.IsWindowPacking data.windowOrder packing →
        data.threshold * (input.object.remainderSupport packing).card +
              2 * (2 * (data.windowOrder - 1) * packing.card) ≤
            input.object.internalWedgeCount
                (input.object.remainderSupport packing) +
              2 * (data.threshold * (data.windowOrder * packing.card) +
                input.object.ambientSurplus
                  (Graph.FiniteObject.windowSupport packing) data.threshold)) →
      curvatureDemandFloor.At input) :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.wedgeSupply
    (pairManifest boundaryDemand wedgeSupply curvatureDemandFloor
      supplyFresh floorFresh distinct)
    (fun inputs =>
      -- The lemma proper, read at the remainder's regions.  The registered
      -- baseline is the only hypothesis, and no packing enters the count.
      let supply : ∀ packing : Finset (Finset inputs.current.object.Vertex),
          inputs.current.object.IsWindowPacking data.windowOrder packing →
          ∀ support : Finset inputs.current.object.Vertex,
            support ⊆ inputs.current.object.remainderSupport packing →
            data.threshold * support.card ≤
              inputs.current.object.internalWedgeCount support +
                2 * inputs.current.object.positiveDeficiency support
                  data.threshold :=
        fun _packing _valid support _inside =>
          inputs.current.object.baseline_mul_card_le_internalWedgeCount_add_two_mul_positiveDeficiency
            support data.threshold data.three_le_threshold
      .cons (key := wedgeSupply) (encodeSupply inputs.current supply)
        (.cons (key := curvatureDemandFloor)
          -- The "in particular": the bound at `R` itself, with the committed
          -- boundary-demand ceiling substituted for its `def⁺(R)`.
          (encodeFloor inputs.current fun packing valid => by
            have wedge :=
              supply packing valid
                (inputs.current.object.remainderSupport packing)
                (Finset.Subset.refl _)
            have ceiling :=
              ceilingOf inputs.current (inputs.get boundaryDemand) packing valid
            omega)
          .nil))

/-! ## Node `[31]`: the curvature target-rank of the remainder

`def:curvature-target-rank`.  `𝒲₂(R)` is the family of raw internal length-two
curvature tests of the remainder; a subfamily *survives* an admissible rank
quotient when the quotient is label-injective on it, and it survives the
admissible quotient system when it survives every functional admissible rank
quotient.  `r_Ω(R)` is the largest surviving subfamily's size, computed by
`Graph.FiniteObject.curvatureTargetRank` against the manuscript's own system.

The row commits that the maximum is attained together with
`lem:target-rank-circuit`: at a maximal surviving subfamily, every raw test left
outside is target-dependent on a subfamily of it.  The manuscript's proof is
exactly the reason: maximality means adjoining the test loses label-injectivity
for some member `q`, the subfamily itself survives `q`, so the loss involves the
test, and `q` is functional, so a finite subfamily determines the test's
quotient value. -/
@[reducible] noncomputable def curvatureTargetRankRow
    (curvatureDemandFloor curvatureTargetRank :
      FactKey (Input BranchState Presentation presentation data))
    (distinct : curvatureDemandFloor ≠ curvatureTargetRank)
    (encode : (input : Input BranchState Presentation presentation data) →
      (∀ packing : Finset (Finset input.object.Vertex),
        input.object.IsWindowPacking data.windowOrder packing →
        ∃ independent ⊆ remainderCurvatureTests input.object packing,
          (remainderQuotientSystem data input.object packing).Survives
              ↑independent ∧
            independent.card =
              remainderCurvatureTargetRank data input.object packing ∧
            ∀ test ∈ remainderCurvatureTests input.object packing,
              test ∉ independent →
              ∃ determiners ⊆ (↑independent : Set _),
                Core.TargetRank.Dependence
                  (remainderQuotientSystem data input.object packing) test
                  determiners) →
      curvatureTargetRank.At input) :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.curvatureTargetRank
    (rowManifest curvatureDemandFloor curvatureTargetRank distinct)
    (fun inputs =>
      .cons (key := curvatureTargetRank)
        (encode inputs.current fun _packing _valid =>
          Core.TargetRank.exists_independent_attaining _)
        .nil)

/-! ## Node `[32]`: the rank-drop decision

`r_Ω(R) < W₂(R) − o(W₂)`?  The yes arm is node `[33]`, Branch D; the no arm is
node `[34]`, Residual B, the full-rank residual `lem:full-rank` is stated on.

Both sides are the two halves of one excluded middle on the manuscript's own
comparison, so the alternatives are exhaustive and mutually exclusive by
construction.  The yes arm carries the dependence, not merely the inequality:
the allowance is subtracted from `W₂(R)`, which is the number of raw tests
(`internalWedgeFamily_card`), so a rank below it is a rank below the family's
own size, and `lem:target-rank-circuit` turns that into a proper
target-dependence.  That dependence is what node `[33]` routes, through
`Graph.CurvatureQuotient.localize`. -/
noncomputable def curvatureRankDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous :
      ExactLedger (Input BranchState Presentation presentation data)
        current known)
    (curvatureTargetRank curvatureRankDrop curvatureFullRank :
      FactKey (Input BranchState Presentation presentation data))
    [Core.Residual.FactKeys.Has curvatureTargetRank known]
    (rankOf : curvatureTargetRank.At current →
      ∀ packing : Finset (Finset current.object.Vertex),
        current.object.IsWindowPacking data.windowOrder packing →
        ∃ independent ⊆ remainderCurvatureTests current.object packing,
          (remainderQuotientSystem data current.object packing).Survives
              ↑independent ∧
            independent.card =
              remainderCurvatureTargetRank data current.object packing ∧
            ∀ test ∈ remainderCurvatureTests current.object packing,
              test ∉ independent →
              ∃ determiners ⊆ (↑independent : Set _),
                Core.TargetRank.Dependence
                  (remainderQuotientSystem data current.object packing) test
                  determiners)
    (encodeDrop :
      (∃ packing : Finset (Finset current.object.Vertex),
        current.object.IsWindowPacking data.windowOrder packing ∧
          remainderCurvatureTargetRank data current.object packing <
              remainderWedgeSupply current.object packing -
                data.rankDefect (remainderWedgeSupply current.object packing) ∧
            ∃ test determiners,
              Core.TargetRank.Dependence
                (remainderQuotientSystem data current.object packing) test
                determiners) →
      curvatureRankDrop.At current)
    (encodeFull :
      (∀ packing : Finset (Finset current.object.Vertex),
        current.object.IsWindowPacking data.windowOrder packing →
        remainderWedgeSupply current.object packing -
            data.rankDefect (remainderWedgeSupply current.object packing) ≤
          remainderCurvatureTargetRank data current.object packing) →
      curvatureFullRank.At current)
    (dropFresh : curvatureRankDrop ∉ known)
    (fullFresh : curvatureFullRank ∉ known) :
    Decision curvatureRankDrop curvatureFullRank previous :=
  Decision.run previous curvatureRankDrop curvatureFullRank
    `Hypostructure.Graph.Strategy.Spine.curvatureRankDichotomy
    (by
      classical
      by_cases drop :
          ∃ packing : Finset (Finset current.object.Vertex),
            current.object.IsWindowPacking data.windowOrder packing ∧
              remainderCurvatureTargetRank data current.object packing <
                remainderWedgeSupply current.object packing -
                  data.rankDefect (remainderWedgeSupply current.object packing)
      · -- Yes: the dependence Branch D is entered with, extracted from the
        -- maximal surviving subfamily node `[31]` committed.  The subfamily is
        -- read from the ledger by exact key; it is not recomputed here.
        refine .inl (encodeDrop ?_)
        obtain ⟨packing, valid, below⟩ := drop
        obtain ⟨independent, subset, _survives, attains, dependent⟩ :=
          rankOf (ExactLedger.get previous curvatureTargetRank) packing valid
        refine ⟨packing, valid, below, ?_⟩
        refine Core.TargetRank.exists_dependence_of_attaining subset attains
          dependent ?_
        rw [Graph.FiniteObject.internalWedgeFamily_card]
        exact lt_of_lt_of_le below (Nat.sub_le _ _)
      · -- No: the full-rank residual, the negation at every packing.
        refine .inr (encodeFull fun packing valid => ?_)
        by_contra short
        exact drop ⟨packing, valid, Nat.lt_of_not_le short⟩)
    dropFresh fullFresh

/-! ## Nodes `[33]` and `[35]`: Branch D, entered with its determination certificate

Node `[33]` is the yes arm of `[32]` and node `[35]` is the same box redrawn as
the entry of the rank-drop branch, so the two carry one statement: Branch D, the
rank-reducing curvature dependence.

The rank drop is committed as an existential dependence.  The manuscript opens
`lem:curvature-dependence-routing`'s proof by turning it into the object the
branch actually routes: *"Choose a determination certificate with
inclusion-minimal connected support.  The certificate has an admissible quotient
`q` and a finite support set `𝒫`."*  So this row unpacks the dependence into
that certificate -- all four clauses of `def:curvature-target-dependence`,
carried by `DeterminationCertificate` -- and commits it with the minimality the
proof chooses.

Branch D is a rank-reducing curvature *dependence*, so the determined coordinate
`a` and its determiners `ℬ` travel with the quotient: dropping them would leave
"some rank-reducing quotient exists", which is a different and weaker statement
and is not what `[38]` and `[40]` route.

Nothing is re-derived.  The dependence's own witness clause already names the
member of the system that realizes it, supplies the rank reduction the branch
was entered on, and supplies the determination; its `determined`, `supported`
and `proper` fields are the membership and properness clauses; and membership in
the manuscript's system is by definition the existence of the admissible
quotient.  The one thing the row does is the manuscript's choice: the supports
carrying a determination certificate form a finite family of `Finset`s, so one
of minimum cardinality exists, and a proper subset is strictly smaller -- which
is inclusion-minimality. -/
@[reducible] noncomputable def branchDependenceRow
    (curvatureRankDrop branchDependence :
      FactKey (Input BranchState Presentation presentation data))
    (distinct : curvatureRankDrop ≠ branchDependence)
    (dropOf : (input : Input BranchState Presentation presentation data) →
      curvatureRankDrop.At input →
      ∃ packing : Finset (Finset input.object.Vertex),
        input.object.IsWindowPacking data.windowOrder packing ∧
          remainderCurvatureTargetRank data input.object packing <
              remainderWedgeSupply input.object packing -
                data.rankDefect (remainderWedgeSupply input.object packing) ∧
            ∃ test determiners,
              Core.TargetRank.Dependence
                (remainderQuotientSystem data input.object packing) test
                determiners)
    (encode : (input : Input BranchState Presentation presentation data) →
      (∃ packing : Finset (Finset input.object.Vertex),
        input.object.IsWindowPacking data.windowOrder packing ∧
          ∃ quotient : remainderQuotient data input.object packing,
            DeterminationCertificate data input.object packing quotient ∧
              ∀ smaller : Finset input.object.Vertex,
                smaller ⊂ quotient.support →
                ∀ narrower : remainderQuotient data input.object packing,
                  narrower.support = smaller →
                  ¬ DeterminationCertificate data input.object packing
                      narrower) →
      branchDependence.At input) :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.branchDependence
    (rowManifest curvatureRankDrop branchDependence distinct)
    (fun inputs =>
      .cons (key := branchDependence)
        (encode inputs.current (by
          classical
          letI : Fintype inputs.current.object.Vertex :=
            @FinEnum.instFintype _ inputs.current.object.vertices
          obtain ⟨packing, valid, _below, test, determiners, dependence⟩ :=
            dropOf inputs.current (inputs.get curvatureRankDrop)
          -- The dependence names the member of the manuscript's own system that
          -- realizes it: it reduces rank on the raw curvature tests *and*
          -- determines the coordinate from the subfamily, which is clause (c).
          obtain ⟨quotient, member, reducing, determines⟩ := dependence.witness
          -- Membership in that system *is* the admissible quotient.
          obtain ⟨⟨admissible, represents⟩, _functional⟩ := member
          subst represents
          -- The dependence, as a determination certificate: clauses (a), (b)
          -- and (d) are the quotient's own fields, and (c) with its properness
          -- clause is what the dependence carries.
          have certified :
              DeterminationCertificate data inputs.current.object packing
                admissible :=
            ⟨reducing, test, dependence.determined, determiners,
              dependence.supported, dependence.proper, determines⟩
          -- *"Choose a determination certificate with inclusion-minimal
          -- connected support."*  The supports that carry a determination
          -- certificate form a finite family; one of minimum size is
          -- inclusion-minimal, because a proper subset is strictly smaller.
          set carriers :=
            (Finset.univ : Finset (Finset inputs.current.object.Vertex)).filter
              fun support => ∃ candidate :
                  remainderQuotient data inputs.current.object packing,
                candidate.support = support ∧
                  DeterminationCertificate data inputs.current.object packing
                    candidate
            with carriers_def
          have inhabited : admissible.support ∈ carriers := by
            simp only [carriers_def, Finset.mem_filter, Finset.mem_univ,
              true_and]
            exact ⟨admissible, rfl, certified⟩
          obtain ⟨chosen, member, least⟩ :=
            Finset.exists_min_image carriers Finset.card ⟨_, inhabited⟩
          simp only [carriers_def, Finset.mem_filter, Finset.mem_univ,
            true_and] at member
          obtain ⟨minimal, supportEq, minimalCertified⟩ := member
          refine ⟨packing, valid, minimal, minimalCertified,
            fun smaller strict narrower narrowerSupport narrowerCertified => ?_⟩
          have carried : smaller ∈ carriers := by
            simp only [carriers_def, Finset.mem_filter, Finset.mem_univ,
              true_and]
            exact ⟨narrower, narrowerSupport, narrowerCertified⟩
          have := least smaller carried
          rw [supportEq] at strict
          exact absurd (Finset.card_lt_card strict) (by omega)))
        .nil)

/-! ## Node `[36]`: the context-validity test, and its terminal `[37]`

*"Valid against every outside context?"*  The no arm is the terminal `[37]`, a
target-defective quotient -- case (i) of `lem:curvature-dependence-routing`.

The branch is the manuscript's eligibility test on the identification: both
clauses of `def:target-complete-quotient`, the boundary-degree fibre and the
all-context response.  Failing either is target-defective and the manuscript
says so of each -- of the second in `def:target-complete-quotient` itself
(*"an identification failing this context-universal test is target-defective"*)
and of the first in the sparse-exit routing (*"a non-fibrewise quotient is
target-defective"*).  Invariant 6 is attributed to `[36]` *and* `[37]` with
failure mode "otherwise target-defective", so `[37]` admits both and the two are
the halves of one negation rather than a third alternative.

`lem:separated-testers` supplies the exhaustiveness -- *"any quotient
identifying `w(u)` with `w(v)` is either context-universal or target-defective"*
-- and `Graph.Response.contextEquivalent_or_targetDefect` is that clause at the
framework's own interface: an identification is separated by an outside context
or it is not, with no third outcome and with the separating context exhibited in
the first case.

Nothing admissible is used to *decide* the branch: the test is the manuscript's
own excluded middle on the identification, and it is decided without looking at
why the quotient was chosen.  Admissibility is spent only afterwards, on the
terminal, where `lem:degree-profile-fibres` and `lem:context-universality`
together close `[37]`. -/
noncomputable def contextValidityDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous :
      ExactLedger (Input BranchState Presentation presentation data)
        current known)
    (contextDefect contextUniversal :
      FactKey (Input BranchState Presentation presentation data))
    (encodeDefect :
      (∃ packing : Finset (Finset current.object.Vertex),
        current.object.IsWindowPacking data.windowOrder packing ∧
          ∃ quotient : remainderQuotient data current.object packing,
            ∃ left right, Identified quotient left right ∧
              (left.boundaryDegreeProfile ≠ right.boundaryDegreeProfile ∨
                Graph.Response.TargetDefect
                  (Graph.HasCycleWithLength data.LengthOK) left right)) →
      contextDefect.At current)
    (encodeUniversal :
      (∀ packing : Finset (Finset current.object.Vertex),
        current.object.IsWindowPacking data.windowOrder packing →
        ∀ quotient : remainderQuotient data current.object packing,
          TargetCompleteAt data quotient) →
      contextUniversal.At current)
    (defectFresh : contextDefect ∉ known)
    (universalFresh : contextUniversal ∉ known) :
    Decision contextDefect contextUniversal previous :=
  Decision.run previous contextDefect contextUniversal
    `Hypostructure.Graph.Strategy.Spine.contextValidityDichotomy
    (by
      classical
      -- The manuscript's eligibility test: is the identification target-complete
      -- -- fibrewise over the boundary degree profile, and valid against every
      -- outside context?
      by_cases universal :
          ∀ packing : Finset (Finset current.object.Vertex),
            current.object.IsWindowPacking data.windowOrder packing →
            ∀ quotient : remainderQuotient data current.object packing,
              TargetCompleteAt data quotient
      · -- Yes: the determination is target-complete.  This is the residual
        -- node `[38]` is stated on.
        exact .inr (encodeUniversal universal)
      · -- No: an identified pair is separated, and the witness is exhibited --
        -- which is what makes `[37]` a terminal rather than a restatement of
        -- the negation.
        refine .inl (encodeDefect ?_)
        simp only [TargetCompleteAt] at universal
        push Not at universal
        obtain ⟨packing, valid, quotient, left, right, identified, failure⟩ :=
          universal
        refine ⟨packing, valid, quotient, left, right, identified, ?_⟩
        by_cases profile :
            left.boundaryDegreeProfile = right.boundaryDegreeProfile
        · -- The fibre clause held, so it was the context clause that failed.
          -- `lem:separated-testers`: the identification admits no third
          -- outcome, so the failure hands back the separating context.
          rcases Graph.Response.contextEquivalent_or_targetDefect
              (Graph.HasCycleWithLength data.LengthOK) left right with
            equivalent | defect
          · exact absurd equivalent (failure profile)
          · exact Or.inr defect
        · -- A non-fibrewise identification: target-defective by
          -- `lem:degree-profile-fibres`, with the mismatch itself the witness.
          exact Or.inl profile)
    defectFresh universalFresh

/-- **The target-defect terminal `[37]` is uninhabited.**

The pair is identified by an *admissible* rank quotient, and
`def:admissible-rank-quotient` requires admissible quotients to preserve the
boundary degree profile and to be target-complete against all `T`-boundaried
contexts.  So neither way of being target-defective can occur: the profiles
agree by `lem:degree-profile-fibres`, and no context separates the pair by
`lem:context-universality`.

This is why `[37]` is a *closed* round node in the manuscript's Part III
diagram.  The branch test at `[36]` still has to offer the alternative -- it is
decided on the identification, not on the certificate's provenance -- and this
is the theorem that closes the arm once it is taken. -/
theorem not_contextDefect
    (object : Graph.FiniteObject.{u})
    (defect : ∃ packing : Finset (Finset object.Vertex),
      object.IsWindowPacking data.windowOrder packing ∧
        ∃ quotient : remainderQuotient data object packing,
          ∃ left right, Identified quotient left right ∧
            (left.boundaryDegreeProfile ≠ right.boundaryDegreeProfile ∨
              Graph.Response.TargetDefect
                (Graph.HasCycleWithLength data.LengthOK) left right)) :
    False := by
  obtain ⟨_packing, _valid, quotient, left, right, identified, separated⟩ :=
    defect
  obtain ⟨fibrewise, universal⟩ :=
    Graph.CurvatureQuotient.targetComplete_of_identified quotient left right
      identified
  rcases separated with different | ⟨outside, distinguishes⟩
  · exact different fibrewise
  · exact distinguishes (universal outside)

/-! ## Nodes `[38]`--`[46]`: the rest of Branch D, and why every arm closes

`lem:curvature-dependence-routing` routes a determination certificate into three
cases and Part III's diagram closes each one:

* `[38]`/`[39]` -- the determination holds already at the proper atom `C`, so
  `q` is a target-complete rank-reducing quotient of `C` and
  `def:admissible-rank-quotient` supplies a strictly smaller proper
  representative.  `cor:uncompressible` forbids it.
* `[40]`--`[42]` -- it holds only after adjoining a connected `Z ⊋ C`, and
  `Z ⊊ G`.  `lem:proper-smearing`: `Z` is a proper boundaried support, so the
  dependence is target-defective or a target-complete compression of `Z`, both
  forbidden.
* `[43]`--`[46]` -- `Z = G`.  `lem:no-silent-global-smearing`: the closed clause
  of `def:admissible-rank-quotient` supplies a strictly smaller admissible closed
  representative `G_q`, which is finite, simple, meets the baseline, and cannot
  contain an accepted cycle because `G` does not.  So `G_q` is a strictly
  smaller counterexample, contradicting minimality.

The two refutations are the same two the manuscript uses, and
`Graph.CurvatureQuotient.localize` is the scope split between them.  It is
stated once here because the three cases differ in *which* support is
compressed, not in why compression is impossible -- which is exactly what the
manuscript says when it routes all three to the same two exclusions. -/
/-- **The barrier node `[45]` raises is impossible**, from the reading it
*stored* rather than from a fresh derivation.

Node `[45]` already committed the disjunction `lem:no-silent-global-smearing`
leaves.  The terminal `[46]` therefore reads it back by exact key and refutes
its two disjuncts -- `lem:replacement` for the proper-support replacement, and
the selection's own minimality and avoidance for the closed representative.
Nothing is recomputed: `Graph.CurvatureQuotient.localize` is applied once, in
the row that commits `[45]`, and never again. -/
theorem not_globalBarrierReading
    {object : Graph.FiniteObject.{u}}
    (baseline : Graph.MinimumDegreeAtLeast data.threshold object)
    (state : BranchState object)
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (minimal : ∀ smaller : Graph.FiniteObject.{u},
      (progress BranchState Presentation presentation data).Smaller
        smaller object →
      Graph.MinimumDegreeAtLeast data.threshold smaller →
      Graph.HasCycleWithLength data.LengthOK smaller)
    {support : Finset object.Vertex}
    (reading :
      Graph.Strategy.InterfaceReplacement.ReplacementSupport
          (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) object support ∨
        ∃ representative : Graph.FiniteObject.{u},
          representative.LexicographicallySmaller object ∧
            Graph.MinimumDegreeAtLeast data.threshold representative ∧
              (Graph.HasCycleWithLength data.LengthOK representative →
                Graph.HasCycleWithLength data.LengthOK object)) :
    False := by
  rcases reading with
    replacement | ⟨representative, smaller, representativeBaseline, transfer⟩
  · exact Graph.Strategy.InterfaceReplacement.not_replacementSupport
      (Graph.MinimumDegreeAtLeast data.threshold) BranchState
      (Graph.minimumDegreeAtLeast_isomorphismInvariant data.threshold)
      Presentation presentation
      (Core.Target.ofPredicate _ (Graph.HasCycleWithLength data.LengthOK))
      ((Graph.cycleTargetInterface data.LengthOK).coreInvariantWithPresentation
        (Graph.MinimumDegreeAtLeast data.threshold) BranchState
        Presentation presentation
        (Graph.minimumDegreeAtLeast_isomorphismInvariant data.threshold))
      { G := object, baseline := baseline, state := state, avoids := avoids,
        minimal := minimal }
      support replacement
  · exact avoids (transfer (minimal representative smaller
      representativeBaseline))

theorem not_determinationCertificate
    {object : Graph.FiniteObject.{u}}
    (baseline : Graph.MinimumDegreeAtLeast data.threshold object)
    (state : BranchState object)
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (minimal : ∀ smaller : Graph.FiniteObject.{u},
      (progress BranchState Presentation presentation data).Smaller
        smaller object →
      Graph.MinimumDegreeAtLeast data.threshold smaller →
      Graph.HasCycleWithLength data.LengthOK smaller)
    {packing : Finset (Finset object.Vertex)}
    {quotient : remainderQuotient data object packing}
    (certified : DeterminationCertificate data object packing quotient) :
    False := by
  -- `[39]` and `[42]` reach their terminal straight from a branch test, with no
  -- row in between to commit the reading, so the scope split is taken here --
  -- once -- and handed to the same refutation `[46]` uses.
  exact not_globalBarrierReading baseline state avoids minimal
    (Graph.CurvatureQuotient.localize quotient certified.1)

/-! ### Node `[38]`: is the determination certified already at `C`?

*"Target-complete with smaller proper representative?"*  The yes arm is the
terminal `[39]`, proper atom compression -- case (ii): *"if it holds for every
outside context already with support `C`, then `q` is a target-complete
rank-reducing quotient of the proper atom `C`"*.  The no arm is node `[40]`: the
determination reaches outside `C`, so the connected support it needs strictly
contains `C`, which is case (iii)'s entry. -/
noncomputable def atomCompressionDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous :
      ExactLedger (Input BranchState Presentation presentation data)
        current known)
    (branchDependence contextUniversal atomCompression delocalizedSupport :
      FactKey (Input BranchState Presentation presentation data))
    [Core.Residual.FactKeys.Has branchDependence known]
    [Core.Residual.FactKeys.Has contextUniversal known]
    (universalOf : contextUniversal.At current →
      ∀ packing : Finset (Finset current.object.Vertex),
        current.object.IsWindowPacking data.windowOrder packing →
        ∀ quotient : remainderQuotient data current.object packing,
          TargetCompleteAt data quotient)
    (certificateOf : branchDependence.At current →
      ∃ packing : Finset (Finset current.object.Vertex),
        current.object.IsWindowPacking data.windowOrder packing ∧
          ∃ quotient : remainderQuotient data current.object packing,
            DeterminationCertificate data current.object packing quotient ∧
              ∀ smaller : Finset current.object.Vertex,
                smaller ⊂ quotient.support →
                ∀ narrower : remainderQuotient data current.object packing,
                  narrower.support = smaller →
                  ¬ DeterminationCertificate data current.object packing
                      narrower)
    (encodeCompression :
      (∃ packing : Finset (Finset current.object.Vertex),
        current.object.IsWindowPacking data.windowOrder packing ∧
          ∃ quotient : remainderQuotient data current.object packing,
            DeterminationCertificate data current.object packing quotient ∧
              TargetCompleteAt data quotient ∧
                quotient.support ⊆
                  current.object.remainderSupport packing) →
      atomCompression.At current)
    (encodeDelocalized :
      (∃ packing : Finset (Finset current.object.Vertex),
        current.object.IsWindowPacking data.windowOrder packing ∧
          ∃ quotient : remainderQuotient data current.object packing,
            DeterminationCertificate data current.object packing quotient ∧
              TargetCompleteAt data quotient ∧
                ¬ quotient.support ⊆
                    current.object.remainderSupport packing ∧
                  current.object.remainderSupport packing ⊂
                    delocalizationSupport data current.object packing
                      quotient) →
      delocalizedSupport.At current)
    (compressionFresh : atomCompression ∉ known)
    (delocalizedFresh : delocalizedSupport ∉ known) :
    Decision atomCompression delocalizedSupport previous :=
  Decision.run previous atomCompression delocalizedSupport
    `Hypostructure.Graph.Strategy.Spine.atomCompressionDichotomy
    (by
      classical
      -- The node's own question, as an excluded middle on its yes arm: is the
      -- determination certified without leaving `C`?
      -- Node `[36]`'s yes arm, read by exact key: the determination this node
      -- asks about is the target-complete one, which is what makes case (ii) a
      -- *target-complete* compression rather than a bare rank reduction.
      have complete := universalOf (ExactLedger.get previous contextUniversal)
      by_cases inside :
          ∃ packing : Finset (Finset current.object.Vertex),
            current.object.IsWindowPacking data.windowOrder packing ∧
              ∃ quotient : remainderQuotient data current.object packing,
                DeterminationCertificate data current.object packing quotient ∧
                  TargetCompleteAt data quotient ∧
                    quotient.support ⊆
                      current.object.remainderSupport packing
      · exact .inl (encodeCompression inside)
      · -- No: the certificate Branch D was entered with reaches outside `C`,
        -- so the support the determination needs strictly contains it.
        refine .inr (encodeDelocalized ?_)
        obtain ⟨packing, valid, quotient, certified, _minimalSupport⟩ :=
          certificateOf (ExactLedger.get previous branchDependence)
        have outside :
            ¬ quotient.support ⊆ current.object.remainderSupport packing :=
          fun contained =>
            inside ⟨packing, valid, quotient, certified,
              complete packing valid quotient, contained⟩
        exact ⟨packing, valid, quotient, certified,
          complete packing valid quotient, outside,
          remainderSupport_ssubset_delocalizationSupport data quotient
            outside⟩)
    compressionFresh delocalizedFresh

/-! ### Node `[41]`: is the enlarged support proper in `G`?

The yes arm is the terminal `[42]`, `lem:proper-smearing`: *"Regard `Z` as a
boundaried graph ... Since `Z ⊊ G`, it is a proper boundaried support.  If the
dependence fails against some outside `∂Z`-context, it is target-defective.  If
it succeeds against every outside context, it is a nontrivial target-complete
compression of the proper support `Z`, forbidden by `cor:uncompressible`."*  The
no arm is node `[43]`, whole-graph delocalization. -/
noncomputable def delocalizationScopeDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous :
      ExactLedger (Input BranchState Presentation presentation data)
        current known)
    (delocalizedSupport properDelocalization globalDelocalization :
      FactKey (Input BranchState Presentation presentation data))
    [Core.Residual.FactKeys.Has delocalizedSupport known]
    (supportOf : delocalizedSupport.At current →
      ∃ packing : Finset (Finset current.object.Vertex),
        current.object.IsWindowPacking data.windowOrder packing ∧
          ∃ quotient : remainderQuotient data current.object packing,
            DeterminationCertificate data current.object packing quotient ∧
              TargetCompleteAt data quotient ∧
                ¬ quotient.support ⊆
                    current.object.remainderSupport packing ∧
                  current.object.remainderSupport packing ⊂
                    delocalizationSupport data current.object packing
                      quotient)
    (encodeProper :
      (∃ packing : Finset (Finset current.object.Vertex),
        current.object.IsWindowPacking data.windowOrder packing ∧
          ∃ quotient : remainderQuotient data current.object packing,
            DeterminationCertificate data current.object packing quotient ∧
              TargetCompleteAt data quotient ∧
                ¬ quotient.support ⊆
                    current.object.remainderSupport packing ∧
                  ∃ vertex, vertex ∉ delocalizationSupport data current.object
                    packing quotient) →
      properDelocalization.At current)
    (encodeGlobal :
      (∃ packing : Finset (Finset current.object.Vertex),
        current.object.IsWindowPacking data.windowOrder packing ∧
          ∃ quotient : remainderQuotient data current.object packing,
            DeterminationCertificate data current.object packing quotient ∧
              TargetCompleteAt data quotient ∧
                ¬ quotient.support ⊆
                    current.object.remainderSupport packing ∧
                  ∀ vertex, vertex ∈ delocalizationSupport data current.object
                    packing quotient) →
      globalDelocalization.At current)
    (properFresh : properDelocalization ∉ known)
    (globalFresh : globalDelocalization ∉ known) :
    Decision properDelocalization globalDelocalization previous :=
  Decision.run previous properDelocalization globalDelocalization
    `Hypostructure.Graph.Strategy.Spine.delocalizationScopeDichotomy
    (by
      classical
      -- The node's own question, as an excluded middle on its yes arm: is the
      -- enlarged support still proper in `G`?
      by_cases proper :
          ∃ packing : Finset (Finset current.object.Vertex),
            current.object.IsWindowPacking data.windowOrder packing ∧
              ∃ quotient : remainderQuotient data current.object packing,
                DeterminationCertificate data current.object packing quotient ∧
                  TargetCompleteAt data quotient ∧
                    ¬ quotient.support ⊆
                        current.object.remainderSupport packing ∧
                      ∃ vertex, vertex ∉ delocalizationSupport data
                        current.object packing quotient
      · exact .inl (encodeProper proper)
      · -- No: the support covers every vertex, so the dependence delocalizes to
        -- the whole graph.
        refine .inr (encodeGlobal ?_)
        obtain ⟨packing, valid, quotient, certified, complete, outside,
          _strict⟩ := supportOf (ExactLedger.get previous delocalizedSupport)
        refine ⟨packing, valid, quotient, certified, complete, outside,
          fun vertex => ?_⟩
        by_contra absent
        exact proper ⟨packing, valid, quotient, certified, complete, outside,
          vertex, absent⟩)
    properFresh globalFresh

/-! ### Nodes `[44]` and `[45]`: the repair identity and the global barrier

`[44]` is `lem:smearing-support-repair`: a delayed compensation component with
`p` boundary leaves, `s` internal vertices, cycle rank `β` and surplus `σ`
satisfies `s = p − 2 + 2β − σ`.  The manuscript proves it from the handshake
identity and the cycle-rank formula, which is exactly
`Graph.OneThreeRepair.Component.identity`.

`[45]` is the barrier `lem:no-silent-global-smearing` raises against a
whole-graph dependence: the closed clause of `def:admissible-rank-quotient`
leaves a rank-reducing quotient either representable by a proper-support
replacement or by a strictly smaller admissible closed representative, and
`Graph.CurvatureQuotient.localize` is that split. -/
@[reducible] noncomputable def globalBarrierRow
    (globalDelocalization repairIdentity globalBarrier :
      FactKey (Input BranchState Presentation presentation data))
    (identityFresh : repairIdentity ≠ globalDelocalization)
    (barrierFresh : globalBarrier ≠ globalDelocalization)
    (distinct : repairIdentity ≠ globalBarrier)
    (globalOf : (input : Input BranchState Presentation presentation data) →
      globalDelocalization.At input →
      ∃ packing : Finset (Finset input.object.Vertex),
        input.object.IsWindowPacking data.windowOrder packing ∧
          ∃ quotient : remainderQuotient data input.object packing,
            DeterminationCertificate data input.object packing quotient ∧
              TargetCompleteAt data quotient ∧
                ¬ quotient.support ⊆ input.object.remainderSupport packing ∧
                  ∀ vertex, vertex ∈
                    delocalizationSupport data input.object packing quotient)
    (encodeIdentity : (input : Input BranchState Presentation presentation data) →
      (∀ component : Graph.OneThreeRepair.Component.{u},
        (component.internal.card : Int) =
          component.boundary.card - 2 + 2 * component.cycleRank -
            component.surplus) →
      repairIdentity.At input)
    (encodeBarrier : (input : Input BranchState Presentation presentation data) →
      (∃ packing : Finset (Finset input.object.Vertex),
        input.object.IsWindowPacking data.windowOrder packing ∧
          ∃ quotient : remainderQuotient data input.object packing,
            DeterminationCertificate data input.object packing quotient ∧
              (Graph.Strategy.InterfaceReplacement.ReplacementSupport
                  (Graph.MinimumDegreeAtLeast data.threshold)
                  (Graph.HasCycleWithLength data.LengthOK) input.object
                  quotient.support ∨
                ∃ representative : Graph.FiniteObject.{u},
                  representative.LexicographicallySmaller input.object ∧
                    Graph.MinimumDegreeAtLeast data.threshold representative ∧
                      (Graph.HasCycleWithLength data.LengthOK representative →
                        Graph.HasCycleWithLength data.LengthOK
                          input.object))) →
      globalBarrier.At input) :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.globalBarrier
    (pairManifest globalDelocalization repairIdentity globalBarrier
      identityFresh barrierFresh distinct)
    (fun inputs =>
      .cons (key := repairIdentity)
        (encodeIdentity inputs.current fun component => component.identity)
        (.cons (key := globalBarrier)
          (encodeBarrier inputs.current (by
            obtain ⟨packing, valid, quotient, certified, _complete, _outside,
              _covers⟩ :=
              globalOf inputs.current (inputs.get globalDelocalization)
            exact ⟨packing, valid, quotient, certified,
              Graph.CurvatureQuotient.localize quotient certified.1⟩))
          .nil))

/-- **The terminals `[39]`, `[42]` and `[46]` are all closed.**

Each of the three names a determination certificate on the selected object, and
`not_determinationCertificate` refutes every one of them: `cor:uncompressible`
kills the proper-support readings and the selection's own minimality kills the
closed representative.  The three differ in *which* support the manuscript says
is being compressed -- `C` at `[39]`, the enlarged `Z ⊊ G` at `[42]`, and `G`
itself at `[46]` -- which is why they are three terminals and not one. -/
theorem not_branchDCertificate
    (object : Graph.FiniteObject.{u})
    (baseline : Graph.MinimumDegreeAtLeast data.threshold object)
    (state : BranchState object)
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (minimal : ∀ smaller : Graph.FiniteObject.{u},
      (progress BranchState Presentation presentation data).Smaller
        smaller object →
      Graph.MinimumDegreeAtLeast data.threshold smaller →
      Graph.HasCycleWithLength data.LengthOK smaller)
    (certificate : ∃ packing : Finset (Finset object.Vertex),
      object.IsWindowPacking data.windowOrder packing ∧
        ∃ quotient : remainderQuotient data object packing,
          DeterminationCertificate data object packing quotient) :
    False := by
  obtain ⟨_packing, _valid, quotient, certified⟩ := certificate
  exact not_determinationCertificate baseline state avoids minimal certified

/-! ## Nodes `[47]`--`[48]`: the forced curvature cost

`cor:forced-curvature-cost`, whose entire proof is "this follows from
`lem:full-rank`, `lem:wedge-lower` and the definitions of `K_win` and `K`".
Both are already ledger facts on this branch: node `[30]`'s demand floor is the
`lem:wedge-lower` half with node `[29]`'s exact ceiling already substituted, and
node `[34]`'s full-rank residual is the `lem:full-rank` half.  The row does the
manuscript's substitution -- the rank replaces the wedge supply it is at most an
allowance below -- and applies the registered cost to both sides.

The registered cost is the *only* thing this row reads that is not on the
branch, and `rem:closure-robust` records that the closure outside the explicit
residuals holds for every nonnegative value of it. -/
@[reducible] noncomputable def forcedCurvatureCostRow
    (curvatureDemandFloor curvatureFullRank forcedCurvatureCost :
      FactKey (Input BranchState Presentation presentation data))
    (distinctRequired : curvatureDemandFloor ≠ curvatureFullRank)
    (floorOf : (input : Input BranchState Presentation presentation data) →
      curvatureDemandFloor.At input →
      ∀ packing : Finset (Finset input.object.Vertex),
        input.object.IsWindowPacking data.windowOrder packing →
        data.threshold * (input.object.remainderSupport packing).card +
              2 * (2 * (data.windowOrder - 1) * packing.card) ≤
            input.object.internalWedgeCount
                (input.object.remainderSupport packing) +
              2 * (data.threshold * (data.windowOrder * packing.card) +
                input.object.ambientSurplus
                  (Graph.FiniteObject.windowSupport packing) data.threshold))
    (rankOf : (input : Input BranchState Presentation presentation data) →
      curvatureFullRank.At input →
      ∀ packing : Finset (Finset input.object.Vertex),
        input.object.IsWindowPacking data.windowOrder packing →
        remainderWedgeSupply input.object packing -
            data.rankDefect (remainderWedgeSupply input.object packing) ≤
          remainderCurvatureTargetRank data input.object packing)
    (encode : (input : Input BranchState Presentation presentation data) →
      (∀ packing : Finset (Finset input.object.Vertex),
        input.object.IsWindowPacking data.windowOrder packing →
        data.curvatureCost *
              (data.threshold * (input.object.remainderSupport packing).card +
                2 * (2 * (data.windowOrder - 1) * packing.card)) ≤
            data.curvatureCost *
                (remainderCurvatureTargetRank data input.object packing +
                  data.rankDefect (remainderWedgeSupply input.object packing)) +
              data.curvatureCost *
                (2 * (data.threshold * (data.windowOrder * packing.card) +
                  input.object.ambientSurplus
                    (Graph.FiniteObject.windowSupport packing)
                    data.threshold))) →
      forcedCurvatureCost.At input) :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.forcedCurvatureCost
    { Requires := [curvatureDemandFloor, curvatureFullRank]
      Produces := [forcedCurvatureCost]
      requiresUnique := by simp [distinctRequired]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := forcedCurvatureCost)
        (encode inputs.current fun packing valid => by
          have floor :=
            floorOf inputs.current (inputs.get curvatureDemandFloor) packing valid
          -- `W₂(R) ≤ r_Ω(R) + o(W₂)`: the full-rank residual, moved across.
          have supply :
              remainderWedgeSupply inputs.current.object packing ≤
                remainderCurvatureTargetRank data inputs.current.object packing +
                  data.rankDefect
                    (remainderWedgeSupply inputs.current.object packing) :=
            Nat.sub_le_iff_le_add.mp
              (rankOf inputs.current (inputs.get curvatureFullRank) packing valid)
          calc data.curvatureCost *
                (data.threshold *
                    (inputs.current.object.remainderSupport packing).card +
                  2 * (2 * (data.windowOrder - 1) * packing.card))
              ≤ data.curvatureCost *
                  ((remainderCurvatureTargetRank data inputs.current.object
                        packing +
                      data.rankDefect
                        (remainderWedgeSupply inputs.current.object packing)) +
                    2 * (data.threshold * (data.windowOrder * packing.card) +
                      inputs.current.object.ambientSurplus
                        (Graph.FiniteObject.windowSupport packing)
                        data.threshold)) :=
                Nat.mul_le_mul_left _
                  (le_trans floor (Nat.add_le_add_right supply _))
            _ = _ := by ring)
        .nil)

/-! ## Nodes `[49]`--`[50]`: the per-vertex remainder entropy split

`def:remainder-entropy` and the decision `prop:two-budget` opens with.  `𝒢(R)`
is the labelled class carrying the constraints node `[27]` has already imposed,
and `η(R) = log₂|𝒢(R)|/|R|`; the split asks `η(R) ≥ (1/d)·log₂ n`.

Exponentiating both sides by `d·|R|` turns that into `n^{|R|} ≤ |𝒢(R)|^d`, an
integer comparison, so no logarithm, division, or rounding is written.  The two
arms are the two halves of one excluded middle, so they are exhaustive and
mutually exclusive by construction, and the arm not taken is absent from the
taken branch's key index. -/
noncomputable def remainderEntropyDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous :
      ExactLedger (Input BranchState Presentation presentation data)
        current known)
    (remainderEntropyHigh remainderEntropyLow :
      FactKey (Input BranchState Presentation presentation data))
    (encodeHigh :
      (∀ packing : Finset (Finset current.object.Vertex),
        current.object.IsWindowPacking data.windowOrder packing →
        Graph.AtLeastEntropyRate current.object.vertexCount
          data.entropyDenominator data.windowOrder data.threshold
          (current.object.remainderSupport packing).card) →
      remainderEntropyHigh.At current)
    (encodeLow :
      (∃ packing : Finset (Finset current.object.Vertex),
        current.object.IsWindowPacking data.windowOrder packing ∧
          Graph.BelowEntropyRate current.object.vertexCount
            data.entropyDenominator data.windowOrder data.threshold
            (current.object.remainderSupport packing).card) →
      remainderEntropyLow.At current)
    (highFresh : remainderEntropyHigh ∉ known)
    (lowFresh : remainderEntropyLow ∉ known) :
    Decision remainderEntropyHigh remainderEntropyLow previous :=
  Decision.run previous remainderEntropyHigh remainderEntropyLow
    `Hypostructure.Graph.Strategy.Spine.remainderEntropyDichotomy
    (by
      classical
      by_cases high :
          ∀ packing : Finset (Finset current.object.Vertex),
            current.object.IsWindowPacking data.windowOrder packing →
            Graph.AtLeastEntropyRate current.object.vertexCount
              data.entropyDenominator data.windowOrder data.threshold
              (current.object.remainderSupport packing).card
      · exact .inl (encodeHigh high)
      · refine .inr (encodeLow ?_)
        push Not at high
        obtain ⟨packing, valid, below⟩ := high
        exact ⟨packing, valid,
          (Graph.not_atLeastEntropyRate_iff _ _ _ _ _).mp below⟩)
    highFresh lowFresh

/-! ## Node `[52]`: window plus remainder accounting

`prop:two-budget` (a) and the high-entropy half of `prop:p13-density`.  The
window package of node `[21]`, the remainder states of node `[51]`, and the
forced curvature coordinates of node `[48]` are one target-testable family, and
`eq:feasibility` compares the states it realizes against the near-cubic
skeleton budget.

This row commits the *demand* side of that comparison, exactly: raising the
joint demand to the `d`-th power clears the `1/d` the entropy split carries, and
substituting the high-entropy arm's own `n^{|R|} ≤ |𝒢(R)|^d` for the remainder
factor gives the manuscript's `2^{rate·p}·n^{|R|/d}·2^{c_Ω·r_Ω(R)}`.  No
independence hypothesis is used to state a lower bound on what the branch has to
distinguish; the budget side is node `[53]`'s comparison. -/
@[reducible] noncomputable def entropyPackageRow
    (remainderEntropyHigh entropyPackageDemand :
      FactKey (Input BranchState Presentation presentation data))
    (distinct : remainderEntropyHigh ≠ entropyPackageDemand)
    (highOf : (input : Input BranchState Presentation presentation data) →
      remainderEntropyHigh.At input →
      ∀ packing : Finset (Finset input.object.Vertex),
        input.object.IsWindowPacking data.windowOrder packing →
        Graph.AtLeastEntropyRate input.object.vertexCount
          data.entropyDenominator data.windowOrder data.threshold
          (input.object.remainderSupport packing).card)
    (encode : (input : Input BranchState Presentation presentation data) →
      (∀ packing : Finset (Finset input.object.Vertex),
        input.object.IsWindowPacking data.windowOrder packing →
        (2 ^ (data.windowRate * Graph.dyadicScaleCount input.object *
              packing.card)) ^ data.entropyDenominator *
              input.object.vertexCount ^
                (input.object.remainderSupport packing).card *
              (2 ^ (data.curvatureCost *
                remainderCurvatureTargetRank data input.object packing)) ^
                data.entropyDenominator ≤
            jointPackageDemand data input.object packing ^
              data.entropyDenominator) →
      entropyPackageDemand.At input) :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.entropyPackageDemand
    (rowManifest remainderEntropyHigh entropyPackageDemand distinct)
    (fun inputs =>
      .cons (key := entropyPackageDemand)
        (encode inputs.current fun packing valid => by
          have high :=
            highOf inputs.current (inputs.get remainderEntropyHigh) packing valid
          rw [jointPackageDemand, mul_pow, mul_pow]
          exact Nat.mul_le_mul (Nat.mul_le_mul (le_refl _) high) (le_refl _))
        .nil)

/-! ## Node `[53]`: the admissible entropy cap, and its terminal `[54]`

`eq:entropy-cap`: no residual graph exists once the remaining non-curvature
budget is strictly smaller than the forced curvature cost.  In exact integer
form that is the joint package demand of node `[52]` against the labelled
skeleton budget of `lem:near-cubic-budget`, which is the same budget node
`[21]` already compared the window package against.

The comparison is a `Nat` trichotomy, so the two arms are exhaustive.  The yes
arm is the manuscript's node `[54]`; the no arm is node `[55]`, Residual C. -/
noncomputable def entropyCapDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous :
      ExactLedger (Input BranchState Presentation presentation data)
        current known)
    (entropyCapActive largeBudgetResidual :
      FactKey (Input BranchState Presentation presentation data))
    (encodeActive :
      (∀ packing : Finset (Finset current.object.Vertex),
        current.object.IsWindowPacking data.windowOrder packing →
        Graph.skeletonBudget current.object <
          jointPackageDemand data current.object packing) →
      entropyCapActive.At current)
    (encodeLarge :
      (∃ packing : Finset (Finset current.object.Vertex),
        current.object.IsWindowPacking data.windowOrder packing ∧
          jointPackageDemand data current.object packing ≤
            Graph.skeletonBudget current.object) →
      largeBudgetResidual.At current)
    (activeFresh : entropyCapActive ∉ known)
    (largeFresh : largeBudgetResidual ∉ known) :
    Decision entropyCapActive largeBudgetResidual previous :=
  Decision.run previous entropyCapActive largeBudgetResidual
    `Hypostructure.Graph.Strategy.Spine.entropyCapDichotomy
    (by
      classical
      by_cases active :
          ∀ packing : Finset (Finset current.object.Vertex),
            current.object.IsWindowPacking data.windowOrder packing →
            Graph.skeletonBudget current.object <
              jointPackageDemand data current.object packing
      · exact .inl (encodeActive active)
      · refine .inr (encodeLarge ?_)
        push Not at active
        obtain ⟨packing, valid, fits⟩ := active
        exact ⟨packing, valid, fits⟩)
    activeFresh largeFresh

/-! ## Node `[55]`: the registered order threshold

`prop:negative-net-charge` is stated "for all sufficiently large `n`", and
nodes `[55]`--`[56]` carry `+o(1)` on every display.  This diamond is that
quantifier, made explicit: the object's order is at or above the registered one,
or it is below it.

The comparison is a `Nat` trichotomy, so the arms are exhaustive, and both are
retained — the small-order arm is the finite residue the manuscript's asymptotic
statements do not address, and it leaves the block rather than being assumed
away.  Node `[19]` already registers its own `o(n)` threshold and retains both
arms of it in exactly this way. -/
noncomputable def orderThresholdDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous :
      ExactLedger (Input BranchState Presentation presentation data)
        current known)
    (largeOrderResidual smallOrderResidual :
      FactKey (Input BranchState Presentation presentation data))
    (encodeLarge :
      (2 ^ data.largeOrderExponent ≤ current.object.vertexCount) →
      largeOrderResidual.At current)
    (encodeSmall :
      (current.object.vertexCount < 2 ^ data.largeOrderExponent) →
      smallOrderResidual.At current)
    (largeFresh : largeOrderResidual ∉ known)
    (smallFresh : smallOrderResidual ∉ known) :
    Decision largeOrderResidual smallOrderResidual previous :=
  Decision.run previous largeOrderResidual smallOrderResidual
    `Hypostructure.Graph.Strategy.Spine.orderThresholdDichotomy
    (if large : 2 ^ data.largeOrderExponent ≤ current.object.vertexCount then
      .inl (encodeLarge large)
    else
      .inr (encodeSmall (Nat.lt_of_not_le large)))
    largeFresh smallFresh

/-! ## Node `[56]`: the large-budget net-deficiency cap

`Δ_net(R) = (def⁺(R) − σ_R)/|R| ≤ τ_win + o(1) < ¼`, which is the manuscript's
own chain: node `[29]`'s ceiling divided by `|R|` gives `Δ_net ≤ 15θ/(1 − 13θ)`,
node `[24]`'s cap gives `θ ≤ θ_win + o(1)`, and `rem:closure-robust` records
`15θ_win/(1 − 13θ_win) = τ_win = 0.22817486846… < ¼`.

Nothing is divided here.  Multiplying through by the registered discharge scale
`s` and by the packing's own density cap turns the chain into one integer
comparison, and eliminating the packing with `|R| + order·p = n` leaves the
manuscript's `A·p₁₃ + s·o(n) < n` with

  `A = s·(δ·order − 2(order−1)) + order`,

the `73` of `cor:global-window-join-pressure` at the manuscript's own values.
Below the quarter, `N₀(R) < 0` — so the *whole* remainder already carries
negative net charge, which is exactly why node `[60]` is a vacuous terminal.

The two numbers this needs beyond the branch are the presentation's own:
`netChargeRate` is `τ_win < ¼` cleared of denominators, and
`surplusThreshold_sublinear` is `σ(G) = o(n)` at the registered order.  Neither
mentions a graph. -/

/-- The collision, as arithmetic.  `R` is the registered rate cleared at the
order exponent, `M` its companion `A·(k+1)`, and `demand` the scaled packing.
Every variable is a bare `Nat`: this is the manuscript's division of
`lem:stub-positive`'s ceiling by `|R|`, performed as one multiplication. -/
private theorem collision_of_margin
    (M R threshold discharge allowance size demand : Nat)
    (ratePos : 0 < R)
    (bound : R * demand ≤ M * (threshold * size + allowance))
    (margin : M * threshold < R)
    (sublinear : (M + R * discharge) * allowance <
      (R - M * threshold) * size) :
    demand + discharge * allowance < size := by
  refine Nat.lt_of_mul_lt_mul_left (a := R) ?_
  have expand : M * (threshold * size + allowance) =
      M * threshold * size + M * allowance := by ring
  have subMul : (R - M * threshold) * size + M * threshold * size =
      R * size := by
    rw [← Nat.add_mul]
    congr 1
    omega
  have regroup : (M + R * discharge) * allowance =
      M * allowance + R * discharge * allowance := by ring
  have lhs : R * (demand + discharge * allowance) =
      R * demand + R * discharge * allowance := by ring
  rw [expand] at bound
  rw [regroup] at sublinear
  rw [lhs]
  omega

@[reducible] noncomputable def netDeficiencyCapRow
    (maximalPacking stubSupply densityCap largeOrderResidual netDeficiencyCap :
      FactKey (Input BranchState Presentation presentation data))
    (packingSupply : maximalPacking ≠ stubSupply)
    (packingDensity : maximalPacking ≠ densityCap)
    (packingOrder : maximalPacking ≠ largeOrderResidual)
    (supplyDensity : stubSupply ≠ densityCap)
    (supplyOrder : stubSupply ≠ largeOrderResidual)
    (densityOrder : densityCap ≠ largeOrderResidual)
    (packingOf : (input : Input BranchState Presentation presentation data) →
      maximalPacking.At input →
      ∃ packing : Finset (Finset input.object.Vertex),
        input.object.IsWindowPacking data.windowOrder packing ∧
          packing.card = input.object.windowPackingNumber data.windowOrder)
    (supplyOf : (input : Input BranchState Presentation presentation data) →
      stubSupply.At input →
      ∀ packing : Finset (Finset input.object.Vertex),
        input.object.IsWindowPacking data.windowOrder packing →
        input.object.positiveDeficiency
              (input.object.remainderSupport packing) data.threshold +
            2 * (data.windowOrder - 1) * packing.card ≤
          data.threshold * (data.windowOrder * packing.card) +
            data.surplusThreshold input.object.vertexCount)
    (densityOf : (input : Input BranchState Presentation presentation data) →
      densityCap.At input →
      2 * (data.windowRate * Graph.dyadicScaleCount input.object *
          input.object.windowPackingNumber data.windowOrder) ≤
        (Graph.dyadicScaleCount input.object + 1) *
          (data.threshold * input.object.vertexCount +
            data.surplusThreshold input.object.vertexCount))
    (orderOf : (input : Input BranchState Presentation presentation data) →
      largeOrderResidual.At input →
      2 ^ data.largeOrderExponent ≤ input.object.vertexCount)
    (encode : (input : Input BranchState Presentation presentation data) →
      (∃ packing : Finset (Finset input.object.Vertex),
        input.object.IsWindowPacking data.windowOrder packing ∧
          input.object.NegativeNetCharge
            (input.object.remainderSupport packing) data.threshold
            data.dischargeScale) →
      netDeficiencyCap.At input) :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.netDeficiencyCap
    { Requires := [maximalPacking, stubSupply, densityCap, largeOrderResidual]
      Produces := [netDeficiencyCap]
      requiresUnique := by
        simp [packingSupply, packingDensity, packingOrder, supplyDensity,
          supplyOrder, densityOrder]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := netDeficiencyCap)
        (encode inputs.current (by
          classical
          obtain ⟨packing, valid, attains⟩ :=
            packingOf inputs.current (inputs.get maximalPacking)
          refine ⟨packing, valid, ?_⟩
          have large := orderOf inputs.current (inputs.get largeOrderResidual)
          have density := densityOf inputs.current (inputs.get densityCap)
          have stub :=
            supplyOf inputs.current (inputs.get stubSupply) packing valid
          have spread := inputs.current.object.remainderSupport_card_add_eq valid
          -- The registered order exponent lies below the object's own dyadic
          -- scale count, so node `[24]`'s `(scaleCount + 1)/scaleCount` slack is
          -- bounded by the registered `(k + 1)/k`.
          have scaleBound :
              data.largeOrderExponent ≤
                Graph.dyadicScaleCount inputs.current.object := by
            have monotone := Nat.log_mono_right (b := 2) large
            rw [Nat.log_pow (by norm_num)] at monotone
            simpa [Graph.dyadicScaleCount, Nat.log2_eq_log_two] using monotone
          have scalesPos :
              0 < Graph.dyadicScaleCount inputs.current.object :=
            Nat.lt_of_lt_of_le data.largeOrderExponent_pos scaleBound
          have ratePos : 0 < 2 * data.windowRate * data.largeOrderExponent := by
            have := data.netChargeRate
            omega
          -- Node `[24]`, with the slack cleared at the registered exponent.
          have cleared :
              (2 * data.windowRate * data.largeOrderExponent) *
                  inputs.current.object.windowPackingNumber data.windowOrder ≤
                (data.largeOrderExponent + 1) *
                  (data.threshold * inputs.current.object.vertexCount +
                    data.surplusThreshold inputs.current.object.vertexCount) := by
            refine Nat.le_of_mul_le_mul_left ?_ scalesPos
            have slack :
                data.largeOrderExponent *
                    (Graph.dyadicScaleCount inputs.current.object + 1) ≤
                  (data.largeOrderExponent + 1) *
                    Graph.dyadicScaleCount inputs.current.object := by
              calc data.largeOrderExponent *
                    (Graph.dyadicScaleCount inputs.current.object + 1)
                  = data.largeOrderExponent *
                      Graph.dyadicScaleCount inputs.current.object +
                    data.largeOrderExponent := by ring
                _ ≤ data.largeOrderExponent *
                      Graph.dyadicScaleCount inputs.current.object +
                    Graph.dyadicScaleCount inputs.current.object :=
                    Nat.add_le_add_left scaleBound _
                _ = (data.largeOrderExponent + 1) *
                      Graph.dyadicScaleCount inputs.current.object := by ring
            calc Graph.dyadicScaleCount inputs.current.object *
                  ((2 * data.windowRate * data.largeOrderExponent) *
                    inputs.current.object.windowPackingNumber data.windowOrder)
                = data.largeOrderExponent *
                    (2 * (data.windowRate *
                      Graph.dyadicScaleCount inputs.current.object *
                      inputs.current.object.windowPackingNumber
                        data.windowOrder)) := by ring
              _ ≤ data.largeOrderExponent *
                    ((Graph.dyadicScaleCount inputs.current.object + 1) *
                      (data.threshold * inputs.current.object.vertexCount +
                        data.surplusThreshold
                          inputs.current.object.vertexCount)) :=
                  Nat.mul_le_mul_left _ density
              _ = (data.largeOrderExponent *
                    (Graph.dyadicScaleCount inputs.current.object + 1)) *
                    (data.threshold * inputs.current.object.vertexCount +
                      data.surplusThreshold inputs.current.object.vertexCount) :=
                  by ring
              _ ≤ ((data.largeOrderExponent + 1) *
                    Graph.dyadicScaleCount inputs.current.object) *
                    (data.threshold * inputs.current.object.vertexCount +
                      data.surplusThreshold inputs.current.object.vertexCount) :=
                  Nat.mul_le_mul_right _ slack
              _ = Graph.dyadicScaleCount inputs.current.object *
                    ((data.largeOrderExponent + 1) *
                      (data.threshold * inputs.current.object.vertexCount +
                        data.surplusThreshold
                          inputs.current.object.vertexCount)) := by ring
          -- The manuscript's `A·p₁₃ + s·o(n) < n`.
          have collision :
              (data.dischargeScale *
                    (data.threshold * data.windowOrder -
                      2 * (data.windowOrder - 1)) + data.windowOrder) *
                  inputs.current.object.windowPackingNumber data.windowOrder +
                data.dischargeScale *
                  data.surplusThreshold inputs.current.object.vertexCount <
              inputs.current.object.vertexCount := by
            refine collision_of_margin
              ((data.dischargeScale *
                  (data.threshold * data.windowOrder -
                    2 * (data.windowOrder - 1)) + data.windowOrder) *
                (data.largeOrderExponent + 1))
              (2 * data.windowRate * data.largeOrderExponent)
              data.threshold data.dischargeScale
              (data.surplusThreshold inputs.current.object.vertexCount)
              inputs.current.object.vertexCount _ ratePos ?_
              data.netChargeRate
              (data.surplusThreshold_sublinear _ large)
            calc (2 * data.windowRate * data.largeOrderExponent) *
                  ((data.dischargeScale *
                      (data.threshold * data.windowOrder -
                        2 * (data.windowOrder - 1)) + data.windowOrder) *
                    inputs.current.object.windowPackingNumber data.windowOrder)
                = (data.dischargeScale *
                      (data.threshold * data.windowOrder -
                        2 * (data.windowOrder - 1)) + data.windowOrder) *
                    ((2 * data.windowRate * data.largeOrderExponent) *
                      inputs.current.object.windowPackingNumber
                        data.windowOrder) := by ring
              _ ≤ (data.dischargeScale *
                      (data.threshold * data.windowOrder -
                        2 * (data.windowOrder - 1)) + data.windowOrder) *
                    ((data.largeOrderExponent + 1) *
                      (data.threshold * inputs.current.object.vertexCount +
                        data.surplusThreshold
                          inputs.current.object.vertexCount)) :=
                  Nat.mul_le_mul_left _ cleared
              _ = ((data.dischargeScale *
                      (data.threshold * data.windowOrder -
                        2 * (data.windowOrder - 1)) + data.windowOrder) *
                    (data.largeOrderExponent + 1)) *
                    (data.threshold * inputs.current.object.vertexCount +
                      data.surplusThreshold inputs.current.object.vertexCount) :=
                  by ring
          -- Node `[29]`'s ceiling at the attaining packing, scaled, with the
          -- coefficient's truncated subtraction cleared.
          have scaledStub := Nat.mul_le_mul_left (k := data.dischargeScale) stub
          rw [Nat.mul_add, Nat.mul_add] at scaledStub
          have twoLe :
              2 * (data.windowOrder - 1) ≤ data.threshold * data.windowOrder := by
            have dominates : 3 * data.windowOrder ≤
                data.threshold * data.windowOrder :=
              Nat.mul_le_mul_right _ data.three_le_threshold
            have positive := data.windowOrder_pos
            omega
          have split :
              (data.dischargeScale *
                    (data.threshold * data.windowOrder -
                      2 * (data.windowOrder - 1)) + data.windowOrder) *
                  packing.card +
                data.dischargeScale *
                  (2 * (data.windowOrder - 1) * packing.card) =
              data.dischargeScale *
                  (data.threshold * (data.windowOrder * packing.card)) +
                data.windowOrder * packing.card := by
            have restore :
                data.threshold * data.windowOrder -
                    2 * (data.windowOrder - 1) + 2 * (data.windowOrder - 1) =
                  data.threshold * data.windowOrder := by omega
            calc (data.dischargeScale *
                    (data.threshold * data.windowOrder -
                      2 * (data.windowOrder - 1)) + data.windowOrder) *
                  packing.card +
                data.dischargeScale *
                  (2 * (data.windowOrder - 1) * packing.card)
                = data.dischargeScale *
                    (data.threshold * data.windowOrder -
                      2 * (data.windowOrder - 1) +
                      2 * (data.windowOrder - 1)) * packing.card +
                  data.windowOrder * packing.card := by ring
              _ = data.dischargeScale * (data.threshold * data.windowOrder) *
                    packing.card + data.windowOrder * packing.card := by
                  rw [restore]
              _ = data.dischargeScale *
                    (data.threshold * (data.windowOrder * packing.card)) +
                  data.windowOrder * packing.card := by ring
          -- The collision is stated at the packing number; the attaining
          -- packing is the one the ceiling was read at.
          rw [← attains] at collision
          rw [Graph.FiniteObject.NegativeNetCharge]
          omega))
        .nil)

/-! ## Nodes `[57]`--`[58]`: net charge and its localization

`def:net-charge` measures an admissible support by
`N₀(X) = def⁺(X) − σ(X) − |V(X)|/s`, and `lem:netcharge-superadd` says the
canonical decomposition of `def:canonical-decomp` is *exact* on all three of the
quantities it is built from: the vertex counts and the assigned surplus add
because the connected components partition the region, and the positive
deficiencies add because a component is a component, so `d_{X_i}(u) = d_R(u)`.

The consequence the manuscript draws, and the only one consumed, is that a
region of negative total charge has a *connected* piece of negative charge.
`Graph.FiniteObject.exists_connected_negativeNetCharge` is exactly that
argument.  It uses no branch fact -- the decomposition is available at every
region of every object -- so this row's manifest requires nothing and its
position in the run is fixed by the ledger index rather than by a manufactured
prerequisite. -/
@[reducible] noncomputable def netChargeLocalizationRow
    (netChargeLocalization :
      FactKey (Input BranchState Presentation presentation data))
    (encode : (input : Input BranchState Presentation presentation data) →
      (∀ packing : Finset (Finset input.object.Vertex),
        input.object.IsWindowPacking data.windowOrder packing →
        input.object.NegativeNetCharge
            (input.object.remainderSupport packing) data.threshold
            data.dischargeScale →
          ∃ piece : Finset input.object.Vertex,
            piece ⊆ input.object.remainderSupport packing ∧
              Graph.SupportComponents.Connected.ConnectedOn input.object piece ∧
              input.object.NegativeNetCharge piece data.threshold
                data.dischargeScale) →
      netChargeLocalization.At input) :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.netChargeLocalization
    { Requires := []
      Produces := [netChargeLocalization]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := netChargeLocalization)
        (encode inputs.current fun packing _valid negative =>
          inputs.current.object.exists_connected_negativeNetCharge
            (inputs.current.object.remainderSupport packing) data.threshold
            data.dischargeScale negative)
        .nil)

/-! ## Node `[59]`: the net-charge sign test

`N₀(R) ≥ 0?`  The yes arm is the manuscript's node `[60]`, the net-cap
contradiction; the no arm is node `[61]`, where a connected negative support is
selected.  Both sides are the two halves of one excluded middle on the exact
integer comparison `def:net-charge` reduces to, so they are exhaustive. -/
noncomputable def netChargeDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous :
      ExactLedger (Input BranchState Presentation presentation data)
        current known)
    (netChargeNonNegative netChargeNegative :
      FactKey (Input BranchState Presentation presentation data))
    (encodeNonNegative :
      (∀ packing : Finset (Finset current.object.Vertex),
        current.object.IsWindowPacking data.windowOrder packing →
        current.object.NonNegativeNetCharge
          (current.object.remainderSupport packing) data.threshold
          data.dischargeScale) →
      netChargeNonNegative.At current)
    (encodeNegative :
      (∃ packing : Finset (Finset current.object.Vertex),
        current.object.IsWindowPacking data.windowOrder packing ∧
          current.object.NegativeNetCharge
            (current.object.remainderSupport packing) data.threshold
            data.dischargeScale) →
      netChargeNegative.At current)
    (nonNegativeFresh : netChargeNonNegative ∉ known)
    (negativeFresh : netChargeNegative ∉ known) :
    Decision netChargeNonNegative netChargeNegative previous :=
  Decision.run previous netChargeNonNegative netChargeNegative
    `Hypostructure.Graph.Strategy.Spine.netChargeDichotomy
    (by
      classical
      by_cases nonNegative :
          ∀ packing : Finset (Finset current.object.Vertex),
            current.object.IsWindowPacking data.windowOrder packing →
            current.object.NonNegativeNetCharge
              (current.object.remainderSupport packing) data.threshold
              data.dischargeScale
      · exact .inl (encodeNonNegative nonNegative)
      · refine .inr (encodeNegative ?_)
        push Not at nonNegative
        obtain ⟨packing, valid, negative⟩ := nonNegative
        exact ⟨packing, valid, Nat.lt_of_not_le negative⟩)
    nonNegativeFresh negativeFresh

/-! ## Node `[60]`: global window-join pressure

`cor:global-window-join-pressure`.  On the arm where every connected admissible
support has nonnegative charge, so does the whole remainder; substituting
`lem:surplus-aware-window-stub`'s two links -- the demand link `def⁺(R) ≤ e(R,W)`
and the capacity link `e(R,W) + 2(order−1)p ≤ δ·order·p + σ_W` -- and
eliminating the packing with `|R| + order·p = n` leaves

  `n + s·σ_R + s·2(order−1)p ≤ s·δ·order·p + s·σ_W + order·p`,

which at the manuscript's registered values is `σ_W − σ_R ≥ (n − 73p₁₃)/4`.
`rem:window-join-pressure-meaning` reads it back: avoiding a negative support
requires a linear excess of window surplus over remainder surplus. -/
@[reducible] noncomputable def windowJoinPressureRow
    (netChargeNonNegative boundaryDemand windowJoinPressure :
      FactKey (Input BranchState Presentation presentation data))
    (distinctRequired : netChargeNonNegative ≠ boundaryDemand)
    (chargeOf : (input : Input BranchState Presentation presentation data) →
      netChargeNonNegative.At input →
      ∀ packing : Finset (Finset input.object.Vertex),
        input.object.IsWindowPacking data.windowOrder packing →
        input.object.NonNegativeNetCharge
          (input.object.remainderSupport packing) data.threshold
          data.dischargeScale)
    (demandOf : (input : Input BranchState Presentation presentation data) →
      boundaryDemand.At input →
      ∀ packing : Finset (Finset input.object.Vertex),
        input.object.IsWindowPacking data.windowOrder packing →
        input.object.positiveDeficiency
              (input.object.remainderSupport packing) data.threshold ≤
            input.object.boundaryIncidence
              (input.object.remainderSupport packing) ∧
          input.object.boundaryIncidence
                (input.object.remainderSupport packing) +
              2 * (data.windowOrder - 1) * packing.card ≤
            data.threshold * (data.windowOrder * packing.card) +
              input.object.ambientSurplus
                (Graph.FiniteObject.windowSupport packing) data.threshold)
    (encode : (input : Input BranchState Presentation presentation data) →
      (∀ packing : Finset (Finset input.object.Vertex),
        input.object.IsWindowPacking data.windowOrder packing →
        input.object.vertexCount +
              data.dischargeScale *
                input.object.ambientSurplus
                  (input.object.remainderSupport packing) data.threshold +
              data.dischargeScale *
                (2 * (data.windowOrder - 1) * packing.card) ≤
            data.dischargeScale *
                (data.threshold * (data.windowOrder * packing.card)) +
              data.dischargeScale *
                input.object.ambientSurplus
                  (Graph.FiniteObject.windowSupport packing) data.threshold +
              data.windowOrder * packing.card) →
      windowJoinPressure.At input) :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.windowJoinPressure
    { Requires := [netChargeNonNegative, boundaryDemand]
      Produces := [windowJoinPressure]
      requiresUnique := by simp [distinctRequired]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := windowJoinPressure)
        (encode inputs.current fun packing valid => by
          obtain ⟨demand, capacity⟩ :=
            demandOf inputs.current (inputs.get boundaryDemand) packing valid
          -- The two links of `lem:surplus-aware-window-stub`, composed.
          have chain :
              inputs.current.object.positiveDeficiency
                    (inputs.current.object.remainderSupport packing)
                    data.threshold +
                  2 * (data.windowOrder - 1) * packing.card ≤
                data.threshold * (data.windowOrder * packing.card) +
                  inputs.current.object.ambientSurplus
                    (Graph.FiniteObject.windowSupport packing) data.threshold :=
            le_trans (Nat.add_le_add_right demand _) capacity
          have scaled := Nat.mul_le_mul_left (k := data.dischargeScale) chain
          rw [Nat.mul_add, Nat.mul_add] at scaled
          have charge :=
            chargeOf inputs.current (inputs.get netChargeNonNegative) packing
              valid
          rw [Graph.FiniteObject.NonNegativeNetCharge] at charge
          have order :=
            inputs.current.object.remainderSupport_card_add_eq valid
          omega)
        .nil)

/-! ## Node `[61]`: the selected connected negative support

`prop:negative-net-charge`.  The negative arm of node `[59]` and the
localization of node `[58]` compose to a connected admissible support of
negative net charge.

The support itself is data and cannot travel: what the ledger records is its
existence, together with the two clauses of `def:admissible` the decomposition
supplies -- that it is a connected piece of the remainder, and that its charge
is negative.  Every other clause of `def:admissible` is inherited from the
remainder by node `[27]`, which holds at every subregion, so none has to be
carried here. -/
@[reducible] noncomputable def negativeSupportRow
    (netChargeNegative netChargeLocalization negativeSupport :
      FactKey (Input BranchState Presentation presentation data))
    (distinctRequired : netChargeNegative ≠ netChargeLocalization)
    (negativeOf : (input : Input BranchState Presentation presentation data) →
      netChargeNegative.At input →
      ∃ packing : Finset (Finset input.object.Vertex),
        input.object.IsWindowPacking data.windowOrder packing ∧
          input.object.NegativeNetCharge
            (input.object.remainderSupport packing) data.threshold
            data.dischargeScale)
    (localizeOf : (input : Input BranchState Presentation presentation data) →
      netChargeLocalization.At input →
      ∀ packing : Finset (Finset input.object.Vertex),
        input.object.IsWindowPacking data.windowOrder packing →
        input.object.NegativeNetCharge
            (input.object.remainderSupport packing) data.threshold
            data.dischargeScale →
          ∃ piece : Finset input.object.Vertex,
            piece ⊆ input.object.remainderSupport packing ∧
              Graph.SupportComponents.Connected.ConnectedOn input.object piece ∧
              input.object.NegativeNetCharge piece data.threshold
                data.dischargeScale)
    (encode : (input : Input BranchState Presentation presentation data) →
      (∃ packing : Finset (Finset input.object.Vertex),
        input.object.IsWindowPacking data.windowOrder packing ∧
          ∃ piece : Finset input.object.Vertex,
            piece ⊆ input.object.remainderSupport packing ∧
              Graph.SupportComponents.Connected.ConnectedOn input.object piece ∧
              input.object.NegativeNetCharge piece data.threshold
                data.dischargeScale) →
      negativeSupport.At input) :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.negativeSupport
    { Requires := [netChargeNegative, netChargeLocalization]
      Produces := [negativeSupport]
      requiresUnique := by simp [distinctRequired]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := negativeSupport)
        (encode inputs.current (by
          obtain ⟨packing, valid, negative⟩ :=
            negativeOf inputs.current (inputs.get netChargeNegative)
          obtain ⟨piece, inside, connected, charge⟩ :=
            localizeOf inputs.current (inputs.get netChargeLocalization) packing
              valid negative
          exact ⟨packing, valid, piece, inside, connected, charge⟩))
        .nil)

/-! ## Node `[62]`: the Type A / Type B split

The selected negative support either carries assigned high-degree surplus or it
does not.  The no arm is node `[63]`, the Type A low-deficiency atom branch; the
yes arm is node `[64]`, the Type B high-degree fan-safe support branch.

The split is decided on the *selected* support's own assigned surplus, which is
what `def:canonical-decomp`'s assignment credits to it -- not on the whole
remainder's.  Both arms carry the support's existence forward with the clause
that distinguishes them, so a consumer of either arm reads a support of the kind
its branch is about and cannot read the other. -/
noncomputable def typeSplitDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous :
      ExactLedger (Input BranchState Presentation presentation data)
        current known)
    (negativeSupport typeALowSurplus typeBHighSurplus :
      FactKey (Input BranchState Presentation presentation data))
    [Core.Residual.FactKeys.Has negativeSupport known]
    (supportOf : negativeSupport.At current →
      ∃ packing : Finset (Finset current.object.Vertex),
        current.object.IsWindowPacking data.windowOrder packing ∧
          ∃ piece : Finset current.object.Vertex,
            piece ⊆ current.object.remainderSupport packing ∧
              Graph.SupportComponents.Connected.ConnectedOn current.object
                piece ∧
              current.object.NegativeNetCharge piece data.threshold
                data.dischargeScale)
    (encodeTypeA :
      (∃ packing : Finset (Finset current.object.Vertex),
        current.object.IsWindowPacking data.windowOrder packing ∧
          ∃ piece : Finset current.object.Vertex,
            piece ⊆ current.object.remainderSupport packing ∧
              Graph.SupportComponents.Connected.ConnectedOn current.object
                piece ∧
              current.object.NegativeNetCharge piece data.threshold
                data.dischargeScale ∧
              current.object.ambientSurplus piece data.threshold = 0) →
      typeALowSurplus.At current)
    (encodeTypeB :
      (∃ packing : Finset (Finset current.object.Vertex),
        current.object.IsWindowPacking data.windowOrder packing ∧
          ∃ piece : Finset current.object.Vertex,
            piece ⊆ current.object.remainderSupport packing ∧
              Graph.SupportComponents.Connected.ConnectedOn current.object
                piece ∧
              current.object.NegativeNetCharge piece data.threshold
                data.dischargeScale ∧
              0 < current.object.ambientSurplus piece data.threshold) →
      typeBHighSurplus.At current)
    (typeAFresh : typeALowSurplus ∉ known)
    (typeBFresh : typeBHighSurplus ∉ known) :
    Decision typeALowSurplus typeBHighSurplus previous :=
  Decision.run previous typeALowSurplus typeBHighSurplus
    `Hypostructure.Graph.Strategy.Spine.typeSplitDichotomy
    (by
      classical
      -- The decision is taken on a `Prop`, so no witness is extracted to build
      -- the branch: the arm not taken supplies the other arm's clause.
      by_cases typeA :
          ∃ packing : Finset (Finset current.object.Vertex),
            current.object.IsWindowPacking data.windowOrder packing ∧
              ∃ piece : Finset current.object.Vertex,
                piece ⊆ current.object.remainderSupport packing ∧
                  Graph.SupportComponents.Connected.ConnectedOn current.object
                    piece ∧
                  current.object.NegativeNetCharge piece data.threshold
                    data.dischargeScale ∧
                  current.object.ambientSurplus piece data.threshold = 0
      · exact .inl (encodeTypeA typeA)
      · refine .inr (encodeTypeB ?_)
        obtain ⟨packing, valid, piece, inside, connected, charge⟩ :=
          supportOf (ExactLedger.get previous negativeSupport)
        refine ⟨packing, valid, piece, inside, connected, charge, ?_⟩
        rcases Nat.eq_zero_or_pos
            (current.object.ambientSurplus piece data.threshold) with
          zero | positive
        · exact absurd
            ⟨packing, valid, piece, inside, connected, charge, zero⟩ typeA
        · exact positive)
    typeAFresh typeBFresh

end Hypostructure.Graph.Strategy.Spine
