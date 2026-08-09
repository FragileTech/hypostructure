import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.TypeADischarge
import Hypostructure.Graph.TypeBMaximalCompletion

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
      (2 ^ (data.windowRate * data.separatedScaleCount current.object.vertexCount *
            current.object.windowPackingNumber data.windowOrder) ≤
          Graph.skeletonBudget current.object ∧
        ∀ family : Finset Nat, current.object.edgeCount ∈ family →
          Graph.skeletonBudget current.object ≤
            Graph.variableEdgeBudget current.object.vertexCount family) →
      barrierCap.At current)
    (encodeOverflow :
      (Graph.skeletonBudget current.object <
        2 ^ (data.windowRate * data.separatedScaleCount current.object.vertexCount *
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
        2 ^ (data.windowRate * data.separatedScaleCount current.object.vertexCount *
          current.object.windowPackingNumber data.windowOrder) then
      .inr (encodeOverflow overflow)
    else
      .inl (encodeCap ⟨Nat.le_of_not_lt overflow, stable⟩))
    capFresh overflowFresh

/-! ## Nodes `[21]`--`[22]`: the separation of the window package

`lem:p13-window-package` builds its coordinate family and then *selects*: the
package "uses `⌊log₂ n⌋ − O(1)` separated dyadic scales", the `O(1)` absorbing
"endpoint collisions with the finitely many reserved boundary and tie-breaking
choices inside the canonical packing".

So separation is the property of the surviving coordinates, and the colliding
ones are discarded.  This diamond is that selection: either the selected
coordinates are separated and each carries the audited rate — the arm on which
`lem:independent-target-entropy` applies — or they collide, and the arm leaves
the block.  Both are retained; nothing about separation is assumed.

The coordinate family is data, so what the arm commits is its existence, exactly
as node `[17]` commits the packing's. -/
noncomputable def windowPackageDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous :
      ExactLedger (Input BranchState Presentation presentation data)
        current known)
    (windowPackageSeparated windowPackageCollided :
      FactKey (Input BranchState Presentation presentation data))
    (encodeSeparated :
      WindowPackageStatement data current.object →
      windowPackageSeparated.At current)
    (encodeCollided :
      ¬ WindowPackageStatement data current.object →
      windowPackageCollided.At current)
    (separatedFresh : windowPackageSeparated ∉ known)
    (collidedFresh : windowPackageCollided ∉ known) :
    Decision windowPackageSeparated windowPackageCollided previous :=
  Decision.run previous windowPackageSeparated windowPackageCollided
    `Hypostructure.Graph.Strategy.Spine.windowPackageDichotomy
    (by
      classical
      by_cases separated : WindowPackageStatement data current.object
      · exact .inl (encodeSeparated separated)
      · exact .inr (encodeCollided separated))
    separatedFresh collidedFresh

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
      2 ^ (data.windowRate * data.separatedScaleCount input.object.vertexCount *
          input.object.windowPackingNumber data.windowOrder)
        ≤ Graph.skeletonBudget input.object)
    (surplusOf : (input : Input BranchState Presentation presentation data) →
      surplusAtOrBelow.At input →
      input.object.degreeSurplus data.threshold ≤
        data.surplusThreshold input.object.vertexCount)
    (encode : (input : Input BranchState Presentation presentation data) →
      (2 * (data.windowRate * data.separatedScaleCount input.object.vertexCount *
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
            (data.windowRate * data.separatedScaleCount object.vertexCount *
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

/-! ## Node `[32]`: exact rank loss or exact full rank

The proof of `lem:full-rank` eliminates every proper target-dependence and then
concludes `r_Ω(R) = W₂(R)`, which implies its displayed all-but-`o(W₂)` bound.
This decision exposes that exact proof step.  Its left arm is any strict rank
loss, together with the dependence extracted by `lem:target-rank-circuit`; its
right arm is exact full rank. -/
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
              remainderWedgeSupply current.object packing ∧
            ∃ test determiners,
              Core.TargetRank.Dependence
                (remainderQuotientSystem data current.object packing) test
                determiners) →
      curvatureRankDrop.At current)
    (encodeFull :
      (∀ packing : Finset (Finset current.object.Vertex),
        current.object.IsWindowPacking data.windowOrder packing →
        remainderCurvatureTargetRank data current.object packing =
          remainderWedgeSupply current.object packing) →
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
                remainderWedgeSupply current.object packing
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
        exact below
      · -- No strict loss: target-rank is bounded above by the raw family and
        -- therefore is exactly the raw wedge count.
        refine .inr (encodeFull fun packing valid => ?_)
        apply Nat.le_antisymm
        · exact Graph.FiniteObject.curvatureTargetRank_le_internalWedgeCount
            _ _ _ _
        · by_contra short
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
              remainderWedgeSupply input.object packing ∧
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
    (residual : Input BranchState Presentation presentation data)
    (defect : ∃ packing : Finset (Finset residual.object.Vertex),
      residual.object.IsWindowPacking data.windowOrder packing ∧
        ∃ quotient : remainderQuotient data residual.object packing,
          ∃ left right, Identified quotient left right ∧
            (left.boundaryDegreeProfile ≠ right.boundaryDegreeProfile ∨
              Graph.Response.TargetDefect
                (Graph.HasCycleWithLength data.LengthOK) left right)) :
    False := by
  obtain ⟨_packing, _valid, quotient, left, right, identified, separated⟩ :=
    defect
  obtain ⟨fibrewise, universal⟩ :=
    Graph.DeclaredQuotient.targetComplete_of_identified quotient left right
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
`Graph.DeclaredQuotient.localize` is the scope split between them.  It is
stated once here because the three cases differ in *which* support is
compressed, not in why compression is impossible -- which is exactly what the
manuscript says when it routes all three to the same two exclusions. -/
/-- **The barrier node `[45]` raises is impossible**, from the reading it
*stored* rather than from a fresh derivation.

Node `[45]` already committed the disjunction `lem:no-silent-global-smearing`
leaves.  The terminal `[46]` therefore reads it back by exact key and refutes
its two disjuncts -- `lem:replacement` for the proper-support replacement, and
the selection's own minimality and avoidance for the closed representative.
Nothing is recomputed: `Graph.DeclaredQuotient.localize` is applied once, in
the row that commits `[45]`, and never again. -/
theorem not_globalBarrierReading
    (residual : Input BranchState Presentation presentation data)
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK residual.object)
    (minimal : ∀ smaller : Graph.FiniteObject.{u},
      (progress BranchState Presentation presentation data).Smaller
        smaller residual.object →
      Graph.MinimumDegreeAtLeast data.threshold smaller →
      Graph.HasCycleWithLength data.LengthOK smaller)
    {support : Finset residual.object.Vertex}
    (reading :
      Graph.Strategy.InterfaceReplacement.ReplacementSupport
          (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) residual.object support ∨
        ∃ representative : Graph.FiniteObject.{u},
          representative.LexicographicallySmaller residual.object ∧
            Graph.MinimumDegreeAtLeast data.threshold representative ∧
              (Graph.HasCycleWithLength data.LengthOK representative →
              Graph.HasCycleWithLength data.LengthOK residual.object)) :
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
      { G := residual.object, baseline := residual.baseline,
        state := residual.branchState, avoids := avoids,
        minimal := minimal }
      support replacement
  · exact avoids (transfer (minimal representative smaller
      representativeBaseline))

theorem not_determinationCertificate
    (residual : Input BranchState Presentation presentation data)
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK residual.object)
    (minimal : ∀ smaller : Graph.FiniteObject.{u},
      (progress BranchState Presentation presentation data).Smaller
        smaller residual.object →
      Graph.MinimumDegreeAtLeast data.threshold smaller →
      Graph.HasCycleWithLength data.LengthOK smaller)
    {packing : Finset (Finset residual.object.Vertex)}
    {quotient : remainderQuotient data residual.object packing}
    (certified : DeterminationCertificate data residual.object packing quotient) :
    False := by
  -- `[39]` and `[42]` reach their terminal straight from a branch test, with no
  -- row in between to commit the reading, so the scope split is taken here --
  -- once -- and handed to the same refutation `[46]` uses.
  exact not_globalBarrierReading residual avoids minimal
    (Graph.DeclaredQuotient.localize quotient certified.1)

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
`Graph.DeclaredQuotient.localize` is that split. -/
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
              Graph.DeclaredQuotient.localize quotient certified.1⟩))
          .nil))

/-- **The terminals `[39]`, `[42]` and `[46]` are all closed.**

Each of the three names a determination certificate on the selected object, and
`not_determinationCertificate` refutes every one of them: `cor:uncompressible`
kills the proper-support readings and the selection's own minimality kills the
closed representative.  The three differ in *which* support the manuscript says
is being compressed -- `C` at `[39]`, the enlarged `Z ⊊ G` at `[42]`, and `G`
itself at `[46]` -- which is why they are three terminals and not one. -/
theorem not_branchDCertificate
    (residual : Input BranchState Presentation presentation data)
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK residual.object)
    (minimal : ∀ smaller : Graph.FiniteObject.{u},
      (progress BranchState Presentation presentation data).Smaller
        smaller residual.object →
      Graph.MinimumDegreeAtLeast data.threshold smaller →
      Graph.HasCycleWithLength data.LengthOK smaller)
    (certificate : ∃ packing : Finset (Finset residual.object.Vertex),
      residual.object.IsWindowPacking data.windowOrder packing ∧
        ∃ quotient : remainderQuotient data residual.object packing,
          DeterminationCertificate data residual.object packing quotient) :
    False := by
  obtain ⟨_packing, _valid, quotient, certified⟩ := certificate
  exact not_determinationCertificate residual avoids minimal certified

/-! ## Nodes `[47]`--`[48]`: the forced curvature cost

`cor:forced-curvature-cost`, whose proof invokes `lem:full-rank` and
`lem:wedge-lower`.  Both are already ledger facts on this branch.  The row
substitutes the exact equality proved by `lem:full-rank` into node `[30]`'s
demand floor and applies the registered cost to both sides.

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
        remainderCurvatureTargetRank data input.object packing =
          remainderWedgeSupply input.object packing)
    (encode : (input : Input BranchState Presentation presentation data) →
      (∀ packing : Finset (Finset input.object.Vertex),
        input.object.IsWindowPacking data.windowOrder packing →
        data.curvatureCost *
              (data.threshold * (input.object.remainderSupport packing).card +
                2 * (2 * (data.windowOrder - 1) * packing.card)) ≤
            data.curvatureCost *
                remainderCurvatureTargetRank data input.object packing +
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
          -- `W₂(R) ≤ r_Ω(R)`, from the exact full-rank ledger fact.
          have supply :
              remainderWedgeSupply inputs.current.object packing ≤
                remainderCurvatureTargetRank data inputs.current.object packing :=
            (rankOf inputs.current (inputs.get curvatureFullRank) packing valid).ge
          calc data.curvatureCost *
                (data.threshold *
                    (inputs.current.object.remainderSupport packing).card +
                  2 * (2 * (data.windowOrder - 1) * packing.card))
              ≤ data.curvatureCost *
                  (remainderCurvatureTargetRank data inputs.current.object
                        packing +
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
          (current.object.positiveDeficiency
            (current.object.remainderSupport packing) data.threshold)
          (current.object.remainderSupport packing).card) →
      remainderEntropyHigh.At current)
    (encodeLow :
      (∃ packing : Finset (Finset current.object.Vertex),
        current.object.IsWindowPacking data.windowOrder packing ∧
          Graph.BelowEntropyRate current.object.vertexCount
            data.entropyDenominator data.windowOrder data.threshold
            (current.object.positiveDeficiency
              (current.object.remainderSupport packing) data.threshold)
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
              (current.object.positiveDeficiency
                (current.object.remainderSupport packing) data.threshold)
              (current.object.remainderSupport packing).card
      · exact .inl (encodeHigh high)
      · refine .inr (encodeLow ?_)
        push Not at high
        obtain ⟨packing, valid, below⟩ := high
        exact ⟨packing, valid,
          (Graph.not_atLeastEntropyRate_iff _ _ _ _ _ _).mp below⟩)
    highFresh lowFresh


/-- The common forward edge of `prop:two-budget` (b) and (c).  The source
fact is branch-specific, but the produced Residual C fact has one semantic key
and the literal source history remains in the ledger tail. -/
@[reducible] noncomputable def lowEntropyLargeBudgetRow
    (source largeBudgetResidual :
      FactKey (Input BranchState Presentation presentation data))
    (distinct : source ≠ largeBudgetResidual)
    (sourceOf :
      (input : Input BranchState Presentation presentation data) →
      source.At input →
      ∃ packing : Finset (Finset input.object.Vertex),
        input.object.IsWindowPacking data.windowOrder packing ∧
          Graph.BelowEntropyRate input.object.vertexCount
            data.entropyDenominator data.windowOrder data.threshold
            (input.object.positiveDeficiency
              (input.object.remainderSupport packing) data.threshold)
            (input.object.remainderSupport packing).card)
    (encode :
      (input : Input BranchState Presentation presentation data) →
      (∃ packing : Finset (Finset input.object.Vertex),
        input.object.IsWindowPacking data.windowOrder packing ∧
          Graph.BelowEntropyRate input.object.vertexCount
            data.entropyDenominator data.windowOrder data.threshold
            (input.object.positiveDeficiency
              (input.object.remainderSupport packing) data.threshold)
            (input.object.remainderSupport packing).card) →
      largeBudgetResidual.At input) :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.lowEntropyLargeBudget
    (rowManifest source largeBudgetResidual distinct)
    (fun inputs =>
      .cons (key := largeBudgetResidual)
        (encode inputs.current
          (sourceOf inputs.current (inputs.get source)))
        .nil)

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
          (input.object.positiveDeficiency
            (input.object.remainderSupport packing) data.threshold)
          (input.object.remainderSupport packing).card)
    (encode : (input : Input BranchState Presentation presentation data) →
      (∀ packing : Finset (Finset input.object.Vertex),
        input.object.IsWindowPacking data.windowOrder packing →
        (2 ^ (data.windowRate * data.separatedScaleCount input.object.vertexCount *
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


/-! ## Node `[60]`: enter the asymptotic order regime

The manuscript uses the net-charge cap only "for all sufficiently large
`n`".  This is the exhaustive pointwise routing of that regime; the canonical
asymptotic endpoint eliminates the complementary arm, and the selected arm is
then an ordinary fact in the exact ledger. -/
noncomputable def netChargeOrderDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous : ExactLedger (Input BranchState Presentation presentation data)
      current known)
    (netChargeLarge netChargeSmall :
      FactKey (Input BranchState Presentation presentation data))
    (encodeLarge :
      Graph.FiniteObject.SufficientlyLargeForNetCap data.threshold
          data.dischargeScale data.windowOrder data.windowRate
          data.spineScale current.object.vertexCount →
        netChargeLarge.At current)
    (encodeSmall :
      ¬ Graph.FiniteObject.SufficientlyLargeForNetCap data.threshold
          data.dischargeScale data.windowOrder data.windowRate
          data.spineScale current.object.vertexCount →
        netChargeSmall.At current)
    (largeFresh : netChargeLarge ∉ known)
    (smallFresh : netChargeSmall ∉ known) :
    Decision netChargeLarge netChargeSmall previous := by
  classical
  exact Decision.run previous netChargeLarge netChargeSmall
    `Hypostructure.Graph.Strategy.Spine.netChargeOrderDichotomy
    (if large : Graph.FiniteObject.SufficientlyLargeForNetCap data.threshold
        data.dischargeScale data.windowOrder data.windowRate
        data.spineScale current.object.vertexCount then
      .inl (encodeLarge large)
    else
      .inr (encodeSmall large))
    largeFresh smallFresh

/-! ## Node `[60]`: the asymptotic net-charge cap

`prop:negative-net-charge` is an eventual statement.  The density cap, the
surplus-aware stub supply, and the paper's sufficiently-large comparison imply
that every canonical maximum-packing remainder has negative net charge.  This
row appends exactly that conclusion; it introduces no retained reserve. -/
@[reducible] noncomputable def netChargeCapRow
    (densityCap stubSupply netChargeLarge netChargeCap :
      FactKey (Input BranchState Presentation presentation data))
    (requiredUnique : [densityCap, stubSupply, netChargeLarge].Nodup)
    (densityOf : (input : Input BranchState Presentation presentation data) →
      densityCap.At input →
      2 * (data.windowRate * data.separatedScaleCount input.object.vertexCount *
        input.object.windowPackingNumber data.windowOrder) ≤
        (Graph.dyadicScaleCount input.object + 1) *
          (data.threshold * input.object.vertexCount +
            data.surplusThreshold input.object.vertexCount))
    (stubOf : (input : Input BranchState Presentation presentation data) →
      stubSupply.At input →
      ∀ packing : Finset (Finset input.object.Vertex),
        input.object.IsWindowPacking data.windowOrder packing →
        input.object.positiveDeficiency
              (input.object.remainderSupport packing) data.threshold +
            2 * (data.windowOrder - 1) * packing.card ≤
          data.threshold * (data.windowOrder * packing.card) +
            data.surplusThreshold input.object.vertexCount)
    (largeOf : (input : Input BranchState Presentation presentation data) →
      netChargeLarge.At input →
      Graph.FiniteObject.SufficientlyLargeForNetCap data.threshold
        data.dischargeScale data.windowOrder data.windowRate data.spineScale
        input.object.vertexCount)
    (encode : (input : Input BranchState Presentation presentation data) →
      (∀ packing : Finset (Finset input.object.Vertex),
        input.object.IsWindowPacking data.windowOrder packing →
        packing.card = input.object.windowPackingNumber data.windowOrder →
          input.object.NegativeNetCharge
            (input.object.remainderSupport packing) data.threshold
            data.dischargeScale) →
      netChargeCap.At input) :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.netChargeCap
    { Requires := [densityCap, stubSupply, netChargeLarge]
      Produces := [netChargeCap]
      requiresUnique := requiredUnique
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := netChargeCap)
        (encode inputs.current (by
          intro packing valid cardinality
          have density := densityOf inputs.current (inputs.get densityCap)
          have density' :
              2 * (data.windowRate * Nat.log2 inputs.current.object.vertexCount *
                packing.card) ≤
              (Nat.log2 inputs.current.object.vertexCount + 1) *
                (data.threshold * inputs.current.object.vertexCount +
                  data.spineScale * Core.ceilSqrt inputs.current.object.vertexCount) := by
            rw [data.separatedScaleCount_eq_log2, Graph.dyadicScaleCount,
              ← cardinality] at density
            simpa [Data.surplusThreshold] using density
          have supply := stubOf inputs.current (inputs.get stubSupply) packing valid
          have supply' :
              inputs.current.object.positiveDeficiency
                    (inputs.current.object.remainderSupport packing) data.threshold +
                  2 * (data.windowOrder - 1) * packing.card ≤
                data.threshold * (data.windowOrder * packing.card) +
                  data.spineScale * Core.ceilSqrt inputs.current.object.vertexCount := by
            simpa [Data.surplusThreshold] using supply
          have cardinality' :
              data.windowOrder * packing.card +
                  (inputs.current.object.remainderSupport packing).card =
                inputs.current.object.vertexCount := by
            simpa [Nat.add_comm] using
              inputs.current.object.remainderSupport_card_add_eq valid
          have thresholdPos : 0 < data.threshold :=
            lt_of_lt_of_le (by omega) data.three_le_threshold
          have debitLe :
              2 * (data.windowOrder - 1) ≤ data.threshold * data.windowOrder := by
            calc
              2 * (data.windowOrder - 1) ≤ 2 * data.windowOrder := by omega
              _ ≤ data.threshold * data.windowOrder :=
                Nat.mul_le_mul_right data.windowOrder
                  (le_trans (by omega) data.three_le_threshold)
          have strictCap :=
            Graph.FiniteObject.strictCap_of_densityCap_of_sufficientlyLarge
              data.threshold data.dischargeScale data.windowOrder data.windowRate
              data.spineScale inputs.current.object.vertexCount packing.card
              (inputs.current.object.remainderSupport packing).card
              data.windowOrder_pos thresholdPos debitLe data.netCapRateSlack
              (largeOf inputs.current (inputs.get netChargeLarge)) density'
              cardinality'
          exact Graph.FiniteObject.negativeNetCharge_of_stubSupply_of_strictCap
            inputs.current.object (inputs.current.object.remainderSupport packing)
            data.threshold data.dischargeScale
            (2 * (data.windowOrder - 1) * packing.card)
            (data.threshold * (data.windowOrder * packing.card) +
              data.spineScale * Core.ceilSqrt inputs.current.object.vertexCount)
            supply' strictCap))
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
          ∃ component ∈ input.object.canonicalPieces
              (input.object.remainderSupport packing),
            input.object.NegativeNetCharge
              (input.object.pieceSupport
                (input.object.remainderSupport packing) component)
              data.threshold data.dischargeScale) →
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
          inputs.current.object.exists_canonicalPiece_negativeNetCharge
            (inputs.current.object.remainderSupport packing) data.threshold
            data.dischargeScale negative)
        .nil)

/-! ## Node `[59]`: the net-charge sign test

`N₀(R) ≥ 0?`  The yes arm is the manuscript's node `[60]`; the no arm is
node `[61]`, where a connected negative support is selected.  Both sides are
the two halves of one excluded middle on the exact integer comparison
`def:net-charge` reduces to, so they are exhaustive.  The decision itself does
not close `[60]`: that terminal additionally needs the strict net-cap estimate
used by `prop:negative-net-charge`. -/
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
        (∀ window : Finset current.object.Vertex,
          current.object.InducesWindow data.windowOrder window →
          ∃ member ∈ packing, ¬ Disjoint window member) →
        current.object.NonNegativeNetCharge
          (current.object.remainderSupport packing) data.threshold
          data.dischargeScale) →
      netChargeNonNegative.At current)
    (encodeNegative :
      (∃ packing : Finset (Finset current.object.Vertex),
        current.object.IsWindowPacking data.windowOrder packing ∧
          (∀ window : Finset current.object.Vertex,
            current.object.InducesWindow data.windowOrder window →
            ∃ member ∈ packing, ¬ Disjoint window member) ∧
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
            (∀ window : Finset current.object.Vertex,
              current.object.InducesWindow data.windowOrder window →
              ∃ member ∈ packing, ¬ Disjoint window member) →
            current.object.NonNegativeNetCharge
              (current.object.remainderSupport packing) data.threshold
              data.dischargeScale
      · exact .inl (encodeNonNegative nonNegative)
      · refine .inr (encodeNegative ?_)
        push Not at nonNegative
        obtain ⟨packing, valid, maximal, negative⟩ := nonNegative
        exact ⟨packing, valid, maximal, Nat.lt_of_not_le negative⟩)
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
requires a linear excess of window surplus over remainder surplus.  This row
proves that exact corollary only; it does not manufacture the asymptotic
quarter-cap needed to turn the corollary into the diagram's terminal. -/
@[reducible] noncomputable def windowJoinPressureRow
    (netChargeNonNegative boundaryDemand windowJoinPressure :
      FactKey (Input BranchState Presentation presentation data))
    (distinctRequired : netChargeNonNegative ≠ boundaryDemand)
    (chargeOf : (input : Input BranchState Presentation presentation data) →
      netChargeNonNegative.At input →
      ∀ packing : Finset (Finset input.object.Vertex),
        input.object.IsWindowPacking data.windowOrder packing →
        (∀ window : Finset input.object.Vertex,
          input.object.InducesWindow data.windowOrder window →
          ∃ member ∈ packing, ¬ Disjoint window member) →
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
        (∀ window : Finset input.object.Vertex,
          input.object.InducesWindow data.windowOrder window →
          ∃ member ∈ packing, ¬ Disjoint window member) →
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
        (encode inputs.current fun packing valid maximal => by
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
              valid maximal
          rw [Graph.FiniteObject.NonNegativeNetCharge] at charge
          have order :=
            inputs.current.object.remainderSupport_card_add_eq valid
          omega)
        .nil)

/-! ## Node `[61]`: the selected connected negative support

`prop:negative-net-charge`.  The negative arm of node `[59]` already contains
the canonical maximal packing and its negative remainder.  Node `[57]`--`[58]`
localizes that charge through the canonical component decomposition.  This row
reads exactly those two facts and appends only the selected connected negative
piece and its containment in the same remainder. -/
@[reducible] noncomputable def negativeSupportRow
    (netChargeNegative netChargeLocalization negativeSupport :
      FactKey (Input BranchState Presentation presentation data))
    (distinctRequired : netChargeNegative ≠ netChargeLocalization)
    (negativeOf : (input : Input BranchState Presentation presentation data) →
      netChargeNegative.At input →
      ∃ packing : Finset (Finset input.object.Vertex),
        input.object.IsWindowPacking data.windowOrder packing ∧
          (∀ window : Finset input.object.Vertex,
            input.object.InducesWindow data.windowOrder window →
            ∃ member ∈ packing, ¬ Disjoint window member) ∧
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
          ∃ component ∈ input.object.canonicalPieces
              (input.object.remainderSupport packing),
            input.object.NegativeNetCharge
              (input.object.pieceSupport
                (input.object.remainderSupport packing) component)
              data.threshold data.dischargeScale)
    (encode : (input : Input BranchState Presentation presentation data) →
      (∃ packing : Finset (Finset input.object.Vertex),
        input.object.IsWindowPacking data.windowOrder packing ∧
          (∀ window : Finset input.object.Vertex,
            input.object.InducesWindow data.windowOrder window →
            ∃ member ∈ packing, ¬ Disjoint window member) ∧
          ∃ component ∈ input.object.canonicalPieces
              (input.object.remainderSupport packing),
            input.object.NegativeNetCharge
              (input.object.pieceSupport
                (input.object.remainderSupport packing) component)
              data.threshold data.dischargeScale) →
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
          obtain ⟨packing, valid, maximal, negative⟩ :=
            negativeOf inputs.current (inputs.get netChargeNegative)
          obtain ⟨component, present, charge⟩ :=
            localizeOf inputs.current (inputs.get netChargeLocalization)
              packing valid negative
          exact ⟨packing, valid, maximal, component, present, charge⟩))
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
          (∀ window : Finset current.object.Vertex,
            current.object.InducesWindow data.windowOrder window →
            ∃ member ∈ packing, ¬ Disjoint window member) ∧
          ∃ component ∈ current.object.canonicalPieces
              (current.object.remainderSupport packing),
            current.object.NegativeNetCharge
              (current.object.pieceSupport
                (current.object.remainderSupport packing) component)
              data.threshold data.dischargeScale)
    (encodeTypeA :
      (∃ packing : Finset (Finset current.object.Vertex),
        current.object.IsWindowPacking data.windowOrder packing ∧
          (∀ window : Finset current.object.Vertex,
            current.object.InducesWindow data.windowOrder window →
            ∃ member ∈ packing, ¬ Disjoint window member) ∧
          ∃ component ∈ current.object.canonicalPieces
              (current.object.remainderSupport packing),
            let piece := current.object.pieceSupport
              (current.object.remainderSupport packing) component
            current.object.NegativeNetCharge piece data.threshold
                data.dischargeScale ∧
              current.object.ambientSurplus piece data.threshold = 0) →
      typeALowSurplus.At current)
    (encodeTypeB :
      (∃ packing : Finset (Finset current.object.Vertex),
        current.object.IsWindowPacking data.windowOrder packing ∧
          (∀ window : Finset current.object.Vertex,
            current.object.InducesWindow data.windowOrder window →
            ∃ member ∈ packing, ¬ Disjoint window member) ∧
          ∃ component ∈ current.object.canonicalPieces
              (current.object.remainderSupport packing),
            let piece := current.object.pieceSupport
              (current.object.remainderSupport packing) component
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
      apply Classical.choice
      obtain ⟨packing, valid, maximal, component, present, charge⟩ :=
        supportOf (ExactLedger.get previous negativeSupport)
      let piece := current.object.pieceSupport
        (current.object.remainderSupport packing) component
      rcases Nat.eq_zero_or_pos
          (current.object.ambientSurplus piece data.threshold) with
        zero | positive
      · exact ⟨.inl (encodeTypeA
          ⟨packing, valid, maximal, component, present, charge, zero⟩)⟩
      · exact ⟨.inr (encodeTypeB
          ⟨packing, valid, maximal, component, present, charge, positive⟩)⟩)
    typeAFresh typeBFresh

/-! ## Node `[68]`, the standing law: the high-neighbourhood normal form

`lem:heavy-neighbourhood-normal-form`.  At a high centre `h` -- one whose degree
is strictly above the baseline -- the manuscript proves three things, and the
whole Type B fan analysis runs on them:

* (a) every vertex of `N_G(h)` has degree exactly the baseline;
* (b) `G[N_G(h)]` is a matching;
* (c) two nonadjacent neighbours of `h` have no common neighbour outside `{h}`.

(a) is the tight-endpoint law of node `[9]` read at the edge `hx`: one endpoint
sits exactly at the baseline, and it is not `h`.  (b) and (c) are the two
quadrilaterals `hxyzh` and `hxzyh`, excluded because the selected object avoids
the accepted lengths and the quadrilateral is one of them -- the registered
`Data.quadrilateralAccepted`, which is where "no power-of-two cycle" enters at
its own interface.

The fact is stated of the *object*, at every high centre at once, because that
is what the manuscript proves and because a centre is data: no fact can carry
one.  Both arms of the degree split below read it. -/
@[reducible] noncomputable def highCentreNormalFormRow
    (selection tightEndpoint highCentreNormalForm :
      FactKey (Input BranchState Presentation presentation data))
    (distinctRequired : selection ≠ tightEndpoint)
    (avoidsOf : (input : Input BranchState Presentation presentation data) →
      selection.At input →
      ¬ Graph.HasCycleWithLength data.LengthOK input.object)
    (tightOf : (input : Input BranchState Presentation presentation data) →
      tightEndpoint.At input →
      ∀ dart : input.object.graph.Dart,
        input.object.degree dart.fst = data.threshold ∨
          input.object.degree dart.snd = data.threshold)
    (encode : (input : Input BranchState Presentation presentation data) →
      (∀ centre : input.object.Vertex,
        Graph.IsHighCentre input.object data.threshold centre →
        Graph.NormalForm input.object data.threshold centre) →
      highCentreNormalForm.At input) :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.highCentreNormalForm
    { Requires := [selection, tightEndpoint]
      Produces := [highCentreNormalForm]
      requiresUnique := by simp [distinctRequired]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := highCentreNormalForm)
        (encode inputs.current
          (fun _centre high =>
            Graph.normalForm
              (tightOf inputs.current (inputs.get tightEndpoint))
              (avoidsOf inputs.current (inputs.get selection))
              data.quadrilateralAccepted high))
        .nil)

/-! ## Node `[68]`: the Type B heavy-centre split

The manuscript asks whether some Type B fan centre has degree above the
high-centre degree `δ + 1` -- for its own baseline, whether `d_G(h) > 4`.  The
yes arm enters `[69]`, the heavy-centre local dichotomy; the no arm enters
`[78]`, where every high centre the support carries sits exactly at `δ + 1`.

The split is taken on a `Prop`, so no centre is extracted to build the branch:
the arm not taken supplies the other arm's clause.  The no arm is committed in
positive form -- *every* high centre of *every* Type B support has degree
exactly `δ + 1` -- which is node `[78]`'s entry condition, and it quantifies
over supports rather than naming one for the same reason node `[64]`'s own fact
does.

This is a `Decision`: the arm not taken is absent from the taken branch's key
index, so no Type B row downstream can read the other alternative. -/
noncomputable def heavyCentreDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous :
      ExactLedger (Input BranchState Presentation presentation data)
        current known)
    (typeBHighSurplus typeBHeavyCentre typeBDegreeFourCentres :
      FactKey (Input BranchState Presentation presentation data))
    [Core.Residual.FactKeys.Has typeBHighSurplus known]
    (supportOf : typeBHighSurplus.At current →
      ∃ packing : Finset (Finset current.object.Vertex),
        current.object.IsWindowPacking data.windowOrder packing ∧
          (∀ window : Finset current.object.Vertex,
            current.object.InducesWindow data.windowOrder window →
            ∃ member ∈ packing, ¬ Disjoint window member) ∧
          ∃ component ∈ current.object.canonicalPieces
              (current.object.remainderSupport packing),
            let piece := current.object.pieceSupport
              (current.object.remainderSupport packing) component
            current.object.NegativeNetCharge piece data.threshold
                data.dischargeScale ∧
              0 < current.object.ambientSurplus piece data.threshold)
    (encodeHeavy :
      (∃ packing : Finset (Finset current.object.Vertex),
        current.object.IsWindowPacking data.windowOrder packing ∧
          (∀ window : Finset current.object.Vertex,
            current.object.InducesWindow data.windowOrder window →
            ∃ member ∈ packing, ¬ Disjoint window member) ∧
          ∃ component ∈ current.object.canonicalPieces
              (current.object.remainderSupport packing),
            let piece := current.object.pieceSupport
              (current.object.remainderSupport packing) component
            current.object.NegativeNetCharge piece data.threshold
                data.dischargeScale ∧
              0 < current.object.ambientSurplus piece data.threshold ∧
              ∃ centre ∈ piece,
                data.threshold + 1 < current.object.degree centre) →
      typeBHeavyCentre.At current)
    (encodeDegreeFour :
      (∃ packing : Finset (Finset current.object.Vertex),
        current.object.IsWindowPacking data.windowOrder packing ∧
          (∀ window : Finset current.object.Vertex,
            current.object.InducesWindow data.windowOrder window →
            ∃ member ∈ packing, ¬ Disjoint window member) ∧
          ∃ component ∈ current.object.canonicalPieces
              (current.object.remainderSupport packing),
            let piece := current.object.pieceSupport
              (current.object.remainderSupport packing) component
            current.object.NegativeNetCharge piece data.threshold
                data.dischargeScale ∧
              0 < current.object.ambientSurplus piece data.threshold ∧
              ∀ centre ∈ piece,
                Graph.IsHighCentre current.object data.threshold centre →
                current.object.degree centre = data.threshold + 1) →
      typeBDegreeFourCentres.At current)
    (heavyFresh : typeBHeavyCentre ∉ known)
    (degreeFourFresh : typeBDegreeFourCentres ∉ known) :
    Decision typeBHeavyCentre typeBDegreeFourCentres previous :=
  Decision.run previous typeBHeavyCentre typeBDegreeFourCentres
    `Hypostructure.Graph.Strategy.Spine.heavyCentreDichotomy
    (by
      classical
      apply Classical.choice
      obtain ⟨packing, valid, maximal, component, present, charge, positive⟩ :=
        supportOf (ExactLedger.get previous typeBHighSurplus)
      let piece := current.object.pieceSupport
        (current.object.remainderSupport packing) component
      by_cases heavy :
          ∃ centre ∈ piece,
            data.threshold + 1 < current.object.degree centre
      · exact ⟨.inl (encodeHeavy
          ⟨packing, valid, maximal, component, present, charge, positive,
            heavy⟩)⟩
      · refine ⟨.inr (encodeDegreeFour
          ⟨packing, valid, maximal, component, present, charge, positive, ?_⟩)⟩
        intro centre member high
        have notAbove :
            ¬ data.threshold + 1 < current.object.degree centre :=
          fun above => heavy ⟨centre, member, above⟩
        rw [Graph.IsHighCentre] at high
        omega)
    heavyFresh degreeFourFresh

/-! ## Node `[69]`: the heavy-centre local dichotomy

`cor:heavy-center-local-dichotomy`.  At a heavy centre `h` -- degree at least
two above the baseline, `d_G(h) ≥ 5` at the manuscript's `δ = 3` -- either two
open ports at `h` are fan-compatible in the sense of
`def:fan-compatible-open-ports`, or at least `d_G(h) − 2` ports at `h` are
triangular, and in particular three are.

The manuscript's argument is `Graph.heavyCentreLocalDichotomy`: the open
endpoints are pairwise adjacent, because a nonadjacent pair would be
fan-compatible by `lem:same-center-open-port-compatibility`; part (b) of the
normal form makes `G[N_G(h)]` a matching, which has no clique of size three, so
at most two endpoints are open; and every remaining port is triangular.  The
"in particular three" is `Graph.three_le_triangularEndpoints_card`, the only
place the *heaviness* of the centre is spent, and it spends it exactly as the
manuscript does: `k − 2 ≥ 3`.

The row reads the normal form and nothing else.  It does not require the
heavy-centre existence fact: the statement is universally quantified over heavy
centres, so it reads no witness, and declaring a requirement the executor does
not consume would be a false dependency. -/
@[reducible] noncomputable def heavyCentreLocalDichotomyRow
    (highCentreNormalForm typeBHeavyCentre typeBLocalDichotomy :
      FactKey (Input BranchState Presentation presentation data))
    (normalNeHeavy : highCentreNormalForm ≠ typeBHeavyCentre)
    (normalFormOf : (input : Input BranchState Presentation presentation data) →
      highCentreNormalForm.At input →
      ∀ centre : input.object.Vertex,
        Graph.IsHighCentre input.object data.threshold centre →
        Graph.NormalForm input.object data.threshold centre)
    (heavyOf : (input : Input BranchState Presentation presentation data) →
      typeBHeavyCentre.At input →
      ∃ packing : Finset (Finset input.object.Vertex),
        input.object.IsWindowPacking data.windowOrder packing ∧
          (∀ window : Finset input.object.Vertex,
            input.object.InducesWindow data.windowOrder window →
            ∃ member ∈ packing, ¬ Disjoint window member) ∧
          ∃ component ∈ input.object.canonicalPieces
              (input.object.remainderSupport packing),
            let piece := input.object.pieceSupport
              (input.object.remainderSupport packing) component
            input.object.NegativeNetCharge piece data.threshold
                data.dischargeScale ∧
              0 < input.object.ambientSurplus piece data.threshold ∧
              ∃ centre ∈ piece,
                data.threshold + 1 < input.object.degree centre)
    (encode : (input : Input BranchState Presentation presentation data) →
      (∃ packing : Finset (Finset input.object.Vertex),
        input.object.IsWindowPacking data.windowOrder packing ∧
          (∀ window : Finset input.object.Vertex,
            input.object.InducesWindow data.windowOrder window →
            ∃ member ∈ packing, ¬ Disjoint window member) ∧
          ∃ component ∈ input.object.canonicalPieces
              (input.object.remainderSupport packing),
            let piece := input.object.pieceSupport
              (input.object.remainderSupport packing) component
            input.object.NegativeNetCharge piece data.threshold
                data.dischargeScale ∧
              0 < input.object.ambientSurplus piece data.threshold ∧
              (∃ centre ∈ piece,
                data.threshold + 1 < input.object.degree centre) ∧
              ∀ centre ∈ piece,
                data.threshold + 1 < input.object.degree centre →
                (∃ left right : input.object.Vertex,
                    Graph.FanCompatible input.object centre left right) ∨
                  (input.object.degree centre - 2 ≤
                      (Graph.triangularEndpoints input.object centre).card ∧
                    3 ≤ (Graph.triangularEndpoints input.object centre).card)) →
      typeBLocalDichotomy.At input) :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.heavyCentreLocalDichotomy
    { Requires := [highCentreNormalForm, typeBHeavyCentre]
      Produces := [typeBLocalDichotomy]
      requiresUnique := by simp [normalNeHeavy]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs => Classical.choice <| by
      let normal :=
        normalFormOf inputs.current (inputs.get highCentreNormalForm)
      obtain ⟨packing, valid, maximal, component, present, charge, positive,
          witness⟩ := heavyOf inputs.current (inputs.get typeBHeavyCentre)
      exact ⟨.cons (key := typeBLocalDichotomy)
        (encode inputs.current ⟨packing, valid, maximal, component, present,
          charge, positive, witness, fun centre _member heavy => by
            -- A heavy centre is in particular a high centre.
            rcases Graph.heavyCentreLocalDichotomy
                (normal centre (Nat.lt_of_succ_lt heavy)) with
              compatible | alternative
            · exact Or.inl compatible
            · exact Or.inr ⟨alternative,
                Graph.three_le_triangularEndpoints_card data.three_le_threshold
                  heavy alternative⟩⟩)
        .nil⟩)

/-! ## Node `[70]`: the certificate-marked fan-degree cap

`lem:fan-certificate`, and `rem:fan-finite` as the observation about it.  A
fan-certificate labelling sends the neighbours of a high centre to legal window
labels that are pairwise `C₂`-compatible; the manuscript proves that such a
family has size at most `α(D) = 2 + 2 + 2 + 2 = 8`, so a certificate-marked fan
has `d_G(h) ≤ 8`.

Nothing here writes `8`.  `D` is `ForbiddenGap 2` read as a relation on the
window's own coordinates -- the differences whose wedge `u — h — v` closes an
accepted cycle of length `4 + d` -- and the bound is
`Graph.WindowCurvature.fanPackingCap`, its independence number, computed from
the registered window order and the registered target.  `rem:fan-finite` is
exactly the claim that this is a structural consequence of the label algebra
rather than a free parameter, and that is what the derivation makes true.

The row reads no prerequisite: the cap is a theorem about the registered label
algebra and the object's own degree, so `Requires := []` is the honest
declaration.  Because an `AtomicCT` carries no predecessor, this one executor
value runs after either arm of node `[68]`, which is where the manuscript places
`[70]`. -/
@[reducible] noncomputable def fanCertificateCapRow
    (fanCertificateCap :
      FactKey (Input BranchState Presentation presentation data))
    (encode : (input : Input BranchState Presentation presentation data) →
      (∀ centre : input.object.Vertex,
        Graph.IsHighCentre input.object data.threshold centre →
        ∀ _marking :
            Graph.FanCertificateLabelling input.object data.windowOrder centre,
          input.object.degree centre ≤
            Graph.WindowCurvature.fanPackingCap data.windowOrder) →
      fanCertificateCap.At input) :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.fanCertificateCap
    (sourceFreeManifest fanCertificateCap)
    (fun inputs =>
      .cons (key := fanCertificateCap)
        (encode inputs.current
          (fun _centre _high marking => marking.degree_le_fanPackingCap))
        .nil)

/-! ## Node `[71]`/`[80]`: is a certificate labelling present?

`def:marked-typeB-fan`.  A Type B fan is *certificate-marked* when the
fan-certificate labelling is part of the assigned support data; a high-degree
centre assigned to a Type B support but not certificate-marked is a
*fan-certificate residual center*, which is charged to the Type B
bridge-residual mass of `def:typeB-residual-mass` and takes no part in the
certificate-closed local discharging step.

The question is therefore scoped to the centres of a Type B support, not to the
object's high centres at large: a high centre lying in no Type B support is not
a residual centre and carries no bridge mass.  That scope is the manuscript's
own, and getting it wrong would charge Type B for centres it never assigned.

The split is taken on a `Prop`, so no centre and no labelling is extracted to
build the branch; the arm not taken supplies the other arm's clause.  This is a
`Decision`, so the arm not taken is absent from the taken branch's key index. -/
noncomputable def fanCertificateDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous :
      ExactLedger (Input BranchState Presentation presentation data)
        current known)
    (typeBHighSurplus fanCertificateMarked fanCertificateResidual :
      FactKey (Input BranchState Presentation presentation data))
    [Core.Residual.FactKeys.Has typeBHighSurplus known]
    (supportOf : typeBHighSurplus.At current →
      ∃ packing : Finset (Finset current.object.Vertex),
        current.object.IsWindowPacking data.windowOrder packing ∧
          (∀ window : Finset current.object.Vertex,
            current.object.InducesWindow data.windowOrder window →
            ∃ member ∈ packing, ¬ Disjoint window member) ∧
          ∃ component ∈ current.object.canonicalPieces
              (current.object.remainderSupport packing),
            let piece := current.object.pieceSupport
              (current.object.remainderSupport packing) component
            current.object.NegativeNetCharge piece data.threshold
                data.dischargeScale ∧
              0 < current.object.ambientSurplus piece data.threshold)
    (encodeMarked :
      (∃ packing : Finset (Finset current.object.Vertex),
        current.object.IsWindowPacking data.windowOrder packing ∧
          (∀ window : Finset current.object.Vertex,
            current.object.InducesWindow data.windowOrder window →
            ∃ member ∈ packing, ¬ Disjoint window member) ∧
          ∃ component ∈ current.object.canonicalPieces
              (current.object.remainderSupport packing),
            let piece := current.object.pieceSupport
              (current.object.remainderSupport packing) component
            current.object.NegativeNetCharge piece data.threshold
                data.dischargeScale ∧
              0 < current.object.ambientSurplus piece data.threshold ∧
              ∀ centre ∈ piece,
                Graph.IsHighCentre current.object data.threshold centre →
                Nonempty (Graph.FanCertificateLabelling current.object
                  data.windowOrder centre)) →
      fanCertificateMarked.At current)
    (encodeResidual :
      (∃ packing : Finset (Finset current.object.Vertex),
        current.object.IsWindowPacking data.windowOrder packing ∧
          (∀ window : Finset current.object.Vertex,
            current.object.InducesWindow data.windowOrder window →
            ∃ member ∈ packing, ¬ Disjoint window member) ∧
          ∃ component ∈ current.object.canonicalPieces
              (current.object.remainderSupport packing),
            let piece := current.object.pieceSupport
              (current.object.remainderSupport packing) component
            current.object.NegativeNetCharge piece data.threshold
                data.dischargeScale ∧
              0 < current.object.ambientSurplus piece data.threshold ∧
              ∃ centre ∈ piece,
                Graph.IsHighCentre current.object data.threshold centre ∧
                  IsEmpty (Graph.FanCertificateLabelling current.object
                    data.windowOrder centre)) →
      fanCertificateResidual.At current)
    (markedFresh : fanCertificateMarked ∉ known)
    (residualFresh : fanCertificateResidual ∉ known) :
    Decision fanCertificateMarked fanCertificateResidual previous :=
  Decision.run previous fanCertificateMarked fanCertificateResidual
    `Hypostructure.Graph.Strategy.Spine.fanCertificateDichotomy
    (by
      classical
      apply Classical.choice
      obtain ⟨packing, valid, maximal, component, present, charge, positive⟩ :=
        supportOf (ExactLedger.get previous typeBHighSurplus)
      let piece := current.object.pieceSupport
        (current.object.remainderSupport packing) component
      by_cases marked :
          ∀ centre ∈ piece,
            Graph.IsHighCentre current.object data.threshold centre →
            Nonempty (Graph.FanCertificateLabelling current.object
              data.windowOrder centre)
      · exact ⟨.inl (encodeMarked
          ⟨packing, valid, maximal, component, present, charge, positive,
            marked⟩)⟩
      · refine ⟨.inr (encodeResidual ?_)⟩
        -- Not every assigned centre is marked, so one of them is a
        -- fan-certificate residual centre.  `push Not` turns the negated
        -- `Nonempty` into `IsEmpty` directly.
        push Not at marked
        obtain ⟨centre, member, high, unmarked⟩ := marked
        exact ⟨packing, valid, maximal, component, present, charge, positive,
          centre, member, high, unmarked⟩)
    markedFresh residualFresh

/-! ## Node `[74]`/`[82]`: the hybrid B1 fan ledger

`lem:typeB-hybrid-B1`, and with it `lem:typeB-hybrid-incidence-budget`,
`def:typeB-hybrid-incidence` and parts (a)--(b) of
`prop:fan-closed-port-typeB-routing`.  The B2 arm of node `[72]`/`[81]` has
supplied the global disjointness; this row supplies the *local* payment, which is
what B2's clause (b) chooses between: at every certificate-marked centre of an
assigned Type B support, the non-`h` incidences of its cubic-closed neighbours
are pairwise distinct carriers, they split into `I_W` and `I_N`, their half-credit
pays `D_B`, the non-window half-credit covers the remaining demand `D_N`, and two
cubic-closed neighbours already make `D_B` positive.

Three prerequisites, all consumed.  `selection` supplies the avoidance that kills
the quadrilateral `u — h — v — z — u`, which is the whole reason two cubic-closed
neighbours cannot share a carrier.  `fanCertificateMarked` supplies a labelling at
the centre and `fanCertificateCap` turns it into `k ≤ α(D)`, which with the
registered `fanCapSlack` is the slack `k + 1 ≤ s·δ` the payment spends — the
manuscript's "and `k ≤ 8`".

`typeBDirectCycleFree` is *not* declared.  The manuscript states the budget lemma
under "none of the direct-cycle conclusions occurs", but its proof of the
disjointness uses only dyadic safety, and no other clause reads it either; the
fact is on this branch's index because the row runs after node `[72]`, and that is
a property of the cursor rather than of the manifest.  Declaring it would be a
false dependency. -/
@[reducible] noncomputable def hybridEntryRow
    (selection fanCertificateCap fanCertificateMarked typeBHybridEntry :
      FactKey (Input BranchState Presentation presentation data))
    (selectionNeCap : selection ≠ fanCertificateCap)
    (selectionNeMarked : selection ≠ fanCertificateMarked)
    (capNeMarked : fanCertificateCap ≠ fanCertificateMarked)
    (avoidsOf : (input : Input BranchState Presentation presentation data) →
      selection.At input →
      ¬ Graph.HasCycleWithLength data.LengthOK input.object)
    (capOf : (input : Input BranchState Presentation presentation data) →
      fanCertificateCap.At input →
      ∀ centre : input.object.Vertex,
        Graph.IsHighCentre input.object data.threshold centre →
        ∀ _marking :
            Graph.FanCertificateLabelling input.object data.windowOrder centre,
          input.object.degree centre ≤
            Graph.WindowCurvature.fanPackingCap data.windowOrder)
    (markedOf : (input : Input BranchState Presentation presentation data) →
      fanCertificateMarked.At input →
      ∃ packing : Finset (Finset input.object.Vertex),
        input.object.IsWindowPacking data.windowOrder packing ∧
          (∀ window : Finset input.object.Vertex,
            input.object.InducesWindow data.windowOrder window →
            ∃ member ∈ packing, ¬ Disjoint window member) ∧
          ∃ component ∈ input.object.canonicalPieces
              (input.object.remainderSupport packing),
            let piece := input.object.pieceSupport
              (input.object.remainderSupport packing) component
            input.object.NegativeNetCharge piece data.threshold
                data.dischargeScale ∧
              0 < input.object.ambientSurplus piece data.threshold ∧
              ∀ centre ∈ piece,
                Graph.IsHighCentre input.object data.threshold centre →
                Nonempty (Graph.FanCertificateLabelling input.object
                  data.windowOrder centre))
    (encode : (input : Input BranchState Presentation presentation data) →
      (∃ packing : Finset (Finset input.object.Vertex),
        input.object.IsWindowPacking data.windowOrder packing ∧
          (∀ window : Finset input.object.Vertex,
            input.object.InducesWindow data.windowOrder window →
            ∃ member ∈ packing, ¬ Disjoint window member) ∧
          ∃ component ∈ input.object.canonicalPieces
              (input.object.remainderSupport packing),
            let piece := input.object.pieceSupport
              (input.object.remainderSupport packing) component
            input.object.NegativeNetCharge piece data.threshold
                data.dischargeScale ∧
              0 < input.object.ambientSurplus piece data.threshold ∧
              ∀ centre ∈ piece,
            Graph.IsHighCentre input.object data.threshold centre →
            ∀ envelope windowSupport : Finset input.object.Vertex,
              (∀ left ∈ Graph.TypeBFanIncidence.closedNeighbours input.object
                  data.threshold envelope centre,
                ∀ right ∈ Graph.TypeBFanIncidence.closedNeighbours input.object
                    data.threshold envelope centre,
                  left ≠ right →
                  ∀ shared : input.object.Vertex,
                    shared ∈ Graph.TypeBHybridIncidence.nonHubIncidences
                      input.object centre left →
                    shared ∉ Graph.TypeBHybridIncidence.nonHubIncidences
                      input.object centre right) ∧
                Graph.TypeBHybridIncidence.windowIncidences input.object
                      data.threshold envelope windowSupport centre +
                    Graph.TypeBHybridIncidence.nonWindowIncidences input.object
                      data.threshold envelope windowSupport centre =
                  (data.threshold - 1) *
                    Graph.TypeBFanIncidence.closedCount input.object
                      data.threshold envelope centre ∧
                2 * Graph.TypeBFanIncidence.scaledDeficit input.object
                        data.threshold data.dischargeScale envelope centre ≤
                    (data.dischargeScale : Int) *
                      ((Graph.TypeBHybridIncidence.windowIncidences input.object
                          data.threshold envelope windowSupport centre : Int) +
                        (Graph.TypeBHybridIncidence.nonWindowIncidences
                          input.object data.threshold envelope windowSupport
                          centre : Int)) ∧
                Graph.TypeBHybridIncidence.nonWindowDemand input.object
                      data.threshold data.dischargeScale envelope windowSupport
                      centre ≤
                    (data.dischargeScale : Int) *
                      (Graph.TypeBHybridIncidence.nonWindowIncidences
                        input.object data.threshold envelope windowSupport
                        centre : Int) ∧
                (2 ≤ Graph.TypeBFanIncidence.closedCount input.object
                    data.threshold envelope centre →
                  0 < Graph.TypeBFanIncidence.scaledDeficit input.object
                    data.threshold data.dischargeScale envelope centre)) →
      typeBHybridEntry.At input) :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.hybridEntry
    { Requires := [selection, fanCertificateCap, fanCertificateMarked]
      Produces := [typeBHybridEntry]
      requiresUnique := by
        simp [selectionNeCap, selectionNeMarked, capNeMarked]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs => Classical.choice <| by
      let avoids := avoidsOf inputs.current (inputs.get selection)
      let cap := capOf inputs.current (inputs.get fanCertificateCap)
      obtain ⟨packing, valid, maximal, component, present, charge, positive,
          marked⟩ := markedOf inputs.current
        (inputs.get fanCertificateMarked)
      exact ⟨.cons (key := typeBHybridEntry)
        (encode inputs.current ⟨packing, valid, maximal, component, present,
          charge, positive,
          fun centre member high envelope windowSupport => by
            -- The marked fan's cap, and with it the manuscript's `k ≤ 8`.
            obtain ⟨marking⟩ :=
              marked centre member high
            have slack :
                inputs.current.object.degree centre + 1 ≤
                  data.dischargeScale * data.threshold :=
              le_trans (Nat.succ_le_succ (cap centre high marking))
                data.fanCapSlack
            refine ⟨?_, ?_, ?_, ?_, ?_⟩
            · -- The carriers are distinct: a shared endpoint is a quadrilateral.
              intro left leftMember right rightMember different shared
                leftIncidence rightIncidence
              exact Graph.TypeBHybridIncidence.endpoints_not_shared avoids
                data.quadrilateralAccepted
                (Graph.TypeBFanIncidence.mem_closedNeighbours_iff.mp leftMember)
                (Graph.TypeBFanIncidence.mem_closedNeighbours_iff.mp rightMember)
                different leftIncidence rightIncidence
            · exact Graph.TypeBHybridIncidence.windowIncidences_add_nonWindowIncidences
                _ _ _ _ _
            · exact Graph.TypeBHybridIncidence.hybridCapacity_pays _ _ _ _ _ _
                data.three_le_threshold slack
            · exact Graph.TypeBHybridIncidence.nonWindowCredit_ge_demand _ _ _ _
                _ _ data.three_le_threshold slack
            · intro two_le
              exact Graph.TypeBHybridIncidence.positive_deficit_of_two_le_closedCount
                _ _ _ _ _ two_le high data.highCentreDeficitSlack⟩)
        .nil⟩)

/-! ## Nodes `[78]`--`[79]`: the degree-four fan profile

`cor:degree-four-local-activation` and the profile Part VII's panel opens with.
Node `[78]` is the no arm of `[68]`, already committed: every high centre a Type B
support carries sits exactly at `δ + 1`.  This row reads that law and the normal
form and commits `[79]`'s readings at every such centre.

The activation dichotomy is `Graph.heavyCentreLocalDichotomy` -- the manuscript's
own argument, and the *same* theorem row 21 uses at a heavy centre.  What differs
is only what the degree buys afterwards: row 21 spends `k ≥ δ + 2` to get three
triangular ports, and here `k = δ + 1` gives `δ − 1`, which is the manuscript's
"at least `4 − |U| ≥ 2`" at its own baseline.  No second dichotomy theorem is
introduced for the degree-four case.

The three profile readings are `TypeBFanIncidence.degreeFourProfile`: the centre
surplus, the count bound `c ≤ k`, and the deficit identity
`D_B = c − (δ − (k+1)α)` at the registered discharge scale.  Nothing writes `7/4`
or `11`; the deficit is carried at the scale `s` as an integer, so the rational
never appears and nothing rounds. -/
@[reducible] noncomputable def degreeFourProfileRow
    (highCentreNormalForm typeBDegreeFourCentres typeBDegreeFourProfile :
      FactKey (Input BranchState Presentation presentation data))
    (normalNeDegreeFour : highCentreNormalForm ≠ typeBDegreeFourCentres)
    (normalFormOf : (input : Input BranchState Presentation presentation data) →
      highCentreNormalForm.At input →
      ∀ centre : input.object.Vertex,
        Graph.IsHighCentre input.object data.threshold centre →
        Graph.NormalForm input.object data.threshold centre)
    (degreeFourOf : (input : Input BranchState Presentation presentation data) →
      typeBDegreeFourCentres.At input →
      ∃ packing : Finset (Finset input.object.Vertex),
        input.object.IsWindowPacking data.windowOrder packing ∧
          (∀ window : Finset input.object.Vertex,
            input.object.InducesWindow data.windowOrder window →
            ∃ member ∈ packing, ¬ Disjoint window member) ∧
          ∃ component ∈ input.object.canonicalPieces
              (input.object.remainderSupport packing),
            let piece := input.object.pieceSupport
              (input.object.remainderSupport packing) component
            input.object.NegativeNetCharge piece data.threshold
                data.dischargeScale ∧
              0 < input.object.ambientSurplus piece data.threshold ∧
              ∀ centre ∈ piece,
                Graph.IsHighCentre input.object data.threshold centre →
                input.object.degree centre = data.threshold + 1)
    (encode : (input : Input BranchState Presentation presentation data) →
      (∃ packing : Finset (Finset input.object.Vertex),
        input.object.IsWindowPacking data.windowOrder packing ∧
          (∀ window : Finset input.object.Vertex,
            input.object.InducesWindow data.windowOrder window →
            ∃ member ∈ packing, ¬ Disjoint window member) ∧
          ∃ component ∈ input.object.canonicalPieces
              (input.object.remainderSupport packing),
            let piece := input.object.pieceSupport
              (input.object.remainderSupport packing) component
            input.object.NegativeNetCharge piece data.threshold
                data.dischargeScale ∧
              0 < input.object.ambientSurplus piece data.threshold ∧
              (∀ centre ∈ piece,
                Graph.IsHighCentre input.object data.threshold centre →
                input.object.degree centre = data.threshold + 1) ∧
              ∀ centre ∈ piece,
                input.object.degree centre = data.threshold + 1 →
                ((∃ left right : input.object.Vertex,
                      Graph.FanCompatible input.object centre left right) ∨
                    data.threshold - 1 ≤
                      (Graph.triangularEndpoints input.object centre).card) ∧
                  input.object.degree centre - data.threshold = 1 ∧
                  ∀ envelope : Finset input.object.Vertex,
                    Graph.TypeBFanIncidence.closedCount input.object
                        data.threshold envelope centre ≤ data.threshold + 1 ∧
                      Graph.TypeBFanIncidence.scaledDeficit input.object
                          data.threshold data.dischargeScale envelope centre =
                        (data.dischargeScale : Int) *
                            (Graph.TypeBFanIncidence.closedCount input.object
                              data.threshold envelope centre : Int) -
                          (data.dischargeScale : Int) *
                            (data.threshold : Int) +
                          ((data.threshold : Int) + 2)) →
      typeBDegreeFourProfile.At input) :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.degreeFourProfile
    { Requires := [highCentreNormalForm, typeBDegreeFourCentres]
      Produces := [typeBDegreeFourProfile]
      requiresUnique := by simp [normalNeDegreeFour]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs => Classical.choice <| by
      let normal :=
        normalFormOf inputs.current (inputs.get highCentreNormalForm)
      obtain ⟨packing, valid, maximal, component, present, charge, positive,
          degreeFour⟩ := degreeFourOf inputs.current
        (inputs.get typeBDegreeFourCentres)
      exact ⟨.cons (key := typeBDegreeFourProfile)
        (encode inputs.current ⟨packing, valid, maximal, component, present,
          charge, positive, degreeFour,
          fun centre _member degree => by
            -- A centre one above the baseline is a high centre, so the normal
            -- form applies and `cor:degree-four-local-activation` fires.
            have high : Graph.IsHighCentre inputs.current.object data.threshold
                centre := by
              rw [Graph.IsHighCentre, degree]
              omega
            refine ⟨?_, ?_⟩
            · rcases Graph.heavyCentreLocalDichotomy (normal centre high) with
                compatible | alternative
              · exact Or.inl compatible
              · exact Or.inr (by omega)
            · obtain ⟨surplus, _counted, _identity, _range⟩ :=
                Graph.TypeBFanIncidence.degreeFourProfile inputs.current.object
                  data.threshold data.dischargeScale ∅ degree
              refine ⟨surplus, fun envelope => ?_⟩
              obtain ⟨_surplus, counted, identity, _range⟩ :=
                Graph.TypeBFanIncidence.degreeFourProfile inputs.current.object
                  data.threshold data.dischargeScale envelope degree
              exact ⟨counted, identity⟩⟩)
        .nil⟩)

/-! ## Node `[72]`, first half: is a direct fan-window cycle present?

`lem:typeB-direct-fan-window-cycles` and `lem:typeB-two-window-cycles`.  Before
any incidence credit is counted, the four direct configurations are removed
structurally: a same-window closed neighbour whose label gap closes a cycle, two
closed neighbours whose wedge through the centre closes one, two whose closed
labels interlace, and two with incidences to distinct packed windows.  Each
display *builds* a cycle whose length the manuscript's arithmetic side condition
declares accepted, so the arm that takes the configuration is uninhabited on a
branch whose object avoids those lengths -- which is why this row's yes arm
closes and its no arm carries `def:direct-cycle-free-closed-pair` forward.

Nothing here writes `{2, 6}` or `{0, 4, 12}`.  Each side condition is
`data.LengthOK` of the length of its own cycle; at the registered target and
window order those readings are exactly the manuscript's sets.

The split is `Classical.em` on the configuration proposition, so no window, no
centre and no neighbour pair is extracted to build the branch, and the arm not
taken supplies the other arm's clause.  This is a `Decision`: the arm not taken
is absent from the taken branch's key index. -/
noncomputable def directCycleDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous :
      ExactLedger (Input BranchState Presentation presentation data)
        current known)
    (typeBDirectCycle typeBDirectCycleFree :
      FactKey (Input BranchState Presentation presentation data))
    (typeBHighSurplus : FactKey
      (Input BranchState Presentation presentation data))
    [Core.Residual.FactKeys.Has typeBHighSurplus known]
    (supportOf : typeBHighSurplus.At current →
      ∃ packing : Finset (Finset current.object.Vertex),
        current.object.IsWindowPacking data.windowOrder packing ∧
          (∀ window : Finset current.object.Vertex,
            current.object.InducesWindow data.windowOrder window →
            ∃ member ∈ packing, ¬ Disjoint window member) ∧
          ∃ component ∈ current.object.canonicalPieces
              (current.object.remainderSupport packing),
            let piece := current.object.pieceSupport
              (current.object.remainderSupport packing) component
            current.object.NegativeNetCharge piece data.threshold
                data.dischargeScale ∧
              0 < current.object.ambientSurplus piece data.threshold)
    (encodeConfiguration :
      (∃ packing : Finset (Finset current.object.Vertex),
        current.object.IsWindowPacking data.windowOrder packing ∧
          (∀ window : Finset current.object.Vertex,
            current.object.InducesWindow data.windowOrder window →
            ∃ member ∈ packing, ¬ Disjoint window member) ∧
          ∃ component ∈ current.object.canonicalPieces
              (current.object.remainderSupport packing),
            let piece := current.object.pieceSupport
              (current.object.remainderSupport packing) component
            current.object.NegativeNetCharge piece data.threshold
                data.dischargeScale ∧
              0 < current.object.ambientSurplus piece data.threshold ∧
              ∃ centre ∈ piece,
                Graph.IsHighCentre current.object data.threshold centre ∧
                  Graph.TypeBDirectCycle.DirectCycleConfiguration current.object
                    data.windowOrder data.LengthOK packing centre) →
      typeBDirectCycle.At current)
    (encodeFree :
      (∃ packing : Finset (Finset current.object.Vertex),
        current.object.IsWindowPacking data.windowOrder packing ∧
          (∀ window : Finset current.object.Vertex,
            current.object.InducesWindow data.windowOrder window →
            ∃ member ∈ packing, ¬ Disjoint window member) ∧
          ∃ component ∈ current.object.canonicalPieces
              (current.object.remainderSupport packing),
            let piece := current.object.pieceSupport
              (current.object.remainderSupport packing) component
            current.object.NegativeNetCharge piece data.threshold
                data.dischargeScale ∧
              0 < current.object.ambientSurplus piece data.threshold ∧
              ∀ centre ∈ piece,
                Graph.IsHighCentre current.object data.threshold centre →
                Graph.TypeBDirectCycle.DirectCycleFree current.object
                  data.windowOrder data.LengthOK packing centre) →
      typeBDirectCycleFree.At current)
    (cycleFresh : typeBDirectCycle ∉ known)
    (freeFresh : typeBDirectCycleFree ∉ known) :
    Decision typeBDirectCycle typeBDirectCycleFree previous :=
  Decision.run previous typeBDirectCycle typeBDirectCycleFree
    `Hypostructure.Graph.Strategy.Spine.directCycleDichotomy
    (by
      classical
      apply Classical.choice
      obtain ⟨packing, valid, maximal, component, present, charge,
        positive⟩ := supportOf (ExactLedger.get previous typeBHighSurplus)
      let piece := current.object.pieceSupport
        (current.object.remainderSupport packing) component
      by_cases configuration :
          ∃ centre ∈ piece,
            Graph.IsHighCentre current.object data.threshold centre ∧
              Graph.TypeBDirectCycle.DirectCycleConfiguration current.object
                data.windowOrder data.LengthOK packing centre
      · exact ⟨.inl (encodeConfiguration
          ⟨packing, valid, maximal, component, present, charge, positive,
            configuration⟩)⟩
      · exact ⟨.inr (encodeFree
          ⟨packing, valid, maximal, component, present, charge, positive,
            fun centre member high present =>
              configuration ⟨centre, member, high, present⟩⟩)⟩)
    cycleFresh freeFresh

/-! ## Node `[72]`/`[81]`, second half: does the B2 disjoint ledger exist?

(B2) of `def:typeB-bridge-statements`.  With the local fan-window ledger complete
-- the direct configurations removed by the row above -- the question is whether
the assigned high-degree centres of the selected canonical Type B support admit
a *simultaneous* choice of candidate ledger entries with pairwise disjoint
carriers.  It is a global question: an entry
that pays at one centre may need a carrier another centre has already spent, so
no local count decides it.

Both arms are the manuscript's own mathematics rather than a proposition and its
negation.  The no arm is `lem:typeB-bridge-to-overlap`: a disjoint-carrier
failure is *represented* by a minimal Type B overlap obstruction, the smallest
failing subfamily of demands, which is the object node `[73]`/`[83]` hands to the
fan-mass accounting.  The yes arm records only the disjoint choice.  Its exact
B2(a)--(c) refinement is committed by the fact-only row below; B2(d) is not
claimed by either row.

This is a `Decision`, so the arm not taken is absent from the taken branch's key
index; the fan-mass row can no more read the ledger than the bridge-reduction row
can read the obstruction. -/
noncomputable def b2AssignmentDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous :
      ExactLedger (Input BranchState Presentation presentation data)
        current known)
    (typeBB2Choice typeBOverlapObstruction :
      FactKey (Input BranchState Presentation presentation data))
    (typeBDirectCycleFree : FactKey
      (Input BranchState Presentation presentation data))
    [Core.Residual.FactKeys.Has typeBDirectCycleFree known]
    (freeOf : typeBDirectCycleFree.At current →
      ∃ packing : Finset (Finset current.object.Vertex),
        current.object.IsWindowPacking data.windowOrder packing ∧
          (∀ window : Finset current.object.Vertex,
            current.object.InducesWindow data.windowOrder window →
            ∃ member ∈ packing, ¬ Disjoint window member) ∧
          ∃ component ∈ current.object.canonicalPieces
              (current.object.remainderSupport packing),
            let piece := current.object.pieceSupport
              (current.object.remainderSupport packing) component
            current.object.NegativeNetCharge piece data.threshold
                data.dischargeScale ∧
              0 < current.object.ambientSurplus piece data.threshold ∧
              ∀ centre ∈ piece,
                Graph.IsHighCentre current.object data.threshold centre →
                Graph.TypeBDirectCycle.DirectCycleFree current.object
                  data.windowOrder data.LengthOK packing centre)
    (encodeChoice :
      (∃ packing : Finset (Finset current.object.Vertex),
        current.object.IsWindowPacking data.windowOrder packing ∧
          (∀ window : Finset current.object.Vertex,
            current.object.InducesWindow data.windowOrder window →
            ∃ member ∈ packing, ¬ Disjoint window member) ∧
          ∃ canonicalPiece :
              Graph.TypeBRefinedSupport.CanonicalPiece current.object packing,
            current.object.NegativeNetCharge canonicalPiece.vertices data.threshold
                data.dischargeScale ∧
              0 < current.object.ambientSurplus canonicalPiece.vertices
                data.threshold ∧
              Graph.TypeBRefinedSupport.HasDisjointChoice current.object
                data.threshold data.dischargeScale canonicalPiece
                (Graph.TypeBRefinedSupport.centres current.object data.threshold
                  canonicalPiece.vertices)) →
      typeBB2Choice.At current)
    (encodeObstruction :
      (∃ packing : Finset (Finset current.object.Vertex),
        current.object.IsWindowPacking data.windowOrder packing ∧
          (∀ window : Finset current.object.Vertex,
            current.object.InducesWindow data.windowOrder window →
            ∃ member ∈ packing, ¬ Disjoint window member) ∧
          ∃ canonicalPiece :
              Graph.TypeBRefinedSupport.CanonicalPiece current.object packing,
            current.object.NegativeNetCharge canonicalPiece.vertices data.threshold
                data.dischargeScale ∧
              0 < current.object.ambientSurplus canonicalPiece.vertices
                data.threshold ∧
              Nonempty (Graph.TypeBRefinedSupport.OverlapObstruction
                current.object data.threshold data.dischargeScale canonicalPiece)) →
      typeBOverlapObstruction.At current)
    (choiceFresh : typeBB2Choice ∉ known)
    (obstructionFresh : typeBOverlapObstruction ∉ known) :
    Decision typeBB2Choice typeBOverlapObstruction previous :=
  Decision.run previous typeBB2Choice typeBOverlapObstruction
    `Hypostructure.Graph.Strategy.Spine.b2AssignmentDichotomy
    (by
      classical
      apply Classical.choice
      obtain ⟨packing, valid, maximal, component, componentMem, negative,
        positive, _directFree⟩ :=
        freeOf (ExactLedger.get previous typeBDirectCycleFree)
      let canonicalPiece :
          Graph.TypeBRefinedSupport.CanonicalPiece current.object packing :=
        ⟨component, componentMem⟩
      rcases Graph.TypeBRefinedSupport.b2_or_overlap current.object
          data.threshold data.dischargeScale canonicalPiece with
        choice | obstruction
      · exact ⟨.inl (encodeChoice
          ⟨packing, valid, maximal, canonicalPiece, negative, positive, choice⟩)⟩
      · exact ⟨.inr (encodeObstruction
          ⟨packing, valid, maximal, canonicalPiece, negative, positive,
            obstruction⟩)⟩)
    choiceFresh obstructionFresh

/-! ## B2 and the live Type B post-ledger core

The successful finite choice above is turned into the manuscript's literal
augmented-ledger partition.  Remainder normalization supplies both window
freeness and the empty internal baseline core; the latter implies hereditary
Type A uncompressibility.  Selection supplies contextual target safety.  Every
remaining connected component is therefore passed to the existing Type A
hygiene theorem on the same ledger, and the component fact reads the ledger's
own `noHighCentre_remaining` theorem for the Type B maximal-core clause.  The
same fact also reads the branch's `uncompressible` entry and packages actual
component-indexed exit-`(7)` productions into the canonical grouped decorated
envelope. -/
@[reducible] noncomputable def disjointPostLedgerComponentsRow
    (typeBB2Choice selection uncompressible remainderNormalized
      typeBDisjointLedger :
      FactKey (Input BranchState Presentation presentation data))
    (requiredUnique :
      [typeBB2Choice, selection, uncompressible, remainderNormalized].Nodup)
    (choiceOf : (input : Input BranchState Presentation presentation data) →
      typeBB2Choice.At input →
      ∃ packing : Finset (Finset input.object.Vertex),
        input.object.IsWindowPacking data.windowOrder packing ∧
          (∀ window : Finset input.object.Vertex,
            input.object.InducesWindow data.windowOrder window →
            ∃ member ∈ packing, ¬ Disjoint window member) ∧
          ∃ canonicalPiece :
              Graph.TypeBRefinedSupport.CanonicalPiece input.object packing,
            input.object.NegativeNetCharge canonicalPiece.vertices data.threshold
                data.dischargeScale ∧
              0 < input.object.ambientSurplus canonicalPiece.vertices
                data.threshold ∧
              Graph.TypeBRefinedSupport.HasDisjointChoice input.object
                data.threshold data.dischargeScale canonicalPiece
                (Graph.TypeBRefinedSupport.centres input.object data.threshold
                  canonicalPiece.vertices))
    (avoidsOf : (input : Input BranchState Presentation presentation data) →
      selection.At input →
        ¬ Graph.HasCycleWithLength data.LengthOK input.object)
    (uncompressibleOf :
      (input : Input BranchState Presentation presentation data) →
      uncompressible.At input →
      ∀ support : Finset input.object.Vertex,
        ¬ Graph.Strategy.InterfaceReplacement.CompressibleSupport
            (Graph.MinimumDegreeAtLeast data.threshold)
            (Graph.HasCycleWithLength data.LengthOK) input.object support)
    (normalizedOf : (input : Input BranchState Presentation presentation data) →
      remainderNormalized.At input →
      ∀ packing : Finset (Finset input.object.Vertex),
        input.object.IsWindowPacking data.windowOrder packing →
        (∀ window : Finset input.object.Vertex,
          input.object.InducesWindow data.windowOrder window →
          ∃ member ∈ packing, ¬ Disjoint window member) →
        ∀ support : Finset input.object.Vertex,
          support ⊆ input.object.remainderSupport packing →
          ¬ input.object.InducesWindow data.windowOrder support ∧
            ¬ Graph.MinimumDegreeAtLeast data.threshold
              (input.object.induce support))
    (encode : (input : Input BranchState Presentation presentation data) →
      (∃ packing : Finset (Finset input.object.Vertex),
        input.object.IsWindowPacking data.windowOrder packing ∧
          (∀ window : Finset input.object.Vertex,
            input.object.InducesWindow data.windowOrder window →
            ∃ member ∈ packing, ¬ Disjoint window member) ∧
          ∃ canonicalPiece :
              Graph.TypeBRefinedSupport.CanonicalPiece input.object packing,
            input.object.NegativeNetCharge canonicalPiece.vertices data.threshold
                data.dischargeScale ∧
              0 < input.object.ambientSurplus canonicalPiece.vertices
                data.threshold ∧
              ∃ ledger : Graph.TypeBRefinedSupport.DisjointLedger input.object
                  data.threshold data.dischargeScale canonicalPiece,
                ledger.ExactAugmentedLedgerRefinement ∧
                  (∀ component : Graph.SupportComponents.Connected.Component
                        input.object ledger.remainingCore,
                      component ∈ Graph.SupportComponents.Connected.order
                          input.object ledger.remainingCore →
                        Graph.TypeBPostLedgerCore.PostLedgerComponent
                          data.typeABPresentation ledger component) ∧
                  ∀ components :
                      Finset (Graph.TypeBMaximalCompletion.RemainingComponent
                        ledger),
                    (∀ component ∈ components,
                      component ∈ Graph.SupportComponents.Connected.order
                        input.object ledger.remainingCore) →
                      ∀ production : ∀ component :
                          Graph.TypeBMaximalCompletion.SelectedComponent ledger
                            components,
                        Graph.TypeBMaximalCompletion.ComponentExitSeven ledger
                          component.1 data.LengthOK
                          (handoffHighDegree input.object)
                          (handoffAbsorbing data input.object packing),
                        ∃ grouped :
                          Graph.DecoratedHandoff.GroupedEnvelopes input.object
                            data.LengthOK
                            (handoffUncompressible data input.object)
                            (handoffWindowFree data input.object)
                            (handoffHighDegree input.object)
                            (handoffAbsorbing data input.object packing)
                            (Graph.TypeBMaximalCompletion.SelectedComponent
                              ledger components),
                          (∀ component :
                              Graph.TypeBMaximalCompletion.SelectedComponent
                                ledger components,
                            (grouped.envelope component).core =
                              Graph.SupportComponents.Connected.vertices
                                input.object ledger.remainingCore component.1) ∧
                            ∀ centre : input.object.Vertex,
                              centre ∈ grouped.centres ↔
                                ∃ component :
                                  Graph.TypeBMaximalCompletion.SelectedComponent
                                    ledger components,
                                  centre =
                                    (production component).separation.separator) →
        typeBDisjointLedger.At input) :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.disjointPostLedgerComponents
    { Requires := [typeBB2Choice, selection, uncompressible, remainderNormalized]
      Produces := [typeBDisjointLedger]
      requiresUnique := requiredUnique
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let choiceFact := choiceOf inputs.current (inputs.get typeBB2Choice)
      let avoids := avoidsOf inputs.current (inputs.get selection)
      let uncompressibleFact := uncompressibleOf inputs.current
        (inputs.get uncompressible)
      let normalized := normalizedOf inputs.current
        (inputs.get remainderNormalized)
      .cons (key := typeBDisjointLedger)
        (encode inputs.current (by
          classical
          obtain ⟨packing, valid, maximal, canonicalPiece, negative, positive,
            choice⟩ := choiceFact
          let ledger : Graph.TypeBRefinedSupport.DisjointLedger
              inputs.current.object data.threshold data.dischargeScale
                canonicalPiece :=
            ⟨Classical.choice choice⟩
          have noBaselineSubsupport : ∀ support : Finset inputs.current.object.Vertex,
              support ⊆ inputs.current.object.remainderSupport packing →
                ¬ Graph.MinimumDegreeAtLeast data.threshold
                  (inputs.current.object.induce support) := by
            intro support subset
            exact (normalized packing valid maximal support subset).2
          have pieceFree : Graph.InducedPathFree
              (inputs.current.object.induce canonicalPiece.vertices)
              data.windowOrder :=
            Graph.FiniteObject.inducedPathFree_induce_of_forall
              inputs.current.object
              (fun support subset =>
                (normalized packing valid maximal support
                  (subset.trans canonicalPiece.vertices_subset_remainder)).1)
          have emptyInternal : Graph.TypeAB.EmptyInternalThreeCore
              data.typeABPresentation inputs.current.object
                canonicalPiece.vertices :=
            Graph.TypeBPostLedgerCore.emptyInternalThreeCore_of_noBaselineSubsupport
              (threshold := data.threshold) rfl
              (fun support subset =>
                noBaselineSubsupport support
                  (subset.trans canonicalPiece.vertices_subset_remainder))
          have targetSafe : Graph.TypeAB.ContextuallyDyadicSafe
              data.typeABPresentation inputs.current.object := by
            simpa [Graph.TypeAB.ContextuallyDyadicSafe,
              Data.typeABPresentation] using avoids
          have hereditary : Graph.TypeAB.HereditarilyTargetUncompressible
              data.typeABPresentation inputs.current.object
                canonicalPiece.vertices :=
            Graph.TypeAB.hereditarilyTargetUncompressible_of_emptyInternalThreeCore
              emptyInternal
          have baseline : ∀ vertex : inputs.current.object.Vertex,
              data.threshold ≤ inputs.current.object.degree vertex := fun vertex =>
            le_trans inputs.current.baseline
              (inputs.current.object.minDegree_le_degree vertex)
          let componentFacts :
              ∀ component : Graph.SupportComponents.Connected.Component
                  inputs.current.object ledger.remainingCore,
                component ∈ Graph.SupportComponents.Connected.order
                    inputs.current.object ledger.remainingCore →
                  Graph.TypeBPostLedgerCore.PostLedgerComponent
                    data.typeABPresentation ledger component :=
            fun component componentMember =>
              Graph.TypeBPostLedgerCore.postLedgerCoreHygiene
                data.typeABPresentation ledger component componentMember rfl
                noBaselineSubsupport pieceFree targetSafe hereditary baseline
          have groupedCoverage :
              ∀ components :
                  Finset (Graph.TypeBMaximalCompletion.RemainingComponent
                    ledger),
                (∀ component ∈ components,
                  component ∈ Graph.SupportComponents.Connected.order
                    inputs.current.object ledger.remainingCore) →
                  ∀ production : ∀ component :
                      Graph.TypeBMaximalCompletion.SelectedComponent ledger
                        components,
                    Graph.TypeBMaximalCompletion.ComponentExitSeven ledger
                      component.1 data.LengthOK
                      (handoffHighDegree inputs.current.object)
                      (handoffAbsorbing data inputs.current.object packing),
                    ∃ grouped :
                      Graph.DecoratedHandoff.GroupedEnvelopes
                        inputs.current.object data.LengthOK
                        (handoffUncompressible data inputs.current.object)
                        (handoffWindowFree data inputs.current.object)
                        (handoffHighDegree inputs.current.object)
                        (handoffAbsorbing data inputs.current.object packing)
                        (Graph.TypeBMaximalCompletion.SelectedComponent ledger
                          components),
                      (∀ component :
                          Graph.TypeBMaximalCompletion.SelectedComponent ledger
                            components,
                        (grouped.envelope component).core =
                          Graph.SupportComponents.Connected.vertices
                            inputs.current.object ledger.remainingCore
                            component.1) ∧
                        ∀ centre : inputs.current.object.Vertex,
                          centre ∈ grouped.centres ↔
                            ∃ component :
                              Graph.TypeBMaximalCompletion.SelectedComponent
                                ledger components,
                              centre =
                                (production component).separation.separator := by
            intro components componentsSubset production
            have windowFree : ∀ component, component ∈ components →
                handoffWindowFree data inputs.current.object
                  (Graph.SupportComponents.Connected.vertices
                    inputs.current.object ledger.remainingCore component) := by
              intro component componentMember window windowSubset induces
              have orderMember := componentsSubset component componentMember
              have componentData := componentFacts component orderMember
              exact (normalized packing valid maximal window
                (windowSubset.trans componentData.containedInRemainder)).1
                induces
            let grouped :=
              Graph.TypeBMaximalCompletion.groupedOfComponentExitSeven
                ledger components production avoids windowFree
                uncompressibleFact
            refine ⟨grouped, ?_, ?_⟩
            · intro component
              exact Graph.TypeBMaximalCompletion.Grouped.envelope_core
                ledger components production avoids windowFree
                uncompressibleFact component
            · intro centre
              exact Graph.TypeBMaximalCompletion.Grouped.mem_centres_iff
                ledger components production avoids windowFree
                uncompressibleFact centre
          exact ⟨packing, valid, maximal, canonicalPiece, negative, positive,
            ledger, ledger.exactAugmentedLedgerRefinement,
            componentFacts, groupedCoverage⟩))
        .nil)

/-! ## Nodes `[73]`/`[75]` and `[83]`/`[84]`: Type B bridge fan mass

This row extends the exact cursor that has already committed a Type B bridge
residual.  The residual fact is a declared requirement and is read through the
sealed inputs before the single bridge-mass fact is appended.
-/
@[reducible] noncomputable def bridgeFanMassRow
    (bridgeResidual typeBBridgeMass :
      FactKey (Input BranchState Presentation presentation data))
    (distinct : bridgeResidual ≠ typeBBridgeMass)
    (encode : (input : Input BranchState Presentation presentation data) →
      bridgeResidual.At input →
      ((∀ packing : Finset (Finset input.object.Vertex),
        input.object.IsWindowPacking data.windowOrder packing →
        ∀ piece : Finset input.object.Vertex,
          piece ⊆ input.object.remainderSupport packing →
          Graph.SupportComponents.Connected.ConnectedOn input.object piece →
          input.object.NegativeNetCharge piece data.threshold data.dischargeScale →
          0 < input.object.ambientSurplus piece data.threshold →
          (∀ centre ∈ piece, Graph.IsHighCentre input.object data.threshold centre →
            ∀ envelope : Finset input.object.Vertex,
              Graph.TypeBEnvelopeCharge.envelopeNegativePart input.object data.threshold
                  data.dischargeScale envelope centre ≤
                data.bridgeMassFactor * data.dischargeScale *
                  (input.object.degree centre - data.threshold)) ∧
            (Graph.TypeBEnvelopeCharge.BridgeResidualComponentAt input.object piece
                data.threshold data.dischargeScale →
              piece.card + data.dischargeScale *
                    input.object.ambientSurplus piece data.threshold ≤
                data.dischargeScale * input.object.positiveDeficiency piece data.threshold +
                  data.bridgeMassFactor * data.dischargeScale *
                    input.object.ambientSurplus piece data.threshold)) ∧
        (∀ packing : Finset (Finset input.object.Vertex),
          input.object.IsWindowPacking data.windowOrder packing →
          ∀ route8 : Finset (Graph.SupportComponents.Connected.Component input.object
              (input.object.remainderSupport packing)),
            (∀ piece ∈ route8,
              input.object.ambientSurplus (input.object.pieceSupport
                (input.object.remainderSupport packing) piece) data.threshold = 0) →
            (∀ piece ∈ input.object.canonicalPieces (input.object.remainderSupport packing),
              piece ∉ route8 →
              Graph.TypeBEnvelopeCharge.BridgeResidualComponentAt input.object
                (input.object.pieceSupport (input.object.remainderSupport packing) piece)
                data.threshold data.dischargeScale) →
            ∑ piece ∈ input.object.canonicalPieces (input.object.remainderSupport packing),
                ((input.object.pieceSupport (input.object.remainderSupport packing) piece).card +
                    data.dischargeScale * input.object.ambientSurplus
                      (input.object.pieceSupport (input.object.remainderSupport packing) piece)
                      data.threshold -
                  data.dischargeScale * input.object.positiveDeficiency
                    (input.object.pieceSupport (input.object.remainderSupport packing) piece)
                    data.threshold) ≤
              Graph.TypeBEnvelopeCharge.route8Deficit input.object
                  (input.object.remainderSupport packing) data.threshold
                  data.dischargeScale route8 +
                data.bridgeMassFactor * data.dischargeScale *
                  input.object.degreeSurplus data.threshold) ∧
        ∀ packing : Finset (Finset input.object.Vertex),
          input.object.IsWindowPacking data.windowOrder packing →
          ∀ ordinary grouped : Finset input.object.Vertex,
            ordinary ⊆ input.object.remainderSupport packing →
            grouped ⊆ input.object.remainderSupport packing →
            ∀ ordinaryRoute8 : Finset
                (Graph.SupportComponents.Connected.Component input.object ordinary),
            ∀ groupedRoute8 : Finset
                (Graph.SupportComponents.Connected.Component input.object grouped),
              (∀ piece ∈ ordinaryRoute8,
                input.object.ambientSurplus (input.object.pieceSupport ordinary piece)
                  data.threshold = 0) →
              (∀ piece ∈ groupedRoute8,
                input.object.ambientSurplus (input.object.pieceSupport grouped piece)
                  data.threshold = 0) →
              (∀ piece ∈ input.object.canonicalPieces ordinary, piece ∉ ordinaryRoute8 →
                Graph.TypeBEnvelopeCharge.BridgeResidualComponentAt input.object
                  (input.object.pieceSupport ordinary piece) data.threshold
                  data.dischargeScale) →
              (∀ piece ∈ input.object.canonicalPieces grouped, piece ∉ groupedRoute8 →
                Graph.TypeBEnvelopeCharge.BridgeResidualComponentAt input.object
                  (input.object.pieceSupport grouped piece) data.threshold
                  data.dischargeScale) →
              ∑ piece ∈ input.object.canonicalPieces ordinary,
                  ((input.object.pieceSupport ordinary piece).card +
                      data.dischargeScale * input.object.ambientSurplus
                        (input.object.pieceSupport ordinary piece) data.threshold -
                    data.dischargeScale * input.object.positiveDeficiency
                      (input.object.pieceSupport ordinary piece) data.threshold) +
                ∑ piece ∈ input.object.canonicalPieces grouped,
                  ((input.object.pieceSupport grouped piece).card +
                      data.dischargeScale * input.object.ambientSurplus
                        (input.object.pieceSupport grouped piece) data.threshold -
                    data.dischargeScale * input.object.positiveDeficiency
                      (input.object.pieceSupport grouped piece) data.threshold) ≤
                Graph.TypeBEnvelopeCharge.route8Deficit input.object ordinary
                    data.threshold data.dischargeScale ordinaryRoute8 +
                  Graph.TypeBEnvelopeCharge.route8Deficit input.object grouped
                      data.threshold data.dischargeScale groupedRoute8 +
                    2 * (data.bridgeMassFactor * data.dischargeScale *
                      input.object.degreeSurplus data.threshold))
 →
      typeBBridgeMass.At input) :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.typeBBridgeMass
    (rowManifest bridgeResidual typeBBridgeMass distinct)
    (fun inputs =>
      let bridgeResidualFact := inputs.get bridgeResidual
      .cons (key := typeBBridgeMass)
        (encode inputs.current bridgeResidualFact (by
          have baseline : ∀ vertex : inputs.current.object.Vertex,
              data.threshold ≤ inputs.current.object.degree vertex := fun vertex =>
            le_trans inputs.current.baseline
              (inputs.current.object.minDegree_le_degree vertex)
          refine ⟨?_, ?_, ?_⟩
          · intro _packing _valid piece _inside _connected _charge _positive
            refine ⟨fun centre _member high envelope => ?_, fun component => ?_⟩
            · exact Graph.TypeBEnvelopeCharge.envelopeNegativePart_le _ high
                data.bridgeMassSlack
            · exact Graph.TypeBEnvelopeCharge.bridgeDeficitBound
                inputs.current.object piece data.bridgeMassSlack baseline
                component.1 component.2
          · intro packing _valid route8 route8Surplus components
            exact Graph.TypeBEnvelopeCharge.bridgeResidualMass_le_route8
              inputs.current.object _ route8 data.bridgeMassSlack baseline
              route8Surplus components
          · intro _packing _valid ordinary grouped _ordinaryInside _groupedInside
              ordinaryRoute8 groupedRoute8
              ordinarySurplus groupedSurplus ordinaryComponents groupedComponents
            exact Graph.TypeBEnvelopeCharge.bridgeResidualMass_le_twice
              inputs.current.object ordinary grouped ordinaryRoute8 groupedRoute8
              data.bridgeMassSlack baseline ordinarySurplus groupedSurplus
              ordinaryComponents groupedComponents))
        .nil)

omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def fanCertificateResidualMassRow :
    @AtomicStrategy (Input BranchState Presentation presentation data) _
      (instFactSystem (BranchState := BranchState)
        (Presentation := Presentation) (presentation := presentation)
        (data := data)) :=
  letI : FactSystem (Input BranchState Presentation presentation data) :=
    instFactSystem (BranchState := BranchState) (Presentation := Presentation)
      (presentation := presentation) (data := data)
  @factOnly (Input BranchState Presentation presentation data) _
    (instFactSystem (BranchState := BranchState)
      (Presentation := Presentation) (presentation := presentation)
      (data := data))
    `Hypostructure.Graph.Strategy.Spine.fanCertificateResidualMass
    { Requires := [K .fanCertificateResidual]
      Produces := [K .fanCertificateResidualMass]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let residual := inputs.get (K .fanCertificateResidual)
      .cons (key := K .fanCertificateResidualMass) (by
        refine ⟨?_⟩
        obtain ⟨packing, valid, maximal, component, componentMem, negative,
          positive, centre, centreMem, high, empty⟩ := residual.down
        exact ⟨packing, valid, maximal, component, componentMem, negative,
          positive, centre, centreMem, high, empty, fun envelope =>
            Graph.TypeBEnvelopeCharge.envelopeNegativePart_le envelope high
              data.bridgeMassSlack⟩)
      .nil)
    0 0

omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def typeBOverlapObstructionMassRow :
    @AtomicStrategy (Input BranchState Presentation presentation data) _
      (instFactSystem (BranchState := BranchState)
        (Presentation := Presentation) (presentation := presentation)
        (data := data)) :=
  letI : FactSystem (Input BranchState Presentation presentation data) :=
    instFactSystem (BranchState := BranchState) (Presentation := Presentation)
      (presentation := presentation) (data := data)
  @factOnly (Input BranchState Presentation presentation data) _
    (instFactSystem (BranchState := BranchState)
      (Presentation := Presentation) (presentation := presentation)
      (data := data))
    `Hypostructure.Graph.Strategy.Spine.typeBOverlapObstructionMass
    { Requires := [K .typeBOverlapObstruction]
      Produces := [K .typeBOverlapObstructionMass]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let residual := inputs.get (K .typeBOverlapObstruction)
      .cons (key := K .typeBOverlapObstructionMass) (by
        refine ⟨?_⟩
        obtain ⟨packing, valid, maximal, canonicalPiece, negative, positive,
          obstruction⟩ := residual.down
        exact ⟨packing, valid, maximal, canonicalPiece, negative, positive,
          obstruction, fun centre _member high envelope =>
            Graph.TypeBEnvelopeCharge.envelopeNegativePart_le envelope high
              data.bridgeMassSlack⟩)
      .nil)
    0 0

omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def typeBExclusionResidualMassRow :
    @AtomicStrategy (Input BranchState Presentation presentation data) _
      (instFactSystem (BranchState := BranchState)
        (Presentation := Presentation) (presentation := presentation)
        (data := data)) :=
  letI : FactSystem (Input BranchState Presentation presentation data) :=
    instFactSystem (BranchState := BranchState) (Presentation := Presentation)
      (presentation := presentation) (data := data)
  @factOnly (Input BranchState Presentation presentation data) _
    (instFactSystem (BranchState := BranchState)
      (Presentation := Presentation) (presentation := presentation)
      (data := data))
    `Hypostructure.Graph.Strategy.Spine.typeBExclusionResidualMass
    { Requires := [K .typeBExclusionResidual]
      Produces := [K .typeBExclusionResidualMass]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let residual := inputs.get (K .typeBExclusionResidual)
      .cons (key := K .typeBExclusionResidualMass) (by
        classical
        refine ⟨?_⟩
        have residualFact := residual.down
        obtain ⟨packing, _packingValid, _packingMaximal, canonicalPiece,
          _negative, _surplus, ledger, exact, _postLedger, negative⟩ :=
          residualFact
        exact ⟨packing, canonicalPiece, ledger, exact, negative,
          fun centre _member high envelope =>
            Graph.TypeBEnvelopeCharge.envelopeNegativePart_le envelope high
              data.bridgeMassSlack⟩)
      .nil)
    0 0

/-! ## Node `[76]`/`[85]`: Type B local selected-entry charge -/
@[reducible] noncomputable def typeBSelectedFanChargeRow
    (fanCertificateMarked typeBHybridEntry typeBDisjointLedger
      typeBSelectedFanCharge :
      FactKey (Input BranchState Presentation presentation data))
    (requiredUnique :
      [fanCertificateMarked, typeBHybridEntry, typeBDisjointLedger].Nodup)
    (encode : (input : Input BranchState Presentation presentation data) →
      (∀ packing : Finset (Finset input.object.Vertex),
        ∀ canonicalPiece :
            Graph.TypeBRefinedSupport.CanonicalPiece input.object packing,
          ∀ ledger : Graph.TypeBRefinedSupport.DisjointLedger input.object
              data.threshold data.dischargeScale canonicalPiece,
            ledger.ExactAugmentedLedgerRefinement →
              (∀ centre
                  (member : centre ∈ Graph.TypeBRefinedSupport.centres
                    input.object data.threshold canonicalPiece.vertices),
                (ledger.choice.entry centre member).IsCandidate data.threshold
                  data.dischargeScale canonicalPiece centre) ∧
                (0 : Int) ≤ ledger.selectedEntryPayment₂) →
      typeBSelectedFanCharge.At input) :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.typeBSelectedFanCharge
    { Requires := [fanCertificateMarked, typeBHybridEntry, typeBDisjointLedger]
      Produces := [typeBSelectedFanCharge]
      requiresUnique := requiredUnique
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let _markedFact := inputs.get fanCertificateMarked
      let _hybridFact := inputs.get typeBHybridEntry
      let _ledgerFact := inputs.get typeBDisjointLedger
      .cons (key := typeBSelectedFanCharge)
        (encode inputs.current (by
          intro packing canonicalPiece ledger _exact
          have hLocalEntry :
              ∀ centre
                  (member : centre ∈ Graph.TypeBRefinedSupport.centres
                    inputs.current.object data.threshold
                    canonicalPiece.vertices),
                (ledger.choice.entry centre member).IsCandidate data.threshold
                  data.dischargeScale canonicalPiece centre := by
            intro centre member
            exact ledger.entry_isCandidate centre member
          have selected :
              (0 : Int) ≤ ledger.selectedEntryPayment₂ := by
            classical
            rw [Graph.TypeBRefinedSupport.DisjointLedger.selectedEntryPayment₂]
            refine Finset.sum_nonneg ?_
            intro hub _member
            exact (hLocalEntry hub.1 hub.2).entryRefines
          exact ⟨hLocalEntry, selected⟩))
        .nil)

/-! ## Node `[76]`/`[85]`: Type B exclusion charge

The charge row runs only after the exact B2 ledger and the selected local-entry
charge facts are present.  It reads both through `FactInputs.get` and appends
the B-ledger implication used by the exclusion dichotomy.
-/
@[reducible] noncomputable def typeBExclusionChargeRow
    (typeBDisjointLedger typeBSelectedFanCharge typeBExclusionCharge :
      FactKey (Input BranchState Presentation presentation data))
    (requiredUnique :
      [typeBDisjointLedger, typeBSelectedFanCharge].Nodup)
    (localChargeOf :
      (input : Input BranchState Presentation presentation data) →
        typeBSelectedFanCharge.At input →
        ∀ packing : Finset (Finset input.object.Vertex),
          ∀ canonicalPiece :
              Graph.TypeBRefinedSupport.CanonicalPiece input.object packing,
            ∀ ledger : Graph.TypeBRefinedSupport.DisjointLedger input.object
                data.threshold data.dischargeScale canonicalPiece,
              ledger.ExactAugmentedLedgerRefinement →
                (∀ centre
                    (member : centre ∈ Graph.TypeBRefinedSupport.centres
                      input.object data.threshold canonicalPiece.vertices),
                  (ledger.choice.entry centre member).IsCandidate data.threshold
                    data.dischargeScale canonicalPiece centre) ∧
                  (0 : Int) ≤ ledger.selectedEntryPayment₂)
    (encode : (input : Input BranchState Presentation presentation data) →
      (∀ packing : Finset (Finset input.object.Vertex),
        ∀ canonicalPiece :
            Graph.TypeBRefinedSupport.CanonicalPiece input.object packing,
          ∀ ledger : Graph.TypeBRefinedSupport.DisjointLedger input.object
              data.threshold data.dischargeScale canonicalPiece,
            ledger.ExactAugmentedLedgerRefinement →
              (0 : Int) ≤ ∑ vertex ∈ ledger.remainingCore,
                Graph.TypeBRefinedSupport.scaledCoreCharge input.object
                  data.threshold data.dischargeScale canonicalPiece.vertices
                  vertex →
              input.object.NonNegativeNetCharge canonicalPiece.vertices
                data.threshold data.dischargeScale) →
      typeBExclusionCharge.At input) :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.typeBExclusionCharge
    { Requires := [typeBDisjointLedger, typeBSelectedFanCharge]
      Produces := [typeBExclusionCharge]
      requiresUnique := requiredUnique
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let _ledgerFact := inputs.get typeBDisjointLedger
      let localCharge := localChargeOf inputs.current
        (inputs.get typeBSelectedFanCharge)
      .cons (key := typeBExclusionCharge)
        (encode inputs.current (by
          intro packing canonicalPiece ledger exact remainingNonnegative
          have selectedNonnegative :
              (0 : Int) ≤ ledger.selectedEntryPayment₂ :=
            (localCharge packing canonicalPiece ledger exact).2
          exact
            Graph.TypeBEnvelopeCharge.nonNegativeNetCharge_of_disjointLedger_remainingCore_nonneg_of_selectedEntryPayment₂_nonnegative
              (object := inputs.current.object) ledger exact
              selectedNonnegative remainingNonnegative))
        .nil)

/-! ## Node `[76]`/`[85]`: Type B exclusion split -/
noncomputable def typeBExclusionDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous :
      ExactLedger (Input BranchState Presentation presentation data)
        current known)
    (typeBDisjointLedger typeBExclusionCharge typeBExcluded
      typeBExclusionResidual :
      FactKey (Input BranchState Presentation presentation data))
    [Core.Residual.FactKeys.Has typeBDisjointLedger known]
    [Core.Residual.FactKeys.Has typeBExclusionCharge known]
    (chargeOf : typeBExclusionCharge.At current →
      ∀ packing : Finset (Finset current.object.Vertex),
        ∀ canonicalPiece :
            Graph.TypeBRefinedSupport.CanonicalPiece current.object packing,
          ∀ ledger : Graph.TypeBRefinedSupport.DisjointLedger current.object
              data.threshold data.dischargeScale canonicalPiece,
            ledger.ExactAugmentedLedgerRefinement →
              (0 : Int) ≤ ∑ vertex ∈ ledger.remainingCore,
                Graph.TypeBRefinedSupport.scaledCoreCharge current.object
                  data.threshold data.dischargeScale canonicalPiece.vertices
                  vertex →
              current.object.NonNegativeNetCharge canonicalPiece.vertices
                data.threshold data.dischargeScale)
    (encodeClosed : False → typeBExcluded.At current)
    (encodeResidual :
      (∃ packing : Finset (Finset current.object.Vertex),
        current.object.IsWindowPacking data.windowOrder packing ∧
          (∀ window : Finset current.object.Vertex,
            current.object.InducesWindow data.windowOrder window →
            ∃ member ∈ packing, ¬ Disjoint window member) ∧
          ∃ canonicalPiece :
              Graph.TypeBRefinedSupport.CanonicalPiece current.object packing,
            current.object.NegativeNetCharge canonicalPiece.vertices
                data.threshold data.dischargeScale ∧
              0 < current.object.ambientSurplus canonicalPiece.vertices
                data.threshold ∧
              ∃ ledger : Graph.TypeBRefinedSupport.DisjointLedger current.object
                  data.threshold data.dischargeScale canonicalPiece,
                ledger.ExactAugmentedLedgerRefinement ∧
                  (∀ component : Graph.SupportComponents.Connected.Component
                        current.object ledger.remainingCore,
                      component ∈ Graph.SupportComponents.Connected.order
                          current.object ledger.remainingCore →
                        Graph.TypeBPostLedgerCore.PostLedgerComponent
                          data.typeABPresentation ledger component) ∧
                  ¬ (0 : Int) ≤ ∑ vertex ∈ ledger.remainingCore,
                    Graph.TypeBRefinedSupport.scaledCoreCharge current.object
                      data.threshold data.dischargeScale canonicalPiece.vertices
                      vertex) →
      typeBExclusionResidual.At current)
    (ledgerOf : typeBDisjointLedger.At current →
      ∃ packing : Finset (Finset current.object.Vertex),
        current.object.IsWindowPacking data.windowOrder packing ∧
          (∀ window : Finset current.object.Vertex,
            current.object.InducesWindow data.windowOrder window →
            ∃ member ∈ packing, ¬ Disjoint window member) ∧
          ∃ canonicalPiece :
              Graph.TypeBRefinedSupport.CanonicalPiece current.object packing,
            current.object.NegativeNetCharge canonicalPiece.vertices
                data.threshold data.dischargeScale ∧
              0 < current.object.ambientSurplus canonicalPiece.vertices
                data.threshold ∧
              ∃ ledger : Graph.TypeBRefinedSupport.DisjointLedger current.object
                  data.threshold data.dischargeScale canonicalPiece,
                ledger.ExactAugmentedLedgerRefinement ∧
                  (∀ component : Graph.SupportComponents.Connected.Component
                        current.object ledger.remainingCore,
                      component ∈ Graph.SupportComponents.Connected.order
                          current.object ledger.remainingCore →
                        Graph.TypeBPostLedgerCore.PostLedgerComponent
                          data.typeABPresentation ledger component))
    (closedFresh : typeBExcluded ∉ known)
    (residualFresh : typeBExclusionResidual ∉ known) :
    Decision typeBExcluded typeBExclusionResidual previous :=
  Decision.run previous
    typeBExcluded typeBExclusionResidual
    `Hypostructure.Graph.Strategy.Spine.typeBExclusionDichotomy
    (by
      classical
      apply Classical.choice
      obtain ⟨packing, valid, maximal, canonicalPiece, negative, surplus,
        ledger, exact, postLedger⟩ :=
        ledgerOf (ExactLedger.get previous typeBDisjointLedger)
      let charge := ∑ vertex ∈ ledger.remainingCore,
        Graph.TypeBRefinedSupport.scaledCoreCharge current.object
          data.threshold data.dischargeScale canonicalPiece.vertices vertex
      by_cases clean : (0 : Int) ≤ charge
      · have nonnegative :=
          chargeOf (ExactLedger.get previous typeBExclusionCharge)
            packing canonicalPiece ledger exact clean
        have contradiction :=
          (current.object.not_negativeNetCharge_iff canonicalPiece.vertices
            data.threshold data.dischargeScale).mpr nonnegative negative
        exact ⟨.inl (encodeClosed contradiction)⟩
      · exact ⟨.inr (encodeResidual ⟨packing, valid, maximal, canonicalPiece,
          negative, surplus, ledger, exact, postLedger, by simpa [charge] using clean⟩)⟩)
    closedFresh residualFresh

/-! ## Node `[88]`: the routing and threshold algebra of a Type A support

`def:typeA-support` is `def:admissible` with `σ(X) = 0`.  Since the object meets
the baseline everywhere, a support of zero assigned surplus has every vertex at
degree exactly `δ`, so its internal degrees never exceed `δ`: the vertices split
into *receivers* of internal degree below `δ` and *full* vertices at `δ`, and
`q(w) = δ − d_X(w)` is also the number of ambient edges leaving `w`.

Two manuscript statements live here.

`lem:typeA-receiver-loads` says the canonical trace `r(u)` is defined for every
full `u` and lands on a receiver.  Its hypothesis is the empty internal
`δ`-core, and that is *inherited*, not assumed: node `[27]` proves that no
subregion of the remainder of a maximal packing meets the baseline, and the
support is such a subregion.  `exists_traceTo_of_no_baseline_subsupport` is the
argument the manuscript gives — the region a full vertex reaches through full
vertices would otherwise keep the whole baseline inside itself.

`lem:typeA-threshold-algebra` says a receiver of internal degree `δ − 1 − j`
has `q(w) = j + 1`, hence saturation threshold `H_j = s·(j+1)`, never above
`s·δ`.  At the manuscript's `δ = 3`, `s = 4` that is `H₀ ≤ 4`, `H₁ ≤ 8`,
`H₂ ≤ 12`.

The support is data and cannot travel, so the fact is stated at every Type A
support of the object at once, exactly as node `[27]` is stated at every
subregion. -/
@[reducible] noncomputable def typeAReceiverRoutingRow
    (remainderNormalized typeAReceiverRouting :
      FactKey (Input BranchState Presentation presentation data))
    (normalizedOf : (input : Input BranchState Presentation presentation data) →
      remainderNormalized.At input →
      ∀ packing : Finset (Finset input.object.Vertex),
        input.object.IsWindowPacking data.windowOrder packing →
        (∀ window : Finset input.object.Vertex,
          input.object.InducesWindow data.windowOrder window →
          ∃ member ∈ packing, ¬ Disjoint window member) →
        ∀ support : Finset input.object.Vertex,
          support ⊆ input.object.remainderSupport packing →
          ¬ input.object.InducesWindow data.windowOrder support ∧
            ¬ Graph.MinimumDegreeAtLeast data.threshold
              (input.object.induce support))
    (encode : (input : Input BranchState Presentation presentation data) →
      (∀ packing : Finset (Finset input.object.Vertex),
        input.object.IsWindowPacking data.windowOrder packing →
        (∀ window : Finset input.object.Vertex,
          input.object.InducesWindow data.windowOrder window →
          ∃ member ∈ packing, ¬ Disjoint window member) →
        ∀ piece : Finset input.object.Vertex,
          piece ⊆ input.object.remainderSupport packing →
          input.object.ambientSurplus piece data.threshold = 0 →
          (∀ vertex ∈ piece,
            input.object.internalDegree piece vertex = data.threshold →
            ∃ receiver : input.object.Vertex,
              input.object.traceReceiver? piece data.threshold vertex =
                  some receiver ∧
                input.object.IsReceiver piece data.threshold receiver) ∧
            (∀ receiver : input.object.Vertex,
              input.object.IsReceiver piece data.threshold receiver →
              data.dischargeScale *
                    input.object.missingPorts piece data.threshold receiver =
                  data.dischargeScale *
                    (data.threshold - 1 -
                      input.object.internalDegree piece receiver + 1) ∧
                data.dischargeScale *
                    input.object.missingPorts piece data.threshold receiver ≤
                  data.dischargeScale * data.threshold)) →
      typeAReceiverRouting.At input) :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.typeAReceiverRouting
    { Requires := [remainderNormalized]
      Produces := [typeAReceiverRouting]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := typeAReceiverRouting)
        (encode inputs.current (by
          classical
          intro packing valid maximal piece inside surplus
          -- `σ(X) = 0` against the standing baseline: every vertex of the
          -- support sits exactly at `δ`, so no internal degree exceeds it.
          have capped : ∀ vertex ∈ piece,
              inputs.current.object.internalDegree piece vertex ≤
                data.threshold := by
            intro vertex member
            have exact : inputs.current.object.degree vertex = data.threshold := by
              -- The standing baseline, read off the residual rather than from
              -- a fact.
              have nonneg : data.threshold ≤ inputs.current.object.degree vertex :=
                le_trans inputs.current.baseline
                  (inputs.current.object.minDegree_le_degree vertex)
              have summand :
                  inputs.current.object.degree vertex - data.threshold = 0 :=
                Nat.eq_zero_of_le_zero
                  (surplus ▸ Finset.single_le_sum
                    (f := fun other =>
                      inputs.current.object.degree other - data.threshold)
                    (fun _ _ => Nat.zero_le _) member)
              omega
            exact exact ▸
              inputs.current.object.internalDegree_le_degree piece vertex
          -- Node `[27]` on the support: no subregion of it meets the baseline.
          have noCore : ∀ inner : Finset inputs.current.object.Vertex,
              inner ⊆ piece →
              ¬ Graph.MinimumDegreeAtLeast data.threshold
                (inputs.current.object.induce inner) := fun inner contained =>
            (normalizedOf inputs.current (inputs.get remainderNormalized) packing
              valid maximal inner (contained.trans inside)).2
          refine ⟨fun vertex member full => ?_, fun receiver isReceiver => ?_⟩
          · obtain ⟨target, trace⟩ :=
              inputs.current.object.exists_traceTo_of_no_baseline_subsupport
                piece data.threshold noCore member (le_of_eq full.symm)
            obtain ⟨found, routed⟩ :=
              Option.isSome_iff_exists.mp
                (inputs.current.object.isSome_traceReceiver?_of_traceTo trace)
            exact ⟨found, routed,
              inputs.current.object.isReceiver_of_traceTo
                (inputs.current.object.traceTo_of_traceReceiver?_eq_some routed)⟩
          · exact ⟨inputs.current.object.saturationThreshold_eq piece
              data.threshold data.dischargeScale isReceiver.2,
              inputs.current.object.saturationThreshold_le piece data.threshold
                data.dischargeScale receiver⟩))
        .nil)

/-! ## Node `[89]`: is some receiver of the Type A support saturated?

`L(w) ≥ s·q(w)?`  The yes arm is node `[93]`, where the saturated receiver's
completion ports are examined; the no arm is node `[90]`, the unsaturated
capacity `L(w) ≤ s·q(w) − 1` that node `[91]`'s discharging spends.

The split is taken on a `Prop`, so no receiver is extracted to build the
branch: the arm not taken supplies the other arm's clause.  The no arm is
committed in the positive, subtraction-free form node `[90]` states —
`1 + L(w) ≤ s·q(w)` — which is `lem:typeA-threshold-algebra`'s "if the
saturated branch has been eliminated" clause and, at the manuscript's own
values, the surviving capacities `3`, `7`, `11`.

This is a `Decision`: the arm not taken is absent from the taken branch's key
index, so no Type A row downstream can read the other alternative. -/
noncomputable def typeASaturationDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous :
      ExactLedger (Input BranchState Presentation presentation data)
        current known)
    (typeALowSurplus typeASaturatedReceiver typeAUnsaturatedReceivers :
      FactKey (Input BranchState Presentation presentation data))
    [Core.Residual.FactKeys.Has typeALowSurplus known]
    (supportOf : typeALowSurplus.At current →
      ∃ packing : Finset (Finset current.object.Vertex),
        current.object.IsWindowPacking data.windowOrder packing ∧
          (∀ window : Finset current.object.Vertex,
            current.object.InducesWindow data.windowOrder window →
            ∃ member ∈ packing, ¬ Disjoint window member) ∧
          ∃ component ∈ current.object.canonicalPieces
              (current.object.remainderSupport packing),
            let piece := current.object.pieceSupport
              (current.object.remainderSupport packing) component
            current.object.NegativeNetCharge piece data.threshold
                data.dischargeScale ∧
              current.object.ambientSurplus piece data.threshold = 0)
    (encodeSaturated :
      (∃ packing : Finset (Finset current.object.Vertex),
        current.object.IsWindowPacking data.windowOrder packing ∧
          (∀ window : Finset current.object.Vertex,
            current.object.InducesWindow data.windowOrder window →
            ∃ member ∈ packing, ¬ Disjoint window member) ∧
          ∃ component ∈ current.object.canonicalPieces
              (current.object.remainderSupport packing),
            let piece := current.object.pieceSupport
              (current.object.remainderSupport packing) component
            current.object.NegativeNetCharge piece data.threshold
                data.dischargeScale ∧
              current.object.ambientSurplus piece data.threshold = 0 ∧
              ∃ receiver : current.object.Vertex,
                current.object.IsReceiver piece data.threshold receiver ∧
                  current.object.Saturated piece data.threshold
                    data.dischargeScale receiver) →
      typeASaturatedReceiver.At current)
    (encodeUnsaturated :
      (∃ packing : Finset (Finset current.object.Vertex),
        current.object.IsWindowPacking data.windowOrder packing ∧
          (∀ window : Finset current.object.Vertex,
            current.object.InducesWindow data.windowOrder window →
            ∃ member ∈ packing, ¬ Disjoint window member) ∧
          ∃ component ∈ current.object.canonicalPieces
              (current.object.remainderSupport packing),
            let piece := current.object.pieceSupport
              (current.object.remainderSupport packing) component
            current.object.NegativeNetCharge piece data.threshold
                data.dischargeScale ∧
              current.object.ambientSurplus piece data.threshold = 0 ∧
          ∀ receiver : current.object.Vertex,
            current.object.IsReceiver piece data.threshold receiver →
            1 + current.object.routedLoad piece data.threshold receiver ≤
              data.dischargeScale *
                current.object.missingPorts piece data.threshold receiver) →
      typeAUnsaturatedReceivers.At current)
    (saturatedFresh : typeASaturatedReceiver ∉ known)
    (unsaturatedFresh : typeAUnsaturatedReceivers ∉ known) :
    Decision typeASaturatedReceiver typeAUnsaturatedReceivers previous :=
  Decision.run previous typeASaturatedReceiver typeAUnsaturatedReceivers
    `Hypostructure.Graph.Strategy.Spine.typeASaturationDichotomy
    (by
      classical
      apply Classical.choice
      obtain ⟨packing, valid, maximal, component, present, negative, zero⟩ :=
        supportOf (ExactLedger.get previous typeALowSurplus)
      let piece := current.object.pieceSupport
        (current.object.remainderSupport packing) component
      by_cases saturated :
          ∃ receiver : current.object.Vertex,
            current.object.IsReceiver piece data.threshold receiver ∧
              current.object.Saturated piece data.threshold
                data.dischargeScale receiver
      · exact ⟨.inl (encodeSaturated
          ⟨packing, valid, maximal, component, present, negative, zero,
            saturated⟩)⟩
      · refine ⟨.inr (encodeUnsaturated ?_)⟩
        refine ⟨packing, valid, maximal, component, present, negative, zero, ?_⟩
        intro receiver isReceiver
        refine (current.object.not_saturated_iff piece data.threshold
          data.dischargeScale receiver).mp ?_
        exact fun full => saturated ⟨receiver, isReceiver, full⟩)
    saturatedFresh unsaturatedFresh

/-! ## Nodes `[90]`--`[91]`: unsaturated Type A discharging -/

/-- **`lem:typeA-unsaturated-discharge`, read from nodes `[88]` and `[90]`.**

The row publishes the exact integral conclusion `|V(X)| ≤ s * def⁺(X)` for
the same negative Type A support quantified by the incoming facts.  The
canonical routing and the unsaturated receiver inequalities are both read by
semantic key. -/
@[reducible] noncomputable def typeAUnsaturatedDischargeRow
    (typeAReceiverRouting typeAUnsaturatedReceivers
      typeAUnsaturatedDischarge :
      FactKey (Input BranchState Presentation presentation data))
    (distinctRequired : typeAReceiverRouting ≠ typeAUnsaturatedReceivers)
    (routingOf : (input : Input BranchState Presentation presentation data) →
      typeAReceiverRouting.At input →
      ∀ packing : Finset (Finset input.object.Vertex),
        input.object.IsWindowPacking data.windowOrder packing →
        (∀ window : Finset input.object.Vertex,
          input.object.InducesWindow data.windowOrder window →
          ∃ member ∈ packing, ¬ Disjoint window member) →
        ∀ piece : Finset input.object.Vertex,
          piece ⊆ input.object.remainderSupport packing →
          input.object.ambientSurplus piece data.threshold = 0 →
          (∀ vertex ∈ piece,
            input.object.internalDegree piece vertex = data.threshold →
            ∃ receiver : input.object.Vertex,
              input.object.traceReceiver? piece data.threshold vertex =
                  some receiver ∧
                input.object.IsReceiver piece data.threshold receiver) ∧
            (∀ receiver : input.object.Vertex,
              input.object.IsReceiver piece data.threshold receiver →
              data.dischargeScale *
                    input.object.missingPorts piece data.threshold receiver =
                  data.dischargeScale *
                    (data.threshold - 1 -
                      input.object.internalDegree piece receiver + 1) ∧
                data.dischargeScale *
                    input.object.missingPorts piece data.threshold receiver ≤
                  data.dischargeScale * data.threshold))
    (unsaturatedOf :
      (input : Input BranchState Presentation presentation data) →
      typeAUnsaturatedReceivers.At input →
      ∃ packing : Finset (Finset input.object.Vertex),
        input.object.IsWindowPacking data.windowOrder packing ∧
        (∀ window : Finset input.object.Vertex,
          input.object.InducesWindow data.windowOrder window →
          ∃ member ∈ packing, ¬ Disjoint window member) ∧
        ∃ component ∈ input.object.canonicalPieces
            (input.object.remainderSupport packing),
          let piece := input.object.pieceSupport
            (input.object.remainderSupport packing) component
          input.object.NegativeNetCharge piece data.threshold
              data.dischargeScale ∧
            input.object.ambientSurplus piece data.threshold = 0 ∧
          ∀ receiver : input.object.Vertex,
            input.object.IsReceiver piece data.threshold receiver →
            1 + input.object.routedLoad piece data.threshold receiver ≤
              data.dischargeScale *
                input.object.missingPorts piece data.threshold receiver)
    (encode : (input : Input BranchState Presentation presentation data) →
      (∃ packing : Finset (Finset input.object.Vertex),
        input.object.IsWindowPacking data.windowOrder packing ∧
        (∀ window : Finset input.object.Vertex,
          input.object.InducesWindow data.windowOrder window →
          ∃ member ∈ packing, ¬ Disjoint window member) ∧
        ∃ component ∈ input.object.canonicalPieces
            (input.object.remainderSupport packing),
          let piece := input.object.pieceSupport
            (input.object.remainderSupport packing) component
          input.object.NegativeNetCharge piece data.threshold
              data.dischargeScale ∧
            input.object.ambientSurplus piece data.threshold = 0 ∧
          piece.card ≤ data.dischargeScale *
            input.object.positiveDeficiency piece data.threshold) →
      typeAUnsaturatedDischarge.At input) :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.typeAUnsaturatedDischarge
    { Requires := [typeAReceiverRouting, typeAUnsaturatedReceivers]
      Produces := [typeAUnsaturatedDischarge]
      requiresUnique := by simp [distinctRequired]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let routing :=
        routingOf inputs.current (inputs.get typeAReceiverRouting)
      let unsaturated :=
        unsaturatedOf inputs.current (inputs.get typeAUnsaturatedReceivers)
      .cons (key := typeAUnsaturatedDischarge)
        (encode inputs.current (by
          obtain ⟨packing, valid, maximal, component, present, negative,
            surplus, receiverBound⟩ := unsaturated
          let piece := inputs.current.object.pieceSupport
            (inputs.current.object.remainderSupport packing) component
          have inside : piece ⊆ inputs.current.object.remainderSupport packing :=
            inputs.current.object.pieceSupport_subset
              (inputs.current.object.remainderSupport packing) component
          have exactDegree : ∀ vertex ∈ piece,
              inputs.current.object.degree vertex = data.threshold := by
            intro vertex member
            have lower : data.threshold ≤ inputs.current.object.degree vertex :=
              le_trans inputs.current.baseline
                (inputs.current.object.minDegree_le_degree vertex)
            have summand :
                inputs.current.object.degree vertex - data.threshold = 0 :=
              Nat.eq_zero_of_le_zero
                (surplus ▸ Finset.single_le_sum
                  (f := fun other =>
                    inputs.current.object.degree other - data.threshold)
                  (fun _ _ => Nat.zero_le _) member)
            omega
          have capped : ∀ vertex ∈ piece,
              inputs.current.object.internalDegree piece vertex ≤
                data.threshold :=
            fun vertex member => (exactDegree vertex member) ▸
              inputs.current.object.internalDegree_le_degree piece vertex
          have discharged :=
            Graph.FiniteObject.unsaturatedDischarge inputs.current.object
              piece data.threshold data.dischargeScale capped
              (routing packing valid maximal piece inside surplus).1
              receiverBound
          exact ⟨packing, valid, maximal, component, present, negative,
            surplus, discharged⟩))
        .nil)

/-! ## Node `[93]`: does a port of the saturated receiver see `s` visible
receiver-entry returns?

`def:typeA-visible-load` counts, at each completion port of the saturated
receiver, the distinct routed loads for which some receiver-entry return through
that port is visible.  The yes arm is `lem:typeA-visible-entry`'s hypothesis and
enters the exit chain `def:typeA-saturated-exits` (1)--(7) at node `[95]`; the
no arm is node `[94]`, where `lem:typeA-silent-excess-count` turns the absence of
a visible-saturated port into the quantitative excess
`S_sil^exc(X) ≥ s·D_A(X)`.

The no arm is *proved*, not assumed: `card_le_sum_silentExcess_add_positive`
`Deficiency` is the manuscript's own count, and its three hypotheses are read
off this branch -- the support sits exactly at the baseline because it carries no
ambient surplus, the routing is total by node `[88]`'s committed fact, and no
saturated receiver has a visible-saturated port because that is the alternative
not taken.

This is a `Decision`: the arm not taken is absent from the taken branch's key
index, so the exit chain cannot read the excess bound and node `[109]` cannot
read the visible-entry hypothesis. -/
noncomputable def typeAVisibleEntryDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous :
      ExactLedger (Input BranchState Presentation presentation data)
        current known)
    (typeAReceiverRouting typeASaturatedReceiver typeAVisibleEntry
      typeAVisibleFirstExcess :
      FactKey (Input BranchState Presentation presentation data))
    [Core.Residual.FactKeys.Has typeAReceiverRouting known]
    [Core.Residual.FactKeys.Has typeASaturatedReceiver known]
    (routingOf : typeAReceiverRouting.At current →
      ∀ packing : Finset (Finset current.object.Vertex),
        current.object.IsWindowPacking data.windowOrder packing →
        (∀ window : Finset current.object.Vertex,
          current.object.InducesWindow data.windowOrder window →
          ∃ member ∈ packing, ¬ Disjoint window member) →
        ∀ piece : Finset current.object.Vertex,
          piece ⊆ current.object.remainderSupport packing →
          current.object.ambientSurplus piece data.threshold = 0 →
          (∀ vertex ∈ piece,
            current.object.internalDegree piece vertex = data.threshold →
            ∃ receiver : current.object.Vertex,
              current.object.traceReceiver? piece data.threshold vertex =
                  some receiver ∧
                current.object.IsReceiver piece data.threshold receiver) ∧
            (∀ receiver : current.object.Vertex,
              current.object.IsReceiver piece data.threshold receiver →
              data.dischargeScale *
                    current.object.missingPorts piece data.threshold receiver =
                  data.dischargeScale *
                    (data.threshold - 1 -
                      current.object.internalDegree piece receiver + 1) ∧
                data.dischargeScale *
                    current.object.missingPorts piece data.threshold receiver ≤
                  data.dischargeScale * data.threshold))
    (saturatedOf : typeASaturatedReceiver.At current →
      ∃ packing : Finset (Finset current.object.Vertex),
        current.object.IsWindowPacking data.windowOrder packing ∧
          (∀ window : Finset current.object.Vertex,
            current.object.InducesWindow data.windowOrder window →
            ∃ member ∈ packing, ¬ Disjoint window member) ∧
          ∃ component ∈ current.object.canonicalPieces
              (current.object.remainderSupport packing),
            let piece := current.object.pieceSupport
              (current.object.remainderSupport packing) component
            current.object.NegativeNetCharge piece data.threshold
                data.dischargeScale ∧
              current.object.ambientSurplus piece data.threshold = 0 ∧
              ∃ receiver : current.object.Vertex,
                current.object.IsReceiver piece data.threshold receiver ∧
                  current.object.Saturated piece data.threshold
                    data.dischargeScale receiver)
    (encodeVisible :
      (∃ packing : Finset (Finset current.object.Vertex),
        current.object.IsWindowPacking data.windowOrder packing ∧
          (∀ window : Finset current.object.Vertex,
            current.object.InducesWindow data.windowOrder window →
            ∃ member ∈ packing, ¬ Disjoint window member) ∧
          ∃ component ∈ current.object.canonicalPieces
              (current.object.remainderSupport packing),
            let piece := current.object.pieceSupport
              (current.object.remainderSupport packing) component
            current.object.NegativeNetCharge piece data.threshold
                data.dischargeScale ∧
              current.object.ambientSurplus piece data.threshold = 0 ∧
              ∃ receiver : current.object.Vertex,
                current.object.IsReceiver piece data.threshold receiver ∧
                  current.object.Saturated piece data.threshold
                    data.dischargeScale receiver ∧
                  Nonempty
                    (Graph.ExitFour.VisibleFourUnpeeledPackage piece
                      data.threshold data.dischargeScale receiver ∅)) →
      typeAVisibleEntry.At current)
    (encodeExcess :
      (∃ packing : Finset (Finset current.object.Vertex),
        current.object.IsWindowPacking data.windowOrder packing ∧
          (∀ window : Finset current.object.Vertex,
            current.object.InducesWindow data.windowOrder window →
            ∃ member ∈ packing, ¬ Disjoint window member) ∧
          ∃ component ∈ current.object.canonicalPieces
              (current.object.remainderSupport packing),
            let piece := current.object.pieceSupport
              (current.object.remainderSupport packing) component
            current.object.NegativeNetCharge piece data.threshold
                data.dischargeScale ∧
              current.object.ambientSurplus piece data.threshold = 0 ∧
              ∃ receiver : current.object.Vertex,
                current.object.IsReceiver piece data.threshold receiver ∧
                  current.object.Saturated piece data.threshold
                      data.dischargeScale receiver ∧
                  Graph.ExitFour.SilentUnpeeledExcessAt piece data.threshold
                      data.dischargeScale receiver ∅ ∧
                  piece.card ≤
                    (∑ other ∈ current.object.receivers piece data.threshold,
                      (Graph.VisibleEntry.silentExcess current.object piece
                        data.threshold data.dischargeScale other).card) +
                      data.dischargeScale *
                        current.object.positiveDeficiency piece data.threshold) →
      typeAVisibleFirstExcess.At current)
    (visibleFresh : typeAVisibleEntry ∉ known)
    (excessFresh : typeAVisibleFirstExcess ∉ known) :
    Decision typeAVisibleEntry typeAVisibleFirstExcess previous :=
  Decision.run previous typeAVisibleEntry typeAVisibleFirstExcess
    `Hypostructure.Graph.Strategy.Spine.typeAVisibleEntryDichotomy
    (by
      classical
      letI : DecidableEq current.object.Vertex := current.object.vertices.decEq
      apply Classical.choice
      obtain ⟨packing, valid, maximal, component, present, negative, zero,
        selectedReceiver, selectedIsReceiver, selectedSaturated⟩ :=
        saturatedOf (ExactLedger.get previous typeASaturatedReceiver)
      let piece := current.object.pieceSupport
        (current.object.remainderSupport packing) component
      have inside : piece ⊆ current.object.remainderSupport packing :=
        current.object.pieceSupport_subset
          (current.object.remainderSupport packing) component
      have routing := routingOf
        (ExactLedger.get previous typeAReceiverRouting)
      have routed := routing packing valid maximal piece inside zero
      have exactDegree : ∀ vertex ∈ piece,
          current.object.degree vertex = data.threshold := by
        intro vertex member
        have lower : data.threshold ≤ current.object.degree vertex :=
          le_trans current.baseline
            (current.object.minDegree_le_degree vertex)
        have summand : current.object.degree vertex - data.threshold = 0 :=
          Nat.eq_zero_of_le_zero
            (zero ▸ Finset.single_le_sum
              (f := fun other =>
                current.object.degree other - data.threshold)
              (fun _ _ => Nat.zero_le _) member)
        omega
      have capped : ∀ vertex ∈ piece,
          current.object.internalDegree piece vertex ≤ data.threshold :=
        fun vertex member => (exactDegree vertex member) ▸
          current.object.internalDegree_le_degree piece vertex
      by_cases visible :
          ∃ receiver : current.object.Vertex,
            current.object.IsReceiver piece data.threshold receiver ∧
              current.object.Saturated piece data.threshold
                  data.dischargeScale receiver ∧
              Graph.ExitFour.VisibleFourUnpeeledAt piece data.threshold
                data.dischargeScale receiver ∅
      · obtain ⟨receiver, isReceiver, saturated, overloaded⟩ := visible
        exact ⟨.inl (encodeVisible
          ⟨packing, valid, maximal, component, present, negative, zero,
            receiver, isReceiver, saturated,
            Graph.ExitFour.visibleFourUnpeeledPackage piece data.threshold
              data.dischargeScale receiver ∅ overloaded⟩)⟩
      · have noVisiblePorts : ∀ receiver : current.object.Vertex,
            current.object.IsReceiver piece data.threshold receiver →
            current.object.Saturated piece data.threshold data.dischargeScale
              receiver →
            ∀ outside ∈ Graph.VisibleEntry.completionPorts current.object piece
              receiver,
              (Graph.VisibleEntry.visibleLoadsAt current.object piece
                data.threshold receiver outside).card + 1 ≤
                  data.dischargeScale := by
          intro receiver isReceiver saturated outside port
          have notOverloaded : ¬ data.dischargeScale ≤
              (Graph.VisibleEntry.visibleLoadsAt current.object piece
                data.threshold receiver outside).card := by
            intro overloaded
            apply visible
            refine ⟨receiver, isReceiver, saturated, outside, port, ?_⟩
            have atEmpty :
                Graph.ExitFour.unpeeledVisibleLoadsAt piece data.threshold
                    receiver outside ∅ =
                  Graph.VisibleEntry.visibleLoadsAt current.object piece
                    data.threshold receiver outside := by
              ext load
              constructor
              · intro member
                exact (Finset.mem_inter.mp member).1
              · intro member
                exact Finset.mem_inter.mpr ⟨member, by
                  simp [Graph.ExitFour.unpeeledLoads,
                    Graph.VisibleEntry.visibleLoadsAt_subset current.object
                      piece data.threshold receiver outside member]⟩
            exact atEmpty.symm ▸ overloaded
          omega
        have supportBound :=
          Graph.VisibleEntry.card_le_sum_silentExcess_add_positiveDeficiency
            current.object piece data.threshold data.dischargeScale
            data.dischargeScale_pos exactDegree capped routed.1 noVisiblePorts
        have selectedAfter : Graph.ExitFour.SaturatedAfter piece data.threshold
            data.dischargeScale selectedReceiver ∅ :=
          (Graph.ExitFour.saturatedAfter_empty piece data.threshold
            data.dischargeScale selectedReceiver).mpr selectedSaturated
        have selectedSilent : Graph.ExitFour.SilentUnpeeledExcessAt piece
            data.threshold data.dischargeScale selectedReceiver ∅ := by
          rcases Graph.ExitFour.visibleFourUnpeeled_or_silentUnpeeledExcess
              piece data.threshold data.dischargeScale selectedReceiver ∅
              (exactDegree selectedReceiver selectedIsReceiver.1)
              selectedIsReceiver selectedAfter with overloaded | silent
          · exact False.elim (visible
              ⟨selectedReceiver, selectedIsReceiver, selectedSaturated,
                overloaded⟩)
          · exact silent
        exact ⟨.inr (encodeExcess
          ⟨packing, valid, maximal, component, present, negative, zero,
            selectedReceiver, selectedIsReceiver, selectedSaturated,
            selectedSilent, supportBound⟩)⟩)
    visibleFresh excessFresh

/-! ## Nodes `[89]`--`[94]`: `lem:typeA-port-return`, the port non-vacuity

*"Every completion port of a Type A support has at least one anchored return.
A completion port is an oriented edge of `G`.  By `lem:bridgeless`, the
underlying edge lies on a cycle in `G`.  Removing the port edge from that cycle
leaves a simple return path in the required orientation."*

This is the fact the saturated port tests are asked under.  Without it the exit
alternatives at nodes `[95]`--`[107]` — each of the shape "some/no anchored
return of the port has property `p`" — would be satisfied vacuously by a port
carrying no returns at all, and the exit list would discharge itself.

`lem:bridgeless` is the framework's `Graph.EdgeContraction.hasReturn_of_minimal`,
and its two hypotheses are the two halves of the selection statement nodes
`[1]`--`[4]` committed.  The row therefore reads `selection` by exact key and
derives nothing else: the degree side condition is the standing baseline, read
off the input.

The fact is stated of the *object*, at every support, receiver and port,
because the manuscript's proof reads only the port edge — it never looks at the
support the port belongs to. -/
@[reducible] noncomputable def typeAPortReturnRow
    (selection typeAPortReturn :
      FactKey (Input BranchState Presentation presentation data))
    (distinct : selection ≠ typeAPortReturn)
    (avoidsOf : (input : Input BranchState Presentation presentation data) →
      selection.At input → ¬ Graph.HasCycleWithLength data.LengthOK input.object)
    (minimalOf : (input : Input BranchState Presentation presentation data) →
      selection.At input →
      ∀ smaller : Graph.FiniteObject.{u},
        smaller.LexicographicallySmaller input.object →
        Graph.MinimumDegreeAtLeast data.threshold smaller →
        Graph.HasCycleWithLength data.LengthOK smaller)
    (encode : (input : Input BranchState Presentation presentation data) →
      (∀ support : Finset input.object.Vertex,
        ∀ receiver outside : input.object.Vertex,
          outside ∈ Graph.VisibleEntry.completionPorts input.object support
            receiver →
          Nonempty (Graph.VisibleEntry.AnchoredReturn input.object receiver
            outside)) →
      typeAPortReturn.At input) :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.typeAPortReturn
    (rowManifest selection typeAPortReturn distinct)
    (fun inputs =>
      let fact := inputs.get selection
      .cons (key := typeAPortReturn)
        (encode inputs.current fun support receiver outside port =>
          Graph.VisibleEntry.exists_anchoredReturn_of_mem_completionPorts
            (LengthOK := data.LengthOK)
            (by have := data.three_le_threshold; omega)
            inputs.current.baseline (avoidsOf inputs.current fact)
            (minimalOf inputs.current fact) support receiver outside port)
        .nil)

/-! ## Node `[93]`, yes arm: clause (Q1) of `def:typeA-exit4-family`

*"The family `𝒬₄(w)` consists of boundary-degree-preserving response quotients
generated by the following canonical constructions.  (Q1) the visible
receiver-entry coordinate identifications tested in `lem:typeA-visible-entry`.
[…] The declared routed-load support is part of the canonical construction: in
(Q1) it is the set of visible routed loads whose response coordinates are
identified."*

Row 16 quantifies over `Graph.ExitFour.ReceiverFamily`, so it never invents a member of
`𝒬₄(w)`; the five generating clauses have to be supplied by the nodes that own
them, and (Q1) is this one's.  `Graph.VisibleEntry.visibleEntryFamily` is the
construction and `Graph/VisibleEntryQuotient.lean` proves its two structural
laws; what this row commits is the branch content, which is what distinguishes
the yes arm from the silent arm:

* the identification is *generated* from the receiver's own declared reading;
* it collapses at least one declared coordinate, because the port carries a
  visible load — at a silent port the same construction collapses nothing;
* its declared routed-load support contains every visible load of the port,
  which is what lets `def:typeA-exit4-peeling` remove a visible load when exit
  `(4)` is taken through this clause.

The reading is quantified over rather than named.  It is the route-8 entry's
reading, owned by nodes `[109]` onwards, so naming one here would be inventing
it; and (Q1) is a statement about whichever reading the receiver carries.

The row runs on node `[93]`'s yes cursor and reads that node's own fact by
exact key. -/
@[reducible] noncomputable def typeAVisibleEntryClauseRow
    (typeAVisibleEntry typeAVisibleEntryClause :
      FactKey (Input BranchState Presentation presentation data))
    (distinct : typeAVisibleEntry ≠ typeAVisibleEntryClause)
    (visibleOf : (input : Input BranchState Presentation presentation data) →
      typeAVisibleEntry.At input →
      ∃ packing : Finset (Finset input.object.Vertex),
        input.object.IsWindowPacking data.windowOrder packing ∧
          (∀ window : Finset input.object.Vertex,
            input.object.InducesWindow data.windowOrder window →
            ∃ member ∈ packing, ¬ Disjoint window member) ∧
          ∃ component ∈ input.object.canonicalPieces
              (input.object.remainderSupport packing),
            let piece := input.object.pieceSupport
              (input.object.remainderSupport packing) component
            input.object.NegativeNetCharge piece data.threshold
                data.dischargeScale ∧
              input.object.ambientSurplus piece data.threshold = 0 ∧
              ∃ receiver : input.object.Vertex,
                input.object.IsReceiver piece data.threshold receiver ∧
                  input.object.Saturated piece data.threshold
                    data.dischargeScale receiver ∧
                  Nonempty
                    (Graph.ExitFour.VisibleFourUnpeeledPackage piece
                      data.threshold data.dischargeScale receiver ∅))
    (encode : (input : Input BranchState Presentation presentation data) →
      (∃ packing : Finset (Finset input.object.Vertex),
        input.object.IsWindowPacking data.windowOrder packing ∧
          (∀ window : Finset input.object.Vertex,
            input.object.InducesWindow data.windowOrder window →
            ∃ member ∈ packing, ¬ Disjoint window member) ∧
          ∃ component ∈ input.object.canonicalPieces
              (input.object.remainderSupport packing),
            let piece := input.object.pieceSupport
              (input.object.remainderSupport packing) component
            input.object.NegativeNetCharge piece data.threshold
                data.dischargeScale ∧
              input.object.ambientSurplus piece data.threshold = 0 ∧
              ∃ receiver : input.object.Vertex,
                input.object.IsReceiver piece data.threshold receiver ∧
                  input.object.Saturated piece data.threshold
                    data.dischargeScale receiver ∧
                  ∃ package : Graph.ExitFour.VisibleFourUnpeeledPackage piece
                      data.threshold data.dischargeScale receiver ∅,
                    (∀ load : package.SelectedLoad,
                      ((∀ vertex ∈
                          (package.selectedReturn load.1 load.2).connector.support,
                        vertex ≠ (package.selectedResponseCoordinate load).entry.1 →
                          vertex ∉ piece) ∧
                        Graph.VisibleEntry.IsChannel input.object piece
                          (package.selectedResponseCoordinate load).channel) ∧
                        (package.selectedPieceChannel load).length =
                          (package.selectedResponseCoordinate load).channel.length ∧
                        (package.selectedContextConnector load).length =
                          (package.selectedResponseCoordinate load).connectorLabel) ∧
                    (∀ selected : package.SelectedGerm,
                      selected ∈ package.germSchedule.values) ∧
                    (∀ pair : package.GermPair,
                      pair ∈ package.germPairSchedule.values ∧
                        Graph.DecoratedHandoff.SeparatesAt
                          pair.left.germ.path pair.right.germ.path
                            pair.firstSeparator.separator ∧
                        pair.separatorOrder = pair.firstSeparator.separator ::
                          pair.firstSeparator.remaining)) →
      typeAVisibleEntryClause.At input) :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.typeAVisibleEntryClause
    (rowManifest typeAVisibleEntry typeAVisibleEntryClause distinct)
    (fun inputs =>
      let port := visibleOf inputs.current (inputs.get typeAVisibleEntry)
      .cons (key := typeAVisibleEntryClause)
        (encode inputs.current (by
          classical
          obtain ⟨packing, valid, maximal, component, present, negative, zero,
            receiver, isReceiver, saturated, packageExists⟩ := port
          obtain ⟨package⟩ := packageExists
          refine ⟨packing, valid, maximal, component, present, negative, zero,
            receiver, isReceiver, saturated, package, ?_, ?_, ?_⟩
          · intro load
            exact ⟨package.selectedResponseCoordinate_ownership load,
              package.selectedPieceChannel_length load,
              package.selectedContextConnector_length load⟩
          · exact fun selected => package.mem_germSchedule selected
          · intro pair
            exact ⟨package.mem_germPairSchedule pair,
              pair.firstSeparator_separatesAt,
              pair.separatorOrder_eq_cons⟩))
        .nil)

/-! ## The shared entry of nodes `[101]`--`[107]`

Figure 8 draws one segment `[101]`--`[107]` with two entries: node `[99]`'s no
arm, which `lem:typeA-unpeeled-visible-routing` routes after exits `(1)`--`(3)`
have been denied, and node `[94]`, which `lem:typeA-unpeeled-silent-routing`
routes.  `lem:typeA-exit4-residual-routing` is the manuscript's own statement
that the two combine — *"let `w` be a saturated Type A receiver with a peeling
set `P₄(w)`; if `L₄(w) ≥ 4q(w)`, then the unpeeled routed loads at `w` realize
one of exits (1)--(8)"* — and its hypothesis is the fact this row commits.  The
exit segment is asked under it and under nothing else, which is what keeps it
one chain of nodes instead of two copies.

Nothing is proved here.  The row reads node `[89]`'s saturation off the ledger
by exact key and refines it: at the empty peeling set `L₄(w) = L(w)`, so
`ExitFour.saturatedAfter_empty` turns that fact into this one.  The peeling set
grows only at node `[102]`, and its `def:typeA-exit4-peeling` witnesses ride
with node `[102]`'s own fact. -/
@[reducible] noncomputable def typeASaturatedExitEntryRow
    (source typeASaturatedExitEntry :
      FactKey (Input BranchState Presentation presentation data))
    (distinct : source ≠ typeASaturatedExitEntry)
    (sourceOf : (input : Input BranchState Presentation presentation data) →
      source.At input →
      ∃ packing : Finset (Finset input.object.Vertex),
        input.object.IsWindowPacking data.windowOrder packing ∧
          (∀ window : Finset input.object.Vertex,
            input.object.InducesWindow data.windowOrder window →
            ∃ member ∈ packing, ¬ Disjoint window member) ∧
          ∃ component ∈ input.object.canonicalPieces
              (input.object.remainderSupport packing),
            let piece := input.object.pieceSupport
              (input.object.remainderSupport packing) component
            input.object.NegativeNetCharge piece data.threshold
                data.dischargeScale ∧
              input.object.ambientSurplus piece data.threshold = 0 ∧
              ∃ receiver : input.object.Vertex,
                input.object.IsReceiver piece data.threshold receiver ∧
                  input.object.Saturated piece data.threshold
                    data.dischargeScale receiver)
    (encode : (input : Input BranchState Presentation presentation data) →
      (∃ packing : Finset (Finset input.object.Vertex),
        input.object.IsWindowPacking data.windowOrder packing ∧
          (∀ window : Finset input.object.Vertex,
            input.object.InducesWindow data.windowOrder window →
            ∃ member ∈ packing, ¬ Disjoint window member) ∧
          ∃ component ∈ input.object.canonicalPieces
              (input.object.remainderSupport packing),
            let piece := input.object.pieceSupport
              (input.object.remainderSupport packing) component
            input.object.NegativeNetCharge piece data.threshold
                data.dischargeScale ∧
              input.object.ambientSurplus piece data.threshold = 0 ∧
              ∃ receiver : input.object.Vertex,
                input.object.IsReceiver piece data.threshold receiver ∧
                  ∃ peeled : Finset input.object.Vertex,
                    peeled ⊆ input.object.routedLoads piece data.threshold
                        receiver ∧
                      Graph.ExitFour.SaturatedAfter piece data.threshold
                        data.dischargeScale receiver peeled) →
      typeASaturatedExitEntry.At input) :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.typeASaturatedExitEntry
    (rowManifest source typeASaturatedExitEntry distinct)
    (fun inputs =>
      .cons (key := typeASaturatedExitEntry)
        (encode inputs.current (by
          classical
          obtain ⟨packing, valid, maximal, component, present, charge,
            surplus, receiver, isReceiver, saturated⟩ :=
            sourceOf inputs.current (inputs.get source)
          let piece := inputs.current.object.pieceSupport
            (inputs.current.object.remainderSupport packing) component
          exact ⟨packing, valid, maximal, component, present, charge,
            surplus, receiver, isReceiver, ∅, Finset.empty_subset _,
            (Graph.ExitFour.saturatedAfter_empty piece data.threshold
              data.dischargeScale receiver).mpr saturated⟩))
        .nil)

/-- **`lem:typeA-saturated-handoff`, finite descent part.**

The row reads the exact saturated receiver/peeling state already committed in
`typeASaturatedExitEntry` and publishes the paper's finite exit-`(4)` descent
principle for that state.  The terminal predicates are not chosen here:
downstream rows instantiate them with the actual closed exits, exit-`(7)`
handoff, and route-8 residual facts once those semantic facts are on the
ledger. -/
@[reducible] noncomputable def typeAExitFourFiniteDescentRow
    (typeASaturatedExitEntry typeAExitFourFiniteDescent :
      FactKey (Input BranchState Presentation presentation data))
    (distinct : typeASaturatedExitEntry ≠ typeAExitFourFiniteDescent)
    (entryOf : (input : Input BranchState Presentation presentation data) →
      typeASaturatedExitEntry.At input →
      ∃ packing : Finset (Finset input.object.Vertex),
        input.object.IsWindowPacking data.windowOrder packing ∧
          (∀ window : Finset input.object.Vertex,
            input.object.InducesWindow data.windowOrder window →
            ∃ member ∈ packing, ¬ Disjoint window member) ∧
          ∃ component ∈ input.object.canonicalPieces
              (input.object.remainderSupport packing),
            let piece := input.object.pieceSupport
              (input.object.remainderSupport packing) component
            input.object.NegativeNetCharge piece data.threshold
                data.dischargeScale ∧
              input.object.ambientSurplus piece data.threshold = 0 ∧
              ∃ receiver : input.object.Vertex,
                input.object.IsReceiver piece data.threshold receiver ∧
                  ∃ peeled : Finset input.object.Vertex,
                    peeled ⊆ input.object.routedLoads piece data.threshold
                        receiver ∧
                      Graph.ExitFour.SaturatedAfter piece data.threshold
                        data.dischargeScale receiver peeled)
    (encode : (input : Input BranchState Presentation presentation data) →
      (∃ packing : Finset (Finset input.object.Vertex),
        input.object.IsWindowPacking data.windowOrder packing ∧
          (∀ window : Finset input.object.Vertex,
            input.object.InducesWindow data.windowOrder window →
            ∃ member ∈ packing, ¬ Disjoint window member) ∧
          ∃ component ∈ input.object.canonicalPieces
              (input.object.remainderSupport packing),
            let piece := input.object.pieceSupport
              (input.object.remainderSupport packing) component
            input.object.NegativeNetCharge piece data.threshold
                data.dischargeScale ∧
              input.object.ambientSurplus piece data.threshold = 0 ∧
              ∃ receiver : input.object.Vertex,
                input.object.IsReceiver piece data.threshold receiver ∧
                  ∃ startPeeled : Finset input.object.Vertex,
                    startPeeled ⊆ input.object.routedLoads piece data.threshold
                        receiver ∧
                      Graph.ExitFour.SaturatedAfter piece data.threshold
                        data.dischargeScale receiver startPeeled ∧
                      ∀ Retained Terminal :
                          Finset input.object.Vertex → Prop,
                        Retained startPeeled →
                        (∀ peeled,
                          peeled ⊆
                            input.object.routedLoads piece data.threshold
                              receiver →
                          Retained peeled →
                          Graph.ExitFour.SaturatedAfter piece data.threshold
                            data.dischargeScale receiver peeled →
                          Terminal peeled ∨
                            ∃ load ∈ input.object.routedLoads piece
                                data.threshold receiver,
                              ∃ fresh : load ∉ peeled, Retained (Finset.cons load peeled fresh)) →
                        (∃ finalPeeled ⊆
                            input.object.routedLoads piece data.threshold
                              receiver,
                          Retained finalPeeled ∧ Terminal finalPeeled) ∨
                        (∃ finalPeeled ⊆
                            input.object.routedLoads piece data.threshold
                              receiver,
                          Retained finalPeeled ∧
                            ¬ Graph.ExitFour.SaturatedAfter piece
                              data.threshold data.dischargeScale receiver
                              finalPeeled)) →
      typeAExitFourFiniteDescent.At input) :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.typeAExitFourFiniteDescent
    (rowManifest typeASaturatedExitEntry typeAExitFourFiniteDescent distinct)
    (fun inputs =>
      .cons (key := typeAExitFourFiniteDescent)
        (encode inputs.current (by
          classical
          obtain ⟨packing, valid, maximal, component, present, negative, zero,
            receiver, isReceiver, startPeeled, startInside, startSaturated⟩ :=
            entryOf inputs.current (inputs.get typeASaturatedExitEntry)
          let piece := inputs.current.object.pieceSupport
            (inputs.current.object.remainderSupport packing) component
          refine ⟨packing, valid, maximal, component, present, negative, zero,
            receiver, isReceiver, startPeeled, startInside, startSaturated,
            ?_⟩
          intro Retained Terminal startRetained step
          exact Graph.ExitFour.terminal_or_unsaturated_from piece
            data.threshold data.dischargeScale receiver startInside
            startRetained step))
        .nil)

/-- **`lem:typeA-exit4-residual-routing`, visible/silent split at the current
peeling state.**

The row reads the current `typeASaturatedExitEntry` state from the ledger and
asks the paper's first question at that state: does a completion port carry
four unpeeled visible returns?  The yes arm commits the canonical visible
package for that same `P₄(w)`; the no arm commits the selected silent residual
excess. -/
noncomputable def typeASaturatedHandoffSplitDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous :
      ExactLedger (Input BranchState Presentation presentation data)
        current known)
    (typeASaturatedExitEntry typeASaturatedHandoffVisible
      typeASaturatedHandoffSilent :
      FactKey (Input BranchState Presentation presentation data))
    [Core.Residual.FactKeys.Has typeASaturatedExitEntry known]
    (entryOf : typeASaturatedExitEntry.At current →
      ∃ packing : Finset (Finset current.object.Vertex),
        current.object.IsWindowPacking data.windowOrder packing ∧
          (∀ window : Finset current.object.Vertex,
            current.object.InducesWindow data.windowOrder window →
            ∃ member ∈ packing, ¬ Disjoint window member) ∧
          ∃ component ∈ current.object.canonicalPieces
              (current.object.remainderSupport packing),
            let piece := current.object.pieceSupport
              (current.object.remainderSupport packing) component
            current.object.NegativeNetCharge piece data.threshold
                data.dischargeScale ∧
              current.object.ambientSurplus piece data.threshold = 0 ∧
              ∃ receiver : current.object.Vertex,
                current.object.IsReceiver piece data.threshold receiver ∧
                  ∃ peeled : Finset current.object.Vertex,
                    peeled ⊆ current.object.routedLoads piece data.threshold
                        receiver ∧
                      Graph.ExitFour.SaturatedAfter piece data.threshold
                        data.dischargeScale receiver peeled)
    (encodeVisible :
      (∃ packing : Finset (Finset current.object.Vertex),
        current.object.IsWindowPacking data.windowOrder packing ∧
          (∀ window : Finset current.object.Vertex,
            current.object.InducesWindow data.windowOrder window →
            ∃ member ∈ packing, ¬ Disjoint window member) ∧
          ∃ component ∈ current.object.canonicalPieces
              (current.object.remainderSupport packing),
            let piece := current.object.pieceSupport
              (current.object.remainderSupport packing) component
            current.object.NegativeNetCharge piece data.threshold
                data.dischargeScale ∧
              current.object.ambientSurplus piece data.threshold = 0 ∧
              ∃ receiver : current.object.Vertex,
                current.object.IsReceiver piece data.threshold receiver ∧
                  ∃ peeled : Finset current.object.Vertex,
                    peeled ⊆ current.object.routedLoads piece data.threshold
                        receiver ∧
                      Graph.ExitFour.SaturatedAfter piece data.threshold
                        data.dischargeScale receiver peeled ∧
                      Nonempty
                        (Graph.ExitFour.VisibleFourUnpeeledPackage piece
                          data.threshold data.dischargeScale receiver peeled)) →
      typeASaturatedHandoffVisible.At current)
    (encodeSilent :
      (∃ packing : Finset (Finset current.object.Vertex),
        current.object.IsWindowPacking data.windowOrder packing ∧
          (∀ window : Finset current.object.Vertex,
            current.object.InducesWindow data.windowOrder window →
            ∃ member ∈ packing, ¬ Disjoint window member) ∧
          ∃ component ∈ current.object.canonicalPieces
              (current.object.remainderSupport packing),
            let piece := current.object.pieceSupport
              (current.object.remainderSupport packing) component
            current.object.NegativeNetCharge piece data.threshold
                data.dischargeScale ∧
              current.object.ambientSurplus piece data.threshold = 0 ∧
              ∃ receiver : current.object.Vertex,
                current.object.IsReceiver piece data.threshold receiver ∧
                  ∃ peeled : Finset current.object.Vertex,
                    peeled ⊆ current.object.routedLoads piece data.threshold
                        receiver ∧
                      Graph.ExitFour.SaturatedAfter piece data.threshold
                        data.dischargeScale receiver peeled ∧
                      Graph.ExitFour.SilentUnpeeledExcessAt piece
                        data.threshold data.dischargeScale receiver peeled) →
      typeASaturatedHandoffSilent.At current)
    (visibleFresh : typeASaturatedHandoffVisible ∉ known)
    (silentFresh : typeASaturatedHandoffSilent ∉ known) :
    Decision typeASaturatedHandoffVisible typeASaturatedHandoffSilent
      previous :=
  Decision.run previous typeASaturatedHandoffVisible
    typeASaturatedHandoffSilent
    `Hypostructure.Graph.Strategy.Spine.typeASaturatedHandoffSplitDichotomy
    (by
      classical
      apply Classical.choice
      obtain ⟨packing, valid, maximal, component, present, negative, zero,
        receiver, isReceiver, peeled, peeledSubset, saturated⟩ :=
        entryOf (ExactLedger.get previous typeASaturatedExitEntry)
      let piece := current.object.pieceSupport
        (current.object.remainderSupport packing) component
      have exactDegree : ∀ vertex ∈ piece,
          current.object.degree vertex = data.threshold := by
        intro vertex member
        have lower : data.threshold ≤ current.object.degree vertex :=
          le_trans current.baseline
            (current.object.minDegree_le_degree vertex)
        have summand : current.object.degree vertex - data.threshold = 0 :=
          Nat.eq_zero_of_le_zero
            (zero ▸ Finset.single_le_sum
              (f := fun other =>
                current.object.degree other - data.threshold)
              (fun _ _ => Nat.zero_le _) member)
        omega
      by_cases visible :
          Graph.ExitFour.VisibleFourUnpeeledAt piece data.threshold
            data.dischargeScale receiver peeled
      · exact ⟨.inl (encodeVisible
          ⟨packing, valid, maximal, component, present, negative, zero,
            receiver, isReceiver, peeled, peeledSubset, saturated,
            Graph.ExitFour.visibleFourUnpeeledPackage piece data.threshold
              data.dischargeScale receiver peeled visible⟩)⟩
      · have silent : Graph.ExitFour.SilentUnpeeledExcessAt piece
            data.threshold data.dischargeScale receiver peeled := by
          rcases Graph.ExitFour.visibleFourUnpeeled_or_silentUnpeeledExcess
              piece data.threshold data.dischargeScale receiver peeled
              (exactDegree receiver isReceiver.1) isReceiver saturated with
            overloaded | silent
          · exact False.elim (visible overloaded)
          · exact silent
        exact ⟨.inr (encodeSilent
          ⟨packing, valid, maximal, component, present, negative, zero,
            receiver, isReceiver, peeled, peeledSubset, saturated,
            silent⟩)⟩)
    visibleFresh silentFresh

/-! ## Node `[101]` inside `lem:typeA-exit4-residual-routing`

After the arbitrary-peeling visible/silent split, exit `(4)` is tested at the
same selected receiver and the same current `P₄(w)`.  The visible and silent
sources have different canonical support clauses, but they commit the same
semantic facts: either an exit-`(4)` witness is present, or the selected current
state carries the no-exit-`(4)` hypothesis used by node `[103]`. -/

noncomputable def typeASaturatedHandoffVisibleExitFourDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous :
      ExactLedger (Input BranchState Presentation presentation data)
        current known)
    (typeASaturatedHandoffVisible typeASaturatedHandoffExitFour
      typeASaturatedHandoffExitFourFree :
      FactKey (Input BranchState Presentation presentation data))
    [Core.Residual.FactKeys.Has typeASaturatedHandoffVisible known]
    (visibleOf : typeASaturatedHandoffVisible.At current →
      ∃ packing : Finset (Finset current.object.Vertex),
        current.object.IsWindowPacking data.windowOrder packing ∧
          (∀ window : Finset current.object.Vertex,
            current.object.InducesWindow data.windowOrder window →
            ∃ member ∈ packing, ¬ Disjoint window member) ∧
          ∃ component ∈ current.object.canonicalPieces
              (current.object.remainderSupport packing),
            let piece := current.object.pieceSupport
              (current.object.remainderSupport packing) component
            current.object.NegativeNetCharge piece data.threshold
                data.dischargeScale ∧
              current.object.ambientSurplus piece data.threshold = 0 ∧
              ∃ receiver : current.object.Vertex,
                current.object.IsReceiver piece data.threshold receiver ∧
                  ∃ peeled : Finset current.object.Vertex,
                    peeled ⊆ current.object.routedLoads piece data.threshold
                        receiver ∧
                      Graph.ExitFour.SaturatedAfter piece data.threshold
                        data.dischargeScale receiver peeled ∧
                      Nonempty
                        (Graph.ExitFour.VisibleFourUnpeeledPackage piece
                          data.threshold data.dischargeScale receiver peeled))
    (encodeExit :
      (∃ packing : Finset (Finset current.object.Vertex),
        current.object.IsWindowPacking data.windowOrder packing ∧
          (∀ window : Finset current.object.Vertex,
            current.object.InducesWindow data.windowOrder window →
            ∃ member ∈ packing, ¬ Disjoint window member) ∧
          ∃ component ∈ current.object.canonicalPieces
              (current.object.remainderSupport packing),
            let piece := current.object.pieceSupport
              (current.object.remainderSupport packing) component
            current.object.NegativeNetCharge piece data.threshold
                data.dischargeScale ∧
              current.object.ambientSurplus piece data.threshold = 0 ∧
              ∃ receiver : current.object.Vertex,
                current.object.IsReceiver piece data.threshold receiver ∧
                  ∃ peeled : Finset current.object.Vertex,
                    peeled ⊆ current.object.routedLoads piece data.threshold
                        receiver ∧
                      Graph.ExitFour.SaturatedAfter piece data.threshold
                        data.dischargeScale receiver peeled ∧
                      ((∃ package :
                          Graph.ExitFour.VisibleFourUnpeeledPackage piece
                            data.threshold data.dischargeScale receiver peeled,
                        ∃ witness : Graph.ExitFour.Witness
                            (Graph.HasCycleWithLength data.LengthOK) piece
                            data.threshold receiver peeled,
                          ∃ load ∈ Graph.ExitFour.selectedVisibleUnpeeledLoads
                              piece data.threshold data.dischargeScale receiver
                              package.outside peeled,
                            witness.load = load) ∨
                        (Graph.ExitFour.SilentUnpeeledExcessAt piece
                            data.threshold data.dischargeScale receiver peeled ∧
                          ∃ witness : Graph.ExitFour.Witness
                              (Graph.HasCycleWithLength data.LengthOK) piece
                              data.threshold receiver peeled,
                            witness.load ∈ Graph.ExitFour.unpeeledExcess piece
                              data.threshold data.dischargeScale receiver peeled))) →
      typeASaturatedHandoffExitFour.At current)
    (encodeFree :
      (∃ packing : Finset (Finset current.object.Vertex),
        current.object.IsWindowPacking data.windowOrder packing ∧
          (∀ window : Finset current.object.Vertex,
            current.object.InducesWindow data.windowOrder window →
            ∃ member ∈ packing, ¬ Disjoint window member) ∧
          ∃ component ∈ current.object.canonicalPieces
              (current.object.remainderSupport packing),
            let piece := current.object.pieceSupport
              (current.object.remainderSupport packing) component
            current.object.NegativeNetCharge piece data.threshold
                data.dischargeScale ∧
              current.object.ambientSurplus piece data.threshold = 0 ∧
              ∃ receiver : current.object.Vertex,
                current.object.IsReceiver piece data.threshold receiver ∧
                  ∃ peeled : Finset current.object.Vertex,
                    peeled ⊆ current.object.routedLoads piece data.threshold
                        receiver ∧
                      Graph.ExitFour.SaturatedAfter piece data.threshold
                        data.dischargeScale receiver peeled ∧
                      ((∃ package :
                          Graph.ExitFour.VisibleFourUnpeeledPackage piece
                            data.threshold data.dischargeScale receiver peeled,
                        ¬ ∃ witness : Graph.ExitFour.Witness
                            (Graph.HasCycleWithLength data.LengthOK) piece
                            data.threshold receiver peeled,
                          ∃ load ∈ Graph.ExitFour.selectedVisibleUnpeeledLoads
                              piece data.threshold data.dischargeScale receiver
                              package.outside peeled,
                            witness.load = load) ∨
                        (Graph.ExitFour.SilentUnpeeledExcessAt piece
                            data.threshold data.dischargeScale receiver peeled ∧
                          ¬ ∃ witness : Graph.ExitFour.Witness
                              (Graph.HasCycleWithLength data.LengthOK) piece
                              data.threshold receiver peeled,
                            witness.load ∈ Graph.ExitFour.unpeeledExcess piece
                              data.threshold data.dischargeScale receiver peeled))) →
      typeASaturatedHandoffExitFourFree.At current)
    (exitFresh : typeASaturatedHandoffExitFour ∉ known)
    (freeFresh : typeASaturatedHandoffExitFourFree ∉ known) :
    Decision typeASaturatedHandoffExitFour
      typeASaturatedHandoffExitFourFree previous :=
  Decision.run previous typeASaturatedHandoffExitFour
    typeASaturatedHandoffExitFourFree
    `Hypostructure.Graph.Strategy.Spine.typeASaturatedHandoffVisibleExitFourDichotomy
    (by
      classical
      apply Classical.choice
      obtain ⟨packing, valid, maximal, component, present, negative, zero,
        receiver, isReceiver, peeled, peeledSubset, saturated, packageWitness⟩ :=
        visibleOf (ExactLedger.get previous typeASaturatedHandoffVisible)
      obtain ⟨package⟩ := packageWitness
      let piece := current.object.pieceSupport
        (current.object.remainderSupport packing) component
      by_cases occurs :
          ∃ witness : Graph.ExitFour.Witness
              (Graph.HasCycleWithLength data.LengthOK) piece data.threshold
              receiver peeled,
            ∃ load ∈ Graph.ExitFour.selectedVisibleUnpeeledLoads
                piece data.threshold data.dischargeScale receiver
                package.outside peeled,
              witness.load = load
      · exact ⟨.inl (encodeExit
          ⟨packing, valid, maximal, component, present, negative, zero,
            receiver, isReceiver, peeled, peeledSubset, saturated,
            Or.inl ⟨package, occurs⟩⟩)⟩
      · exact ⟨.inr (encodeFree
          ⟨packing, valid, maximal, component, present, negative, zero,
            receiver, isReceiver, peeled, peeledSubset, saturated,
            Or.inl ⟨package, occurs⟩⟩)⟩)
    exitFresh freeFresh

@[reducible] noncomputable def typeASaturatedHandoffSilentFromFirstExcessRow
    (typeAVisibleFirstExcess typeASaturatedHandoffSilent :
      FactKey (Input BranchState Presentation presentation data))
    (distinct : typeAVisibleFirstExcess ≠ typeASaturatedHandoffSilent)
    (excessOf : (input : Input BranchState Presentation presentation data) →
      typeAVisibleFirstExcess.At input →
      ∃ packing : Finset (Finset input.object.Vertex),
        input.object.IsWindowPacking data.windowOrder packing ∧
          (∀ window : Finset input.object.Vertex,
            input.object.InducesWindow data.windowOrder window →
            ∃ member ∈ packing, ¬ Disjoint window member) ∧
          ∃ component ∈ input.object.canonicalPieces
              (input.object.remainderSupport packing),
            let piece := input.object.pieceSupport
              (input.object.remainderSupport packing) component
            input.object.NegativeNetCharge piece data.threshold
                data.dischargeScale ∧
              input.object.ambientSurplus piece data.threshold = 0 ∧
              ∃ receiver : input.object.Vertex,
                input.object.IsReceiver piece data.threshold receiver ∧
                  input.object.Saturated piece data.threshold
                    data.dischargeScale receiver ∧
                  Graph.ExitFour.SilentUnpeeledExcessAt piece data.threshold
                    data.dischargeScale receiver ∅)
    (encode : (input : Input BranchState Presentation presentation data) →
      (∃ packing : Finset (Finset input.object.Vertex),
        input.object.IsWindowPacking data.windowOrder packing ∧
          (∀ window : Finset input.object.Vertex,
            input.object.InducesWindow data.windowOrder window →
            ∃ member ∈ packing, ¬ Disjoint window member) ∧
          ∃ component ∈ input.object.canonicalPieces
              (input.object.remainderSupport packing),
            let piece := input.object.pieceSupport
              (input.object.remainderSupport packing) component
            input.object.NegativeNetCharge piece data.threshold
                data.dischargeScale ∧
              input.object.ambientSurplus piece data.threshold = 0 ∧
              ∃ receiver : input.object.Vertex,
                input.object.IsReceiver piece data.threshold receiver ∧
                  ∃ peeled : Finset input.object.Vertex,
                    peeled ⊆ input.object.routedLoads piece data.threshold
                        receiver ∧
                      Graph.ExitFour.SaturatedAfter piece data.threshold
                        data.dischargeScale receiver peeled ∧
                      Graph.ExitFour.SilentUnpeeledExcessAt piece
                        data.threshold data.dischargeScale receiver peeled) →
      typeASaturatedHandoffSilent.At input) :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly
    `Hypostructure.Graph.Strategy.Spine.typeASaturatedHandoffSilentFromFirstExcess
    (rowManifest typeAVisibleFirstExcess typeASaturatedHandoffSilent distinct)
    (fun inputs =>
      .cons (key := typeASaturatedHandoffSilent)
        (encode inputs.current (by
          classical
          obtain ⟨packing, valid, maximal, component, present, negative, zero,
            receiver, isReceiver, saturated, silent⟩ :=
            excessOf inputs.current (inputs.get typeAVisibleFirstExcess)
          let piece := inputs.current.object.pieceSupport
            (inputs.current.object.remainderSupport packing) component
          exact ⟨packing, valid, maximal, component, present, negative, zero,
            receiver, isReceiver, ∅, Finset.empty_subset _,
            (Graph.ExitFour.saturatedAfter_empty piece data.threshold
              data.dischargeScale receiver).mpr saturated, silent⟩))
        .nil)

noncomputable def typeASaturatedHandoffSilentExitFourDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous :
      ExactLedger (Input BranchState Presentation presentation data)
        current known)
    (typeASaturatedHandoffSilent typeASaturatedHandoffExitFour
      typeASaturatedHandoffExitFourFree :
      FactKey (Input BranchState Presentation presentation data))
    [Core.Residual.FactKeys.Has typeASaturatedHandoffSilent known]
    (silentOf : typeASaturatedHandoffSilent.At current →
      ∃ packing : Finset (Finset current.object.Vertex),
        current.object.IsWindowPacking data.windowOrder packing ∧
          (∀ window : Finset current.object.Vertex,
            current.object.InducesWindow data.windowOrder window →
            ∃ member ∈ packing, ¬ Disjoint window member) ∧
          ∃ component ∈ current.object.canonicalPieces
              (current.object.remainderSupport packing),
            let piece := current.object.pieceSupport
              (current.object.remainderSupport packing) component
            current.object.NegativeNetCharge piece data.threshold
                data.dischargeScale ∧
              current.object.ambientSurplus piece data.threshold = 0 ∧
              ∃ receiver : current.object.Vertex,
                current.object.IsReceiver piece data.threshold receiver ∧
                  ∃ peeled : Finset current.object.Vertex,
                    peeled ⊆ current.object.routedLoads piece data.threshold
                        receiver ∧
                      Graph.ExitFour.SaturatedAfter piece data.threshold
                        data.dischargeScale receiver peeled ∧
                      Graph.ExitFour.SilentUnpeeledExcessAt piece
                        data.threshold data.dischargeScale receiver peeled)
    (encodeExit :
      (∃ packing : Finset (Finset current.object.Vertex),
        current.object.IsWindowPacking data.windowOrder packing ∧
          (∀ window : Finset current.object.Vertex,
            current.object.InducesWindow data.windowOrder window →
            ∃ member ∈ packing, ¬ Disjoint window member) ∧
          ∃ component ∈ current.object.canonicalPieces
              (current.object.remainderSupport packing),
            let piece := current.object.pieceSupport
              (current.object.remainderSupport packing) component
            current.object.NegativeNetCharge piece data.threshold
                data.dischargeScale ∧
              current.object.ambientSurplus piece data.threshold = 0 ∧
              ∃ receiver : current.object.Vertex,
                current.object.IsReceiver piece data.threshold receiver ∧
                  ∃ peeled : Finset current.object.Vertex,
                    peeled ⊆ current.object.routedLoads piece data.threshold
                        receiver ∧
                      Graph.ExitFour.SaturatedAfter piece data.threshold
                        data.dischargeScale receiver peeled ∧
                      ((∃ package :
                          Graph.ExitFour.VisibleFourUnpeeledPackage piece
                            data.threshold data.dischargeScale receiver peeled,
                        ∃ witness : Graph.ExitFour.Witness
                            (Graph.HasCycleWithLength data.LengthOK) piece
                            data.threshold receiver peeled,
                          ∃ load ∈ Graph.ExitFour.selectedVisibleUnpeeledLoads
                              piece data.threshold data.dischargeScale receiver
                              package.outside peeled,
                            witness.load = load) ∨
                        (Graph.ExitFour.SilentUnpeeledExcessAt piece
                            data.threshold data.dischargeScale receiver peeled ∧
                          ∃ witness : Graph.ExitFour.Witness
                              (Graph.HasCycleWithLength data.LengthOK) piece
                              data.threshold receiver peeled,
                            witness.load ∈ Graph.ExitFour.unpeeledExcess piece
                              data.threshold data.dischargeScale receiver peeled))) →
      typeASaturatedHandoffExitFour.At current)
    (encodeFree :
      (∃ packing : Finset (Finset current.object.Vertex),
        current.object.IsWindowPacking data.windowOrder packing ∧
          (∀ window : Finset current.object.Vertex,
            current.object.InducesWindow data.windowOrder window →
            ∃ member ∈ packing, ¬ Disjoint window member) ∧
          ∃ component ∈ current.object.canonicalPieces
              (current.object.remainderSupport packing),
            let piece := current.object.pieceSupport
              (current.object.remainderSupport packing) component
            current.object.NegativeNetCharge piece data.threshold
                data.dischargeScale ∧
              current.object.ambientSurplus piece data.threshold = 0 ∧
              ∃ receiver : current.object.Vertex,
                current.object.IsReceiver piece data.threshold receiver ∧
                  ∃ peeled : Finset current.object.Vertex,
                    peeled ⊆ current.object.routedLoads piece data.threshold
                        receiver ∧
                      Graph.ExitFour.SaturatedAfter piece data.threshold
                        data.dischargeScale receiver peeled ∧
                      ((∃ package :
                          Graph.ExitFour.VisibleFourUnpeeledPackage piece
                            data.threshold data.dischargeScale receiver peeled,
                        ¬ ∃ witness : Graph.ExitFour.Witness
                            (Graph.HasCycleWithLength data.LengthOK) piece
                            data.threshold receiver peeled,
                          ∃ load ∈ Graph.ExitFour.selectedVisibleUnpeeledLoads
                              piece data.threshold data.dischargeScale receiver
                              package.outside peeled,
                            witness.load = load) ∨
                        (Graph.ExitFour.SilentUnpeeledExcessAt piece
                            data.threshold data.dischargeScale receiver peeled ∧
                          ¬ ∃ witness : Graph.ExitFour.Witness
                              (Graph.HasCycleWithLength data.LengthOK) piece
                              data.threshold receiver peeled,
                            witness.load ∈ Graph.ExitFour.unpeeledExcess piece
                              data.threshold data.dischargeScale receiver peeled))) →
      typeASaturatedHandoffExitFourFree.At current)
    (exitFresh : typeASaturatedHandoffExitFour ∉ known)
    (freeFresh : typeASaturatedHandoffExitFourFree ∉ known) :
    Decision typeASaturatedHandoffExitFour
      typeASaturatedHandoffExitFourFree previous :=
  Decision.run previous typeASaturatedHandoffExitFour
    typeASaturatedHandoffExitFourFree
    `Hypostructure.Graph.Strategy.Spine.typeASaturatedHandoffSilentExitFourDichotomy
    (by
      classical
      apply Classical.choice
      obtain ⟨packing, valid, maximal, component, present, negative, zero,
        receiver, isReceiver, peeled, peeledSubset, saturated, silent⟩ :=
        silentOf (ExactLedger.get previous typeASaturatedHandoffSilent)
      let piece := current.object.pieceSupport
        (current.object.remainderSupport packing) component
      by_cases occurs :
          ∃ witness : Graph.ExitFour.Witness
              (Graph.HasCycleWithLength data.LengthOK) piece data.threshold
              receiver peeled,
            witness.load ∈ Graph.ExitFour.unpeeledExcess piece data.threshold
              data.dischargeScale receiver peeled
      · exact ⟨.inl (encodeExit
          ⟨packing, valid, maximal, component, present, negative, zero,
            receiver, isReceiver, peeled, peeledSubset, saturated,
            Or.inr ⟨silent, occurs⟩⟩)⟩
      · exact ⟨.inr (encodeFree
          ⟨packing, valid, maximal, component, present, negative, zero,
            receiver, isReceiver, peeled, peeledSubset, saturated,
            Or.inr ⟨silent, occurs⟩⟩)⟩)
    exitFresh freeFresh

/-! ## Node `[103]`: exit `(5)`, target-complete compression

The predecessor is the exact no-exit-`(4)` fact from the current saturated
handoff state.  The decision tests only whether the paper's target-complete
proper-support compression exists at this same residual. -/

noncomputable def typeAExitFiveDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous :
      ExactLedger (Input BranchState Presentation presentation data)
        current known)
    (typeASaturatedHandoffExitFourFree typeAExitFive typeAExitFiveFree :
      FactKey (Input BranchState Presentation presentation data))
    [Core.Residual.FactKeys.Has typeASaturatedHandoffExitFourFree known]
    (freeOf : typeASaturatedHandoffExitFourFree.At current →
      ∃ packing : Finset (Finset current.object.Vertex),
        current.object.IsWindowPacking data.windowOrder packing ∧
          (∀ window : Finset current.object.Vertex,
            current.object.InducesWindow data.windowOrder window →
            ∃ member ∈ packing, ¬ Disjoint window member) ∧
          ∃ component ∈ current.object.canonicalPieces
              (current.object.remainderSupport packing),
            let piece := current.object.pieceSupport
              (current.object.remainderSupport packing) component
            current.object.NegativeNetCharge piece data.threshold
                data.dischargeScale ∧
              current.object.ambientSurplus piece data.threshold = 0 ∧
              ∃ receiver : current.object.Vertex,
                current.object.IsReceiver piece data.threshold receiver ∧
                  ∃ peeled : Finset current.object.Vertex,
                    peeled ⊆ current.object.routedLoads piece data.threshold
                        receiver ∧
                      Graph.ExitFour.SaturatedAfter piece data.threshold
                        data.dischargeScale receiver peeled ∧
                      ((∃ package :
                          Graph.ExitFour.VisibleFourUnpeeledPackage piece
                            data.threshold data.dischargeScale receiver peeled,
                        ¬ ∃ witness : Graph.ExitFour.Witness
                            (Graph.HasCycleWithLength data.LengthOK) piece
                            data.threshold receiver peeled,
                          ∃ load ∈ Graph.ExitFour.selectedVisibleUnpeeledLoads
                              piece data.threshold data.dischargeScale receiver
                              package.outside peeled,
                            witness.load = load) ∨
                        (Graph.ExitFour.SilentUnpeeledExcessAt piece
                            data.threshold data.dischargeScale receiver peeled ∧
                          ¬ ∃ witness : Graph.ExitFour.Witness
                              (Graph.HasCycleWithLength data.LengthOK) piece
                              data.threshold receiver peeled,
                            witness.load ∈ Graph.ExitFour.unpeeledExcess piece
                              data.threshold data.dischargeScale receiver peeled)))
    (encodeExit :
      (∃ packing : Finset (Finset current.object.Vertex),
        current.object.IsWindowPacking data.windowOrder packing ∧
          (∀ window : Finset current.object.Vertex,
            current.object.InducesWindow data.windowOrder window →
            ∃ member ∈ packing, ¬ Disjoint window member) ∧
          ∃ component ∈ current.object.canonicalPieces
              (current.object.remainderSupport packing),
            let piece := current.object.pieceSupport
              (current.object.remainderSupport packing) component
            current.object.NegativeNetCharge piece data.threshold
                data.dischargeScale ∧
              current.object.ambientSurplus piece data.threshold = 0 ∧
              ∃ receiver : current.object.Vertex,
                current.object.IsReceiver piece data.threshold receiver ∧
                  ∃ peeled : Finset current.object.Vertex,
                    peeled ⊆ current.object.routedLoads piece data.threshold
                        receiver ∧
                      Graph.ExitFour.SaturatedAfter piece data.threshold
                        data.dischargeScale receiver peeled ∧
                      ((∃ package :
                          Graph.ExitFour.VisibleFourUnpeeledPackage piece
                            data.threshold data.dischargeScale receiver peeled,
                        ¬ ∃ witness : Graph.ExitFour.Witness
                            (Graph.HasCycleWithLength data.LengthOK) piece
                            data.threshold receiver peeled,
                          ∃ load ∈ Graph.ExitFour.selectedVisibleUnpeeledLoads
                              piece data.threshold data.dischargeScale receiver
                              package.outside peeled,
                            witness.load = load) ∨
                        (Graph.ExitFour.SilentUnpeeledExcessAt piece
                            data.threshold data.dischargeScale receiver peeled ∧
                          ¬ ∃ witness : Graph.ExitFour.Witness
                              (Graph.HasCycleWithLength data.LengthOK) piece
                              data.threshold receiver peeled,
                            witness.load ∈ Graph.ExitFour.unpeeledExcess piece
                              data.threshold data.dischargeScale receiver peeled)) ∧
                      ∃ support : Finset current.object.Vertex,
                        Graph.Strategy.InterfaceReplacement.CompressibleSupport
                          (Graph.MinimumDegreeAtLeast data.threshold)
                          (Graph.HasCycleWithLength data.LengthOK)
                          current.object support) →
      typeAExitFive.At current)
    (encodeFree :
      (∃ packing : Finset (Finset current.object.Vertex),
        current.object.IsWindowPacking data.windowOrder packing ∧
          (∀ window : Finset current.object.Vertex,
            current.object.InducesWindow data.windowOrder window →
            ∃ member ∈ packing, ¬ Disjoint window member) ∧
          ∃ component ∈ current.object.canonicalPieces
              (current.object.remainderSupport packing),
            let piece := current.object.pieceSupport
              (current.object.remainderSupport packing) component
            current.object.NegativeNetCharge piece data.threshold
                data.dischargeScale ∧
              current.object.ambientSurplus piece data.threshold = 0 ∧
              ∃ receiver : current.object.Vertex,
                current.object.IsReceiver piece data.threshold receiver ∧
                  ∃ peeled : Finset current.object.Vertex,
                    peeled ⊆ current.object.routedLoads piece data.threshold
                        receiver ∧
                      Graph.ExitFour.SaturatedAfter piece data.threshold
                        data.dischargeScale receiver peeled ∧
                      ((∃ package :
                          Graph.ExitFour.VisibleFourUnpeeledPackage piece
                            data.threshold data.dischargeScale receiver peeled,
                        ¬ ∃ witness : Graph.ExitFour.Witness
                            (Graph.HasCycleWithLength data.LengthOK) piece
                            data.threshold receiver peeled,
                          ∃ load ∈ Graph.ExitFour.selectedVisibleUnpeeledLoads
                              piece data.threshold data.dischargeScale receiver
                              package.outside peeled,
                            witness.load = load) ∨
                        (Graph.ExitFour.SilentUnpeeledExcessAt piece
                            data.threshold data.dischargeScale receiver peeled ∧
                          ¬ ∃ witness : Graph.ExitFour.Witness
                              (Graph.HasCycleWithLength data.LengthOK) piece
                              data.threshold receiver peeled,
                            witness.load ∈ Graph.ExitFour.unpeeledExcess piece
                              data.threshold data.dischargeScale receiver peeled)) ∧
                      ¬ ∃ support : Finset current.object.Vertex,
                        Graph.Strategy.InterfaceReplacement.CompressibleSupport
                          (Graph.MinimumDegreeAtLeast data.threshold)
                          (Graph.HasCycleWithLength data.LengthOK)
                          current.object support) →
      typeAExitFiveFree.At current)
    (exitFresh : typeAExitFive ∉ known)
    (freeFresh : typeAExitFiveFree ∉ known) :
    Decision typeAExitFive typeAExitFiveFree previous :=
  Decision.run previous typeAExitFive typeAExitFiveFree
    `Hypostructure.Graph.Strategy.Spine.typeAExitFiveDichotomy
    (by
      classical
      apply Classical.choice
      obtain ⟨packing, valid, maximal, component, present, negative, zero,
        receiver, isReceiver, peeled, peeledSubset, saturated, noExitFour⟩ :=
        freeOf (ExactLedger.get previous typeASaturatedHandoffExitFourFree)
      by_cases compression :
          ∃ support : Finset current.object.Vertex,
            Graph.Strategy.InterfaceReplacement.CompressibleSupport
              (Graph.MinimumDegreeAtLeast data.threshold)
              (Graph.HasCycleWithLength data.LengthOK) current.object support
      · exact ⟨.inl (encodeExit
          ⟨packing, valid, maximal, component, present, negative, zero,
            receiver, isReceiver, peeled, peeledSubset, saturated,
            noExitFour, compression⟩)⟩
      · exact ⟨.inr (encodeFree
          ⟨packing, valid, maximal, component, present, negative, zero,
            receiver, isReceiver, peeled, peeledSubset, saturated,
            noExitFour, compression⟩)⟩)
    exitFresh freeFresh

/-! ## Nodes `[105]`--`[106]`: exit `(6)`, delocalization

The predecessor is the exact selected no-exit-`(5)` fact.  Node `[105]` asks
whether that same saturated handoff state carries a delocalizing declared
response equality.  Node `[106]` then spends the graph-owned localization
theorem for that committed equality: a proper enlarging support gives the
proper-smearing replacement, and whole-graph support gives the closed
representative of no-silent-global-smearing. -/

noncomputable def typeAExitSixDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous :
      ExactLedger (Input BranchState Presentation presentation data)
        current known)
    (typeAExitFiveFree typeAExitSix typeAExitSixFree :
      FactKey (Input BranchState Presentation presentation data))
    [Core.Residual.FactKeys.Has typeAExitFiveFree known]
    (freeOf : typeAExitFiveFree.At current →
      ∃ packing : Finset (Finset current.object.Vertex),
        current.object.IsWindowPacking data.windowOrder packing ∧
          (∀ window : Finset current.object.Vertex,
            current.object.InducesWindow data.windowOrder window →
            ∃ member ∈ packing, ¬ Disjoint window member) ∧
          ∃ component ∈ current.object.canonicalPieces
              (current.object.remainderSupport packing),
            let piece := current.object.pieceSupport
              (current.object.remainderSupport packing) component
            current.object.NegativeNetCharge piece data.threshold
                data.dischargeScale ∧
              current.object.ambientSurplus piece data.threshold = 0 ∧
              ∃ receiver : current.object.Vertex,
                current.object.IsReceiver piece data.threshold receiver ∧
                  ∃ peeled : Finset current.object.Vertex,
                    peeled ⊆ current.object.routedLoads piece data.threshold
                        receiver ∧
                      Graph.ExitFour.SaturatedAfter piece data.threshold
                        data.dischargeScale receiver peeled ∧
                      ((∃ package :
                          Graph.ExitFour.VisibleFourUnpeeledPackage piece
                            data.threshold data.dischargeScale receiver peeled,
                        ¬ ∃ witness : Graph.ExitFour.Witness
                            (Graph.HasCycleWithLength data.LengthOK) piece
                            data.threshold receiver peeled,
                          ∃ load ∈ Graph.ExitFour.selectedVisibleUnpeeledLoads
                              piece data.threshold data.dischargeScale receiver
                              package.outside peeled,
                            witness.load = load) ∨
                        (Graph.ExitFour.SilentUnpeeledExcessAt piece
                            data.threshold data.dischargeScale receiver peeled ∧
                          ¬ ∃ witness : Graph.ExitFour.Witness
                              (Graph.HasCycleWithLength data.LengthOK) piece
                              data.threshold receiver peeled,
                            witness.load ∈ Graph.ExitFour.unpeeledExcess piece
                              data.threshold data.dischargeScale receiver peeled)) ∧
                      ¬ ∃ support : Finset current.object.Vertex,
                        Graph.Strategy.InterfaceReplacement.CompressibleSupport
                          (Graph.MinimumDegreeAtLeast data.threshold)
                          (Graph.HasCycleWithLength data.LengthOK)
                          current.object support)
    (encodeExit :
      (∃ packing : Finset (Finset current.object.Vertex),
        current.object.IsWindowPacking data.windowOrder packing ∧
          (∀ window : Finset current.object.Vertex,
            current.object.InducesWindow data.windowOrder window →
            ∃ member ∈ packing, ¬ Disjoint window member) ∧
          ∃ component ∈ current.object.canonicalPieces
              (current.object.remainderSupport packing),
            let piece := current.object.pieceSupport
              (current.object.remainderSupport packing) component
            current.object.NegativeNetCharge piece data.threshold
                data.dischargeScale ∧
              current.object.ambientSurplus piece data.threshold = 0 ∧
              ∃ receiver : current.object.Vertex,
                current.object.IsReceiver piece data.threshold receiver ∧
                  ∃ peeled : Finset current.object.Vertex,
                    peeled ⊆ current.object.routedLoads piece data.threshold
                        receiver ∧
                      Graph.ExitFour.SaturatedAfter piece data.threshold
                        data.dischargeScale receiver peeled ∧
                      ((∃ package :
                          Graph.ExitFour.VisibleFourUnpeeledPackage piece
                            data.threshold data.dischargeScale receiver peeled,
                        ¬ ∃ witness : Graph.ExitFour.Witness
                            (Graph.HasCycleWithLength data.LengthOK) piece
                            data.threshold receiver peeled,
                          ∃ load ∈ Graph.ExitFour.selectedVisibleUnpeeledLoads
                              piece data.threshold data.dischargeScale receiver
                              package.outside peeled,
                            witness.load = load) ∨
                        (Graph.ExitFour.SilentUnpeeledExcessAt piece
                            data.threshold data.dischargeScale receiver peeled ∧
                          ¬ ∃ witness : Graph.ExitFour.Witness
                              (Graph.HasCycleWithLength data.LengthOK) piece
                              data.threshold receiver peeled,
                            witness.load ∈ Graph.ExitFour.unpeeledExcess piece
                              data.threshold data.dischargeScale receiver peeled)) ∧
                      (¬ ∃ support : Finset current.object.Vertex,
                        Graph.Strategy.InterfaceReplacement.CompressibleSupport
                          (Graph.MinimumDegreeAtLeast data.threshold)
                          (Graph.HasCycleWithLength data.LengthOK)
                          current.object support) ∧
                      ExitSixDelocalizes data current.object piece) →
      typeAExitSix.At current)
    (encodeFree :
      (∃ packing : Finset (Finset current.object.Vertex),
        current.object.IsWindowPacking data.windowOrder packing ∧
          (∀ window : Finset current.object.Vertex,
            current.object.InducesWindow data.windowOrder window →
            ∃ member ∈ packing, ¬ Disjoint window member) ∧
          ∃ component ∈ current.object.canonicalPieces
              (current.object.remainderSupport packing),
            let piece := current.object.pieceSupport
              (current.object.remainderSupport packing) component
            current.object.NegativeNetCharge piece data.threshold
                data.dischargeScale ∧
              current.object.ambientSurplus piece data.threshold = 0 ∧
              ∃ receiver : current.object.Vertex,
                current.object.IsReceiver piece data.threshold receiver ∧
                  ∃ peeled : Finset current.object.Vertex,
                    peeled ⊆ current.object.routedLoads piece data.threshold
                        receiver ∧
                      Graph.ExitFour.SaturatedAfter piece data.threshold
                        data.dischargeScale receiver peeled ∧
                      ((∃ package :
                          Graph.ExitFour.VisibleFourUnpeeledPackage piece
                            data.threshold data.dischargeScale receiver peeled,
                        ¬ ∃ witness : Graph.ExitFour.Witness
                            (Graph.HasCycleWithLength data.LengthOK) piece
                            data.threshold receiver peeled,
                          ∃ load ∈ Graph.ExitFour.selectedVisibleUnpeeledLoads
                              piece data.threshold data.dischargeScale receiver
                              package.outside peeled,
                            witness.load = load) ∨
                        (Graph.ExitFour.SilentUnpeeledExcessAt piece
                            data.threshold data.dischargeScale receiver peeled ∧
                          ¬ ∃ witness : Graph.ExitFour.Witness
                              (Graph.HasCycleWithLength data.LengthOK) piece
                              data.threshold receiver peeled,
                            witness.load ∈ Graph.ExitFour.unpeeledExcess piece
                              data.threshold data.dischargeScale receiver peeled)) ∧
                      (¬ ∃ support : Finset current.object.Vertex,
                        Graph.Strategy.InterfaceReplacement.CompressibleSupport
                          (Graph.MinimumDegreeAtLeast data.threshold)
                          (Graph.HasCycleWithLength data.LengthOK)
                          current.object support) ∧
                      ¬ ExitSixDelocalizes data current.object piece) →
      typeAExitSixFree.At current)
    (exitFresh : typeAExitSix ∉ known)
    (freeFresh : typeAExitSixFree ∉ known) :
    Decision typeAExitSix typeAExitSixFree previous :=
  Decision.run previous typeAExitSix typeAExitSixFree
    `Hypostructure.Graph.Strategy.Spine.typeAExitSixDichotomy
    (by
      classical
      apply Classical.choice
      obtain ⟨packing, valid, maximal, component, present, negative, zero,
        receiver, isReceiver, peeled, peeledSubset, saturated,
        noExitFour, noCompression⟩ :=
        freeOf (ExactLedger.get previous typeAExitFiveFree)
      by_cases delocalizes :
          ExitSixDelocalizes data current.object
            (current.object.pieceSupport
              (current.object.remainderSupport packing) component)
      · exact ⟨.inl (encodeExit
          ⟨packing, valid, maximal, component, present, negative, zero,
            receiver, isReceiver, peeled, peeledSubset, saturated, noExitFour,
            noCompression, delocalizes⟩)⟩
      · exact ⟨.inr (encodeFree
          ⟨packing, valid, maximal, component, present, negative, zero,
            receiver, isReceiver, peeled, peeledSubset, saturated, noExitFour,
            noCompression, delocalizes⟩)⟩)
    exitFresh freeFresh

noncomputable def typeAExitSixScopeDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous :
      ExactLedger (Input BranchState Presentation presentation data)
        current known)
    (typeAExitSix typeAExitSixProper typeAExitSixGlobal :
      FactKey (Input BranchState Presentation presentation data))
    [Core.Residual.FactKeys.Has typeAExitSix known]
    (exitOf : typeAExitSix.At current →
      ∃ packing : Finset (Finset current.object.Vertex),
        current.object.IsWindowPacking data.windowOrder packing ∧
          (∀ window : Finset current.object.Vertex,
            current.object.InducesWindow data.windowOrder window →
            ∃ member ∈ packing, ¬ Disjoint window member) ∧
          ∃ component ∈ current.object.canonicalPieces
              (current.object.remainderSupport packing),
            let piece := current.object.pieceSupport
              (current.object.remainderSupport packing) component
            current.object.NegativeNetCharge piece data.threshold
                data.dischargeScale ∧
              current.object.ambientSurplus piece data.threshold = 0 ∧
              ∃ receiver : current.object.Vertex,
                current.object.IsReceiver piece data.threshold receiver ∧
                  ∃ peeled : Finset current.object.Vertex,
                    peeled ⊆ current.object.routedLoads piece data.threshold
                        receiver ∧
                      Graph.ExitFour.SaturatedAfter piece data.threshold
                        data.dischargeScale receiver peeled ∧
                      ((∃ package :
                          Graph.ExitFour.VisibleFourUnpeeledPackage piece
                            data.threshold data.dischargeScale receiver peeled,
                        ¬ ∃ witness : Graph.ExitFour.Witness
                            (Graph.HasCycleWithLength data.LengthOK) piece
                            data.threshold receiver peeled,
                          ∃ load ∈ Graph.ExitFour.selectedVisibleUnpeeledLoads
                              piece data.threshold data.dischargeScale receiver
                              package.outside peeled,
                            witness.load = load) ∨
                        (Graph.ExitFour.SilentUnpeeledExcessAt piece
                            data.threshold data.dischargeScale receiver peeled ∧
                          ¬ ∃ witness : Graph.ExitFour.Witness
                              (Graph.HasCycleWithLength data.LengthOK) piece
                              data.threshold receiver peeled,
                            witness.load ∈ Graph.ExitFour.unpeeledExcess piece
                              data.threshold data.dischargeScale receiver peeled)) ∧
                      (¬ ∃ support : Finset current.object.Vertex,
                        Graph.Strategy.InterfaceReplacement.CompressibleSupport
                          (Graph.MinimumDegreeAtLeast data.threshold)
                          (Graph.HasCycleWithLength data.LengthOK)
                          current.object support) ∧
                      ExitSixDelocalizes data current.object piece)
    (encodeProper :
      (∃ support : Finset current.object.Vertex,
        Graph.Strategy.InterfaceReplacement.ReplacementSupport
          (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) current.object support) →
      typeAExitSixProper.At current)
    (encodeGlobal :
      (∃ representative : Graph.FiniteObject.{u},
        representative.LexicographicallySmaller current.object ∧
          Graph.MinimumDegreeAtLeast data.threshold representative ∧
            (Graph.HasCycleWithLength data.LengthOK representative →
              Graph.HasCycleWithLength data.LengthOK current.object)) →
      typeAExitSixGlobal.At current)
    (properFresh : typeAExitSixProper ∉ known)
    (globalFresh : typeAExitSixGlobal ∉ known) :
    Decision typeAExitSixProper typeAExitSixGlobal previous :=
  Decision.run previous typeAExitSixProper typeAExitSixGlobal
    `Hypostructure.Graph.Strategy.Spine.typeAExitSixScopeDichotomy
    (by
      classical
      apply Classical.choice
      obtain ⟨_packing, _valid, _maximal, _component, _present, _negative,
        _zero, _receiver, _isReceiver, _peeled, _peeledSubset, _saturated,
        _noExitFour, _noCompression, presented, _supportEq, delocalizes⟩ :=
        exitOf (ExactLedger.get previous typeAExitSix)
      obtain ⟨delocalization⟩ := delocalizes
      rcases delocalization.localize with proper | global
      · exact ⟨.inl (encodeProper ⟨_, proper⟩)⟩
      · exact ⟨.inr (encodeGlobal global)⟩)
    properFresh globalFresh

/-! ## Nodes `[107]`--`[109]`: exit `(7)` and route-8 residual

The predecessor is the exact selected no-exit-`(6)` fact.  Node `[107]`
decides only whether that same selected saturated handoff state produces a
decorated handoff envelope.  Node `[108]` records the admissible Type B
interface for the produced envelope.  Node `[109]` commits the route-8 residual
fact from the selected no-handoff branch.
-/

noncomputable def typeAExitSevenDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous :
      ExactLedger (Input BranchState Presentation presentation data)
        current known)
    (typeAExitSixFree typeAExitSevenProduced typeAExitSevenFree :
      FactKey (Input BranchState Presentation presentation data))
    [Core.Residual.FactKeys.Has typeAExitSixFree known]
    (freeOf : typeAExitSixFree.At current →
      SelectedNoExitSixWith data current.object (fun _ _ => True))
    (encodeProduced :
      SelectedNoExitSixWith data current.object
        (fun packing piece =>
          HandoffProduced data current.object packing piece) →
        typeAExitSevenProduced.At current)
    (encodeFree :
      SelectedNoExitSixWith data current.object
        (fun packing piece =>
          ¬ HandoffProduced data current.object packing piece) →
        typeAExitSevenFree.At current)
    (producedFresh : typeAExitSevenProduced ∉ known)
    (freeFresh : typeAExitSevenFree ∉ known) :
    Decision typeAExitSevenProduced typeAExitSevenFree previous :=
  Decision.run previous typeAExitSevenProduced typeAExitSevenFree
    `Hypostructure.Graph.Strategy.Spine.typeAExitSevenDichotomy
    (by
      classical
      apply Classical.choice
      obtain ⟨packing, valid, maximal, component, present, negative, zero,
        receiver, isReceiver, peeled, peeledSubset, saturated, noExitFour,
        noCompression, noDelocalization, _⟩ :=
        freeOf (ExactLedger.get previous typeAExitSixFree)
      let piece := current.object.pieceSupport
        (current.object.remainderSupport packing) component
      by_cases produced :
          HandoffProduced data current.object packing piece
      · exact ⟨.inl (encodeProduced
          ⟨packing, valid, maximal, component, present, negative, zero,
            receiver, isReceiver, peeled, peeledSubset, saturated, noExitFour,
            noCompression, noDelocalization, produced⟩)⟩
      · exact ⟨.inr (encodeFree
          ⟨packing, valid, maximal, component, present, negative, zero,
            receiver, isReceiver, peeled, peeledSubset, saturated, noExitFour,
            noCompression, noDelocalization, produced⟩)⟩)
    producedFresh freeFresh

@[reducible] noncomputable def typeAExitSevenHandoffRow
    (selection uncompressible typeAExitSevenProduced typeAExitSevenHandoff :
      FactKey (Input BranchState Presentation presentation data))
    (distinctRequired :
      [selection, uncompressible, typeAExitSevenProduced].Nodup)
    (avoidsOf : (input : Input BranchState Presentation presentation data) →
      selection.At input →
        ¬ Graph.HasCycleWithLength data.LengthOK input.object)
    (uncompressibleOf :
      (input : Input BranchState Presentation presentation data) →
        uncompressible.At input →
          ∀ support : Finset input.object.Vertex,
            ¬ Graph.Strategy.InterfaceReplacement.CompressibleSupport
              (Graph.MinimumDegreeAtLeast data.threshold)
              (Graph.HasCycleWithLength data.LengthOK) input.object support)
    (producedOf :
      (input : Input BranchState Presentation presentation data) →
        typeAExitSevenProduced.At input →
          SelectedNoExitSixWith data input.object
            (fun packing piece =>
              HandoffProduced data input.object packing piece))
    (encode :
      (input : Input BranchState Presentation presentation data) →
        SelectedNoExitSixWith data input.object
          (fun packing piece =>
            HandoffAdmissible data input.object packing piece) →
        typeAExitSevenHandoff.At input) :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.typeAExitSevenHandoff
    { Requires := [selection, uncompressible, typeAExitSevenProduced]
      Produces := [typeAExitSevenHandoff]
      requiresUnique := distinctRequired
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let produced :=
        producedOf inputs.current (inputs.get typeAExitSevenProduced)
      .cons (key := typeAExitSevenHandoff)
        (encode inputs.current (by
          obtain ⟨packing, valid, maximal, component, present, negative, zero,
            receiver, isReceiver, peeled, peeledSubset, saturated, noExitFour,
            noCompression, noDelocalization, producedEnvelope⟩ := produced
          let piece := inputs.current.object.pieceSupport
            (inputs.current.object.remainderSupport packing) component
          obtain ⟨envelope, coreEq, decorated⟩ := producedEnvelope
          have inside : piece ⊆
              inputs.current.object.remainderSupport packing :=
            inputs.current.object.pieceSupport_subset
              (inputs.current.object.remainderSupport packing) component
          have windowFree :
              handoffWindowFree data inputs.current.object envelope.core := by
            intro window subset windowInduces
            exact
              (inputs.current.object.not_inducesWindow_of_subset_remainderSupport
                maximal (fun vertex member => inside (by
                  simpa [piece, coreEq] using subset member))) windowInduces
          have admissible :
              Graph.DecoratedHandoff.Admissible inputs.current.object
                data.LengthOK (handoffUncompressible data inputs.current.object)
                (handoffWindowFree data inputs.current.object) envelope :=
            Graph.DecoratedHandoff.admissible_of_envelope
              (avoidsOf inputs.current (inputs.get selection)) windowFree
              (uncompressibleOf inputs.current (inputs.get uncompressible))
          exact
            ⟨packing, valid, maximal, component, present, negative, zero,
              receiver, isReceiver, peeled, peeledSubset, saturated,
              noExitFour, noCompression, noDelocalization,
              ⟨envelope, coreEq, decorated, admissible⟩⟩))
        .nil)

@[reducible] noncomputable def route8ResidualRow
    (typeAExitFourFiniteDescent typeASaturatedHandoffSilent
      typeASaturatedHandoffExitFourFree typeAExitFiveFree typeAExitSixFree
      typeAExitSevenFree route8Residual :
      FactKey (Input BranchState Presentation presentation data))
    (distinctRequired :
      [typeAExitFourFiniteDescent, typeASaturatedHandoffSilent,
        typeASaturatedHandoffExitFourFree, typeAExitFiveFree, typeAExitSixFree,
        typeAExitSevenFree].Nodup)
    (freeOf :
      (input : Input BranchState Presentation presentation data) →
        typeAExitSevenFree.At input →
          SelectedNoExitSixWith data input.object
            (fun packing piece =>
              ¬ HandoffProduced data input.object packing piece))
    (encode :
      (input : Input BranchState Presentation presentation data) →
        SelectedNoExitSixWith data input.object
          (fun packing piece =>
            ¬ HandoffProduced data input.object packing piece) →
        route8Residual.At input) :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.route8Residual
    { Requires := [typeAExitFourFiniteDescent, typeASaturatedHandoffSilent,
        typeASaturatedHandoffExitFourFree, typeAExitFiveFree, typeAExitSixFree,
        typeAExitSevenFree]
      Produces := [route8Residual]
      requiresUnique := distinctRequired
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let _finiteDescent := inputs.get typeAExitFourFiniteDescent
      let _silent := inputs.get typeASaturatedHandoffSilent
      let _exitFourFree := inputs.get typeASaturatedHandoffExitFourFree
      let _exitFiveFree := inputs.get typeAExitFiveFree
      let _exitSixFree := inputs.get typeAExitSixFree
      let free := freeOf inputs.current (inputs.get typeAExitSevenFree)
      .cons (key := route8Residual) (encode inputs.current free) .nil)

omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def route8ResidualProfileRow
    : @AtomicStrategy (Input BranchState Presentation presentation data) _
        (instFactSystem (BranchState := BranchState)
          (Presentation := Presentation) (presentation := presentation)
          (data := data)) :=
  letI : FactSystem (Input BranchState Presentation presentation data) :=
    instFactSystem (BranchState := BranchState) (Presentation := Presentation)
      (presentation := presentation) (data := data)
  @factOnly (Input BranchState Presentation presentation data) _
    (instFactSystem (BranchState := BranchState)
      (Presentation := Presentation) (presentation := presentation)
      (data := data))
    `Hypostructure.Graph.Strategy.Spine.route8ResidualProfile
    { Requires := [K .route8Residual]
      Produces := [K .route8ResidualProfile]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let residual := inputs.get (K .route8Residual)
      .cons (key := K .route8ResidualProfile)
        ⟨silentCoreResidualProfile_of_route8Residual residual.down⟩ .nil)
    0 0

omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def route8GlobalSqueezeRow
    : @AtomicStrategy (Input BranchState Presentation presentation data) _
        (instFactSystem (BranchState := BranchState)
          (Presentation := Presentation) (presentation := presentation)
          (data := data)) :=
  letI : FactSystem (Input BranchState Presentation presentation data) :=
    instFactSystem (BranchState := BranchState) (Presentation := Presentation)
      (presentation := presentation) (data := data)
  @factOnly (Input BranchState Presentation presentation data) _
    (instFactSystem (BranchState := BranchState)
      (Presentation := Presentation) (presentation := presentation)
      (data := data))
    `Hypostructure.Graph.Strategy.Spine.route8GlobalSqueeze
    { Requires := [K .route8ResidualProfile, K .largeBudgetResidual]
      Produces := [K .route8GlobalSqueeze]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let profile := inputs.get (K .route8ResidualProfile)
      let largeBudget := inputs.get (K .largeBudgetResidual)
      .cons (key := K .route8GlobalSqueeze)
        ⟨⟨profile.down, largeBudget.down⟩⟩ .nil)
    0 0

omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def route8BurdenAndDeficitRow
    : @AtomicStrategy (Input BranchState Presentation presentation data) _
        (instFactSystem (BranchState := BranchState)
          (Presentation := Presentation) (presentation := presentation)
          (data := data)) :=
  letI : FactSystem (Input BranchState Presentation presentation data) :=
    instFactSystem (BranchState := BranchState) (Presentation := Presentation)
      (presentation := presentation) (data := data)
  @factOnly (Input BranchState Presentation presentation data) _
    (instFactSystem (BranchState := BranchState)
      (Presentation := Presentation) (presentation := presentation)
      (data := data))
    `Hypostructure.Graph.Strategy.Spine.route8BurdenAndDeficit
    { Requires := [K .route8GlobalSqueeze, K .typeAVisibleFirstExcess]
      Produces := [K .route8BasinBurden, K .route8LargeBudgetDeficit]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp [K_eq_iff]
      producesNonempty := by simp }
    (fun inputs =>
      let global := inputs.get (K .route8GlobalSqueeze)
      let excess := inputs.get (K .typeAVisibleFirstExcess)
      let burden : Route8BasinBurden data inputs.current.object :=
        ⟨global.down, excess.down⟩
      .cons (key := K .route8BasinBurden) ⟨burden⟩
        (.cons (key := K .route8LargeBudgetDeficit)
          ⟨⟨burden, global.down.2⟩⟩ .nil))
    0 0

omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def route8CarrierCoreRow
    : @AtomicStrategy (Input BranchState Presentation presentation data) _
        (instFactSystem (BranchState := BranchState)
          (Presentation := Presentation) (presentation := presentation)
          (data := data)) :=
  letI : FactSystem (Input BranchState Presentation presentation data) :=
    instFactSystem (BranchState := BranchState) (Presentation := Presentation)
      (presentation := presentation) (data := data)
  @factOnly (Input BranchState Presentation presentation data) _
    (instFactSystem (BranchState := BranchState)
      (Presentation := Presentation) (presentation := presentation)
      (data := data))
    `Hypostructure.Graph.Strategy.Spine.route8CarrierCore
    { Requires := [K .route8LargeBudgetDeficit]
      Produces := [K .route8CarrierCore]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let deficit := inputs.get (K .route8LargeBudgetDeficit)
      .cons (key := K .route8CarrierCore)
        ⟨⟨deficit.down, by
          letI : DecidableEq inputs.current.object.Vertex :=
            inputs.current.object.vertices.decEq
          intro presented
          exact (presented.toEntry
            (Graph.HasCycleWithLength data.LengthOK)).carrierCoreFacts⟩⟩ .nil)
    0 0

omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def route8SmallCoreCollapseRow
    : @AtomicStrategy (Input BranchState Presentation presentation data) _
        (instFactSystem (BranchState := BranchState)
          (Presentation := Presentation) (presentation := presentation)
          (data := data)) :=
  letI : FactSystem (Input BranchState Presentation presentation data) :=
    instFactSystem (BranchState := BranchState) (Presentation := Presentation)
      (presentation := presentation) (data := data)
  @factOnly (Input BranchState Presentation presentation data) _
    (instFactSystem (BranchState := BranchState)
      (Presentation := Presentation) (presentation := presentation)
      (data := data))
    `Hypostructure.Graph.Strategy.Spine.route8SmallCoreCollapse
    { Requires := [K .route8CarrierCore]
      Produces := [K .route8SmallCoreCollapse]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let core := inputs.get (K .route8CarrierCore)
      .cons (key := K .route8SmallCoreCollapse)
        ⟨⟨core.down, by
          letI : DecidableEq inputs.current.object.Vertex :=
            inputs.current.object.vertices.decEq
          intro presented
          exact (presented.toEntry
            (Graph.HasCycleWithLength data.LengthOK)).smallCoreCollapseFacts⟩⟩ .nil)
    0 0

omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def route8TwoCarrierReductionRow
    : @AtomicStrategy (Input BranchState Presentation presentation data) _
        (instFactSystem (BranchState := BranchState)
          (Presentation := Presentation) (presentation := presentation)
          (data := data)) :=
  letI : FactSystem (Input BranchState Presentation presentation data) :=
    instFactSystem (BranchState := BranchState) (Presentation := Presentation)
      (presentation := presentation) (data := data)
  @factOnly (Input BranchState Presentation presentation data) _
    (instFactSystem (BranchState := BranchState)
      (Presentation := Presentation) (presentation := presentation)
      (data := data))
    `Hypostructure.Graph.Strategy.Spine.route8TwoCarrierReduction
    { Requires := [K .route8SmallCoreCollapse]
      Produces := [K .route8TwoCarrierReduction]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let collapse := inputs.get (K .route8SmallCoreCollapse)
      .cons (key := K .route8TwoCarrierReduction)
        ⟨⟨collapse.down, by
          letI : DecidableEq inputs.current.object.Vertex :=
            inputs.current.object.vertices.decEq
          intro Index indexDec entries core supply core_subset threshold
            discharge ambient deficit rate
          letI : DecidableEq Index := indexDec
          exact Graph.Route8.exists_indexedTwoCarrierCore entries core supply
            core_subset deficit rate⟩⟩ .nil)
    0 0

omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def route8CarrierDeletionWitnessesRow
    : @AtomicStrategy (Input BranchState Presentation presentation data) _
        (instFactSystem (BranchState := BranchState)
          (Presentation := Presentation) (presentation := presentation)
          (data := data)) :=
  letI : FactSystem (Input BranchState Presentation presentation data) :=
    instFactSystem (BranchState := BranchState) (Presentation := Presentation)
      (presentation := presentation) (data := data)
  @factOnly (Input BranchState Presentation presentation data) _
    (instFactSystem (BranchState := BranchState)
      (Presentation := Presentation) (presentation := presentation)
      (data := data))
    `Hypostructure.Graph.Strategy.Spine.route8CarrierDeletionWitnesses
    { Requires := [K .route8TwoCarrierReduction]
      Produces := [K .route8CarrierDeletionWitnesses]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let reduction := inputs.get (K .route8TwoCarrierReduction)
      .cons (key := K .route8CarrierDeletionWitnesses)
        ⟨⟨reduction.down, by
          letI : DecidableEq inputs.current.object.Vertex :=
            inputs.current.object.vertices.decEq
          intro presented Index indexDec entries core threshold index two core_eq
          letI : DecidableEq Index := indexDec
          let entry := presented.toEntry (Graph.HasCycleWithLength data.LengthOK)
          exact Graph.Route8.twoCarrierDeletionWitnesses (Target :=
            Graph.HasCycleWithLength data.LengthOK) entry.carriers
            entry.coordinates entry.car entry.car_subset entry.state entries
            core two core_eq⟩⟩ .nil)
    0 0

omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def route8PrivateCarrierContradictionRow
    : @AtomicStrategy (Input BranchState Presentation presentation data) _
        (instFactSystem (BranchState := BranchState)
          (Presentation := Presentation) (presentation := presentation)
          (data := data)) :=
  letI : FactSystem (Input BranchState Presentation presentation data) :=
    instFactSystem (BranchState := BranchState) (Presentation := Presentation)
      (presentation := presentation) (data := data)
  @factOnly (Input BranchState Presentation presentation data) _
    (instFactSystem (BranchState := BranchState)
      (Presentation := Presentation) (presentation := presentation)
      (data := data))
    `Hypostructure.Graph.Strategy.Spine.route8PrivateCarrierContradiction
    { Requires := [K .route8CarrierDeletionWitnesses]
      Produces := [K .route8PrivateCarrierBudget,
        K .route8NoTwoCarrierContradiction]
      requiresUnique := by simp
      producesUnique := by simp [K_eq_iff]
      producesNonempty := by simp }
    (fun inputs =>
      let witnesses := inputs.get (K .route8CarrierDeletionWitnesses)
      let budget : Route8PrivateCarrierBudget data inputs.current.object :=
        ⟨witnesses.down, by
          letI : DecidableEq inputs.current.object.Vertex :=
            inputs.current.object.vertices.decEq
          intro Index indexDec entries core supply core_subset threshold noTwo
          letI : DecidableEq Index := indexDec
          exact Graph.Route8.privateCarrierBudget_of_noTwoCarrier entries core
            supply core_subset noTwo⟩
      .cons (key := K .route8PrivateCarrierBudget) ⟨budget⟩
        (.cons (key := K .route8NoTwoCarrierContradiction)
          ⟨⟨budget, by
            letI : DecidableEq inputs.current.object.Vertex :=
              inputs.current.object.vertices.decEq
            intro Index indexDec entries core supply core_subset threshold
              discharge ambient deficit rate noTwo
            letI : DecidableEq Index := indexDec
            exact Graph.Route8.noTwoCarrier_contradiction entries core supply
              core_subset deficit rate noTwo⟩⟩ .nil))
    0 0

omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def route8PressureDescentRow
    : @AtomicStrategy (Input BranchState Presentation presentation data) _
        (instFactSystem (BranchState := BranchState)
          (Presentation := Presentation) (presentation := presentation)
          (data := data)) :=
  letI : FactSystem (Input BranchState Presentation presentation data) :=
    instFactSystem (BranchState := BranchState) (Presentation := Presentation)
      (presentation := presentation) (data := data)
  @factOnly (Input BranchState Presentation presentation data) _
    (instFactSystem (BranchState := BranchState)
      (Presentation := Presentation) (presentation := presentation)
      (data := data))
    `Hypostructure.Graph.Strategy.Spine.route8PressureDescent
    { Requires := [K .typeAExitFourFiniteDescent,
        K .route8NoTwoCarrierContradiction]
      Produces := [K .route8PressureDescent]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let finiteDescent := inputs.get (K .typeAExitFourFiniteDescent)
      let noTwo := inputs.get (K .route8NoTwoCarrierContradiction)
      .cons (key := K .route8PressureDescent)
        ⟨⟨noTwo.down, finiteDescent.down⟩⟩ .nil)
    0 0

omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def route8TerminalNoGoRow
    : @AtomicStrategy (Input BranchState Presentation presentation data) _
        (instFactSystem (BranchState := BranchState)
          (Presentation := Presentation) (presentation := presentation)
          (data := data)) :=
  letI : FactSystem (Input BranchState Presentation presentation data) :=
    instFactSystem (BranchState := BranchState) (Presentation := Presentation)
      (presentation := presentation) (data := data)
  @factOnly (Input BranchState Presentation presentation data) _
    (instFactSystem (BranchState := BranchState)
      (Presentation := Presentation) (presentation := presentation)
      (data := data))
    `Hypostructure.Graph.Strategy.Spine.route8TerminalNoGo
    { Requires := [K .route8PressureDescent,
        K .route8CarrierDeletionWitnesses]
      Produces := [K .route8TerminalNoGo]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let pressure := inputs.get (K .route8PressureDescent)
      let witnesses := inputs.get (K .route8CarrierDeletionWitnesses)
      .cons (key := K .route8TerminalNoGo)
        ⟨⟨pressure.down, witnesses.down, by
          letI : DecidableEq inputs.current.object.Vertex :=
            inputs.current.object.vertices.decEq
          intro presented
          let entry := presented.toEntry (Graph.HasCycleWithLength data.LengthOK)
          letI : DecidableEq entry.Coordinate := entry.coordinateDecEq
          exact (Graph.Route8.terminalTwoCarrierNoGoFacts
            (Target := Graph.HasCycleWithLength data.LengthOK) entry.carriers
            entry.coordinates entry.car entry.car_subset entry.state :
              Graph.Route8.TerminalTwoCarrierNoGoFacts
                (Graph.HasCycleWithLength data.LengthOK) entry.carriers
                entry.coordinates entry.car entry.car_subset entry.state)⟩⟩ .nil)
    0 0

/-! ## Node `[95]`: exit `(1)`, the Mersenne anchored return

`def:typeA-saturated-exits` (1): *"an anchored return through a completion port
of `w` has length in `Mers`"*, where `w` is a saturated receiver in a Type A
support.  That clause is stated at the receiver and quantifies *anchored*
returns through *any* of its completion ports: unlike clause (2) it carries no
visibility condition and does not restrict to receiver-entry returns, and
neither restriction is written here.  Node `[93]`'s visible-entry hypothesis is
read off the ledger by exact key — it is what puts the branch on the exit list —
but it is not conjoined into the alternative, because conjoining it would
strengthen the yes arm and weaken the no arm this row hands to node `[97]`.

Both arms are the receiver's, not the object's: the alternative names the
receiver's own completion ports through `Graph.VisibleEntry.completionPorts` and
the return through `Graph.VisibleEntry.AnchoredReturn`, so nothing here is a
search for a cycle anywhere in the object.

The yes arm closes.  `lem:typeA-exits-discharged`: *"Exit (1) gives an
edge-rooted Mersenne return, hence a power-of-two cycle by
`lem:return-equivalence`."*  That cycle is denied by the return-avoidance
invariant nodes `[5]`--`[7]` committed, so the branch that commits this fact is
uninhabited; the closure itself is the framework's, read off the two facts by
`Incompatible`, and no row of this block performs it.

The no arm is the hypothesis exit `(2)` is asked under at node `[97]`: no
anchored return through any completion port of any saturated receiver has
accepted length.

This is a `Decision`: the arm not taken is absent from the taken branch's key
index, so nothing downstream of node `[97]` can read the Mersenne return and the
closed arm cannot read the exit-`(1)`-free hypothesis. -/
noncomputable def typeAExitOneDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous :
      ExactLedger (Input BranchState Presentation presentation data)
        current known)
    (typeAVisibleEntry typeAExitOneReturn typeAExitOneFree :
      FactKey (Input BranchState Presentation presentation data))
    [Core.Residual.FactKeys.Has typeAVisibleEntry known]
    (visibleOf : typeAVisibleEntry.At current →
      ∃ packing : Finset (Finset current.object.Vertex),
        current.object.IsWindowPacking data.windowOrder packing ∧
          (∀ window : Finset current.object.Vertex,
            current.object.InducesWindow data.windowOrder window →
            ∃ member ∈ packing, ¬ Disjoint window member) ∧
          ∃ component ∈ current.object.canonicalPieces
              (current.object.remainderSupport packing),
            let piece := current.object.pieceSupport
              (current.object.remainderSupport packing) component
            current.object.NegativeNetCharge piece data.threshold
                data.dischargeScale ∧
              current.object.ambientSurplus piece data.threshold = 0 ∧
              ∃ receiver : current.object.Vertex,
                current.object.IsReceiver piece data.threshold receiver ∧
                  current.object.Saturated piece data.threshold
                      data.dischargeScale receiver ∧
                  Nonempty
                    (Graph.ExitFour.VisibleFourUnpeeledPackage piece
                      data.threshold data.dischargeScale receiver ∅))
    (encodeReturn :
      (∃ packing : Finset (Finset current.object.Vertex),
        current.object.IsWindowPacking data.windowOrder packing ∧
          (∀ window : Finset current.object.Vertex,
            current.object.InducesWindow data.windowOrder window →
            ∃ member ∈ packing, ¬ Disjoint window member) ∧
          ∃ component ∈ current.object.canonicalPieces
              (current.object.remainderSupport packing),
            let piece := current.object.pieceSupport
              (current.object.remainderSupport packing) component
            current.object.NegativeNetCharge piece data.threshold
                data.dischargeScale ∧
              current.object.ambientSurplus piece data.threshold = 0 ∧
              ∃ receiver : current.object.Vertex,
                current.object.IsReceiver piece data.threshold receiver ∧
                  current.object.Saturated piece data.threshold
                      data.dischargeScale receiver ∧
                  ∃ package : Graph.ExitFour.VisibleFourUnpeeledPackage piece
                      data.threshold data.dischargeScale receiver ∅,
                    ∃ return' : Graph.VisibleEntry.AnchoredReturn current.object
                        receiver package.outside,
                      Graph.ShiftedCycleLength data.LengthOK
                        return'.path.length) →
      typeAExitOneReturn.At current)
    (encodeFree :
      (∃ packing : Finset (Finset current.object.Vertex),
        current.object.IsWindowPacking data.windowOrder packing ∧
          (∀ window : Finset current.object.Vertex,
            current.object.InducesWindow data.windowOrder window →
            ∃ member ∈ packing, ¬ Disjoint window member) ∧
          ∃ component ∈ current.object.canonicalPieces
              (current.object.remainderSupport packing),
            let piece := current.object.pieceSupport
              (current.object.remainderSupport packing) component
            current.object.NegativeNetCharge piece data.threshold
                data.dischargeScale ∧
              current.object.ambientSurplus piece data.threshold = 0 ∧
              ∃ receiver : current.object.Vertex,
                current.object.IsReceiver piece data.threshold receiver ∧
                  current.object.Saturated piece data.threshold
                      data.dischargeScale receiver ∧
                  ∃ package : Graph.ExitFour.VisibleFourUnpeeledPackage piece
                      data.threshold data.dischargeScale receiver ∅,
                    ∀ return' : Graph.VisibleEntry.AnchoredReturn current.object
                        receiver package.outside,
                      ¬ Graph.ShiftedCycleLength data.LengthOK
                        return'.path.length) →
      typeAExitOneFree.At current)
    (returnFresh : typeAExitOneReturn ∉ known)
    (freeFresh : typeAExitOneFree ∉ known) :
    Decision typeAExitOneReturn typeAExitOneFree previous :=
  Decision.run previous typeAExitOneReturn typeAExitOneFree
    `Hypostructure.Graph.Strategy.Spine.typeAExitOneDichotomy
    (by
      classical
      apply Classical.choice
      obtain ⟨packing, valid, maximal, component, present, negative, zero,
        receiver, isReceiver, saturated, packageExists⟩ :=
        visibleOf (ExactLedger.get previous typeAVisibleEntry)
      obtain ⟨package⟩ := packageExists
      by_cases realized :
          ∃ return' : Graph.VisibleEntry.AnchoredReturn current.object receiver
              package.outside,
            Graph.ShiftedCycleLength data.LengthOK return'.path.length
      · exact ⟨.inl (encodeReturn
          ⟨packing, valid, maximal, component, present, negative, zero,
            receiver, isReceiver, saturated, package, realized⟩)⟩
      · exact ⟨.inr (encodeFree
          ⟨packing, valid, maximal, component, present, negative, zero,
            receiver, isReceiver, saturated, package,
            fun return' accepted => realized ⟨return', accepted⟩⟩)⟩)
    returnFresh freeFresh

/-! ## Node `[97]`: exit `(2)`, the common-port theta

`def:typeA-saturated-exits` (2): *"two anchored receiver-entry returns through
one completion port are internally vertex-disjoint as anchored paths and their
lengths sum to a power of two"*.  As at node `[95]`, the port is the one node
`[93]` fixed, so the visible-count clause rides with the configuration on both
arms and the two returns are asked of that port.

Both returns are `def:typeA-visible-load`'s *receiver-entry* returns
`P = Γ ∘ Q`, not arbitrary paths of the object: the alternative names them
through `Graph.VisibleEntry.ReceiverEntryReturn` at the receiver's own
completion port, and `Graph.VisibleEntry.ExitTwoThrough` is that pair together
with the exit's two side conditions -- internal disjointness of the underlying
anchored paths, and acceptance of `|P₁| + |P₂|`.

The yes arm closes.  `lem:typeA-common-port-return-cycle`: two anchored returns
through one port share both endpoints, so internal disjointness makes their
union a simple cycle of length `|P₁| + |P₂|`, and the exit's own side condition
says that length is accepted.  `lem:typeA-exits-discharged` lists exit `(2)`
among the closed exits for exactly this reason.  That cycle is denied by the
return-avoidance invariant nodes `[5]`--`[7]` committed, so the branch that
commits this fact is uninhabited; the closure is the framework's, read off the
two facts by `Incompatible`, and no row of this block performs it.

The no arm is the hypothesis exit `(3)` is asked under at node `[99]`: no two
receiver-entry returns through one completion port are internally disjoint with accepted
total length.

This is a `Decision`: the arm not taken is absent from the taken branch's key
index, so nothing downstream of node `[99]` can read the theta pair and the
closed arm cannot read the exit-`(2)`-free hypothesis. -/
noncomputable def typeAExitTwoDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous :
      ExactLedger (Input BranchState Presentation presentation data)
        current known)
    (typeAVisibleEntry typeAExitTwoTheta typeAExitTwoFree :
      FactKey (Input BranchState Presentation presentation data))
    [Core.Residual.FactKeys.Has typeAVisibleEntry known]
    (visibleOf : typeAVisibleEntry.At current →
      ∃ packing : Finset (Finset current.object.Vertex),
        current.object.IsWindowPacking data.windowOrder packing ∧
          (∀ window : Finset current.object.Vertex,
            current.object.InducesWindow data.windowOrder window →
            ∃ member ∈ packing, ¬ Disjoint window member) ∧
          ∃ component ∈ current.object.canonicalPieces
              (current.object.remainderSupport packing),
            let piece := current.object.pieceSupport
              (current.object.remainderSupport packing) component
            current.object.NegativeNetCharge piece data.threshold
                data.dischargeScale ∧
              current.object.ambientSurplus piece data.threshold = 0 ∧
              ∃ receiver : current.object.Vertex,
                current.object.IsReceiver piece data.threshold receiver ∧
                  current.object.Saturated piece data.threshold
                      data.dischargeScale receiver ∧
                  Nonempty
                    (Graph.ExitFour.VisibleFourUnpeeledPackage piece
                      data.threshold data.dischargeScale receiver ∅))
    (encodeTheta :
      (∃ packing : Finset (Finset current.object.Vertex),
        current.object.IsWindowPacking data.windowOrder packing ∧
          (∀ window : Finset current.object.Vertex,
            current.object.InducesWindow data.windowOrder window →
            ∃ member ∈ packing, ¬ Disjoint window member) ∧
          ∃ component ∈ current.object.canonicalPieces
              (current.object.remainderSupport packing),
            let piece := current.object.pieceSupport
              (current.object.remainderSupport packing) component
            current.object.NegativeNetCharge piece data.threshold
                data.dischargeScale ∧
              current.object.ambientSurplus piece data.threshold = 0 ∧
              ∃ receiver : current.object.Vertex,
                current.object.IsReceiver piece data.threshold receiver ∧
                  current.object.Saturated piece data.threshold
                      data.dischargeScale receiver ∧
                  ∃ package : Graph.ExitFour.VisibleFourUnpeeledPackage piece
                      data.threshold data.dischargeScale receiver ∅,
                    Graph.VisibleEntry.ExitTwoThrough current.object piece
                      data.LengthOK receiver package.outside) →
      typeAExitTwoTheta.At current)
    (encodeFree :
      (∃ packing : Finset (Finset current.object.Vertex),
        current.object.IsWindowPacking data.windowOrder packing ∧
          (∀ window : Finset current.object.Vertex,
            current.object.InducesWindow data.windowOrder window →
            ∃ member ∈ packing, ¬ Disjoint window member) ∧
          ∃ component ∈ current.object.canonicalPieces
              (current.object.remainderSupport packing),
            let piece := current.object.pieceSupport
              (current.object.remainderSupport packing) component
            current.object.NegativeNetCharge piece data.threshold
                data.dischargeScale ∧
              current.object.ambientSurplus piece data.threshold = 0 ∧
              ∃ receiver : current.object.Vertex,
                current.object.IsReceiver piece data.threshold receiver ∧
                  current.object.Saturated piece data.threshold
                      data.dischargeScale receiver ∧
                  ∃ package : Graph.ExitFour.VisibleFourUnpeeledPackage piece
                      data.threshold data.dischargeScale receiver ∅,
                    ¬ Graph.VisibleEntry.ExitTwoThrough current.object piece
                      data.LengthOK receiver package.outside) →
      typeAExitTwoFree.At current)
    (thetaFresh : typeAExitTwoTheta ∉ known)
    (freeFresh : typeAExitTwoFree ∉ known) :
    Decision typeAExitTwoTheta typeAExitTwoFree previous :=
  Decision.run previous typeAExitTwoTheta typeAExitTwoFree
    `Hypostructure.Graph.Strategy.Spine.typeAExitTwoDichotomy
    (by
      classical
      apply Classical.choice
      obtain ⟨packing, valid, maximal, component, present, negative, zero,
        receiver, isReceiver, saturated, packageExists⟩ :=
        visibleOf (ExactLedger.get previous typeAVisibleEntry)
      obtain ⟨package⟩ := packageExists
      let piece := current.object.pieceSupport
        (current.object.remainderSupport packing) component
      by_cases realized : Graph.VisibleEntry.ExitTwoThrough current.object piece
          data.LengthOK receiver package.outside
      · exact ⟨.inl (encodeTheta
          ⟨packing, valid, maximal, component, present, negative, zero,
            receiver, isReceiver, saturated, package, realized⟩)⟩
      · exact ⟨.inr (encodeFree
          ⟨packing, valid, maximal, component, present, negative, zero,
            receiver, isReceiver, saturated, package, realized⟩)⟩)
    thetaFresh freeFresh

/-! ## Node `[99]`: exit `(3)`, the `P₁₃` label collision

`def:typeA-saturated-exits` (3): *"a shared `P₁₃` window violates the
corresponding legal-label relation `C_s`"*.  `lem:typeA-visible-entry` states
the test it is: *"if two traces pass through a common `P₁₃` window, their labels
are governed by the relations `C_s` of `lem:labels`; failure of the
corresponding `C_s` test is the stated label collision, which is exit (3)"*, and
`lem:typeA-exits-discharged` discharges it as *"precisely failure of the legal
`P₁₃` label relation from `lem:labels`; by definition of the relation, it
creates a target event"*.

As at nodes `[95]` and `[97]`, the configuration is node `[93]`'s, so the visible
port rides with it on both arms and the packing the windows come from is that
configuration's own.  The exit itself is the manuscript's *local label test*:
two outside vertices attach to one packed window, the simple path joining them
avoids that window, and the cycle their attachment coordinates close through the
window has accepted length.
`Graph.WindowLabelCollision.labelCollision_iff_not_safe` is the statement that
this last clause *is* `¬ C_s(S(x), S(y))` at the registered dyadic target, so
the alternative is `lem:labels`' own relation and not a surrogate for it.

The yes arm closes.  `Graph.WindowLabelCollision.hasCycleWithLength_of_labelCollision`
*builds* the cycle `x p_i P p_j y Q x`, whose length is the manuscript's
`s + 2 + |i − j|` and which the collision's own side condition declares
accepted; the selected object avoids every accepted length, so the branch that
commits this fact is uninhabited.  The closure is the framework's, read off the
selection and this fact by `Incompatible`, and no row of this block performs it.
The one thing the construction asks of the target is that the degenerate closure
be rejected -- one attachment counted twice with no connector -- and that is
`Data.degenerateClosureRejected`, the registered analogue of
`Data.quadrilateralAccepted`; nothing here writes `2`, `4`, `8`, or `{2, 6}`.

The no arm is the manuscript's *"assume exits (1)--(3) do not occur"* at its
third clause: every shared window of the packing satisfies its legal-label
relation at every outside connector.  It is the hypothesis the exit-`(4)` family
of `def:typeA-exit4-family` is built under at node `[101]`.

This is a `Decision`: the arm not taken is absent from the taken branch's key
index, so nothing downstream of node `[101]` can read the collision and the
closed arm cannot read the exit-`(3)`-free hypothesis. -/
noncomputable def typeAExitThreeDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous :
      ExactLedger (Input BranchState Presentation presentation data)
        current known)
    (typeAVisibleEntry typeAExitThreeCollision typeAExitThreeFree :
      FactKey (Input BranchState Presentation presentation data))
    [Core.Residual.FactKeys.Has typeAVisibleEntry known]
    (visibleOf : typeAVisibleEntry.At current →
      ∃ packing : Finset (Finset current.object.Vertex),
        current.object.IsWindowPacking data.windowOrder packing ∧
          (∀ window : Finset current.object.Vertex,
            current.object.InducesWindow data.windowOrder window →
            ∃ member ∈ packing, ¬ Disjoint window member) ∧
          ∃ component ∈ current.object.canonicalPieces
              (current.object.remainderSupport packing),
            let piece := current.object.pieceSupport
              (current.object.remainderSupport packing) component
            current.object.NegativeNetCharge piece data.threshold
                data.dischargeScale ∧
              current.object.ambientSurplus piece data.threshold = 0 ∧
              ∃ receiver : current.object.Vertex,
                current.object.IsReceiver piece data.threshold receiver ∧
                  current.object.Saturated piece data.threshold
                      data.dischargeScale receiver ∧
                  Nonempty
                    (Graph.ExitFour.VisibleFourUnpeeledPackage piece
                      data.threshold data.dischargeScale receiver ∅))
    (encodeCollision :
      (∃ packing : Finset (Finset current.object.Vertex),
        current.object.IsWindowPacking data.windowOrder packing ∧
          (∀ window : Finset current.object.Vertex,
            current.object.InducesWindow data.windowOrder window →
            ∃ member ∈ packing, ¬ Disjoint window member) ∧
          ∃ component ∈ current.object.canonicalPieces
              (current.object.remainderSupport packing),
            let piece := current.object.pieceSupport
              (current.object.remainderSupport packing) component
            current.object.NegativeNetCharge piece data.threshold
                data.dischargeScale ∧
              current.object.ambientSurplus piece data.threshold = 0 ∧
              ∃ receiver : current.object.Vertex,
                current.object.IsReceiver piece data.threshold receiver ∧
                  current.object.Saturated piece data.threshold
                      data.dischargeScale receiver ∧
                  ∃ package : Graph.ExitFour.VisibleFourUnpeeledPackage piece
                      data.threshold data.dischargeScale receiver ∅,
                    Graph.WindowLabelCollision.LabelCollision current.object
                      data.windowOrder data.LengthOK packing) →
      typeAExitThreeCollision.At current)
    (encodeFree :
      (∃ packing : Finset (Finset current.object.Vertex),
        current.object.IsWindowPacking data.windowOrder packing ∧
          (∀ window : Finset current.object.Vertex,
            current.object.InducesWindow data.windowOrder window →
            ∃ member ∈ packing, ¬ Disjoint window member) ∧
          ∃ component ∈ current.object.canonicalPieces
              (current.object.remainderSupport packing),
            let piece := current.object.pieceSupport
              (current.object.remainderSupport packing) component
            current.object.NegativeNetCharge piece data.threshold
                data.dischargeScale ∧
              current.object.ambientSurplus piece data.threshold = 0 ∧
              ∃ receiver : current.object.Vertex,
                current.object.IsReceiver piece data.threshold receiver ∧
                  current.object.Saturated piece data.threshold
                      data.dischargeScale receiver ∧
                  ∃ package : Graph.ExitFour.VisibleFourUnpeeledPackage piece
                      data.threshold data.dischargeScale receiver ∅,
                    Graph.WindowLabelCollision.LabelCollisionFree current.object
                      data.windowOrder data.LengthOK packing) →
      typeAExitThreeFree.At current)
    (collisionFresh : typeAExitThreeCollision ∉ known)
    (freeFresh : typeAExitThreeFree ∉ known) :
    Decision typeAExitThreeCollision typeAExitThreeFree previous :=
  Decision.run previous typeAExitThreeCollision typeAExitThreeFree
    `Hypostructure.Graph.Strategy.Spine.typeAExitThreeDichotomy
    (by
      classical
      apply Classical.choice
      obtain ⟨packing, valid, maximal, component, present, negative, zero,
        receiver, isReceiver, saturated, packageExists⟩ :=
        visibleOf (ExactLedger.get previous typeAVisibleEntry)
      obtain ⟨package⟩ := packageExists
      by_cases realized : Graph.WindowLabelCollision.LabelCollision
          current.object data.windowOrder data.LengthOK packing
      · exact ⟨.inl (encodeCollision
          ⟨packing, valid, maximal, component, present, negative, zero,
            receiver, isReceiver, saturated, package, realized⟩)⟩
      · exact ⟨.inr (encodeFree
          ⟨packing, valid, maximal, component, present, negative, zero,
            receiver, isReceiver, saturated, package, realized⟩)⟩)
    collisionFresh freeFresh

/-! ## Node `[101]`: exit `(4)`, target-defective peeling witness

This is the selected-residual branch of `def:typeA-exit4-peeling`: after exits
`(1)`, `(2)`, and `(3)` are absent, the question is whether the exact visible
package on the incoming ledger carries a generated target-defective quotient
supporting one unpeeled routed load.  The no arm is the negation for that same
package; it is not a global route-8 assertion. -/
noncomputable def typeAExitFourDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous :
      ExactLedger (Input BranchState Presentation presentation data)
        current known)
    (typeAExitThreeFree typeAExitFour typeAExitFourFree :
      FactKey (Input BranchState Presentation presentation data))
    [Core.Residual.FactKeys.Has typeAExitThreeFree known]
    (freeOf : typeAExitThreeFree.At current →
      ∃ packing : Finset (Finset current.object.Vertex),
        current.object.IsWindowPacking data.windowOrder packing ∧
          (∀ window : Finset current.object.Vertex,
            current.object.InducesWindow data.windowOrder window →
            ∃ member ∈ packing, ¬ Disjoint window member) ∧
          ∃ component ∈ current.object.canonicalPieces
              (current.object.remainderSupport packing),
            let piece := current.object.pieceSupport
              (current.object.remainderSupport packing) component
            current.object.NegativeNetCharge piece data.threshold
                data.dischargeScale ∧
              current.object.ambientSurplus piece data.threshold = 0 ∧
              ∃ receiver : current.object.Vertex,
                current.object.IsReceiver piece data.threshold receiver ∧
                  current.object.Saturated piece data.threshold
                    data.dischargeScale receiver ∧
                  ∃ package : Graph.ExitFour.VisibleFourUnpeeledPackage piece
                      data.threshold data.dischargeScale receiver ∅,
                    Graph.WindowLabelCollision.LabelCollisionFree current.object
                      data.windowOrder data.LengthOK packing)
    (encodeExit :
      (∃ packing : Finset (Finset current.object.Vertex),
        current.object.IsWindowPacking data.windowOrder packing ∧
          (∀ window : Finset current.object.Vertex,
            current.object.InducesWindow data.windowOrder window →
            ∃ member ∈ packing, ¬ Disjoint window member) ∧
          ∃ component ∈ current.object.canonicalPieces
              (current.object.remainderSupport packing),
            let piece := current.object.pieceSupport
              (current.object.remainderSupport packing) component
            current.object.NegativeNetCharge piece data.threshold
                data.dischargeScale ∧
              current.object.ambientSurplus piece data.threshold = 0 ∧
              ∃ receiver : current.object.Vertex,
                current.object.IsReceiver piece data.threshold receiver ∧
                  current.object.Saturated piece data.threshold
                    data.dischargeScale receiver ∧
                  ∃ package : Graph.ExitFour.VisibleFourUnpeeledPackage piece
                      data.threshold data.dischargeScale receiver ∅,
                    ∃ witness : Graph.ExitFour.Witness
                        (Graph.HasCycleWithLength data.LengthOK) piece
                        data.threshold receiver ∅,
                      ∃ load ∈ Graph.ExitFour.selectedVisibleUnpeeledLoads
                          piece data.threshold data.dischargeScale receiver
                          package.outside ∅,
                        witness.load = load) →
      typeAExitFour.At current)
    (encodeFree :
      (∃ packing : Finset (Finset current.object.Vertex),
        current.object.IsWindowPacking data.windowOrder packing ∧
          (∀ window : Finset current.object.Vertex,
            current.object.InducesWindow data.windowOrder window →
            ∃ member ∈ packing, ¬ Disjoint window member) ∧
          ∃ component ∈ current.object.canonicalPieces
              (current.object.remainderSupport packing),
            let piece := current.object.pieceSupport
              (current.object.remainderSupport packing) component
            current.object.NegativeNetCharge piece data.threshold
                data.dischargeScale ∧
              current.object.ambientSurplus piece data.threshold = 0 ∧
              ∃ receiver : current.object.Vertex,
                current.object.IsReceiver piece data.threshold receiver ∧
                  current.object.Saturated piece data.threshold
                    data.dischargeScale receiver ∧
                  ∃ package : Graph.ExitFour.VisibleFourUnpeeledPackage piece
                      data.threshold data.dischargeScale receiver ∅,
                    ¬ ∃ witness : Graph.ExitFour.Witness
                        (Graph.HasCycleWithLength data.LengthOK) piece
                        data.threshold receiver ∅,
                      ∃ load ∈ Graph.ExitFour.selectedVisibleUnpeeledLoads
                          piece data.threshold data.dischargeScale receiver
                          package.outside ∅,
                        witness.load = load) →
      typeAExitFourFree.At current)
    (exitFresh : typeAExitFour ∉ known)
    (freeFresh : typeAExitFourFree ∉ known) :
    Decision typeAExitFour typeAExitFourFree previous :=
  Decision.run previous typeAExitFour typeAExitFourFree
    `Hypostructure.Graph.Strategy.Spine.typeAExitFourDichotomy
    (by
      classical
      apply Classical.choice
      obtain ⟨packing, valid, maximal, component, present, negative, zero,
        receiver, isReceiver, saturated, package, _labelFree⟩ :=
        freeOf (ExactLedger.get previous typeAExitThreeFree)
      let piece := current.object.pieceSupport
        (current.object.remainderSupport packing) component
      by_cases occurs :
          ∃ witness : Graph.ExitFour.Witness
              (Graph.HasCycleWithLength data.LengthOK) piece data.threshold
              receiver ∅,
            ∃ load ∈ Graph.ExitFour.selectedVisibleUnpeeledLoads
                piece data.threshold data.dischargeScale receiver
                package.outside ∅,
              witness.load = load
      · exact ⟨.inl (encodeExit
          ⟨packing, valid, maximal, component, present, negative, zero,
            receiver, isReceiver, saturated, package, occurs⟩)⟩
      · exact ⟨.inr (encodeFree
          ⟨packing, valid, maximal, component, present, negative, zero,
            receiver, isReceiver, saturated, package, occurs⟩)⟩)
    exitFresh freeFresh

/-- **Node `[102]`, `lem:typeA-exit4-discharge`.**

This is the deterministic ledger update after node `[101]`'s yes arm.  It reads
the exact exit-`(4)` witness already committed, inserts that witness's unpeeled
routed load into `P₄(w)`, and publishes the two facts the next receiver test
will consume: the enlarged peeling set is still a routed-load peeling set and
the residual load has dropped by exactly one.

No receiver is reselected here and no global exit family is quantified. -/
@[reducible] noncomputable def typeAExitFourPeelingStepRow
    (typeAExitFour typeAExitFourPeeled :
      FactKey (Input BranchState Presentation presentation data))
    (distinct : typeAExitFour ≠ typeAExitFourPeeled)
    (exitOf : (input : Input BranchState Presentation presentation data) →
      typeAExitFour.At input →
      ∃ packing : Finset (Finset input.object.Vertex),
        input.object.IsWindowPacking data.windowOrder packing ∧
          (∀ window : Finset input.object.Vertex,
            input.object.InducesWindow data.windowOrder window →
            ∃ member ∈ packing, ¬ Disjoint window member) ∧
          ∃ component ∈ input.object.canonicalPieces
              (input.object.remainderSupport packing),
            let piece := input.object.pieceSupport
              (input.object.remainderSupport packing) component
            input.object.NegativeNetCharge piece data.threshold
                data.dischargeScale ∧
              input.object.ambientSurplus piece data.threshold = 0 ∧
              ∃ receiver : input.object.Vertex,
                input.object.IsReceiver piece data.threshold receiver ∧
                  input.object.Saturated piece data.threshold data.dischargeScale
                    receiver ∧
                  ∃ package : Graph.ExitFour.VisibleFourUnpeeledPackage piece
                      data.threshold data.dischargeScale receiver ∅,
                    ∃ witness : Graph.ExitFour.Witness
                        (Graph.HasCycleWithLength data.LengthOK) piece
                        data.threshold receiver ∅,
                      ∃ load ∈ Graph.ExitFour.selectedVisibleUnpeeledLoads
                          piece data.threshold data.dischargeScale receiver
                          package.outside ∅,
                        witness.load = load)
    (encode : (input : Input BranchState Presentation presentation data) →
      (∃ packing : Finset (Finset input.object.Vertex),
        input.object.IsWindowPacking data.windowOrder packing ∧
          (∀ window : Finset input.object.Vertex,
            input.object.InducesWindow data.windowOrder window →
            ∃ member ∈ packing, ¬ Disjoint window member) ∧
          ∃ component ∈ input.object.canonicalPieces
              (input.object.remainderSupport packing),
            let piece := input.object.pieceSupport
              (input.object.remainderSupport packing) component
            input.object.NegativeNetCharge piece data.threshold
                data.dischargeScale ∧
              input.object.ambientSurplus piece data.threshold = 0 ∧
              ∃ receiver : input.object.Vertex,
                input.object.IsReceiver piece data.threshold receiver ∧
                  input.object.Saturated piece data.threshold data.dischargeScale
                    receiver ∧
                  ∃ package : Graph.ExitFour.VisibleFourUnpeeledPackage piece
                      data.threshold data.dischargeScale receiver ∅,
                    ∃ witness : Graph.ExitFour.Witness
                        (Graph.HasCycleWithLength data.LengthOK) piece
                        data.threshold receiver ∅,
                      ∃ load ∈ Graph.ExitFour.selectedVisibleUnpeeledLoads
                          piece data.threshold data.dischargeScale receiver
                          package.outside ∅,
                        witness.load = load ∧
                          Graph.ExitFour.Witness.nextPeeled witness ⊆
                            input.object.routedLoads piece data.threshold
                              receiver ∧
                          Graph.ExitFour.residualLoad piece data.threshold
                              receiver
                              (Graph.ExitFour.Witness.nextPeeled witness) + 1 =
                            Graph.ExitFour.residualLoad piece data.threshold
                              receiver ∅) →
      typeAExitFourPeeled.At input) :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.typeAExitFourPeelingStep
    (rowManifest typeAExitFour typeAExitFourPeeled distinct)
    (fun inputs =>
      .cons (key := typeAExitFourPeeled)
        (encode inputs.current (by
          classical
          obtain ⟨packing, valid, maximal, component, present, negative, zero,
            receiver, isReceiver, saturated, package, witness, load, selected,
            witness_eq⟩ :=
            exitOf inputs.current (inputs.get typeAExitFour)
          let piece := inputs.current.object.pieceSupport
            (inputs.current.object.remainderSupport packing) component
          have routed : witness.load ∈
              inputs.current.object.routedLoads piece data.threshold receiver :=
            Graph.ExitFour.Witness.routed witness
          have unpeeled : witness.load ∈
              Graph.ExitFour.unpeeledLoads piece data.threshold receiver ∅ :=
            witness.unpeeled
          exact ⟨packing, valid, maximal, component, present, negative, zero,
            receiver, isReceiver, saturated, package, witness, load, selected,
            witness_eq,
            Graph.ExitFour.insert_subset_routedLoads piece data.threshold
              receiver (Finset.empty_subset _) routed,
            Graph.ExitFour.residualLoad_insert piece data.threshold receiver
              unpeeled⟩))
        .nil)

/-- **Node `[102]`/loop retest.**

After the exit-`(4)` peel has been committed, the same receiver is tested at the
new peeling set.  The yes arm is exactly the shared saturated exit entry again,
now with `P₄(w)` enlarged.  The no arm publishes the cleared nonnegative
receiver-charge inequality from `lem:typeA-exit4-peeling-charge`.
-/
noncomputable def typeAExitFourRetestDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous :
      ExactLedger (Input BranchState Presentation presentation data)
        current known)
    (typeAExitFourPeeled typeASaturatedExitEntry
      typeAExitFourReceiverDischarged :
      FactKey (Input BranchState Presentation presentation data))
    [Core.Residual.FactKeys.Has typeAExitFourPeeled known]
    (peeledOf : typeAExitFourPeeled.At current →
      ∃ packing : Finset (Finset current.object.Vertex),
        current.object.IsWindowPacking data.windowOrder packing ∧
          (∀ window : Finset current.object.Vertex,
            current.object.InducesWindow data.windowOrder window →
            ∃ member ∈ packing, ¬ Disjoint window member) ∧
          ∃ component ∈ current.object.canonicalPieces
              (current.object.remainderSupport packing),
            let piece := current.object.pieceSupport
              (current.object.remainderSupport packing) component
            current.object.NegativeNetCharge piece data.threshold
                data.dischargeScale ∧
              current.object.ambientSurplus piece data.threshold = 0 ∧
              ∃ receiver : current.object.Vertex,
                current.object.IsReceiver piece data.threshold receiver ∧
                  current.object.Saturated piece data.threshold
                    data.dischargeScale receiver ∧
                  ∃ package : Graph.ExitFour.VisibleFourUnpeeledPackage piece
                      data.threshold data.dischargeScale receiver ∅,
                    ∃ witness : Graph.ExitFour.Witness
                        (Graph.HasCycleWithLength data.LengthOK) piece
                        data.threshold receiver ∅,
                      ∃ load ∈ Graph.ExitFour.selectedVisibleUnpeeledLoads
                          piece data.threshold data.dischargeScale receiver
                          package.outside ∅,
                        witness.load = load ∧
                          Graph.ExitFour.Witness.nextPeeled witness ⊆
                            current.object.routedLoads piece data.threshold
                              receiver ∧
                          Graph.ExitFour.residualLoad piece data.threshold
                              receiver
                              (Graph.ExitFour.Witness.nextPeeled witness) + 1 =
                            Graph.ExitFour.residualLoad piece data.threshold
                              receiver ∅)
    (encodeSaturated :
      (∃ packing : Finset (Finset current.object.Vertex),
        current.object.IsWindowPacking data.windowOrder packing ∧
          (∀ window : Finset current.object.Vertex,
            current.object.InducesWindow data.windowOrder window →
            ∃ member ∈ packing, ¬ Disjoint window member) ∧
          ∃ component ∈ current.object.canonicalPieces
              (current.object.remainderSupport packing),
            let piece := current.object.pieceSupport
              (current.object.remainderSupport packing) component
            current.object.NegativeNetCharge piece data.threshold
                data.dischargeScale ∧
              current.object.ambientSurplus piece data.threshold = 0 ∧
              ∃ receiver : current.object.Vertex,
                current.object.IsReceiver piece data.threshold receiver ∧
                  ∃ peeled : Finset current.object.Vertex,
                    peeled ⊆ current.object.routedLoads piece data.threshold
                        receiver ∧
                      Graph.ExitFour.SaturatedAfter piece data.threshold
                        data.dischargeScale receiver peeled) →
      typeASaturatedExitEntry.At current)
    (encodeDischarged :
      (∃ packing : Finset (Finset current.object.Vertex),
        current.object.IsWindowPacking data.windowOrder packing ∧
          (∀ window : Finset current.object.Vertex,
            current.object.InducesWindow data.windowOrder window →
            ∃ member ∈ packing, ¬ Disjoint window member) ∧
          ∃ component ∈ current.object.canonicalPieces
              (current.object.remainderSupport packing),
            let piece := current.object.pieceSupport
              (current.object.remainderSupport packing) component
            current.object.NegativeNetCharge piece data.threshold
                data.dischargeScale ∧
              current.object.ambientSurplus piece data.threshold = 0 ∧
              ∃ receiver : current.object.Vertex,
                current.object.IsReceiver piece data.threshold receiver ∧
                  current.object.Saturated piece data.threshold
                    data.dischargeScale receiver ∧
                  ∃ package : Graph.ExitFour.VisibleFourUnpeeledPackage piece
                      data.threshold data.dischargeScale receiver ∅,
                    ∃ witness : Graph.ExitFour.Witness
                        (Graph.HasCycleWithLength data.LengthOK) piece
                        data.threshold receiver ∅,
                      ∃ load ∈ Graph.ExitFour.selectedVisibleUnpeeledLoads
                          piece data.threshold data.dischargeScale receiver
                          package.outside ∅,
                        witness.load = load ∧
                          Graph.ExitFour.Witness.nextPeeled witness ⊆
                            current.object.routedLoads piece data.threshold
                              receiver ∧
                          Graph.ExitFour.residualLoad piece data.threshold
                              receiver
                              (Graph.ExitFour.Witness.nextPeeled witness) + 1 =
                            Graph.ExitFour.residualLoad piece data.threshold
                              receiver ∅ ∧
                          ¬ Graph.ExitFour.SaturatedAfter piece data.threshold
                              data.dischargeScale receiver
                              (Graph.ExitFour.Witness.nextPeeled witness) ∧
                          1 + Graph.ExitFour.residualLoad piece data.threshold
                              receiver
                              (Graph.ExitFour.Witness.nextPeeled witness) ≤
                            data.dischargeScale *
                              current.object.missingPorts piece data.threshold
                                receiver) →
      typeAExitFourReceiverDischarged.At current)
    (saturatedFresh : typeASaturatedExitEntry ∉ known)
    (dischargedFresh : typeAExitFourReceiverDischarged ∉ known) :
    Decision typeASaturatedExitEntry typeAExitFourReceiverDischarged
      previous :=
  Decision.run previous typeASaturatedExitEntry
    typeAExitFourReceiverDischarged
    `Hypostructure.Graph.Strategy.Spine.typeAExitFourRetestDichotomy
    (by
      classical
      apply Classical.choice
      obtain ⟨packing, valid, maximal, component, present, negative, zero,
        receiver, isReceiver, saturated, package, witness, load, selected,
        witness_eq, nextSubset, drop⟩ :=
        peeledOf (ExactLedger.get previous typeAExitFourPeeled)
      let piece := current.object.pieceSupport
        (current.object.remainderSupport packing) component
      by_cases stillSaturated :
          Graph.ExitFour.SaturatedAfter piece data.threshold data.dischargeScale
            receiver (Graph.ExitFour.Witness.nextPeeled witness)
      · exact ⟨.inl (encodeSaturated
          ⟨packing, valid, maximal, component, present, negative, zero,
            receiver, isReceiver, Graph.ExitFour.Witness.nextPeeled witness,
            nextSubset, stillSaturated⟩)⟩
      · have nonnegative :=
          (Graph.ExitFour.not_saturatedAfter_iff piece data.threshold
            data.dischargeScale receiver
            (Graph.ExitFour.Witness.nextPeeled witness)).mp stillSaturated
        exact ⟨.inr (encodeDischarged
          ⟨packing, valid, maximal, component, present, negative, zero,
            receiver, isReceiver, saturated, package, witness, load, selected,
            witness_eq, nextSubset, drop, stillSaturated, nonnegative⟩)⟩)
    saturatedFresh dischargedFresh


end Hypostructure.Graph.Strategy.Spine
