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
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def returnAvoidanceRow :
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
    `Hypostructure.Graph.Strategy.Spine.returnAvoidance
    { Requires := [K .selection]
      Produces := [K .returnAvoidance]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .returnAvoidance)
        (show Value BranchState Presentation presentation data
            .returnAvoidance inputs.current from
          ⟨
          ((Graph.not_hasCycleWithLength_iff_returnLengthSets_disjoint data.LengthOK
              inputs.current.object).mp
            (inputs.get (K .selection)).down.1)⟩)
        .nil)
    0 0

/-! ## Node `[8]`: no proper subgraph satisfies the baseline

`lem:no-proper-core`.  A proper subgraph is strictly smaller in the registered
order, so minimality forces it to have an accepted cycle; but every cycle of a
proper subgraph is a cycle of the ambient graph
(`Graph.cycleProperSubgraphTargetMonotone`), which the selected object does not
have.  So no proper subgraph satisfies the baseline. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def noProperBaselineRow :
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
    `Hypostructure.Graph.Strategy.Spine.noProperBaseline
    { Requires := [K .selection]
      Produces := [K .noProperBaseline]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let fact := inputs.get (K .selection)
      .cons (key := K .noProperBaseline)
        (show Value BranchState Presentation presentation data
            .noProperBaseline inputs.current from
          ⟨fun subgraph baseline =>
          fact.down.1
            ((Graph.cycleProperSubgraphTargetMonotone data.LengthOK).map subgraph
              (fact.down.2 subgraph.value subgraph.decreases baseline))⟩)
        .nil)
    0 0

/-! ## Nodes `[9]`--`[10]`: deletion criticality

`lem:deletion-critical`.  If some oriented edge had *both* endpoints strictly
above the threshold, deleting it would preserve the baseline
(`Graph.DeletionCriticalityProfile.baseline_of_not_critical`, the profile's own
one-edge accounting) while producing a proper subgraph — which node `[8]` has
just excluded.  So every edge has an endpoint exactly at the threshold, and
"equivalently", as the manuscript puts it, the vertices strictly above the
threshold are pairwise nonadjacent.

Both clauses are derived here, and the second is derived from the first exactly
as the manuscript derives it.  Both are appended to the same ExactLedger. -/

omit [FactSystem (Input BranchState Presentation presentation data)] in
/-- **Nodes `[9]`--`[10]`.** -/
@[reducible] noncomputable def deletionCriticalityRow :
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
    `Hypostructure.Graph.Strategy.Spine.deletionCriticality
    { Requires := [K .noProperBaseline]
      Produces := [K .tightEndpoint, K .slackIndependent]
      requiresUnique := by simp
      producesUnique := by simp [K_eq_iff]
      producesNonempty := by simp }
    (fun inputs =>
      let object := inputs.current.object
      let profile := Graph.minimumDegreeDeletionCriticalityProfile data.threshold
      let noProper := (inputs.get (K .noProperBaseline)).down
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
      .cons (key := K .tightEndpoint)
        (show Value BranchState Presentation presentation data
            .tightEndpoint inputs.current from ⟨tight⟩)
        (.cons (key := K .slackIndependent)
          -- Node `[10]`: two adjacent slack carriers would contradict `[9]`.
          (show Value BranchState Presentation presentation data
              .slackIndependent inputs.current from
            ⟨fun left right leftSlack rightSlack adjacent =>
            match tight ⟨(left, right), adjacent⟩ with
            | .inl atThreshold => Nat.ne_of_lt' leftSlack atThreshold
            | .inr atThreshold => Nat.ne_of_lt' rightSlack atThreshold⟩)
          .nil))
    0 0

/-! ## Node `[11]`: boundary-degree fibres

`lem:degree-profile-fibres`.  Condition (a) of
`def:target-complete-quotient` says that every target-complete identification
of two boundaried pieces has the same boundary-degree profile.  Equivalently,
two states in different fibres cannot be quotient-merged.  The statement is
about every target-complete identification, not only the narrower admissible
rank quotients represented by `Graph.DeclaredQuotient`.

The manuscript proof only unfolds that condition.  Accordingly this row has
no predecessor requirement, but its produced proposition is indexed by
`inputs.current.object`; the field projection is performed inside the sealed
executor and the residual instance is appended to the literal ledger. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def degreeProfileFibresRow :
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
    `Hypostructure.Graph.Strategy.Spine.degreeProfileFibres
    (sourceFreeManifest (K .degreeProfileFibres))
    (fun inputs =>
      .cons (key := K .degreeProfileFibres)
        (show Value BranchState Presentation presentation data
            .degreeProfileFibres inputs.current from
          ⟨fun _support _left _right complete => complete.profile_eq⟩)
        .nil)
    0 0

/-! ## Node `[12]`: context-universality

`lem:context-universality`.  Condition (b) of
`def:target-complete-quotient` says that every target-complete identification
has the same target response in every outside context.  Like node `[11]`, this
is a field projection from the paper's target-completeness hypothesis.  The
row is source-free, publishes exactly that semantic fact, and appends it to the
literal ledger. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def targetCompleteContextUniversalityRow :
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
    `Hypostructure.Graph.Strategy.Spine.targetCompleteContextUniversality
    (sourceFreeManifest (K .targetCompleteContextUniversality))
    (fun inputs =>
      .cons (key := K .targetCompleteContextUniversality)
        (show Value BranchState Presentation presentation data
            .targetCompleteContextUniversality inputs.current from
          ⟨fun _support _left _right complete => complete.contextEquivalent⟩)
        .nil)
    0 0

/-! ## `lem:bridgeless`: the selected object has no bridge

*"The graph `G` has no bridge.  Consequently every edge of `G` lies on a
cycle; equivalently, `R_e(G) ≠ ∅` for every oriented edge."*  The manuscript's
proof contracts a bridge into a smaller counterexample; that is the framework's
`Graph.EdgeContraction.hasReturn_of_minimal`, whose two hypotheses are the two
halves of the selection fact and whose degree side condition is the standing
baseline.  The row reads `K .selection` and derives nothing else. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def bridgelessRow :
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
    `Hypostructure.Graph.Strategy.Spine.bridgeless
    { Requires := [K .selection]
      Produces := [K .bridgeless]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let selection := (inputs.get (K .selection)).down
      .cons (key := K .bridgeless)
        (show Value BranchState Presentation presentation data
            .bridgeless inputs.current from
          ⟨fun contraction => by
            have baseline := inputs.current.baseline
            have degreeSum : data.threshold + 2 ≤
                inputs.current.object.degree contraction.tail +
                  inputs.current.object.degree contraction.head := by
              have three := data.three_le_threshold
              have left := le_trans baseline
                (inputs.current.object.minDegree_le_degree contraction.tail)
              have right := le_trans baseline
                (inputs.current.object.minDegree_le_degree contraction.head)
              omega
            exact contraction.hasReturn_of_minimal (LengthOK := data.LengthOK)
              degreeSum baseline selection.1 selection.2⟩)
        .nil)
    0 0

/-! ## Nodes `[13]`--`[14]`: interface replacement

`lem:replacement` and `cor:uncompressible`.  A target-complete compression of a
proper atom would produce a strictly smaller baseline object whose obstruction
profile is contained in the original's; minimality gives that object the target,
context-universality carries the target back through the shared outside
context, and the reconstruction is isomorphic to the selected object, which
avoids the target.

Node `[13]` records the one-way replacement exclusion itself.  Its proof is
performed at the literal residual: the four represented replacement hypotheses
construct the replacement, and the selection fact supplies precisely
minimality and target avoidance.

The node `[13]` executor spells out its argument locally and reads nothing but
the selected context's `avoids` and `target_of_smaller`.  It therefore consumes
the selection fact and nothing else; no closure record, registration, or
payload stands between the fact and its consequence. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def replacementExclusionRow :
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
    `Hypostructure.Graph.Strategy.Spine.replacementExclusion
    { Requires := [K .selection]
      Produces := [K .replacementExclusion]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let fact := inputs.get (K .selection)
      let context :
          Core.MinimalCounterexampleContext
            (problem BranchState Presentation presentation data)
            (Graph.HasCycleWithLength data.LengthOK)
            (progress BranchState Presentation presentation data) :=
        { G := inputs.current.object
          baseline := inputs.current.baseline
          state := inputs.current.branchState
          avoids := fact.down.1
          minimal := fact.down.2 }
      let targetInvariant : Core.TargetInvariant
          (Graph.isomorphismEquivalenceWithPresentation
            (Graph.MinimumDegreeAtLeast data.threshold) BranchState
            Presentation presentation
            (Graph.minimumDegreeAtLeast_isomorphismInvariant data.threshold))
          (Graph.HasCycleWithLength data.LengthOK) := by
        simpa [Graph.minimumDegreeIsomorphismSemantics] using
          (Graph.minimumDegreeCycleTargetInvariant data.threshold BranchState
            Presentation presentation data.LengthOK)
      let profile :=
        Graph.Strategy.InterfaceReplacement.profileWithPresentation
          (Baseline := Graph.MinimumDegreeAtLeast data.threshold)
          (BranchState := BranchState)
          (baselineInvariant :=
            Graph.minimumDegreeAtLeast_isomorphismInvariant data.threshold)
          Presentation presentation
          (T := Core.Target.ofPredicate _
            (Graph.HasCycleWithLength data.LengthOK)) targetInvariant
      .cons (key := K .replacementExclusion)
        (show Value BranchState Presentation presentation data
            .replacementExclusion inputs.current from
          ⟨fun support replacementSupport => by
            rcases replacementSupport with
              ⟨connected, proper, replacement, signatureEq, baseline, smaller,
                obstructionLE⟩
            let site :=
              Graph.Strategy.InterfaceReplacement.SupportAtom.properAtom
                context.G support connected proper
            let replacement' : profile.assembly.Replacement context.G site :=
              { atom := replacement
                compatible := trivial }
            let strictReplacement : profile.StrictReplacement context site :=
              { replacement := replacement'
                signature_eq := congrArg ULift.up signatureEq
                obstruction_le := by
                  intro outside _ _ replacementTarget
                  exact obstructionLE outside replacementTarget
                baseline := baseline
                smaller := smaller }
            have replacementTarget : Graph.HasCycleWithLength data.LengthOK
                (profile.assembly.replace strictReplacement.replacement) :=
              context.target_of_smaller strictReplacement.smaller
                strictReplacement.baseline
            have sourceTarget : Graph.HasCycleWithLength data.LengthOK
                (profile.assembly.assemble
                  (profile.assembly.atom context.G site)
                  (profile.assembly.context context.G site)) :=
              strictReplacement.obstruction_le
                (profile.assembly.context context.G site)
                (profile.assembly.extractedCompatible context.G site)
                strictReplacement.replacement.compatible replacementTarget
            exact context.avoids
              ((profile.targetInvariant.target_iff
                (profile.assembly.reconstruct context.G site)).mp sourceTarget)⟩)
        .nil)
    0 0

omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def interfaceReplacementRow :
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
    `Hypostructure.Graph.Strategy.Spine.interfaceReplacement
    { Requires := [K .replacementExclusion]
      Produces := [K .uncompressible]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let replacementExcluded :=
        (inputs.get (K .replacementExclusion)).down
      .cons (key := K .uncompressible)
        (show Value BranchState Presentation presentation data
            .uncompressible inputs.current from
          ⟨fun support compressible => by
              rcases compressible with
                ⟨connected, proper, replacement, signatureEq, baseline, smaller,
                  contextUniversal⟩
              exact replacementExcluded support
                ⟨connected, proper, replacement, signatureEq, baseline, smaller,
                  fun outside replacementTarget =>
                    (contextUniversal outside).mp replacementTarget⟩⟩)
        .nil)
    0 0

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
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def obstructionPackingRow :
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
    `Hypostructure.Graph.Strategy.Spine.obstructionPacking
    { Requires := [K .selection]
      Produces := [K .maximalPacking]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let object := inputs.current.object
      let avoids := (inputs.get (K .selection)).down.1
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
      .cons (key := K .maximalPacking)
        (show Value BranchState Presentation presentation data
            .maximalPacking inputs.current from
          ⟨by
          obtain ⟨support, window⟩ := carried
          obtain ⟨packing, valid, attains⟩ := attaining
          exact ⟨object.windowPackingNumber_pos data.windowOrder_pos window,
            packing, valid, attains,
            fun other otherWindow =>
              object.exists_mem_not_disjoint_of_card_eq data.windowOrder_pos
                valid attains otherWindow⟩⟩)
        .nil)
    0 0

/-! ## Node `[18]`: the exact finite local algebra

For every induced window of the literal active object, the row publishes
exactly the two assertions of `lem:labels`: the cardinality of the legal-label
set and its displayed size distribution.  The manuscript's `C_s` and `Ω₂` are
already the definitions `WindowCurvature.Safe` and
`WindowCurvature.curvatureTwo`; they are deliberately not republished as
stronger reflection theorems over raw (possibly illegal) labels.

No predecessor fact is needed: the direct enumeration depends only on the
registered window order, while the produced proposition is indexed by the
active object's actual induced-window supports.
-/
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def localAlgebraRow :
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
    `Hypostructure.Graph.Strategy.Spine.localAlgebra
    { Requires := []
      Produces := [K .localAlgebra]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let object := inputs.current.object
      .cons (key := K .localAlgebra)
        (show Value BranchState Presentation presentation data
            .localAlgebra inputs.current from
          ⟨fun (_support : Finset object.Vertex) _window =>
            ⟨data.labelCount, data.labelSizeDistribution⟩⟩)
        .nil)
    0 0

/-! ## Node `[21]`: the finite barrier enumeration

`lem:curv-enum` is already computed by the registered certified presentation.
This row reads no predecessor fact (`Requires := []`, exactly as `lem:labels`
at node `[18]`) and publishes the safe, curvature-positive, and flat counts
and their exact logarithmic entropy ratio on the literal incoming ledger.  It
performs no second enumeration, copies no numerical answer, and constructs no
label carrier.  `lem:curv-enum` is projected directly from the registered
presentation.
-/
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def barrierEnumerationRow :
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
    `Hypostructure.Graph.Strategy.Spine.barrierEnumeration
    { Requires := []
      Produces := [K .barrierEnumeration]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .barrierEnumeration)
        (show Value BranchState Presentation presentation data
            .barrierEnumeration inputs.current from
          ⟨by
            change BarrierEnumerationStatement data
            let barrier := data.windowBarrier
            letI := barrier.indexFintype
            let row := data.curvatureBarrierRow
            let left := barrier.table.counts.leftLength row
            let right := barrier.table.counts.rightLength row
            let safe := barrier.table.counts.storedSafe row
            let flat := barrier.table.counts.storedFlat row
            let curvaturePositive := safe - flat
            refine ⟨safe, curvaturePositive, flat, rfl, rfl, rfl,
              barrier.table.storedSafe_eq row, ?_,
              barrier.table.storedFlat_eq row, rfl⟩
            change barrier.table.counts.storedSafe row -
                barrier.table.counts.storedFlat row =
              barrier.profile.obstructedCount left right
            rw [barrier.table.storedSafe_eq, barrier.table.storedFlat_eq]
            rfl⟩)
        .nil)
    0 0

/-! ## Node `[21]`: the separated window package

`lem:p13-window-package`.  For every selected dyadic scale, the complete
certified table contributes the ratio between the products of its safe and
flat columns.  The package compounds that exact ratio across all scales and
only then takes the integer logarithm.  This is the manuscript's
`(c₁₃ - o(1)) p₁₃ log₂ n` exponent; taking the integer floor before
scale aggregation would incorrectly replace `c₁₃` by `118`.

The scale factor is not decorative: without it the demand grows a whole
`log₂ n` slower than the manuscript's, and the cap node `[22]`--`[24]` derives
from it degrades to `θ ≲ 1.5·log₂ n / rate`, which bounds nothing as `n` grows.

The cap arm carries `lem:variable-edge-budget` with it: the budget the arm
retained is stable when the edge count is only known to lie in an admissible
family, because the exact stratum is one of the family's and the family's own
union bound dominates it (`sum_edgeStratumCount_le_variableEdgeBudget` is the
summed form of the same count).  That is what makes the retained cap survive
`rem:budget-robustness` rather than depending on the exact `m`.

`lem:p13-window-package` is proved on the literal near-cubic residual.  The
label-injectivity clauses are refuted through the ledger's `lem:replacement`
fact (`K .replacementExclusion`) and the selection's minimality, exactly as
`DeclaredQuotient.localize` splits them. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def windowPackageRow :
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
    `Hypostructure.Graph.Strategy.Spine.windowPackage
    { Requires := [K .maximalPacking, K .replacementExclusion, K .selection]
      Produces := [K .windowPackageSeparated]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .windowPackageSeparated)
        (show Value BranchState Presentation presentation data
            .windowPackageSeparated inputs.current from
          ⟨by
            classical
            simp only [Holds]
            let noReplacement := (inputs.get (K .replacementExclusion)).down
            let selected := (inputs.get (K .selection)).down
            obtain ⟨_positive, packing, valid, maximum, maximal⟩ :=
              (inputs.get (K .maximalPacking)).down
            refine ⟨packing, valid, maximum, maximal, ?_⟩
            let barrier := data.windowBarrier
            letI := barrier.indexFintype
            let scales := data.separatedScaleCount
              inputs.current.object.vertexCount
            let safe := Core.Finite.CertifiedTableAggregation.safeProduct
              barrier.table
            let flat := Core.Finite.CertifiedTableAggregation.flatProduct
              barrier.table
            let bits := windowPackageBits data inputs.current.object
            have bitsEq : bits = Nat.log2 ((safe ^ scales - 1) / flat ^ scales) := rfl
            -- `|ℐ_win| ≥ (c₁₃ − o(1)) log₂ n` per window: the registered rate,
            -- floored once per scale, is dominated by the compounded floor.
            have rateLe : data.windowRate * scales ≤ bits := by
              rw [bitsEq]
              have flatPos : 0 < flat := barrier.flatPositive
              have improves : flat ≤ safe := barrier.improves
              rcases Nat.eq_zero_or_pos scales with scalesZero | scalesPos
              · simp [scalesZero]
              rcases lt_or_eq_of_le improves with flatLt | flatEq
              · -- `2 ^ rate · flat ≤ safe − 1`, then compound across the scales.
                have rateBound : 2 ^ data.windowRate * flat ≤ safe - 1 := by
                  have rateDef : data.windowRate =
                      Nat.log2 ((safe - 1) / flat) := by
                    rw [data.windowRate_eq_barrier]
                    show Core.Finite.CertifiedTableAggregation.binaryRateFloor
                      barrier.table = _
                    rw [Core.Finite.CertifiedTableAggregation.binaryRateFloor,
                      if_neg (Nat.ne_of_gt flatPos)]
                  rw [rateDef]
                  rcases Nat.eq_zero_or_pos ((safe - 1) / flat) with qZero | qPos
                  · rw [qZero]
                    simp only [Nat.log2_zero, pow_zero, one_mul]
                    omega
                  · calc 2 ^ Nat.log2 ((safe - 1) / flat) * flat
                        ≤ ((safe - 1) / flat) * flat :=
                          Nat.mul_le_mul_right _ (by
                            simpa [Nat.log2_eq_log_two] using
                              Nat.pow_log_le_self 2 (Nat.ne_of_gt qPos))
                      _ ≤ safe - 1 := Nat.div_mul_le_self _ _
                have compounded : 2 ^ (data.windowRate * scales) * flat ^ scales ≤
                    safe ^ scales - 1 := by
                  have step : (2 ^ data.windowRate * flat) ^ scales ≤
                      (safe - 1) ^ scales :=
                    Nat.pow_le_pow_left rateBound scales
                  rw [mul_pow, ← pow_mul] at step
                  refine step.trans ?_
                  -- `(S − 1)^s ≤ S^s − 1` for `S ≥ 1`, `s ≥ 1`.
                  have onePos : 1 ≤ safe := le_trans (Nat.one_le_iff_ne_zero.mpr
                    (Nat.ne_of_gt flatPos)) improves
                  have : (safe - 1) ^ scales + 1 ≤ safe ^ scales := by
                    have := Nat.pow_le_pow_left (Nat.sub_le safe 1) scales
                    have strict : (safe - 1) ^ scales < safe ^ scales :=
                      Nat.pow_lt_pow_left (by omega) (Nat.ne_of_gt scalesPos)
                    omega
                  omega
                have flatPowPos : 0 < flat ^ scales := pow_pos flatPos scales
                have divBound : 2 ^ (data.windowRate * scales) ≤
                    (safe ^ scales - 1) / flat ^ scales :=
                  (Nat.le_div_iff_mul_le flatPowPos).mpr compounded
                have quotientPos : (safe ^ scales - 1) / flat ^ scales ≠ 0 :=
                  Nat.ne_of_gt (lt_of_lt_of_le (Nat.one_le_two_pow) divBound)
                exact (Nat.le_log2 quotientPos).mpr divBound
              · -- `flat = safe`: the registered rate is `0`.
                have rateZero : data.windowRate = 0 := by
                  rw [data.windowRate_eq_barrier]
                  show Core.Finite.CertifiedTableAggregation.binaryRateFloor
                    barrier.table = 0
                  rw [Core.Finite.CertifiedTableAggregation.binaryRateFloor,
                    if_neg (Nat.ne_of_gt flatPos)]
                  have : (safe - 1) / flat = 0 :=
                    Nat.div_eq_of_lt (by omega)
                  change Nat.log2 ((safe - 1) / flat) = 0
                  rw [this]
                  rfl
                simp [rateZero]
            let Coordinate := Graph.DeclaredSignature.Coordinate
              inputs.current.object.Vertex
                (Fin bits × Finset inputs.current.object.Vertex)
            let package : Finset inputs.current.object.Vertex →
                Finset Coordinate := fun window =>
              Finset.univ.image fun bit =>
                Graph.DeclaredSignature.Coordinate.base
                  .windowLabel (bit, window) window
            let family := packing.biUnion package
            have packageCard : ∀ window, (package window).card = bits := by
              intro window
              rw [Finset.card_image_iff.mpr]
              · simp
              · intro left _ right _ equality
                cases equality
                rfl
            have packagesDisjoint :
                ∀ left ∈ packing, ∀ right ∈ packing, left ≠ right →
                  Disjoint (package left) (package right) := by
              intro left _leftMem right _rightMem different
              rw [Finset.disjoint_left]
              intro coordinate leftMember rightMember
              obtain ⟨leftBit, _, leftEq⟩ := Finset.mem_image.mp leftMember
              obtain ⟨rightBit, _, rightEq⟩ := Finset.mem_image.mp rightMember
              rw [← leftEq] at rightEq
              have supportEq := congrArg
                Graph.DeclaredSignature.Coordinate.support rightEq
              simp only [Graph.DeclaredSignature.Coordinate.support_base]
                at supportEq
              exact different supportEq.symm
            have familyCard : family.card = bits * packing.card := by
              rw [Finset.card_biUnion]
              · simp_rw [packageCard]
                simp [Nat.mul_comm]
              · intro left leftMem right rightMem different
                exact packagesDisjoint left leftMem right rightMem different
            refine ⟨(fun window _member => by
                simpa only [package, bits] using packageCard window),
              (by simpa only [package] using packagesDisjoint),
              (by simpa only [family, bits] using familyCard),
              (by simpa only [bits, scales] using rateLe), ?_, ?_⟩
            · intro declared _functional
              by_contra reducing
              rcases declared.localize reducing with replacement |
                ⟨representative, smaller, baseline, transfer⟩
              · exact noReplacement declared.support replacement
              · exact selected.1 (transfer (selected.2 representative smaller baseline))
            · intro BaselineCoordinate baseline baselineSupport
                _baselineIndependent
              intro declared _functional
              by_contra reducing
              rcases declared.localize reducing with replacement |
                ⟨representative, smaller, baselineObject, transfer⟩
              · exact noReplacement declared.support replacement
              · exact selected.1
                  (transfer (selected.2 representative smaller baselineObject))⟩)
        .nil)
    0 0

/-! ## Node `[22]`: the canonical hot/cold partition

`def:cold-window-ledger`.  The manuscript fixes the maximal packing once (the
lexicographically first object with the extremal property, `lem:skeleton-dominates`)
and splits it into hot and cold windows.  `canonicalWindowPacking` is that fixed
packing, so its defining specification is the whole input of the split: the row
reads no predecessor fact and re-proves nothing.  `hot` and `cold` are the
canonical filters inside the ledger proposition; they are not callback arguments
or mutable routing state. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def hotColdPartitionRow :
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
    `Hypostructure.Graph.Strategy.Spine.hotColdPartition
    { Requires := []
      Produces := [K .hotColdPartition]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .hotColdPartition)
        (show Value BranchState Presentation presentation data
            .hotColdPartition inputs.current from
          ⟨by
            classical
            let object := inputs.current.object
            let packing := canonicalWindowPacking data object
            have packingFacts :
                object.IsWindowPacking data.windowOrder packing ∧
                  packing.card = object.windowPackingNumber data.windowOrder :=
              Classical.choose_spec
                (object.exists_windowPacking_card_eq data.windowOrder)
            let hot := canonicalHotWindows data object
            let cold := canonicalColdWindows data object
            have hotFacts :
                hot ⊆ packing ∧
                  (WindowFamilyRealized data object hot ∨
                    (hot = ∅ ∧ ¬ WindowFamilyRealized data object ∅)) ∧
                  ∀ other : Finset (Finset object.Vertex), other ⊆ packing →
                    WindowFamilyRealized data object other →
                      other.card ≤ hot.card :=
              Classical.choose_spec (exists_maximal_windowFamilyRealized data object)
            show IsHotColdWindowPartition data object packing hot cold
            refine ⟨packingFacts.1, packingFacts.2, ?_, hotFacts, ?_, ?_, ?_⟩
            · intro support window
              exact object.exists_mem_not_disjoint_of_card_eq
                data.windowOrder_pos packingFacts.1 packingFacts.2 window
            · intro window
              simp [cold, packing, hot, canonicalColdWindows]
            · exact Finset.disjoint_sdiff
            · intro window
              constructor
              · intro member
                by_cases inHot : window ∈ hot
                · exact Or.inl inHot
                · exact Or.inr (by
                    simp [cold, packing, hot, canonicalColdWindows, member, inHot])
              · intro member
                rcases member with member | member
                · exact hotFacts.1 member
                · exact (Finset.mem_sdiff.mp member).1⟩)
        .nil)
    0 0

/-! ## Node `[23]`: the live-hot window overflow -/

/-! **Node `[23]`, the live-hot entropy comparison.**  On the literal overflow
residual, `def:cold-window-ledger` says that the canonical hot family either
has its full package realized by labelled skeletons or is empty.  In the first
case `lem:p13-window-package` converts the registered rate into a lower bound
on the realized state count and `lem:skeleton-dominates` bounds that count by
the skeleton budget.  In the empty case the required package has one state,
while the selected object's skeleton class is nonempty.  Thus the exact cap
opposite to the overflow arm holds.

All three manuscript premises are read through `FactInputs.get`, and the
statement is indexed by `inputs.current`; no detached graph or proof payload is
accepted by the row. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def liveHotBarrierCapRow :
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
    `Hypostructure.Graph.Strategy.Spine.liveHotBarrierCap
    { Requires :=
        [K .hotColdPartition, K .skeletonDominates, K .windowPackageSeparated]
      Produces := [K .barrierCap]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .barrierCap)
        (show Value BranchState Presentation presentation data
            .barrierCap inputs.current from
          ⟨by
            let object := inputs.current.object
            change 2 ^ (data.windowRate *
                data.separatedScaleCount object.vertexCount *
                (canonicalHotWindows data object).card) ≤
              Graph.skeletonBudget object
            have split := (inputs.get (K .hotColdPartition)).down
            have dominates := (inputs.get (K .skeletonDominates)).down
            have package := (inputs.get (K .windowPackageSeparated)).down
            obtain
              ⟨_valid, _attains, _maximal, hotFacts, _coldIff, _disjoint, _cover⟩ :=
                split
            obtain ⟨_hotSubset, retained, _hotMaximal⟩ := hotFacts
            obtain ⟨_packing, _packingValid, _packingCard, _packingMaximal,
              _packageCard, _packagesDisjoint, _familyCard, rateLe, _⟩ := package
            have exponentLe :
                data.windowRate * data.separatedScaleCount object.vertexCount *
                    (canonicalHotWindows data object).card ≤
                  windowPackageBits data object *
                    (canonicalHotWindows data object).card :=
              Nat.mul_le_mul_right _ rateLe
            rcases retained with
              ⟨State, stateOf, packageStates, _retainedCode⟩ |
                ⟨hotEmpty, _emptyUnrealized⟩
            · have realizedBound := dominates.2 State stateOf
              exact (Nat.pow_le_pow_right (by norm_num) exponentLe).trans
                (packageStates.trans realizedBound)
            · rw [hotEmpty]
              simp only [Finset.card_empty, Nat.mul_zero, pow_zero]
              exact Graph.skeletonBudget_pos object⟩)
        .nil)
    0 0

/-! ## Node `[24]`: `prop:p13-density`, after the cold branch closes

The manuscript's `[24]` reads "cold branch begins; continued at `[145]`--`[157]`;
after closure, `θ ≤ θ_win + o(1)`".  The finite density cap `K .densityCap` is
therefore produced only once the cold branch has been closed on the literal
residual; the former row that derived it at `[24]` from a cap on *all* windows
did not follow the manuscript and is deleted.  Until the cold closure is wired,
the producer of `K .densityCap` is absent and every consumer fails loudly. -/

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
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def remainderNormalizationRow :
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
    `Hypostructure.Graph.Strategy.Spine.remainderNormalization
    { Requires := [K .selection]
      Produces := [K .remainderNormalized]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let object := inputs.current.object
      let avoids := (inputs.get (K .selection)).down.1
      .cons (key := K .remainderNormalized)
        (show Value BranchState Presentation presentation data
            .remainderNormalized inputs.current from
          ⟨fun _packing _valid maximal support inside =>
            ⟨object.not_inducesWindow_of_subset_remainderSupport maximal inside,
              object.not_baseline_induce_of_subset_remainderSupport
                data.freeForcesTarget avoids maximal inside⟩⟩)
        .nil)
    0 0

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
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def boundaryDemandRow :
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
    `Hypostructure.Graph.Strategy.Spine.boundaryDemand
    { Requires := [K .remainderNormalized]
      Produces := [K .boundaryDemand]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      -- Node `[28]` is entered only on the normalized remainder residual.  Read
      -- that literal predecessor fact; the framework retains it when the new
      -- demand fact is appended.
      let _normalized := inputs.get (K .remainderNormalized)
      -- The standing baseline, read off the residual rather than from a fact.
      let baseline : ∀ vertex : inputs.current.object.Vertex,
          data.threshold ≤ inputs.current.object.degree vertex :=
        fun vertex => le_trans inputs.current.baseline
          (inputs.current.object.minDegree_le_degree vertex)
      .cons (key := K .boundaryDemand)
        -- `lem:surplus-aware-window-stub`: the demand link and the capacity
        -- link, each at its own hypothesis and neither near-cubic.
        (show Value BranchState Presentation presentation data
            .boundaryDemand inputs.current from
          ⟨fun packing valid =>
            ⟨inputs.current.object.positiveDeficiency_le_boundaryIncidence
              (inputs.current.object.remainderSupport packing) data.threshold
              baseline,
            inputs.current.object.boundaryIncidence_add_internal_mass_le valid
              baseline⟩⟩)
        .nil)
    0 0

/-! Node `[29]`, `lem:stub-positive`.  This is deliberately a second ledger
append after node `[28]`: it reads the registered boundary-demand chain and the
near-cubic surplus ceiling from that literal residual, then publishes only the
finite external-incidence supply bound. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def stubSupplyRow :
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
    `Hypostructure.Graph.Strategy.Spine.stubSupply
    { Requires := [K .boundaryDemand, K .surplusAtOrBelow]
      Produces := [K .stubSupply]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let baseline : ∀ vertex : inputs.current.object.Vertex,
          data.threshold ≤ inputs.current.object.degree vertex :=
        fun vertex => le_trans inputs.current.baseline
          (inputs.current.object.minDegree_le_degree vertex)
      let demand := (inputs.get (K .boundaryDemand)).down
      let ceiling := (inputs.get (K .surplusAtOrBelow)).down
      .cons (key := K .stubSupply)
        (show Value BranchState Presentation presentation data
            .stubSupply inputs.current from
          ⟨fun packing valid => by
          have links := demand packing valid
          have windowSurplus :=
            inputs.current.object.ambientSurplus_le_degreeSurplus
              (Graph.FiniteObject.windowSupport packing) data.threshold baseline
          have globalSurplus :
              inputs.current.object.degreeSurplus data.threshold ≤
                data.surplusThreshold inputs.current.object.vertexCount := ceiling
          omega⟩)
        .nil)
    0 0

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

The node exists for its "in particular", and that is the second clause.
Substituting the boundary-demand ceiling of nodes `[28]`--`[29]` for `def⁺(R)`
turns the bound into the demand floor of the final collision -- invariant 28 --
which is why this row consumes `stubSupply`: the manuscript's own
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
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def wedgeSupplyRow :
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
    `Hypostructure.Graph.Strategy.Spine.wedgeSupply
    { Requires := [K .stubSupply]
      Produces := [K .wedgeSupply]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
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
      .cons (key := K .wedgeSupply)
        (show Value BranchState Presentation presentation data
            .wedgeSupply inputs.current from
          ⟨⟨supply, fun packing valid => by
            have wedge :=
              supply packing valid
                (inputs.current.object.remainderSupport packing)
                (Finset.Subset.refl _)
            have ceiling :=
              (inputs.get (K .stubSupply)).down packing valid
            omega⟩⟩)
        .nil)
    0 0

/-! ## Node `[31]`: the curvature target-rank of the remainder

`def:exact-response-profile`, `def:admissible-rank-quotient`,
`def:functional-rank-quotient`, `def:curvature-target-rank`, at the atom
remainder `R` of every maximal packing.

* The declared raw curvature coordinates of `R` (clause (D4) of
  `def:declared-coordinate-signature`) are its internal length-two wedges,
  `𝒲₂(R)`; the profile is *exact* — "two distinct coordinate labels remain
  distinct entries even if their numerical values in the embedded graph
  coincide" — so the labelled family has exactly `W₂(R)` entries
  (`internalWedgeFamily_card`).
* An admissible rank quotient of that family (`remainderQuotient`, i.e.
  `Graph.CurvatureQuotient`) carries the connected determination support, the
  boundary-degree fibre and all-context target-completeness clauses of
  `def:target-complete-quotient`, and the two representative clauses of
  `def:admissible-rank-quotient`; a rank-reducing one is therefore represented
  by a strictly smaller proper representative or a strictly smaller admissible
  closed representative (`DeclaredQuotient.localize`).
* The admissible quotient system used to compute target rank consists of the
  admissible quotients that are functional on the family
  (`RankQuotient.FunctionalOn`); a subfamily survives it when every such
  quotient is label-injective on it, and `r_Ω(R)` is the maximum size of a
  surviving subfamily — attained, and an upper bound for every surviving
  subfamily (`exists_attaining_curvatureTargetRank`,
  `card_le_curvatureTargetRank`).

The row reads the atom-remainder normalization of nodes `[25]`--`[27]` — the
remainder is the region whose raw tests are ranked — and publishes the three
definitional facts on the same residual.  `lem:target-rank-circuit` is the next
row. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def curvatureTargetRankRow :
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
    `Hypostructure.Graph.Strategy.Spine.curvatureTargetRank
    { Requires := [K .remainderNormalized]
      Produces := [K .exactResponseProfile, K .admissibleRankQuotient,
        K .curvatureTargetRank]
      requiresUnique := by simp
      producesUnique := by simp [K_eq_iff]
      producesNonempty := by simp }
    (fun inputs =>
      -- Node `[31]` ranks the raw curvature tests of the atom remainder; read
      -- that literal predecessor fact.
      let _normalized := inputs.get (K .remainderNormalized)
      .cons (key := K .exactResponseProfile)
        (show Value BranchState Presentation presentation data
            .exactResponseProfile inputs.current from
          ⟨fun packing _valid _card =>
            Graph.FiniteObject.internalWedgeFamily_card inputs.current.object
              (inputs.current.object.remainderSupport packing)⟩)
        (.cons (key := K .admissibleRankQuotient)
          (show Value BranchState Presentation presentation data
              .admissibleRankQuotient inputs.current from
            ⟨fun _packing _valid _card quotient reducing =>
              quotient.localize reducing⟩)
          (.cons (key := K .curvatureTargetRank)
            (show Value BranchState Presentation presentation data
                .curvatureTargetRank inputs.current from
              ⟨fun packing _valid _card =>
                ⟨Graph.FiniteObject.exists_attaining_curvatureTargetRank
                    (Graph.MinimumDegreeAtLeast data.threshold)
                    (Graph.HasCycleWithLength data.LengthOK) inputs.current.object
                    (inputs.current.object.remainderSupport packing),
                  fun _candidate subset survives =>
                    Graph.FiniteObject.card_le_curvatureTargetRank
                      (Graph.MinimumDegreeAtLeast data.threshold)
                      (Graph.HasCycleWithLength data.LengthOK) inputs.current.object
                      (inputs.current.object.remainderSupport packing) subset survives⟩⟩)
            .nil)))
    0 0

/-! ## `lem:target-rank-circuit`: finite proper dependence

For a maximal surviving subfamily `𝓘` and a raw test `a ∉ 𝓘`, adjoining `a`
cannot survive every functional admissible quotient — the maximality clause of
`K .curvatureTargetRank` is what forbids it — so some functional admissible
quotient is label-injective on `𝓘` but not on `𝓘 ∪ {a}`, and its functional
clause supplies the finite determining subfamily `ℬ ⊆ 𝓘`; `a ∉ ℬ`, so the
dependence is proper.  The "in particular" is the contrapositive at a maximal
surviving family. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def targetRankCircuitRow :
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
    `Hypostructure.Graph.Strategy.Spine.targetRankCircuit
    { Requires := [K .curvatureTargetRank]
      Produces := [K .targetRankCircuit]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let rank := (inputs.get (K .curvatureTargetRank)).down
      .cons (key := K .targetRankCircuit)
        (show Value BranchState Presentation presentation data
            .targetRankCircuit inputs.current from
          ⟨fun packing valid card => by
            classical
            obtain ⟨_attained, maximal⟩ := rank packing valid card
            refine ⟨fun independent subset survives maximum test testMem outside => ?_,
              fun noDependence => ?_⟩
            · -- `𝓘 ∪ {a}` does not survive: its size would exceed `r_Ω(R)`.
              have notSurvive : ¬ Graph.FiniteObject.SurvivesCurvatureSystem
                  (Graph.MinimumDegreeAtLeast data.threshold)
                  (Graph.HasCycleWithLength data.LengthOK) inputs.current.object
                  (inputs.current.object.remainderSupport packing)
                  (insert test independent) := by
                intro survivesInsert
                have le := maximal (insert test independent)
                  (Finset.insert_subset testMem subset) survivesInsert
                rw [Finset.card_insert_of_notMem outside] at le
                omega
              simp only [Graph.FiniteObject.SurvivesCurvatureSystem, not_forall]
                at notSurvive
              obtain ⟨quotient, functional, notInjective⟩ := notSurvive
              have injective := survives quotient functional
              have insertCoe : (↑(insert test independent) :
                  Set (inputs.current.object.InternalWedge
                    (inputs.current.object.remainderSupport packing))) =
                  insert test ↑independent := by simp
              rw [Core.TargetRank.RankQuotient.LabelInjectiveOn, insertCoe] at notInjective
              obtain ⟨determiners, finite, determinersSubset, determines⟩ :=
                functional (Finset.coe_subset.2 subset) testMem
                  (by simpa using outside) injective notInjective
              refine ⟨determiners, determinersSubset, finite,
                fun mem => outside (determinersSubset mem), quotient, functional, ?_,
                determines⟩
              intro injectiveFamily
              exact notInjective (injectiveFamily.mono (by
                rw [← insertCoe]
                exact Finset.coe_subset.2 (Finset.insert_subset testMem subset)))
            · exact Graph.FiniteObject.survives_of_no_dependence
                (Graph.MinimumDegreeAtLeast data.threshold)
                (Graph.HasCycleWithLength data.LengthOK) inputs.current.object
                (inputs.current.object.remainderSupport packing) noDependence⟩)
        .nil)
    0 0


/-! ## Node `[32]`: the finite circuit form of the rank split

The paragraph immediately after `lem:target-rank-circuit` states the exact
finite implication `r_Ω(R) < W₂(R) ⇒` a raw curvature coordinate is
target-dependent.  The complementary finite arm is `r_Ω(R) = W₂(R)`;
`lem:full-rank` later records its weaker asymptotic consequence
`r_Ω(R) ≥ W₂(R) - o(W₂(R))`.  This decision publishes precisely those
two finite branch facts on the concrete remainder. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
noncomputable def curvatureRankDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : @FactKeys (Input BranchState Presentation presentation data)
      _ (factSystem BranchState Presentation presentation data)}
    (previous :
      @ExactLedger (Input BranchState Presentation presentation data)
        _ (factSystem BranchState Presentation presentation data) current known)
    [@Core.Residual.FactKeys.Has
      (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data)
      (K .targetRankCircuit) known]
    (dropFresh : K .curvatureRankDrop ∉ known)
    (fullFresh : K .curvatureFullRank ∉ known) :
    @Decision (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data) current known
      (K .curvatureRankDrop) (K .curvatureFullRank) previous :=
  @Decision.run (Input BranchState Presentation presentation data) _
    (factSystem BranchState Presentation presentation data) current known
    previous (K .curvatureRankDrop) (K .curvatureFullRank)
    `Hypostructure.Graph.Strategy.Spine.curvatureRankDichotomy
    (by
      classical
      -- `lem:target-rank-circuit` at the manuscript's fixed maximal packing.
      let circuit := (@ExactLedger.get
        (Input BranchState Presentation presentation data) _
        (factSystem BranchState Presentation presentation data)
        current known previous (K .targetRankCircuit)).down
      let packing := canonicalWindowPacking data current.object
      have packingSpec := Classical.choose_spec
        (current.object.exists_windowPacking_card_eq data.windowOrder)
      have valid : current.object.IsWindowPacking data.windowOrder packing := packingSpec.1
      have packingCard : packing.card = current.object.windowPackingNumber data.windowOrder :=
        packingSpec.2
      have extract := (circuit packing valid packingCard).1
      have attained := Graph.FiniteObject.exists_attaining_curvatureTargetRank
        (Graph.MinimumDegreeAtLeast data.threshold)
        (Graph.HasCycleWithLength data.LengthOK) current.object
        (current.object.remainderSupport packing)
      let independent := Classical.choose attained
      have independentSpec := Classical.choose_spec attained
      have independentSubset : independent ⊆ _ := independentSpec.1
      have survives : Graph.FiniteObject.SurvivesCurvatureSystem
          (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) current.object
          (current.object.remainderSupport packing) independent := independentSpec.2.1
      have rank : independent.card = _ := independentSpec.2.2
      clear_value independent
      by_cases below :
          remainderCurvatureTargetRank data current.object packing <
            remainderWedgeSupply current.object packing
      · refine .inl ⟨⟨packing, valid, packingCard, below, ?_⟩⟩
        have outside : ∃ test ∈
            current.object.internalWedgeFamily
              (current.object.remainderSupport packing),
            test ∉ independent := by
          by_contra noOutside
          push Not at noOutside
          have familySubset :
              current.object.internalWedgeFamily
                  (current.object.remainderSupport packing) ⊆ independent :=
            noOutside
          have equal : independent =
              current.object.internalWedgeFamily
                (current.object.remainderSupport packing) :=
            Finset.Subset.antisymm independentSubset familySubset
          rw [equal, Graph.FiniteObject.internalWedgeFamily_card] at rank
          exact (Nat.ne_of_lt below) rank.symm
        obtain ⟨test, testMember, testOutside⟩ := outside
        obtain ⟨determiners, determinersSubset, finite, proper, declared,
          functional, reducing, determines⟩ :=
          extract independent independentSubset survives rank test testMember testOutside
        exact ⟨test, testMember, determiners,
          determinersSubset.trans independentSubset, finite, proper,
          declared, functional, reducing, determines⟩
      · refine .inr ⟨⟨packing, valid, packingCard, ?_⟩⟩
        apply Nat.le_antisymm
        · change
            current.object.curvatureTargetRank
                (Graph.MinimumDegreeAtLeast data.threshold)
                (Graph.HasCycleWithLength data.LengthOK)
                (current.object.remainderSupport packing) ≤
              current.object.internalWedgeCount
                (current.object.remainderSupport packing)
          rw [← rank]
          calc
            independent.card ≤
                (current.object.internalWedgeFamily
                  (current.object.remainderSupport packing)).card :=
              Finset.card_le_card independentSubset
            _ = current.object.internalWedgeCount
                  (current.object.remainderSupport packing) :=
              Graph.FiniteObject.internalWedgeFamily_card
                (object := current.object)
                (support := current.object.remainderSupport packing)
        exact Nat.le_of_not_gt below)
    dropFresh fullFresh

/-! ## Nodes `[33]` and `[35]`: minimal curvature-dependence support

The rank-drop arm already contains a concrete proper determination.  Following
`lem:curvature-dependence-routing`, this row chooses, for its fixed determined
coordinate, a certificate whose connected declared support is inclusion-minimal.
All candidates are local mathematical objects; the sole proof-data input and
output are the exact-ledger facts named in the manifest. -/
@[reducible] noncomputable def branchDependenceRow
    (data : Data.{u}) :
    AtomicStrategy (Input BranchState Presentation presentation data) := by
  classical
  exact
    factOnly `Hypostructure.Graph.Strategy.Spine.branchDependence
      (rowManifest (K .curvatureRankDrop) (K .branchDependence)
        (by simp [K_eq_iff]))
      (fun inputs =>
        let inherited := (inputs.get (K .curvatureRankDrop)).down
        .cons (key := K .branchDependence)
          ⟨by
            letI : Fintype inputs.current.object.Vertex :=
              @FinEnum.instFintype _ inputs.current.object.vertices
            rcases inherited with
              ⟨packing, valid, packingCard, below, test, testMember,
                determiners, determinersSubset, finite, proper, declared,
                functional, reducing, determines⟩
            let support := inputs.current.object.remainderSupport packing
            let family := inputs.current.object.internalWedgeFamily support
            let supportData := family
            have supportDataCarried : ∀ coordinate ∈ supportData,
                Graph.FiniteObject.internalWedgeSupport
                    (region := support) coordinate ⊆ declared.support := by
              intro coordinate coordinateMember
              exact declared.carries coordinate coordinateMember
            have certified :
                DeterminationCertificate data inputs.current.object packing test
                  determiners declared supportData :=
              ⟨testMember, determinersSubset, finite, proper, functional,
                reducing, determines, rfl, supportDataCarried⟩
            refine ⟨packing, valid, packingCard, below, test, ?_⟩
            dsimp only
            set Supports :=
              inputs.current.object.vertexFinset.powerset.filter
                fun candidateSupport =>
                  ∃ basis candidate,
                    candidate.support = candidateSupport ∧
                      ∃ candidateSupportData,
                        DeterminationCertificate data inputs.current.object
                          packing test basis candidate candidateSupportData
            change ∃ selectedDeterminers selectedQuotient selectedSupportData,
              DeterminationCertificate data inputs.current.object packing test
                    selectedDeterminers selectedQuotient selectedSupportData ∧
                ∀ smaller : Finset inputs.current.object.Vertex,
                  smaller ⊂ selectedQuotient.support →
                    ∀ narrower : remainderQuotient data inputs.current.object packing,
                      narrower.support = smaller →
                        ∀ narrowerDeterminers narrowerSupportData,
                          ¬ DeterminationCertificate data inputs.current.object
                            packing test narrowerDeterminers narrower
                              narrowerSupportData
            have inhabited : declared.support ∈ Supports := by
              simp only [Supports, Finset.mem_filter, Finset.mem_powerset]
              exact ⟨by intro vertex _; simp, determiners, declared, rfl,
                supportData, certified⟩
            obtain ⟨leastSupport, leastMember, least⟩ :=
              Finset.exists_min_image Supports Finset.card ⟨_, inhabited⟩
            have leastInSupports := leastMember
            simp only [Supports, Finset.mem_filter, Finset.mem_powerset]
              at leastInSupports
            rcases leastInSupports with ⟨_, leastInSupports⟩
            obtain ⟨chosenDeterminers, chosen, supportEq,
              chosenSupportData, chosenCertified⟩ := leastInSupports
            subst leastSupport
            refine ⟨chosenDeterminers, chosen, chosenSupportData,
              chosenCertified, ?_⟩
            intro smaller strict narrower narrowerSupport narrowerDeterminers
              narrowerSupportData narrowerCertified
            have carried : smaller ∈ Supports := by
              simp only [Supports, Finset.mem_filter, Finset.mem_powerset]
              exact ⟨by intro vertex _; simp, narrowerDeterminers, narrower,
                narrowerSupport, narrowerSupportData, narrowerCertified⟩
            have minimum := least smaller carried
            exact absurd (Finset.card_lt_card strict) (by omega)⟩
          .nil)

/-! ## Node `[36]`: the context-validity test

The literal `[33]` residual contains one inclusion-minimal determination
certificate.  Node `[36]` asks the paper's exact question of that certificate:
does its determination remain valid against every outside context?  The no arm
exhibits an identified pair and a distinguishing context; the yes arm records
context universality for that same certificate.  Boundary-fibre preservation
is already part of the admissible quotient and is not a second test here. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
noncomputable def contextValidityDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : @FactKeys (Input BranchState Presentation presentation data)
      _ (factSystem BranchState Presentation presentation data)}
    (previous :
      @ExactLedger (Input BranchState Presentation presentation data)
        _ (factSystem BranchState Presentation presentation data) current known)
    [@Core.Residual.FactKeys.Has
      (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data)
      (K .branchDependence) known]
    (defectFresh : K .contextDefect ∉ known)
    (universalFresh : K .contextUniversal ∉ known) :
    @Decision (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data) current known
      (K .contextDefect) (K .contextUniversal) previous :=
  @Decision.run (Input BranchState Presentation presentation data) _
    (factSystem BranchState Presentation presentation data) current known
    previous (K .contextDefect) (K .contextUniversal)
    `Hypostructure.Graph.Strategy.Spine.contextValidityDichotomy
    (by
      classical
      let inherited := (@ExactLedger.get
        (Input BranchState Presentation presentation data) _
        (factSystem BranchState Presentation presentation data)
        current known previous (K .branchDependence)).down
      let packing := Classical.choose inherited
      have packingSpec := Classical.choose_spec inherited
      let test := Classical.choose packingSpec.2.2.2
      have testSpec := Classical.choose_spec packingSpec.2.2.2
      dsimp only at testSpec
      let determiners := Classical.choose testSpec
      have determinersSpec := Classical.choose_spec testSpec
      let quotient := Classical.choose determinersSpec
      have quotientSpec := Classical.choose_spec determinersSpec
      let supportData := Classical.choose quotientSpec
      have selected := Classical.choose_spec quotientSpec
      have certified := selected.1
      have minimal := selected.2
      have valid := packingSpec.1
      have packingCard := packingSpec.2.1
      by_cases universal :
          ∀ left right, Identified quotient left right →
            Graph.Response.ContextEquivalent
              (Graph.HasCycleWithLength data.LengthOK) left right
      · exact .inr ⟨⟨packing, valid, packingCard, test, determiners, quotient,
          supportData, certified, minimal, universal⟩⟩
      · refine .inl ⟨⟨packing, valid, packingCard, test, determiners, quotient,
          supportData, certified, minimal, ?_⟩⟩
        push Not at universal
        obtain ⟨left, right, identified, failure⟩ := universal
        exact ⟨left, right, identified,
          Graph.Response.targetDefect_of_not_contextEquivalent failure⟩)
    defectFresh universalFresh

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
`Graph.DeclaredQuotient.localize` is the scope split between them. -/

/-! ### Node `[38]`: is the determination certified already at `C`?

*"Target-complete with smaller proper representative?"*  The yes arm is the
terminal `[39]`, proper atom compression -- case (ii): *"if it holds for every
outside context already with support `C`, then `q` is a target-complete
rank-reducing quotient of the proper atom `C`"*.  The no arm is node `[40]`: the
determination reaches outside `C`, so the connected support it needs strictly
contains `C`, which is case (iii)'s entry. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
noncomputable def atomCompressionDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : @FactKeys (Input BranchState Presentation presentation data)
      _ (factSystem BranchState Presentation presentation data)}
    (previous :
      @ExactLedger (Input BranchState Presentation presentation data)
        _ (factSystem BranchState Presentation presentation data) current known)
    [@Core.Residual.FactKeys.Has
      (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data)
      (K .contextUniversal) known]
    [@Core.Residual.FactKeys.Has
      (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data)
      (K .degreeProfileFibres) known]
    [@Core.Residual.FactKeys.Has
      (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data)
      (K .targetCompleteContextUniversality) known]
    [@Core.Residual.FactKeys.Has
      (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data)
      (K .maximalPacking) known]
    (compressionFresh : K .atomCompression ∉ known)
    (delocalizedFresh : K .delocalizedSupport ∉ known) :
    @Decision (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data) current known
      (K .atomCompression) (K .delocalizedSupport) previous :=
  @Decision.run (Input BranchState Presentation presentation data) _
    (factSystem BranchState Presentation presentation data) current known
    previous (K .atomCompression) (K .delocalizedSupport)
    `Hypostructure.Graph.Strategy.Spine.atomCompressionDichotomy
    (by
      classical
      let inherited := (@ExactLedger.get
        (Input BranchState Presentation presentation data) _
        (factSystem BranchState Presentation presentation data)
        current known previous (K .contextUniversal)).down
      let packing := Classical.choose inherited
      have packingSpec := Classical.choose_spec inherited
      have valid := packingSpec.1
      have packingCard := packingSpec.2.1
      let test := Classical.choose packingSpec.2.2
      have testSpec := Classical.choose_spec packingSpec.2.2
      let determiners := Classical.choose testSpec
      have determinersSpec := Classical.choose_spec testSpec
      let quotient := Classical.choose determinersSpec
      have quotientSpec := Classical.choose_spec determinersSpec
      let supportData := Classical.choose quotientSpec
      have selected := Classical.choose_spec quotientSpec
      have certified := selected.1
      have universal := selected.2.2
      have packingPositive :=
        (@ExactLedger.get
          (Input BranchState Presentation presentation data) _
          (factSystem BranchState Presentation presentation data)
          current known previous (K .maximalPacking)).down.1
      have complete : TargetCompleteAt data quotient := by
        intro left right identified
        have targetComplete : Graph.Response.TargetComplete
            Graph.BoundaryPiece.boundaryDegreeProfile
            (Graph.HasCycleWithLength data.LengthOK) left right :=
          ⟨quotient.fibrewise left right identified,
            universal left right identified⟩
        exact ⟨(@ExactLedger.get
              (Input BranchState Presentation presentation data) _
              (factSystem BranchState Presentation presentation data)
              current known previous (K .degreeProfileFibres)).down
                quotient.support left right targetComplete,
          (@ExactLedger.get
            (Input BranchState Presentation presentation data) _
            (factSystem BranchState Presentation presentation data)
            current known previous
              (K .targetCompleteContextUniversality)).down
              quotient.support left right targetComplete⟩
      by_cases inside :
          quotient.support ⊆ current.object.remainderSupport packing
      · have packingNonempty : packing.Nonempty :=
          Finset.card_pos.mp (packingCard ▸ packingPositive)
        let member := Classical.choose packingNonempty
        have memberMem := Classical.choose_spec packingNonempty
        have windowNonempty :=
          current.object.nonempty_of_inducesWindow data.windowOrder_pos
            (valid.1 member memberMem)
        let vertex := Classical.choose windowNonempty
        have vertexMem := Classical.choose_spec windowNonempty
        have supportProper : ∃ vertex, vertex ∉ quotient.support := by
          refine ⟨vertex, ?_⟩
          intro vertexInSupport
          have vertexInRemainder := inside vertexInSupport
          exact
            (current.object.notMem_windowSupport_of_mem_remainderSupport
              vertexInRemainder)
              (current.object.mem_windowSupport memberMem vertexMem)
        have reducing : quotient.toRankQuotient.RankReducingOn
            ↑(remainderCurvatureTests current.object packing) :=
          certified.2.2.2.2.2.1
        have replacement := quotient.properRepresentative supportProper reducing
        exact .inl ⟨⟨packing, valid, quotient,
          ⟨test, determiners, supportData, certified⟩, complete, inside,
          replacement⟩⟩
      · exact .inr ⟨⟨packing, valid, quotient,
          ⟨test, determiners, supportData, certified⟩, complete, inside,
          remainderSupport_ssubset_delocalizationSupport data quotient
            inside⟩⟩)
    compressionFresh delocalizedFresh

/-! ### Node `[41]`: is the enlarged support proper in `G`?

The yes arm is the terminal `[42]`, `lem:proper-smearing`: *"Regard `Z` as a
boundaried graph ... Since `Z ⊊ G`, it is a proper boundaried support.  If the
dependence fails against some outside `∂Z`-context, it is target-defective.  If
it succeeds against every outside context, it is a nontrivial target-complete
compression of the proper support `Z`, forbidden by `cor:uncompressible`."*  The
no arm is node `[43]`, whole-graph delocalization. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
noncomputable def delocalizationScopeDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : @FactKeys (Input BranchState Presentation presentation data)
      _ (factSystem BranchState Presentation presentation data)}
    (previous :
      @ExactLedger (Input BranchState Presentation presentation data)
        _ (factSystem BranchState Presentation presentation data) current known)
    [@Core.Residual.FactKeys.Has
      (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data)
      (K .delocalizedSupport) known]
    (properFresh : K .properDelocalization ∉ known)
    (globalFresh : K .globalDelocalization ∉ known) :
    @Decision (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data) current known
      (K .properDelocalization) (K .globalDelocalization) previous :=
  @Decision.run (Input BranchState Presentation presentation data) _
    (factSystem BranchState Presentation presentation data) current known
    previous (K .properDelocalization) (K .globalDelocalization)
    `Hypostructure.Graph.Strategy.Spine.delocalizationScopeDichotomy
    (by
      classical
      let inherited := (@ExactLedger.get
        (Input BranchState Presentation presentation data) _
        (factSystem BranchState Presentation presentation data)
        current known previous (K .delocalizedSupport)).down
      let packing := Classical.choose inherited
      have packingSpec := Classical.choose_spec inherited
      have valid := packingSpec.1
      let quotient := Classical.choose packingSpec.2
      have quotientSpec := Classical.choose_spec packingSpec.2
      have certificate := quotientSpec.1
      have complete := quotientSpec.2.1
      have outside := quotientSpec.2.2.1
      by_cases proper :
          ∃ vertex, vertex ∉
            delocalizationSupport data current.object packing quotient
      · let vertex := Classical.choose proper
        have vertexOutside := Classical.choose_spec proper
        have supportProper : ∃ vertex, vertex ∉ quotient.support := by
          refine ⟨vertex, ?_⟩
          intro vertexInSupport
          exact vertexOutside (Finset.mem_union_left _ vertexInSupport)
        let test := Classical.choose certificate
        have testSpec := Classical.choose_spec certificate
        let determiners := Classical.choose testSpec
        have determinersSpec := Classical.choose_spec testSpec
        let supportData := Classical.choose determinersSpec
        have certified := Classical.choose_spec determinersSpec
        have reducing : quotient.toRankQuotient.RankReducingOn
            ↑(remainderCurvatureTests current.object packing) :=
          certified.2.2.2.2.2.1
        have replacement := quotient.properRepresentative supportProper reducing
        exact .inl ⟨⟨packing, valid, quotient,
          ⟨test, determiners, supportData, certified⟩, complete, outside,
          vertex, vertexOutside, replacement⟩⟩
      · push Not at proper
        exact .inr ⟨⟨packing, valid, quotient, certificate, complete, outside,
          proper⟩⟩)
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
@[reducible] noncomputable def repairIdentityRow
    (data : Data.{u}) :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.repairIdentity
    { Requires := [K .globalDelocalization]
      Produces := [K .repairIdentity]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .repairIdentity)
        ⟨fun component => by
          have _selectedSupport :=
            (inputs.get (K .globalDelocalization)).down
          exact component.identity⟩
        .nil)

@[reducible] noncomputable def globalBarrierRow
    (data : Data.{u}) :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.globalBarrier
    { Requires := [K .globalDelocalization, K .repairIdentity]
      Produces := [K .globalBarrier]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .globalBarrier)
        ⟨by
          obtain ⟨packing, valid, quotient, certificate, _complete, _outside,
            _covers⟩ := (inputs.get (K .globalDelocalization)).down
          have _repairIdentity := (inputs.get (K .repairIdentity)).down
          obtain ⟨test, determiners, supportData, certified⟩ := certificate
          have reducing : quotient.toRankQuotient.RankReducingOn
              ↑(remainderCurvatureTests inputs.current.object packing) :=
            certified.2.2.2.2.2.1
          exact ⟨packing, valid, quotient,
            ⟨test, determiners, supportData, certified⟩,
            Graph.DeclaredQuotient.localize quotient reducing⟩⟩
        .nil)

/-! ## Nodes `[47]`--`[48]`: the forced curvature cost

`cor:forced-curvature-cost`, whose proof invokes `lem:full-rank` and
`lem:wedge-lower`.  Both are already ledger facts on this branch: the exact
full rank `r_Ω(R) = W₂(R)` of node `[34]` and the demand floor of node `[30]`
(`K .wedgeSupply`'s "in particular").  The row substitutes the equality into
the floor and applies the registered cost to both sides.

The registered cost is the *only* thing this row reads that is not on the
branch, and `rem:closure-robust` records that the closure outside the explicit
residuals holds for every nonnegative value of it. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def forcedCurvatureCostRow :
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
    `Hypostructure.Graph.Strategy.Spine.forcedCurvatureCost
    { Requires := [K .wedgeSupply, K .curvatureFullRank]
      Produces := [K .forcedCurvatureCost]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      -- `lem:wedge-lower`'s "in particular": node `[30]`'s demand floor.
      let floor := (inputs.get (K .wedgeSupply)).down.2
      let rank := (inputs.get (K .curvatureFullRank)).down
      .cons (key := K .forcedCurvatureCost)
        (show Value BranchState Presentation presentation data
            .forcedCurvatureCost inputs.current from ⟨by
          rcases rank with ⟨packing, valid, maximal, rankEq⟩
          refine ⟨packing, valid, maximal, ?_⟩
          have demand := floor packing valid
          -- `W₂(R) ≤ r_Ω(R)`, from the exact full-rank ledger fact.
          have supply :
              remainderWedgeSupply inputs.current.object packing ≤
                remainderCurvatureTargetRank data inputs.current.object packing :=
            rankEq.ge
          calc data.curvatureCost *
                (data.threshold *
                    (inputs.current.object.remainderSupport packing).card +
                  2 * (2 * (data.windowOrder - 1) * packing.card))
              ≤ data.curvatureCost *
                  (remainderCurvatureTargetRank data inputs.current.object
                        packing +
                    2 * (data.threshold * (data.windowOrder * packing.card) +
                      data.surplusThreshold inputs.current.object.vertexCount)) :=
                Nat.mul_le_mul_left _
                  (le_trans demand (Nat.add_le_add_right supply _))
            _ = _ := by ring⟩)
        .nil)
    0 0

/-! ## Nodes `[49]`--`[50]`: the per-vertex remainder entropy split

`def:remainder-entropy` and the decision `prop:two-budget` opens with.  `𝒢(R)`
is the labelled class carrying the constraints node `[27]` has already imposed,
and `η(R) = log₂|𝒢(R)|/|R|`; the split asks `η(R) ≥ (1/d)·log₂ n`.

Exponentiating both sides by `d·|R|` turns that into `n^{|R|} ≤ |𝒢(R)|^d`, an
integer comparison, so no logarithm, division, or rounding is written.  The two
arms are the two halves of one excluded middle, so they are exhaustive and
mutually exclusive by construction, and the arm not taken is absent from the
taken branch's key index. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
noncomputable def remainderEntropyDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : @FactKeys (Input BranchState Presentation presentation data)
      _ (factSystem BranchState Presentation presentation data)}
    (previous :
      @ExactLedger (Input BranchState Presentation presentation data)
        _ (factSystem BranchState Presentation presentation data) current known)
    [@FactKeys.Has (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data)
      (K .forcedCurvatureCost) known]
    (highFresh : K .remainderEntropyHigh ∉ known)
    (lowFresh : K .remainderEntropyLow ∉ known) :
    @Decision (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data) current known
      (K .remainderEntropyHigh) (K .remainderEntropyLow) previous :=
  -- Node `[49]` is asked of the residual carrying node `[48]`'s forced cost.
  let _cost := (@ExactLedger.get (Input BranchState Presentation presentation data) _
    (factSystem BranchState Presentation presentation data)
    current known previous (K .forcedCurvatureCost)).down
  @Decision.run (Input BranchState Presentation presentation data) _
    (factSystem BranchState Presentation presentation data) current known
    previous (K .remainderEntropyHigh) (K .remainderEntropyLow)
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
              (current.object.internalEdgeCount
                (current.object.remainderSupport packing))
              (current.object.remainderSupport packing).card
      · exact .inl ⟨high⟩
      · refine .inr ⟨?_⟩
        push Not at high
        obtain ⟨packing, valid, below⟩ := high
        exact ⟨packing, valid,
          (Graph.not_atLeastEntropyRate_iff _ _ _ _ _ _ _).mp below⟩)
    highFresh lowFresh


omit [FactSystem (Input BranchState Presentation presentation data)] in
/-- **Node `[55]`, Residual C on the low-entropy arm.**

The low arm of `prop:two-budget` is itself the second alternative in the
paper's Residual C statement.  Read that exact fact from the current ledger and
append only the canonical Residual C key.  Node `[56]`'s net-deficiency bound
is a separate subsequent fact and is not published here. -/
@[reducible] noncomputable def lowEntropyLargeBudgetRow :
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
    `Hypostructure.Graph.Strategy.Spine.lowEntropyLargeBudget
    { Requires := [K .remainderEntropyLow]
      Produces := [K .largeBudgetResidual]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .largeBudgetResidual)
        (show Value BranchState Presentation presentation data
            .largeBudgetResidual inputs.current from
          ⟨Or.inr (inputs.get (K .remainderEntropyLow)).down⟩)
        .nil)
    0 0

/-! ## Node `[56]`: the large-budget net-deficiency cap (density-cap arm)

This is the manuscript's displayed bound `def⁺(R) − σ(R) ≤ (1/4 − ε)|R|`
"for all sufficiently large `n`", in the exact cleared finite form: reading the
density cap and the registered sufficiently-large predicate gives the strict
scaled inequality the net-charge step consumes.  The implication is stored on
the literal Residual C ledger of the `[24]` bounded arm. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def netDeficiencyCapRow :
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
    `Hypostructure.Graph.Strategy.Spine.netDeficiencyCap
    { Requires := [K .largeBudgetResidual, K .densityCap]
      Produces := [K .netDeficiencyCap]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let _residual := (inputs.get (K .largeBudgetResidual)).down
      .cons (key := K .netDeficiencyCap)
        (show Value BranchState Presentation presentation data
            .netDeficiencyCap inputs.current from
          ⟨by
            intro packing valid cardinality large
            have density :
                2 * (data.windowRate *
                  data.separatedScaleCount inputs.current.object.vertexCount *
                  inputs.current.object.windowPackingNumber data.windowOrder) ≤
                (Graph.dyadicScaleCount inputs.current.object + 1) *
                  (data.threshold * inputs.current.object.vertexCount +
                    data.surplusThreshold inputs.current.object.vertexCount) +
                data.densitySlack * (data.windowRate *
                  data.separatedScaleCount inputs.current.object.vertexCount) *
                  data.surplusThreshold inputs.current.object.vertexCount :=
              (inputs.get (K .densityCap)).down
            have density' :
                2 * (data.windowRate * Nat.log2 inputs.current.object.vertexCount *
                  packing.card) ≤
                (Nat.log2 inputs.current.object.vertexCount + 1) *
                  (data.threshold * inputs.current.object.vertexCount +
                    data.spineScale *
                      Core.ceilSqrt inputs.current.object.vertexCount) +
                data.densitySlack * (data.windowRate * Nat.log2 inputs.current.object.vertexCount) *
                  (data.spineScale *
                    Core.ceilSqrt inputs.current.object.vertexCount) := by
              rw [data.separatedScaleCount_eq_log2, Graph.dyadicScaleCount,
                ← cardinality] at density
              simpa [Data.surplusThreshold] using density
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
            exact Graph.FiniteObject.strictCap_of_densityCap_of_sufficientlyLarge
              data.threshold data.dischargeScale data.windowOrder data.windowRate
              data.spineScale data.densitySlack inputs.current.object.vertexCount packing.card
              (inputs.current.object.remainderSupport packing).card
              data.windowOrder_pos thresholdPos debitLe data.netCapRateSlack
              large density' cardinality'⟩)
        .nil)
    0 0


/-! ## Node `[56]`, the large-budget net-deficiency cap (route-8 arm).

On the `[147]` arm the strict cap of `prop:negative-net-charge` is read from
`K .coldRoute8Below` -- the route-8 carrier inequality `τ(θ) < 3/13 < 1/4` in
its exact form `(δs+1)·(stubs·p + T(n)) + δ·F·s·T(n) < δ·(n − order·p)` -- rather
than from the density cap; it implies the cap
`s·(δ·order·p + T(n)) < s·2(order−1)·p + |R|` outright, with the surplus
allowance already inside the route-8 inequality. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def routeEightNetDeficiencyCapRow :
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
    `Hypostructure.Graph.Strategy.Spine.routeEightNetDeficiencyCap
    { Requires := [K .largeBudgetResidual, K .coldRoute8Below]
      Produces := [K .netDeficiencyCap]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let _residual := (inputs.get (K .largeBudgetResidual)).down
      let below := (inputs.get (K .coldRoute8Below)).down
      .cons (key := K .netDeficiencyCap)
        (show Value BranchState Presentation presentation data
            .netDeficiencyCap inputs.current from
          ⟨by
            intro packing valid cardinality _large
            have canonicalCard :
                (canonicalWindowPacking data inputs.current.object).card =
                  inputs.current.object.windowPackingNumber data.windowOrder :=
              (Classical.choose_spec
                (inputs.current.object.exists_windowPacking_card_eq data.windowOrder)).2
            change (data.threshold * data.dischargeScale + 1) *
                (coldExternalStubCount data *
                  (canonicalWindowPacking data inputs.current.object).card +
                  data.surplusThreshold inputs.current.object.vertexCount) +
                data.threshold * (data.bridgeMassFactor * data.dischargeScale *
                  data.surplusThreshold inputs.current.object.vertexCount) <
              data.threshold * (inputs.current.object.vertexCount -
                data.windowOrder * (canonicalWindowPacking data inputs.current.object).card)
              at below
            rw [canonicalCard, ← cardinality] at below
            have cardinality' :
                (inputs.current.object.remainderSupport packing).card +
                    data.windowOrder * packing.card =
                  inputs.current.object.vertexCount :=
              inputs.current.object.remainderSupport_card_add_eq valid
            have remEq : inputs.current.object.vertexCount -
                data.windowOrder * packing.card =
                (inputs.current.object.remainderSupport packing).card := by omega
            have three := data.threshold_eq_three
            simp only [coldExternalStubCount, Data.surplusThreshold] at below ⊢
            rw [three, remEq] at below
            rw [three]
            obtain ⟨o, ho⟩ : ∃ o, data.windowOrder = o + 1 :=
              ⟨data.windowOrder - 1, by have := data.windowOrder_pos; omega⟩
            rw [ho] at below ⊢
            have stubsEq : 3 * (o + 1) - 2 * (o + 1 - 1) = o + 3 := by omega
            rw [stubsEq] at below
            simp only [Nat.add_sub_cancel] at below ⊢
            nlinarith [below, Nat.zero_le ((o + 3) * packing.card),
              Nat.zero_le (data.spineScale * Core.ceilSqrt inputs.current.object.vertexCount),
              Nat.zero_le (data.bridgeMassFactor * data.dischargeScale *
                (data.spineScale * Core.ceilSqrt inputs.current.object.vertexCount))]⟩)
        .nil)
    0 0

/-! ## Node `[56]`, the large-budget net-deficiency cap (dense arm).

On the `[21]` unrealized residual the manuscript's `τ(θ) < 1/4` reading of
`prop:negative-net-charge` is a decision of its own (`K .denseDeficiencyBelow`,
the exact strict comparison at the fixed maximal packing); this row is node
`[56]` on its yes arm: the same conditional cap for every maximal packing, read
off that decision (all maximal packings have the same size and the same
remainder count `n − order·p`). -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def denseNetDeficiencyCapRow :
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
    `Hypostructure.Graph.Strategy.Spine.denseNetDeficiencyCap
    { Requires := [K .largeBudgetResidual, K .denseDeficiencyBelow]
      Produces := [K .netDeficiencyCap]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let _residual := (inputs.get (K .largeBudgetResidual)).down
      let below := (inputs.get (K .denseDeficiencyBelow)).down
      .cons (key := K .netDeficiencyCap)
        (show Value BranchState Presentation presentation data
            .netDeficiencyCap inputs.current from
          ⟨by
            intro packing valid cardinality _large
            have canonicalCard :
                (canonicalWindowPacking data inputs.current.object).card =
                  inputs.current.object.windowPackingNumber data.windowOrder :=
              (Classical.choose_spec
                (inputs.current.object.exists_windowPacking_card_eq data.windowOrder)).2
            change data.dischargeScale *
                (data.threshold * (data.windowOrder *
                  (canonicalWindowPacking data inputs.current.object).card) +
                  data.spineScale * Core.ceilSqrt inputs.current.object.vertexCount) <
              data.dischargeScale *
                  (2 * (data.windowOrder - 1) *
                    (canonicalWindowPacking data inputs.current.object).card) +
                (inputs.current.object.vertexCount - data.windowOrder *
                  (canonicalWindowPacking data inputs.current.object).card) at below
            rw [canonicalCard, ← cardinality] at below
            have cardinality' :
                data.windowOrder * packing.card +
                    (inputs.current.object.remainderSupport packing).card =
                  inputs.current.object.vertexCount := by
              simpa [Nat.add_comm] using
                inputs.current.object.remainderSupport_card_add_eq valid
            have remainder :
                inputs.current.object.vertexCount - data.windowOrder * packing.card =
                  (inputs.current.object.remainderSupport packing).card := by
              omega
            rw [remainder] at below
            exact below⟩)
        .nil)
    0 0

/-! ## Nodes `[120]`--`[122]`, the private-carrier rate of the route-8 census

`rem:route8-carrier-margin`, `prop:typeA-route8-carrier-reduction`: the rate
`(δs+1)·|∂R| + δ·F·s·T(n) < δ·|R|` (`τ < 3/13` with the `o(|R|)` allowances of the
near-cubic spine).  On the `[147]` arm it is exactly `K .coldRoute8Below` read
through `|∂R| = e(R,W) ≤ stubs·p + σ_W ≤ stubs·p + T(n)`
(`lem:surplus-aware-window-stub`, `Route8.card_cutEdges_eq_boundaryIncidence`,
`σ_W ≤ σ(G) ≤ T(n)`).  On the other spine arms it is decided
(`route8RateDichotomy`): the density cap decides it only for sufficiently large
`n`, and the dense arm's `τ < 1/4` does not decide it at all — the manuscript's
delicate density interval (row 2 of `tab:cold-branch-ledger`). -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def route8RateFromColdBelowRow :
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
    `Hypostructure.Graph.Strategy.Spine.route8RateFromColdBelow
    { Requires := [K .coldRoute8Below, K .surplusAtOrBelow]
      Produces := [K .route8Rate]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let below := (inputs.get (K .coldRoute8Below)).down
      let ceiling := (inputs.get (K .surplusAtOrBelow)).down
      .cons (key := K .route8Rate)
        (show Value BranchState Presentation presentation data
            .route8Rate inputs.current from
          ⟨by
            set object := inputs.current.object with hobj
            set packing := canonicalWindowPacking data object with hpack
            have valid : object.IsWindowPacking data.windowOrder packing :=
              (Classical.choose_spec
                (object.exists_windowPacking_card_eq data.windowOrder)).1
            have baseline : ∀ vertex : object.Vertex, data.threshold ≤ object.degree vertex :=
              fun vertex => le_trans inputs.current.baseline
                (object.minDegree_le_degree vertex)
            -- `lem:surplus-aware-window-stub`'s capacity link, read off the object
            -- (the same derivation node `[28]` publishes).
            have capacity := object.boundaryIncidence_add_internal_mass_le valid baseline
            have windowSurplus :
                object.ambientSurplus (Graph.FiniteObject.windowSupport packing)
                    data.threshold ≤ data.surplusThreshold object.vertexCount :=
              le_trans (object.ambientSurplus_le_degreeSurplus _ data.threshold baseline)
                ceiling
            have supplyEq := Graph.Route8Census.card_supply object packing
            have remainder := object.remainderSupport_card_add_eq valid
            change (data.threshold * data.dischargeScale + 1) *
                (coldExternalStubCount data * packing.card +
                  data.surplusThreshold object.vertexCount) +
                data.threshold * (data.bridgeMassFactor * data.dischargeScale *
                  data.surplusThreshold object.vertexCount) <
              data.threshold * (object.vertexCount - data.windowOrder * packing.card) at below
            change (data.threshold * data.dischargeScale + 1) *
                (Graph.Route8Census.supply object packing).card +
                data.threshold * (data.bridgeMassFactor * data.dischargeScale *
                  data.surplusThreshold object.vertexCount) <
              data.threshold * (object.remainderSupport packing).card
            rw [supplyEq]
            have remEq : object.vertexCount - data.windowOrder * packing.card =
                (object.remainderSupport packing).card := by omega
            rw [remEq] at below
            have debit : 2 * (data.windowOrder - 1) ≤ data.threshold * data.windowOrder := by
              have := data.three_le_threshold
              have := Nat.mul_le_mul_right data.windowOrder this
              omega
            have prod : coldExternalStubCount data * packing.card =
                data.threshold * (data.windowOrder * packing.card) -
                  2 * (data.windowOrder - 1) * packing.card := by
              simp only [coldExternalStubCount]
              rw [Nat.sub_mul, Nat.mul_assoc]
            have debit' : 2 * (data.windowOrder - 1) * packing.card ≤
                data.threshold * (data.windowOrder * packing.card) := by
              have := Nat.mul_le_mul_right packing.card debit
              rw [Nat.mul_assoc data.threshold] at this
              exact this
            have supplyLe : object.boundaryIncidence (object.remainderSupport packing) ≤
                coldExternalStubCount data * packing.card +
                  data.surplusThreshold object.vertexCount := by
              rw [prod]
              omega
            have := Nat.mul_le_mul_left (data.threshold * data.dischargeScale + 1) supplyLe
            omega⟩)
        .nil)
    0 0

/-! The rate reading as a decision (`rem:route8-carrier-margin` on an arm whose
density fact does not decide it): `K .route8Rate` or its exact complement. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
noncomputable def route8RateDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : @FactKeys (Input BranchState Presentation presentation data)
      _ (factSystem BranchState Presentation presentation data)}
    (previous :
      @ExactLedger (Input BranchState Presentation presentation data)
        _ (factSystem BranchState Presentation presentation data) current known)
    [@Core.Residual.FactKeys.Has
      (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data)
      (K .selection) known]
    (rateFresh : K .route8Rate ∉ known)
    (failsFresh : K .route8RateFails ∉ known) :
    @Decision (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data) current known
      (K .route8Rate) (K .route8RateFails) previous :=
  @Decision.run (Input BranchState Presentation presentation data) _
    (factSystem BranchState Presentation presentation data) current known
    previous (K .route8Rate) (K .route8RateFails)
    `Hypostructure.Graph.Strategy.Spine.route8RateDichotomy
    (by
      classical
      let _selected := (@ExactLedger.get
        (Input BranchState Presentation presentation data) _
        (factSystem BranchState Presentation presentation data)
        current known previous (K .selection)).down
      exact if rate : Graph.Route8Census.Rate current.object
          (canonicalWindowPacking data current.object) data.threshold data.dischargeScale
          (data.bridgeMassFactor * data.dischargeScale *
            data.surplusThreshold current.object.vertexCount) then
        .inl ⟨rate⟩
      else
        .inr ⟨rate⟩)
    rateFresh failsFresh

/-! Nodes `[111]`--`[113]`, `[120]`: the census is its two readings on one
ledger. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def route8CensusRow :
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
    `Hypostructure.Graph.Strategy.Spine.route8Census
    { Requires := [K .route8Deficit, K .route8Rate]
      Produces := [K .route8Census]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let deficit := (inputs.get (K .route8Deficit)).down
      let rate := (inputs.get (K .route8Rate)).down
      .cons (key := K .route8Census)
        (show Value BranchState Presentation presentation data
            .route8Census inputs.current from ⟨⟨deficit, rate⟩⟩)
        .nil)
    0 0

/-! ## Node `[52]`: window plus remainder accounting

`prop:two-budget` (a) and the high-entropy half of `prop:p13-density`.  The
window package of node `[21]` and the remainder states of node `[51]` are one
target-testable family, and `eq:feasibility` compares the states it realizes
against the near-cubic skeleton budget.  The forced curvature cost of node
`[48]` is `def:Theta`'s sharpening, which `rem:closure-robust` says the closure
does not need and which is realized by remainder graphs already counted in the
remainder class; it is not a further factor of the demand.

This row commits the *demand* side of that comparison, exactly: raising the
joint demand to the `d`-th power clears the `1/d` the entropy split carries, and
substituting the high-entropy arm's own `n^{|R|} ≤ |𝒢(R)|^d` for the remainder
factor gives the manuscript's `2^{rate·p}·n^{|R|/d}`.  No independence
hypothesis is used to state a lower bound on what the branch has to distinguish;
the budget side is node `[53]`'s comparison. -/
@[reducible] noncomputable def entropyPackageRow
    (data : Data.{u}) :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.entropyPackageDemand
    { Requires := [K .remainderEntropyHigh]
      Produces := [K .entropyPackageDemand]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .entropyPackageDemand)
        (show Value BranchState Presentation presentation data
            .entropyPackageDemand inputs.current from
          ⟨by
            simp only [Holds]
            have packingSpec := Classical.choose_spec
              (inputs.current.object.exists_windowPacking_card_eq data.windowOrder)
            have high :=
              (inputs.get (K .remainderEntropyHigh)).down
                (canonicalWindowPacking data inputs.current.object) packingSpec.1
            rw [jointPackageDemand, mul_pow]
            exact Nat.mul_le_mul (le_refl _) high⟩)
        .nil)

/-! ## Node `[53]`: the admissible entropy cap, and its terminal `[54]`

`eq:entropy-cap`: no residual graph exists once the remaining non-curvature
budget is strictly smaller than the forced curvature cost.  In exact integer
form that is the joint package demand of node `[52]` against the labelled
skeleton budget of `lem:near-cubic-budget`, which is the same budget node
`[21]` already compared the window package against.

The comparison is a `Nat` trichotomy, so the two arms are exhaustive.  The yes
arm is the manuscript's node `[54]`; the no arm is node `[55]`, Residual C. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
noncomputable def entropyCapDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : @FactKeys (Input BranchState Presentation presentation data)
      _ (factSystem BranchState Presentation presentation data)}
    (previous :
      @ExactLedger (Input BranchState Presentation presentation data)
        _ (factSystem BranchState Presentation presentation data) current known)
    [@FactKeys.Has (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data)
      (K .entropyPackageDemand) known]
    (activeFresh : K .entropyCapActive ∉ known)
    (largeFresh : K .largeBudgetResidual ∉ known) :
    @Decision (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data) current known
      (K .entropyCapActive) (K .largeBudgetResidual) previous :=
  @Decision.run (Input BranchState Presentation presentation data) _
    (factSystem BranchState Presentation presentation data) current known
    previous (K .entropyCapActive) (K .largeBudgetResidual)
    `Hypostructure.Graph.Strategy.Spine.entropyCapDichotomy
    (by
      classical
      have _packageDemand :=
        (@ExactLedger.get (Input BranchState Presentation presentation data) _
          (factSystem BranchState Presentation presentation data)
          current known previous (K .entropyPackageDemand)).down
      by_cases active :
          Graph.skeletonBudget current.object < jointPackageDemand data current.object
      · exact .inl ⟨active⟩
      · exact .inr ⟨Or.inl (Nat.le_of_not_lt active)⟩)
    activeFresh largeFresh

/-! ## Node `[57]` = `[173]`: the exact collision test

`lem:exact-collision-test`.  Node `[56]`'s collision is an inequality of the
current object — with the actual surpluses, the actual hot and cold window
counts, and the exact skeleton budget — and node `[173]` decides it on the
object: `def⁺(R) − σ_R < |R|/s` at every maximal packing (`NegativeNetCharge`),
which is exactly `K .netChargeCap`.  Its yes arm continues at `[58]`; its no arm
is the absorbed-germ residual `[174]` (`K .exactCollisionFails`).  No condition
on `n` is used (`rem:no-sufficient-order`): the sufficient-order reading of
node `[57]` and the cap row that consumed it are gone. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
noncomputable def exactCollisionDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : @FactKeys (Input BranchState Presentation presentation data)
      _ (factSystem BranchState Presentation presentation data)}
    (previous :
      @ExactLedger (Input BranchState Presentation presentation data)
        _ (factSystem BranchState Presentation presentation data) current known)
    (capFresh : K .netChargeCap ∉ known)
    (failsFresh : K .exactCollisionFails ∉ known) :
    @Decision (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data) current known
      (K .netChargeCap) (K .exactCollisionFails) previous :=
  @Decision.run (Input BranchState Presentation presentation data) _
    (factSystem BranchState Presentation presentation data) current known
    previous (K .netChargeCap) (K .exactCollisionFails)
    `Hypostructure.Graph.Strategy.Spine.exactCollisionDichotomy
    (by
      classical
      exact if holds : ∀ packing : Finset (Finset current.object.Vertex),
          current.object.IsWindowPacking data.windowOrder packing →
            packing.card = current.object.windowPackingNumber data.windowOrder →
              current.object.NegativeNetCharge (current.object.remainderSupport packing)
                data.threshold data.dischargeScale then
        .inl ⟨holds⟩
      else
        .inr ⟨by
          push_neg at holds
          obtain ⟨packing, valid, cardinality, notNegative⟩ := holds
          exact ⟨packing, valid, cardinality,
            (Graph.FiniteObject.not_negativeNetCharge_iff current.object _ _ _).1
              notNegative⟩⟩)
    capFresh failsFresh

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
    (data : Data.{u}) :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.netChargeLocalization
    { Requires := []
      Produces := [K .netChargeLocalization]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .netChargeLocalization)
        (show Value BranchState Presentation presentation data
            .netChargeLocalization inputs.current from
          ⟨fun packing _valid negative =>
            inputs.current.object.exists_canonicalPiece_negativeNetCharge
              (inputs.current.object.remainderSupport packing) data.threshold
              data.dischargeScale negative⟩)
        .nil)

/-! ## Node `[59]`: the net-charge sign test

`N₀(R) ≥ 0?`  Here `R` is the complement of the one maximum packing selected
at node `[27]`, not a quantifier over every maximal packing.  The executor reads
that witness from `K .maximalPacking`, decides its exact integer charge, and
carries the same packing in either branch fact.  The yes arm is the manuscript's
node `[60]`; the no arm is node `[61]`, where a connected negative support is
selected.  The decision itself does not close `[60]`: that terminal additionally
uses the strict net-cap estimate of `prop:negative-net-charge`. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
noncomputable def netChargeDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : @FactKeys (Input BranchState Presentation presentation data)
      _ (factSystem BranchState Presentation presentation data)}
    (previous :
      @ExactLedger (Input BranchState Presentation presentation data)
        _ (factSystem BranchState Presentation presentation data) current known)
    [@FactKeys.Has (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data)
      (K .maximalPacking) known]
    (nonNegativeFresh : K .netChargeNonNegative ∉ known)
    (negativeFresh : K .netChargeNegative ∉ known) :
    @Decision (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data) current known
      (K .netChargeNonNegative) (K .netChargeNegative) previous :=
  @Decision.run (Input BranchState Presentation presentation data) _
    (factSystem BranchState Presentation presentation data) current known
    previous (K .netChargeNonNegative) (K .netChargeNegative)
    `Hypostructure.Graph.Strategy.Spine.netChargeDichotomy
    (by
      classical
      have selected :=
        (@ExactLedger.get (Input BranchState Presentation presentation data) _
          (factSystem BranchState Presentation presentation data)
          current known previous (K .maximalPacking)).down
      let packing := Classical.choose selected.2
      have packingSpec := Classical.choose_spec selected.2
      have valid := packingSpec.1
      have cardinality := packingSpec.2.1
      have maximal := packingSpec.2.2
      by_cases nonNegative : current.object.NonNegativeNetCharge
          (current.object.remainderSupport packing) data.threshold
          data.dischargeScale
      · exact .inl ⟨packing, valid, cardinality, maximal, nonNegative⟩
      · exact .inr ⟨packing, valid, cardinality, maximal,
          Nat.lt_of_not_le nonNegative⟩)
    nonNegativeFresh negativeFresh

/-! ## Node `[61]`: the selected connected negative support

`prop:negative-net-charge`.  The negative arm of node `[59]` already contains
the canonical maximal packing and its negative remainder.  Node `[57]`--`[58]`
localizes that charge through the canonical component decomposition.  This row
reads exactly those two facts and appends only the selected connected negative
piece and its containment in the same remainder. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def negativeSupportRow
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
    `Hypostructure.Graph.Strategy.Spine.negativeSupport
    { Requires := [K .netChargeNegative, K .netChargeLocalization]
      Produces := [K .negativeSupport]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .negativeSupport)
        (show Value BranchState Presentation presentation data
            .negativeSupport inputs.current from ⟨by
          obtain ⟨packing, valid, _cardinality, maximal, negative⟩ :=
            (inputs.get (K .netChargeNegative)).down
          obtain ⟨component, present, charge⟩ :=
            (inputs.get (K .netChargeLocalization)).down packing valid negative
          exact ⟨packing, valid, maximal, component, present, charge⟩⟩)
        .nil)
    0 0

/-! ## Node `[62]`: the Type A / Type B split

The selected negative support either carries assigned high-degree surplus or it
does not.  The no arm is node `[63]`, the Type A low-deficiency atom branch; the
yes arm is node `[64]`, the Type B high-degree fan-safe support branch.

The split is decided on the *selected* support's own assigned surplus, which is
what `def:canonical-decomp`'s assignment credits to it -- not on the whole
remainder's.  Both arms carry the support's existence forward with the clause
that distinguishes them, so a consumer of either arm reads a support of the kind
its branch is about and cannot read the other. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
noncomputable def typeSplitDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : @FactKeys (Input BranchState Presentation presentation data)
      _ (factSystem BranchState Presentation presentation data)}
    (previous :
      @ExactLedger (Input BranchState Presentation presentation data)
        _ (factSystem BranchState Presentation presentation data) current known)
    [@FactKeys.Has (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data)
      (K .negativeSupport) known]
    (typeAFresh : K .typeALowSurplus ∉ known)
    (typeBFresh : K .typeBHighSurplus ∉ known) :
    @Decision (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data) current known
      (K .typeALowSurplus) (K .typeBHighSurplus) previous :=
  @Decision.run (Input BranchState Presentation presentation data) _
    (factSystem BranchState Presentation presentation data) current known
    previous (K .typeALowSurplus) (K .typeBHighSurplus)
    `Hypostructure.Graph.Strategy.Spine.typeSplitDichotomy
    (by
      classical
      have support :=
        (@ExactLedger.get (Input BranchState Presentation presentation data) _
          (factSystem BranchState Presentation presentation data)
          current known previous (K .negativeSupport)).down
      let packing := Classical.choose support
      have packingSpec := Classical.choose_spec support
      have valid := packingSpec.1
      have maximal := packingSpec.2.1
      let component := Classical.choose packingSpec.2.2
      have componentSpec := Classical.choose_spec packingSpec.2.2
      have present := componentSpec.1
      have charge := componentSpec.2
      let piece := current.object.pieceSupport
        (current.object.remainderSupport packing) component
      by_cases zero : current.object.ambientSurplus piece data.threshold = 0
      · exact .inl ⟨packing, valid, maximal, component, present, charge, zero⟩
      · exact .inr ⟨packing, valid, maximal, component, present, charge,
          Nat.pos_of_ne_zero zero⟩)
    typeAFresh typeBFresh

/-! ## Node `[67]`, the standing law: the high-neighbourhood normal form

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
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def cubicBaselineRow
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
    `Hypostructure.Graph.Strategy.Spine.cubicBaseline
    { Requires := []
      Produces := [K .cubicBaseline]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun _inputs =>
      .cons (key := K .cubicBaseline) ⟨data.threshold_eq_three⟩ .nil)
    0 0

@[reducible] noncomputable def highCentreNormalFormRow
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
    `Hypostructure.Graph.Strategy.Spine.highCentreNormalForm
    { Requires := [K .selection, K .tightEndpoint]
      Produces := [K .highCentreNormalForm]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let tight := (inputs.get (K .tightEndpoint)).down
      let avoids := (inputs.get (K .selection)).down.1
      .cons (key := K .highCentreNormalForm)
        ⟨fun centre high =>
          { neighbourTight := by
              intro x adjacent
              rcases tight ⟨(centre, x), adjacent⟩ with centreTight | endpointTight
              · exact absurd centreTight (Nat.ne_of_gt high)
              · exact endpointTight
            inducedMatching := by
              intro x y z centreX centreY centreZ distinct xy yz
              exact Graph.not_quadrilateral avoids data.quadrilateralAccepted
                centreX xy yz centreZ.symm centreY.ne distinct
            noCommonNeighbourOutside := by
              intro x y z centreX centreY distinct _nonadjacent outside xz yz
              exact Graph.not_quadrilateral avoids data.quadrilateralAccepted
                centreX xz yz.symm centreY.symm (Ne.symm outside) distinct }⟩
        .nil)
    0 0

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
omit [FactSystem (Input BranchState Presentation presentation data)] in
noncomputable def heavyCentreDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : @FactKeys (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data)}
    (previous :
      @ExactLedger (Input BranchState Presentation presentation data) _
        (factSystem BranchState Presentation presentation data) current known)
    [@FactKeys.Has (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data)
      (K .typeBDecoratedAssignedSupport) known]
    (heavyFresh : K .typeBHeavyCentre ∉ known)
    (degreeFourFresh : K .typeBDegreeFourCentres ∉ known) :
    @Decision (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data) current known
      (K .typeBHeavyCentre) (K .typeBDegreeFourCentres) previous :=
  @Decision.run (Input BranchState Presentation presentation data) _
    (factSystem BranchState Presentation presentation data) current known
    previous (K .typeBHeavyCentre) (K .typeBDegreeFourCentres)
    `Hypostructure.Graph.Strategy.Spine.heavyCentreDichotomy
    (by
      classical
      apply Classical.choice
      obtain ⟨packing, valid, maximal, component, present, negative, zero,
        receiver, isReceiver, peeled, peeledSubset, saturated, noExitFour,
        noCompression, noDelocalization, envelope, coreEq, nonempty, high,
        assigned, _admissible⟩ :=
        (@ExactLedger.get (Input BranchState Presentation presentation data) _
          (factSystem BranchState Presentation presentation data)
          current known previous (K .typeBDecoratedAssignedSupport)).down
      have highRegistered : ∀ centre ∈ envelope.decorations,
          data.threshold < current.object.degree centre := by
        intro centre member
        simpa [Graph.IsHighCentre] using high centre member
      by_cases heavy :
          ∃ centre ∈ envelope.decorations,
            data.threshold + 1 < current.object.degree centre
      · exact ⟨.inl ⟨packing, valid, maximal, component, present, negative,
          zero, receiver, isReceiver, peeled, peeledSubset, saturated,
          noExitFour, noCompression, noDelocalization,
          ⟨envelope, coreEq, nonempty, highRegistered, assigned, heavy⟩⟩⟩
      · refine ⟨.inr ⟨packing, valid, maximal, component, present, negative,
          zero, receiver, isReceiver, peeled, peeledSubset, saturated,
          noExitFour, noCompression, noDelocalization,
          ⟨envelope, coreEq, nonempty, highRegistered, assigned, ?_⟩⟩⟩
        intro centre member
        have lower := highRegistered centre member
        have upper : ¬ data.threshold + 1 < current.object.degree centre :=
          fun above => heavy ⟨centre, member, above⟩
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

omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def heavyCentreLocalDichotomyRow
    : @AtomicStrategy (Input BranchState Presentation presentation data) _
        (factSystem BranchState Presentation presentation data) :=
  letI : FactSystem (Input BranchState Presentation presentation data) :=
    factSystem BranchState Presentation presentation data
  @factOnly (Input BranchState Presentation presentation data) _
    (factSystem BranchState Presentation presentation data)
    `Hypostructure.Graph.Strategy.Spine.heavyCentreLocalDichotomy
    { Requires := [K .cubicBaseline, K .highCentreNormalForm,
        K .typeBHeavyCentre]
      Produces := [K .typeBLocalDichotomy]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let baseline := (inputs.get (K .cubicBaseline)).down
      let normal := (inputs.get (K .highCentreNormalForm)).down
      let heavy := (inputs.get (K .typeBHeavyCentre)).down
      .cons (key := K .typeBLocalDichotomy)
        ⟨by
          obtain ⟨packing, valid, maximal, component, present, negative, zero,
            receiver, isReceiver, peeled, peeledSubset, saturated, noExitFour,
            noCompression, noDelocalization, envelope, coreEq, nonempty, high,
            assigned, heavyWitness⟩ := heavy
          refine ⟨packing, valid, maximal, component, present, negative, zero,
            receiver, isReceiver, peeled, peeledSubset, saturated, noExitFour,
            noCompression, noDelocalization,
            ⟨envelope, coreEq, nonempty, high, assigned, heavyWitness, ?_⟩⟩
          intro centre member centreHeavy
          have highCentre :
              Graph.IsHighCentre inputs.current.object data.threshold centre := by
            simpa [Graph.IsHighCentre] using high centre member
          rcases Graph.heavyCentreLocalDichotomy
              (normal centre highCentre) with compatible | triangular
          · exact Or.inl compatible
          · exact Or.inr ⟨triangular, by
              have degreeLower : data.threshold + 2 ≤
                  inputs.current.object.degree centre := by omega
              have subLower : data.threshold ≤
                  inputs.current.object.degree centre - 2 := by omega
              have cardLower : data.threshold ≤
                  (Graph.triangularEndpoints inputs.current.object centre).card :=
                le_trans subLower triangular
              rw [baseline] at cardLower
              exact cardLower⟩⟩
        .nil)
    0 0

/-! ## Nodes `[64]`--`[65]`, `[68]`, `[69]` at the ordinary Type B entry

Node `[62]`'s yes arm enters `[64]` with an admissible support `X` carrying
assigned surplus (`K .typeBHighSurplus`).  `def:canonical-decomp` assigns every
surplus unit `d_G(h) − 3` of a high centre `h ∈ V_{≥4}(G) ∩ V(R)` to the piece
containing `h`, so `σ(X) = Σ_{h ∈ X}(d_G(h) − δ)` and `σ(X) > 0` says `X` has a
high centre: node `[65]`'s *assigned support* is `X` with its own high centres as
fan centres, each with fan `N_G(h)` (the ordinary adjacent fan,
`def:decorated-fan-envelope`'s special case `ℓ(a) = 0`; the decorated handoff
data belong to the `[66]` input from Type A exit `(7)`, whose own rows sit
above).  Node `[67]` is `lem:heavy-neighbourhood-normal-form`
(`highCentreNormalFormRow`, stated of the object).  Node `[68]` asks whether some
assigned fan centre is heavy — degree above the high-centre degree `δ + 1` — and
`[69]` is `cor:heavy-center-local-dichotomy` at every heavy fan centre.  Every
fact is stated at every ordinary Type B support the object carries
(`TypeBSupportWith`), because a support is data. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def typeBAssignedSupportRow :
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
    `Hypostructure.Graph.Strategy.Spine.typeBAssignedSupport
    { Requires := [K .typeBHighSurplus]
      Produces := [K .typeBAssignedSupport, K .typeBFanEntry]
      requiresUnique := by simp
      producesUnique := by simp [K_eq_iff]
      producesNonempty := by simp }
    (fun inputs =>
      let typeB := (inputs.get (K .typeBHighSurplus)).down
      -- `σ(X) = Σ_{v ∈ X}(d_G(v) − δ) > 0` forces a vertex above the baseline:
      -- otherwise every summand is zero.
      let highCentre : ∀ packing component,
          inputs.current.object.IsWindowPacking data.windowOrder packing →
          0 < inputs.current.object.ambientSurplus
            (inputs.current.object.pieceSupport
              (inputs.current.object.remainderSupport packing) component)
            data.threshold →
          ∃ centre ∈ inputs.current.object.pieceSupport
              (inputs.current.object.remainderSupport packing) component,
            Graph.IsHighCentre inputs.current.object data.threshold centre := by
        intro packing component _valid positive
        classical
        by_contra none
        push Not at none
        have zero : inputs.current.object.ambientSurplus
            (inputs.current.object.pieceSupport
              (inputs.current.object.remainderSupport packing) component)
            data.threshold = 0 := by
          unfold Graph.FiniteObject.ambientSurplus
          refine Finset.sum_eq_zero fun vertex member => ?_
          have := none vertex member
          simp only [Graph.IsHighCentre, not_lt] at this
          omega
        omega
      .cons (key := K .typeBAssignedSupport)
        (show Value BranchState Presentation presentation data
            .typeBAssignedSupport inputs.current from
          ⟨by
            obtain ⟨packing, valid, maximal, component, present, charge, positive⟩ :=
              typeB
            exact ⟨packing, valid, maximal, component, present, charge, positive,
              highCentre packing component valid positive⟩⟩)
        (.cons (key := K .typeBFanEntry)
          (show Value BranchState Presentation presentation data
              .typeBFanEntry inputs.current from
            ⟨by
              classical
              obtain ⟨packing, valid, maximal, component, present, charge, positive⟩ :=
                typeB
              obtain ⟨centre, member, high⟩ := highCentre packing component valid positive
              refine ⟨packing, valid, maximal, component, present,
                Graph.TypeBRefinedSupport.centres inputs.current.object data.threshold
                  (inputs.current.object.pieceSupport
                    (inputs.current.object.remainderSupport packing) component),
                Or.inl ⟨charge, positive, rfl⟩, ?_, ?_⟩
              · exact ⟨centre, Graph.TypeBRefinedSupport.mem_centres.2 ⟨member, high⟩⟩
              · intro vertex vertexMem
                exact (Graph.TypeBRefinedSupport.mem_centres.1 vertexMem).2⟩)
          .nil))
    0 0

omit [FactSystem (Input BranchState Presentation presentation data)] in
noncomputable def typeBFanDegreeDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : @FactKeys (Input BranchState Presentation presentation data) _
      (instFactSystem (BranchState := BranchState)
        (Presentation := Presentation) (presentation := presentation)
        (data := data))}
    (previous :
      @ExactLedger (Input BranchState Presentation presentation data) _
        (instFactSystem (BranchState := BranchState)
          (Presentation := Presentation) (presentation := presentation)
          (data := data)) current known)
    [@FactKeys.Has (Input BranchState Presentation presentation data) _
      (instFactSystem (BranchState := BranchState)
        (Presentation := Presentation) (presentation := presentation)
        (data := data)) (K .typeBAssignedSupport) known]
    (heavyFresh : K .typeBFanHeavyCentre ∉ known)
    (degreeFourFresh : K .typeBFanDegreeFourCentres ∉ known) :
    @Decision (Input BranchState Presentation presentation data) _
      (instFactSystem (BranchState := BranchState)
        (Presentation := Presentation) (presentation := presentation)
        (data := data)) current known
      (K .typeBFanHeavyCentre) (K .typeBFanDegreeFourCentres) previous :=
  letI : FactSystem (Input BranchState Presentation presentation data) :=
    instFactSystem (BranchState := BranchState) (Presentation := Presentation)
      (presentation := presentation) (data := data)
  Decision.run previous (K .typeBFanHeavyCentre) (K .typeBFanDegreeFourCentres)
    `Hypostructure.Graph.Strategy.Spine.typeBFanDegreeDichotomy
    (by
      classical
      apply Classical.choice
      obtain ⟨packing, valid, maximal, component, present, charge, positive, centres⟩ :=
        (ExactLedger.get previous (K .typeBAssignedSupport)).down
      let piece := current.object.pieceSupport
        (current.object.remainderSupport packing) component
      by_cases heavy : ∃ centre ∈ piece, data.threshold + 1 < current.object.degree centre
      · exact ⟨.inl ⟨packing, valid, maximal, component, present, charge, positive,
          centres, heavy⟩⟩
      · refine ⟨.inr ⟨packing, valid, maximal, component, present, charge, positive,
          centres, ?_⟩⟩
        intro centre member high
        have upper : ¬ data.threshold + 1 < current.object.degree centre :=
          fun above => heavy ⟨centre, member, above⟩
        simp only [Graph.IsHighCentre] at high
        omega)
    heavyFresh degreeFourFresh

omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def typeBFanLocalDichotomyRow :
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
    `Hypostructure.Graph.Strategy.Spine.typeBFanLocalDichotomy
    { Requires := [K .highCentreNormalForm, K .typeBFanHeavyCentre]
      Produces := [K .typeBFanLocalDichotomy]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let normal := (inputs.get (K .highCentreNormalForm)).down
      let heavy := (inputs.get (K .typeBFanHeavyCentre)).down
      .cons (key := K .typeBFanLocalDichotomy)
        (show Value BranchState Presentation presentation data
            .typeBFanLocalDichotomy inputs.current from
          ⟨by
            obtain ⟨packing, valid, maximal, component, present, charge, positive,
              _centres, heavyWitness⟩ := heavy
            refine ⟨packing, valid, maximal, component, present, charge, positive,
              heavyWitness, ?_⟩
            intro centre _member centreHeavy
            have highCentre :
                Graph.IsHighCentre inputs.current.object data.threshold centre := by
              simp only [Graph.IsHighCentre]
              omega
            rcases Graph.heavyCentreLocalDichotomy (normal centre highCentre) with
              compatible | triangular
            · exact Or.inl compatible
            · exact Or.inr ⟨triangular,
                Graph.three_le_triangularEndpoints_card data.three_le_threshold
                  centreHeavy triangular⟩⟩)
        .nil)
    0 0

/-! ## Nodes `[78]`--`[79]` at the ordinary Type B entry: the degree-four fan profile

`cor:degree-four-local-activation` and the profile Part VII's panel opens with, on
the ordinary Type B support of node `[64]`.  Node `[78]` is the no arm of `[68]`,
already committed (`K .typeBFanDegreeFourCentres`): every assigned fan centre of
the support sits exactly at `δ + 1`.  This row reads that law and the normal form
and commits `[79]`'s readings at every such centre: the activation dichotomy is
`Graph.heavyCentreLocalDichotomy` — the same theorem `[69]` uses — with `k = δ + 1`
giving `δ − 1` triangular ports (the manuscript's "at least `4 − |U| ≥ 2`"), and
the three readings are `TypeBFanIncidence.degreeFourProfile`: centre surplus `1`,
`c ≤ k`, and `D_B = c − (δ − (k+1)α)` at the registered discharge scale; nothing
writes `7/4`. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def typeBFanDegreeFourProfileRow :
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
    `Hypostructure.Graph.Strategy.Spine.typeBFanDegreeFourProfile
    { Requires := [K .highCentreNormalForm, K .typeBFanDegreeFourCentres]
      Produces := [K .typeBFanDegreeFourProfile]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let normal := (inputs.get (K .highCentreNormalForm)).down
      let degreeFour := (inputs.get (K .typeBFanDegreeFourCentres)).down
      .cons (key := K .typeBFanDegreeFourProfile)
        (show Value BranchState Presentation presentation data
            .typeBFanDegreeFourProfile inputs.current from
          ⟨by
            obtain ⟨packing, valid, maximal, component, present, charge, positive,
              centres, degrees⟩ := degreeFour
            refine ⟨packing, valid, maximal, component, present, charge, positive,
              centres, ?_⟩
            intro centre member high
            have degree := degrees centre member high
            refine ⟨degree, ?_, ?_, ?_⟩
            · rcases Graph.heavyCentreLocalDichotomy (normal centre high) with
                compatible | triangular
              · exact Or.inl compatible
              · refine Or.inr ?_
                rw [degree] at triangular
                omega
            · omega
            · intro fanEnvelope
              obtain ⟨_surplus, counted, identity, _range⟩ :=
                Graph.TypeBFanIncidence.degreeFourProfile inputs.current.object
                  data.threshold data.dischargeScale fanEnvelope degree
              exact ⟨counted, identity⟩⟩)
        .nil)
    0 0

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
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def fanCertificateCapRow :
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
    `Hypostructure.Graph.Strategy.Spine.fanCertificateCap
    (sourceFreeManifest (K .fanCertificateCap))
    (fun inputs =>
      .cons (key := K .fanCertificateCap)
        (show Value BranchState Presentation presentation data
            .fanCertificateCap inputs.current from
          ⟨fun _centre _high marking => marking.degree_le_fanPackingCap⟩)
        .nil)
    0 0

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
omit [FactSystem (Input BranchState Presentation presentation data)] in
noncomputable def fanCertificateDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : @FactKeys (Input BranchState Presentation presentation data) _
      (instFactSystem (BranchState := BranchState)
        (Presentation := Presentation) (presentation := presentation)
        (data := data))}
    (previous :
      @ExactLedger (Input BranchState Presentation presentation data) _
        (instFactSystem (BranchState := BranchState)
          (Presentation := Presentation) (presentation := presentation)
          (data := data)) current known)
    [@FactKeys.Has (Input BranchState Presentation presentation data) _
      (instFactSystem (BranchState := BranchState)
        (Presentation := Presentation) (presentation := presentation)
        (data := data)) (K .typeBFanEntry) known]
    (markedFresh : K .fanCertificateMarked ∉ known)
    (residualFresh : K .fanCertificateResidual ∉ known) :
    @Decision (Input BranchState Presentation presentation data) _
      (instFactSystem (BranchState := BranchState)
        (Presentation := Presentation) (presentation := presentation)
        (data := data)) current known
      (K .fanCertificateMarked) (K .fanCertificateResidual) previous :=
  letI : FactSystem (Input BranchState Presentation presentation data) :=
    instFactSystem (BranchState := BranchState) (Presentation := Presentation)
      (presentation := presentation) (data := data)
  Decision.run previous (K .fanCertificateMarked) (K .fanCertificateResidual)
    `Hypostructure.Graph.Strategy.Spine.fanCertificateDichotomy
    (by
      classical
      apply Classical.choice
      obtain ⟨packing, valid, maximal, component, present, centres, assigned,
        _nonempty, high⟩ := (ExactLedger.get previous (K .typeBFanEntry)).down
      by_cases marked :
          ∀ centre ∈ centres,
            Nonempty (Graph.FanCertificateLabelling current.object
              data.windowOrder centre)
      · exact ⟨.inl ⟨packing, valid, maximal, component, present, centres, assigned,
          marked⟩⟩
      · refine ⟨.inr ⟨?_⟩⟩
        -- Not every assigned centre is marked, so one of them is a
        -- fan-certificate residual centre.
        push Not at marked
        obtain ⟨centre, member, unmarked⟩ := marked
        exact ⟨packing, valid, maximal, component, present, centres, assigned,
          centre, member, high centre member, unmarked⟩)
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
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def hybridEntryRow :
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
    `Hypostructure.Graph.Strategy.Spine.hybridEntry
    { Requires := [K .selection, K .fanCertificateCap, K .fanCertificateMarked]
      Produces := [K .typeBHybridEntry]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs => Classical.choice <| by
      let avoids := (inputs.get (K .selection)).down.1
      let cap := (inputs.get (K .fanCertificateCap)).down
      obtain ⟨packing, valid, maximal, component, present, centres, assigned,
          marked⟩ := (inputs.get (K .fanCertificateMarked)).down
      exact ⟨.cons (key := K .typeBHybridEntry)
        (⟨packing, valid, maximal, component, present, centres, assigned,
          fun centre member high envelope windowSupport => by
            -- The marked fan's cap, and with it the manuscript's `k ≤ 8`.
            obtain ⟨marking⟩ :=
              marked centre member
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
    0 0

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

omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def degreeFourProfileRow
    : @AtomicStrategy (Input BranchState Presentation presentation data) _
        (factSystem BranchState Presentation presentation data) :=
  letI : FactSystem (Input BranchState Presentation presentation data) :=
    factSystem BranchState Presentation presentation data
  @factOnly (Input BranchState Presentation presentation data) _
    (factSystem BranchState Presentation presentation data)
    `Hypostructure.Graph.Strategy.Spine.degreeFourProfile
    { Requires := [K .cubicBaseline, K .highCentreNormalForm,
        K .typeBDegreeFourCentres]
      Produces := [K .typeBDegreeFourProfile]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let baseline := (inputs.get (K .cubicBaseline)).down
      let normal := (inputs.get (K .highCentreNormalForm)).down
      let degreeFour := (inputs.get (K .typeBDegreeFourCentres)).down
      .cons (key := K .typeBDegreeFourProfile)
        ⟨by
          obtain ⟨packing, valid, maximal, component, present, negative, zero,
            receiver, isReceiver, peeled, peeledSubset, saturated, noExitFour,
            noCompression, noDelocalization, envelope, coreEq, nonempty, high,
            assigned, degrees⟩ := degreeFour
          refine ⟨packing, valid, maximal, component, present, negative, zero,
            receiver, isReceiver, peeled, peeledSubset, saturated, noExitFour,
            noCompression, noDelocalization,
            ⟨envelope, coreEq, nonempty, high, assigned, degrees, ?_⟩⟩
          intro centre member
          have degree := degrees centre member
          have degreeThreshold :
              inputs.current.object.degree centre = data.threshold + 1 := by
            exact degree
          have highCentre :
              Graph.IsHighCentre inputs.current.object data.threshold centre := by
            simpa [Graph.IsHighCentre] using high centre member
          refine ⟨?_, ?_, ?_⟩
          · rcases Graph.heavyCentreLocalDichotomy
                (normal centre highCentre) with compatible | triangular
            · exact Or.inl compatible
            · exact Or.inr (by
                have thresholdThree : data.threshold = 3 := baseline
                omega)
          · omega
          · intro fanEnvelope
            obtain ⟨_surplus, counted, identity, _range⟩ :=
              Graph.TypeBFanIncidence.degreeFourProfile inputs.current.object
                data.threshold data.dischargeScale fanEnvelope degreeThreshold
            exact ⟨counted, identity⟩⟩
        .nil)
    0 0

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
omit [FactSystem (Input BranchState Presentation presentation data)] in
noncomputable def directCycleDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : @FactKeys (Input BranchState Presentation presentation data) _
      (instFactSystem (BranchState := BranchState)
        (Presentation := Presentation) (presentation := presentation)
        (data := data))}
    (previous :
      @ExactLedger (Input BranchState Presentation presentation data) _
        (instFactSystem (BranchState := BranchState)
          (Presentation := Presentation) (presentation := presentation)
          (data := data)) current known)
    [@FactKeys.Has (Input BranchState Presentation presentation data) _
      (instFactSystem (BranchState := BranchState)
        (Presentation := Presentation) (presentation := presentation)
        (data := data)) (K .fanCertificateMarked) known]
    (cycleFresh : K .typeBDirectCycle ∉ known)
    (freeFresh : K .typeBDirectCycleFree ∉ known) :
    @Decision (Input BranchState Presentation presentation data) _
      (instFactSystem (BranchState := BranchState)
        (Presentation := Presentation) (presentation := presentation)
        (data := data)) current known
      (K .typeBDirectCycle) (K .typeBDirectCycleFree) previous :=
  letI : FactSystem (Input BranchState Presentation presentation data) :=
    instFactSystem (BranchState := BranchState) (Presentation := Presentation)
      (presentation := presentation) (data := data)
  Decision.run previous (K .typeBDirectCycle) (K .typeBDirectCycleFree)
    `Hypostructure.Graph.Strategy.Spine.directCycleDichotomy
    (by
      classical
      apply Classical.choice
      obtain ⟨packing, valid, maximal, component, present, centres, assigned,
        _marked⟩ := (ExactLedger.get previous (K .fanCertificateMarked)).down
      by_cases configuration :
          ∃ centre ∈ centres,
            Graph.IsHighCentre current.object data.threshold centre ∧
              Graph.TypeBDirectCycle.DirectCycleConfiguration current.object
                data.windowOrder data.LengthOK packing centre
      · exact ⟨.inl ⟨packing, valid, maximal, component, present, centres, assigned,
            configuration⟩⟩
      · exact ⟨.inr ⟨packing, valid, maximal, component, present, centres, assigned,
            fun centre member high present =>
              configuration ⟨centre, member, high, present⟩⟩⟩)
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
omit [FactSystem (Input BranchState Presentation presentation data)] in
noncomputable def b2AssignmentDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : @FactKeys (Input BranchState Presentation presentation data) _
      (instFactSystem (BranchState := BranchState)
        (Presentation := Presentation) (presentation := presentation)
        (data := data))}
    (previous :
      @ExactLedger (Input BranchState Presentation presentation data) _
        (instFactSystem (BranchState := BranchState)
          (Presentation := Presentation) (presentation := presentation)
          (data := data)) current known)
    [@FactKeys.Has (Input BranchState Presentation presentation data) _
      (instFactSystem (BranchState := BranchState)
        (Presentation := Presentation) (presentation := presentation)
        (data := data)) (K .typeBDirectCycleFree) known]
    [@FactKeys.Has (Input BranchState Presentation presentation data) _
      (instFactSystem (BranchState := BranchState)
        (Presentation := Presentation) (presentation := presentation)
        (data := data)) (K .typeBFanEntry) known]
    (choiceFresh : K .typeBB2Choice ∉ known)
    (obstructionFresh : K .typeBOverlapObstruction ∉ known) :
    @Decision (Input BranchState Presentation presentation data) _
      (instFactSystem (BranchState := BranchState)
        (Presentation := Presentation) (presentation := presentation)
        (data := data)) current known
      (K .typeBB2Choice) (K .typeBOverlapObstruction) previous :=
  letI : FactSystem (Input BranchState Presentation presentation data) :=
    instFactSystem (BranchState := BranchState) (Presentation := Presentation)
      (presentation := presentation) (data := data)
  Decision.run previous (K .typeBB2Choice) (K .typeBOverlapObstruction)
    `Hypostructure.Graph.Strategy.Spine.b2AssignmentDichotomy
    (by
      classical
      apply Classical.choice
      -- The B2 disjoint choice is a question about the assigned Type B
      -- support `X = (Y_X, H_X)` of `[65]`/`[66]` (`def:typeB-assigned-ledger`:
      -- the counted core with its assigned centres in either manuscript form);
      -- the direct-cycle-free fact of `[72]` places the row on its branch.
      let _directFree := ExactLedger.get previous (K .typeBDirectCycleFree)
      obtain ⟨packing, valid, maximal, component, componentMem, centres, assigned,
        _nonempty, _high⟩ :=
        (ExactLedger.get previous (K .typeBFanEntry)).down
      let canonicalPiece :
          Graph.TypeBRefinedSupport.CanonicalPiece current.object packing :=
        ⟨component, componentMem⟩
      have assigned' : TypeBAssignedCentres data current.object packing
          canonicalPiece.vertices centres := assigned
      rcases Graph.TypeBRefinedSupport.b2_or_overlap current.object
          data.threshold data.dischargeScale canonicalPiece centres
          (TypeBAssignedCentres.high data current.object assigned') with
        choice | obstruction
      · exact ⟨.inl ⟨packing, valid, maximal, canonicalPiece, centres, assigned', choice⟩⟩
      · exact ⟨.inr ⟨packing, valid, maximal, canonicalPiece, centres, assigned',
            obstruction⟩⟩)
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
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def disjointPostLedgerComponentsRow :
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
    `Hypostructure.Graph.Strategy.Spine.disjointPostLedgerComponents
    { Requires := [K .typeBB2Choice, K .selection, K .uncompressible,
        K .remainderNormalized]
      Produces := [K .typeBDisjointLedger]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let choiceFact := (inputs.get (K .typeBB2Choice)).down
      let avoids := (inputs.get (K .selection)).down.1
      let uncompressibleFact := (inputs.get (K .uncompressible)).down
      let normalized := (inputs.get (K .remainderNormalized)).down
      .cons (key := K .typeBDisjointLedger)
        (⟨by
          classical
          obtain ⟨packing, valid, maximal, canonicalPiece, centres, assigned,
            choice⟩ := choiceFact
          let ledger : Graph.TypeBRefinedSupport.DisjointLedger
              inputs.current.object data.threshold data.dischargeScale
                canonicalPiece centres :=
            ⟨Classical.choice choice,
              TypeBAssignedCentres.high data inputs.current.object assigned,
              TypeBAssignedCentres.centres_subset data inputs.current.object assigned⟩
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
                      (handoffHighDegree data inputs.current.object)
                      (handoffAbsorbing data inputs.current.object packing),
                    ∃ grouped :
                      Graph.DecoratedHandoff.GroupedEnvelopes
                        inputs.current.object data.LengthOK
                        (handoffUncompressible data inputs.current.object)
                        (handoffWindowFree data inputs.current.object)
                        (handoffHighDegree data inputs.current.object)
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
              intro component componentMember
              have orderMember := componentsSubset component componentMember
              have componentData := componentFacts component orderMember
              constructor
              · intro window windowSubset induces
                exact (normalized packing valid maximal window
                  (windowSubset.trans componentData.containedInRemainder)).1
                  induces
              · intro internal internalSubset
                exact (normalized packing valid maximal internal
                  (internalSubset.trans componentData.containedInRemainder)).2
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
          exact ⟨packing, valid, maximal, canonicalPiece, centres, assigned,
            ledger, ledger.exactAugmentedLedgerRefinement,
            componentFacts, groupedCoverage⟩⟩)
        .nil)
    0 0

/-! ## Nodes `[73]`/`[75]` and `[83]`/`[84]`: Type B bridge fan mass

This row extends the literal cursor that has committed the Type B handoff.
That fact is read through the sealed inputs before the single canonical
bridge-mass fact is appended.
-/
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def bridgeFanMassRow :
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
    `Hypostructure.Graph.Strategy.Spine.typeBBridgeMass
    { Requires := [K .typeBHandoff]
      Produces := [K .typeBBridgeMass]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let _handoff := inputs.get (K .typeBHandoff)
      .cons (key := K .typeBBridgeMass) ⟨by
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
            ordinaryComponents groupedComponents⟩
      .nil)
    0 0

omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def typeBBridgeSublinearRow :
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
    `Hypostructure.Graph.Strategy.Spine.typeBBridgeSublinear
    { Requires := [K .typeBBridgeMass]
      Produces := [K .typeBBridgeSublinear]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let bridge := inputs.get (K .typeBBridgeMass)
      .cons (key := K .typeBBridgeSublinear) ⟨bridge.down.2.1⟩ .nil)
    0 0

omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def branchKillClosedRow :
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
    `Hypostructure.Graph.Strategy.Spine.branchKillClosed
    { Requires := [K .largeBudgetResidual, K .negativeSupport]
      Produces := [K .branchKillClosed]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let largeBudget := inputs.get (K .largeBudgetResidual)
      let negative := inputs.get (K .negativeSupport)
      .cons (key := K .branchKillClosed)
        ⟨largeBudget.down, negative.down⟩ .nil)
    0 0

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
        obtain ⟨packing, valid, maximal, component, componentMem, centres, assigned,
          centre, centreMem, high, empty⟩ := residual.down
        exact ⟨packing, valid, maximal, component, componentMem, centres, assigned,
          centre, centreMem, high, empty, fun envelope =>
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
        obtain ⟨packing, valid, maximal, canonicalPiece, centres, assigned,
          obstruction⟩ := residual.down
        exact ⟨packing, valid, maximal, canonicalPiece, centres, assigned,
          obstruction, fun centre member envelope =>
            Graph.TypeBEnvelopeCharge.envelopeNegativePart_le envelope
              (TypeBAssignedCentres.high data inputs.current.object assigned centre member)
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
        obtain ⟨packing, packingValid, packingMaximal, canonicalPiece,
          centres, assigned, ledger, exact, _postLedger, negative⟩ :=
          residualFact
        exact ⟨packing, packingValid, packingMaximal, canonicalPiece, centres, assigned,
          ledger, exact, negative,
          fun centre member envelope =>
            Graph.TypeBEnvelopeCharge.envelopeNegativePart_le envelope
              (TypeBAssignedCentres.high data inputs.current.object assigned centre member)
              data.bridgeMassSlack⟩)
      .nil)
    0 0

/-! ## Node `[76]`/`[85]`: Type B local selected-entry charge -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def typeBSelectedFanChargeRow :
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
    `Hypostructure.Graph.Strategy.Spine.typeBSelectedFanCharge
    { Requires := [K .fanCertificateMarked, K .typeBHybridEntry, K .typeBDisjointLedger]
      Produces := [K .typeBSelectedFanCharge]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let _markedFact := inputs.get (K .fanCertificateMarked)
      let _hybridFact := inputs.get (K .typeBHybridEntry)
      let _ledgerFact := inputs.get (K .typeBDisjointLedger)
      .cons (key := K .typeBSelectedFanCharge)
        (⟨by
          intro packing canonicalPiece centres ledger _exact
          have hLocalEntry :
              ∀ centre (member : centre ∈ centres),
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
          exact ⟨hLocalEntry, selected⟩⟩)
        .nil)
    0 0

/-! ## Node `[76]`/`[85]`: Type B exclusion charge

The charge row runs only after the exact B2 ledger and the selected local-entry
charge facts are present.  It reads both through `FactInputs.get` and appends
the B-ledger implication used by the exclusion dichotomy.
-/
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def typeBExclusionChargeRow :
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
    `Hypostructure.Graph.Strategy.Spine.typeBExclusionCharge
    { Requires := [K .typeBDisjointLedger, K .typeBSelectedFanCharge]
      Produces := [K .typeBExclusionCharge]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let _ledgerFact := inputs.get (K .typeBDisjointLedger)
      let localCharge := (inputs.get (K .typeBSelectedFanCharge)).down
      .cons (key := K .typeBExclusionCharge)
        (⟨by
          intro packing canonicalPiece centres ledger exact remainingNonnegative
          have selectedNonnegative :
              (0 : Int) ≤ ledger.selectedEntryPayment₂ :=
            (localCharge packing canonicalPiece centres ledger exact).2
          exact
            Graph.TypeBEnvelopeCharge.nonNegativeNetCharge_of_disjointLedger_remainingCore_nonneg_of_selectedEntryPayment₂_nonnegative
              (object := inputs.current.object) ledger exact
              selectedNonnegative remainingNonnegative⟩)
        .nil)
    0 0

/-! ## Node `[76]`/`[85]`: Type B exclusion split -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
noncomputable def typeBExclusionDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : @FactKeys (Input BranchState Presentation presentation data) _
      (instFactSystem (BranchState := BranchState)
        (Presentation := Presentation) (presentation := presentation)
        (data := data))}
    (previous :
      @ExactLedger (Input BranchState Presentation presentation data) _
        (instFactSystem (BranchState := BranchState)
          (Presentation := Presentation) (presentation := presentation)
          (data := data)) current known)
    [@FactKeys.Has (Input BranchState Presentation presentation data) _
      (instFactSystem (BranchState := BranchState)
        (Presentation := Presentation) (presentation := presentation)
        (data := data)) (K .typeBDisjointLedger) known]
    [@FactKeys.Has (Input BranchState Presentation presentation data) _
      (instFactSystem (BranchState := BranchState)
        (Presentation := Presentation) (presentation := presentation)
        (data := data)) (K .typeBExclusionCharge) known]
    (closedFresh : K .typeBExcluded ∉ known)
    (residualFresh : K .typeBExclusionResidual ∉ known) :
    @Decision (Input BranchState Presentation presentation data) _
      (instFactSystem (BranchState := BranchState)
        (Presentation := Presentation) (presentation := presentation)
        (data := data)) current known
      (K .typeBExcluded) (K .typeBExclusionResidual) previous :=
  letI : FactSystem (Input BranchState Presentation presentation data) :=
    instFactSystem (BranchState := BranchState) (Presentation := Presentation)
      (presentation := presentation) (data := data)
  Decision.run previous (K .typeBExcluded) (K .typeBExclusionResidual)
    `Hypostructure.Graph.Strategy.Spine.typeBExclusionDichotomy
    (by
      classical
      apply Classical.choice
      obtain ⟨packing, valid, maximal, canonicalPiece, centres, assigned,
        ledger, exact, postLedger, _groupedCoverage⟩ :=
        (ExactLedger.get previous (K .typeBDisjointLedger)).down
      -- Both manuscript forms of the assigned support carry the negative net
      -- charge of the counted core (`def:typeB-assigned-ledger`).
      have negative : current.object.NegativeNetCharge canonicalPiece.vertices
          data.threshold data.dischargeScale := by
        rcases assigned with ⟨negative, _, _⟩ | ⟨negative, _, _⟩ <;> exact negative
      let charge := ∑ vertex ∈ ledger.remainingCore,
        Graph.TypeBRefinedSupport.scaledCoreCharge current.object
          data.threshold data.dischargeScale canonicalPiece.vertices vertex
      by_cases clean : (0 : Int) ≤ charge
      · have nonnegative :=
          (ExactLedger.get previous (K .typeBExclusionCharge)).down
            packing canonicalPiece centres ledger exact clean
        have contradiction :=
          (current.object.not_negativeNetCharge_iff canonicalPiece.vertices
            data.threshold data.dischargeScale).mpr nonnegative negative
        exact ⟨.inl ⟨contradiction⟩⟩
      · exact ⟨.inr ⟨packing, valid, maximal, canonicalPiece, centres, assigned,
          ledger, exact, postLedger, by simpa [charge] using clean⟩⟩)
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
    (data : Data.{u}) :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.typeAReceiverRouting
    (rowManifest (K .remainderNormalized) (K .typeAReceiverRouting)
      (by simp [K_eq_iff]))
    (fun inputs =>
      let normalized := (inputs.get (K .remainderNormalized)).down
      .cons (key := K .typeAReceiverRouting)
        ⟨by
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
            (normalized packing valid maximal inner (contained.trans inside)).2
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
                data.dischargeScale receiver⟩⟩
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
omit [FactSystem (Input BranchState Presentation presentation data)] in
noncomputable def typeASaturationDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : @FactKeys (Input BranchState Presentation presentation data)
      _ (factSystem BranchState Presentation presentation data)}
    (previous :
      @ExactLedger (Input BranchState Presentation presentation data)
        _ (factSystem BranchState Presentation presentation data) current known)
    [@FactKeys.Has (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data)
      (K .typeALowSurplus) known]
    (saturatedFresh : K .typeASaturatedReceiver ∉ known)
    (unsaturatedFresh : K .typeAUnsaturatedReceivers ∉ known) :
    @Decision (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data) current known
      (K .typeASaturatedReceiver) (K .typeAUnsaturatedReceivers) previous :=
  @Decision.run (Input BranchState Presentation presentation data) _
    (factSystem BranchState Presentation presentation data) current known
    previous (K .typeASaturatedReceiver) (K .typeAUnsaturatedReceivers)
    `Hypostructure.Graph.Strategy.Spine.typeASaturationDichotomy
    (by
      classical
      apply Classical.choice
      obtain ⟨packing, valid, maximal, component, present, negative, zero⟩ :=
        (@ExactLedger.get (Input BranchState Presentation presentation data) _
          (factSystem BranchState Presentation presentation data)
          current known previous (K .typeALowSurplus)).down
      let piece := current.object.pieceSupport
        (current.object.remainderSupport packing) component
      by_cases saturated :
          ∃ receiver : current.object.Vertex,
            current.object.IsReceiver piece data.threshold receiver ∧
              current.object.Saturated piece data.threshold
                data.dischargeScale receiver
      · exact ⟨.inl ⟨⟨packing, valid, maximal, component, present, negative, zero,
          saturated⟩⟩⟩
      · refine ⟨.inr ⟨⟨packing, valid, maximal, component, present, negative, zero, ?_⟩⟩⟩
        intro receiver isReceiver
        refine (current.object.not_saturated_iff piece data.threshold
          data.dischargeScale receiver).mp ?_
        exact fun full => saturated ⟨receiver, isReceiver, full⟩)
    saturatedFresh unsaturatedFresh

/-! ## Nodes `[90]`--`[91]`: unsaturated Type A discharging

`lem:typeA-unsaturated-discharge`, read from nodes `[88]` and `[90]`.  The row
publishes the exact integral conclusion `|V(X)| ≤ s * def⁺(X)` for the same
negative Type A support quantified by the incoming facts.  The canonical
routing and the unsaturated receiver inequalities are both read by semantic
key. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def typeAUnsaturatedDischargeRow :
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
    `Hypostructure.Graph.Strategy.Spine.typeAUnsaturatedDischarge
    { Requires := [K .typeAReceiverRouting, K .typeAUnsaturatedReceivers]
      Produces := [K .typeAUnsaturatedDischarge]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let routing := (show Value BranchState Presentation presentation data
          .typeAReceiverRouting inputs.current from
        inputs.get (K .typeAReceiverRouting)).down
      let unsaturated := (show Value BranchState Presentation presentation data
          .typeAUnsaturatedReceivers inputs.current from
        inputs.get (K .typeAUnsaturatedReceivers)).down
      .cons (key := K .typeAUnsaturatedDischarge)
        (show Value BranchState Presentation presentation data
            .typeAUnsaturatedDischarge inputs.current from ⟨by
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
            surplus, discharged⟩⟩)
        .nil)
    0 0

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
omit [FactSystem (Input BranchState Presentation presentation data)] in
noncomputable def typeAVisibleEntryDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : @FactKeys (Input BranchState Presentation presentation data)
      _ (factSystem BranchState Presentation presentation data)}
    (previous :
      @ExactLedger (Input BranchState Presentation presentation data)
        _ (factSystem BranchState Presentation presentation data) current known)
    [@FactKeys.Has (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data)
      (K .typeAReceiverRouting) known]
    [@FactKeys.Has (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data)
      (K .typeASaturatedReceiver) known]
    (visibleFresh : K .typeAVisibleEntry ∉ known)
    (excessFresh : K .typeAVisibleFirstExcess ∉ known) :
    @Decision (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data) current known
      (K .typeAVisibleEntry) (K .typeAVisibleFirstExcess) previous :=
  @Decision.run (Input BranchState Presentation presentation data) _
    (factSystem BranchState Presentation presentation data) current known
    previous (K .typeAVisibleEntry) (K .typeAVisibleFirstExcess)
    `Hypostructure.Graph.Strategy.Spine.typeAVisibleEntryDichotomy
    (by
      classical
      letI : DecidableEq current.object.Vertex := current.object.vertices.decEq
      apply Classical.choice
      obtain ⟨packing, valid, maximal, component, present, negative, zero,
        selectedReceiver, selectedIsReceiver, selectedSaturated⟩ :=
        (@ExactLedger.get (Input BranchState Presentation presentation data) _
          (factSystem BranchState Presentation presentation data)
          current known previous (K .typeASaturatedReceiver)).down
      let piece := current.object.pieceSupport
        (current.object.remainderSupport packing) component
      have inside : piece ⊆ current.object.remainderSupport packing :=
        current.object.pieceSupport_subset
          (current.object.remainderSupport packing) component
      have routing := (@ExactLedger.get (Input BranchState Presentation presentation data) _
          (factSystem BranchState Presentation presentation data)
          current known previous (K .typeAReceiverRouting)).down
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
        exact ⟨.inl ⟨⟨packing, valid, maximal, component, present, negative, zero,
            receiver, isReceiver, saturated,
            Graph.ExitFour.visibleFourUnpeeledPackage piece data.threshold
              data.dischargeScale receiver ∅ overloaded⟩⟩⟩
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
        exact ⟨.inr ⟨⟨packing, valid, maximal, component, present, negative, zero,
            selectedReceiver, selectedIsReceiver, selectedSaturated,
            selectedSilent, supportBound⟩⟩⟩)
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
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def typeAPortReturnRow :
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
    `Hypostructure.Graph.Strategy.Spine.typeAPortReturn
    { Requires := [K .typeAReceiverRouting, K .selection]
      Produces := [K .typeAPortReturn]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let _routing := (show Value BranchState Presentation presentation data
          .typeAReceiverRouting inputs.current from
        inputs.get (K .typeAReceiverRouting)).down
      let selection := (show Value BranchState Presentation presentation data
          .selection inputs.current from inputs.get (K .selection)).down
      .cons (key := K .typeAPortReturn)
        (show Value BranchState Presentation presentation data
            .typeAPortReturn inputs.current from
          ⟨fun support receiver outside port =>
            Graph.VisibleEntry.exists_anchoredReturn_of_mem_completionPorts
              (LengthOK := data.LengthOK)
              (by have := data.three_le_threshold; omega)
              inputs.current.baseline selection.1 selection.2
              support receiver outside port⟩)
        .nil)
    0 0

/-! ## Nodes `[107]`--`[109]` and dashed input `[66]`

The predecessor is the exact selected no-exit-`(6)` fact.  Node `[107]`
decides only whether that same selected saturated handoff state produces a
decorated handoff envelope.  Node `[108]` records the admissible Type B
interface for the produced envelope.  The dashed Part VI input `[66]` is the
same `K .typeAExitSevenHandoff` fact passed unchanged from `[108]` to `[65]`;
it is a routing edge, so it deliberately makes no duplicate ledger commit.
Node `[109]` routes the selected no-handoff residual unchanged into Part IX;
node `[110]` is the first new route-8 publication.
-/

omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def typeAExitSevenHandoffRow
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
    `Hypostructure.Graph.Strategy.Spine.typeAExitSevenHandoff
    { Requires := [K .selection, K .uncompressible, K .remainderNormalized,
        K .typeAExitSevenProduced]
      Produces := [K .typeAExitSevenHandoff]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let produced :=
        (inputs.get (K .typeAExitSevenProduced)).down
      .cons (key := K .typeAExitSevenHandoff)
        ⟨by
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
          have normalized := (inputs.get (K .remainderNormalized)).down
          have coreInside : envelope.core ⊆
              inputs.current.object.remainderSupport packing := by
            intro vertex member
            exact inside (by simpa [piece, coreEq] using member)
          have windowFree :
              handoffWindowFree data inputs.current.object envelope.core := by
            constructor
            · intro window subset windowInduces
              exact (normalized packing valid maximal window
                (subset.trans coreInside)).1 windowInduces
            · intro internal subset
              exact (normalized packing valid maximal internal
                (subset.trans coreInside)).2
          have admissible :
              Graph.DecoratedHandoff.Admissible inputs.current.object
                data.LengthOK (handoffUncompressible data inputs.current.object)
                (handoffWindowFree data inputs.current.object) envelope :=
            { dyadicSafe := (inputs.get (K .selection)).down.1
              coreWindowFree := windowFree
              uncompressible := (inputs.get (K .uncompressible)).down
              fanReturnSafe := fun centre centreMember first firstMember second
                  secondMember different =>
                (envelope.fanSafe centre centreMember first firstMember second
                  secondMember different).1 }
          exact
            ⟨packing, valid, maximal, component, present, negative, zero,
              receiver, isReceiver, peeled, peeledSubset, saturated,
              noExitFour, noCompression, noDelocalization,
              ⟨envelope, coreEq, decorated, admissible⟩⟩⟩
        .nil)
    0 0

omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def typeBDecoratedAssignedSupportRow
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
    `Hypostructure.Graph.Strategy.Spine.typeBDecoratedAssignedSupport
    { Requires := [K .typeAExitSevenHandoff]
      Produces := [K .typeBDecoratedAssignedSupport, K .typeBFanEntry]
      requiresUnique := by simp
      producesUnique := by simp [K_eq_iff]
      producesNonempty := by simp }
    (fun inputs =>
      let handoff := (inputs.get (K .typeAExitSevenHandoff)).down
      .cons (key := K .typeBDecoratedAssignedSupport)
        ⟨by
          obtain ⟨packing, valid, maximal, component, present, negative, zero,
            receiver, isReceiver, peeled, peeledSubset, saturated, noExitFour,
            noCompression, noDelocalization, envelope, coreEq, nonempty,
            admissible⟩ := handoff
          have high : ∀ centre ∈ envelope.decorations,
              Graph.IsHighCentre inputs.current.object data.threshold centre := by
            intro centre member
            simpa [Graph.IsHighCentre] using
              envelope.decorations_high centre member
          exact ⟨packing, valid, maximal, component, present, negative, zero,
            receiver, isReceiver, peeled, peeledSubset, saturated, noExitFour,
            noCompression, noDelocalization,
            ⟨envelope, coreEq, nonempty, high,
              fun centre member =>
                ⟨envelope.assigned_nonempty centre member,
                  envelope.assigned_adj centre member⟩,
              admissible⟩⟩⟩
        (.cons (key := K .typeBFanEntry)
          -- Node `[66]`: the decorated envelope enters the common Type B fan
          -- support with the decorations as its assigned centres
          -- (`def:typeB-assigned-ledger`, `lem:decorated-fan-admissibility`).
          ⟨by
            obtain ⟨packing, valid, maximal, component, present, negative, zero,
              _receiver, _isReceiver, _peeled, _peeledSubset, _saturated, _noExitFour,
              _noCompression, _noDelocalization, envelope, coreEq, nonempty,
              _admissible⟩ := handoff
            refine ⟨packing, valid, maximal, component, present, envelope.decorations,
              Or.inr ⟨negative, zero, envelope, coreEq, rfl, nonempty,
                fun centre member =>
                  ⟨envelope.assigned_nonempty centre member,
                    envelope.assigned_adj centre member⟩⟩,
              nonempty, fun centre member => ?_⟩
            simpa [Graph.IsHighCentre] using
              envelope.decorations_high centre member⟩
          .nil))
    0 0

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
    { Requires := [K .typeAExitSevenFree]
      Produces := [K .route8ResidualProfile]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let residual := inputs.get (K .typeAExitSevenFree)
      .cons (key := K .route8ResidualProfile)
        ⟨by
          obtain ⟨packing, valid, maximal, component, present, negative, zero,
            receiver, isReceiver, peeled, peeledSubset, saturated, routing,
            noCompression, noDelocalization, noHandoff⟩ := residual.down
          exact ⟨packing, valid, maximal, component, present, negative, zero,
            receiver, isReceiver, peeled, peeledSubset, saturated, routing,
            noCompression, noDelocalization, noHandoff⟩⟩ .nil)
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
@[reducible] noncomputable def route8BasinBurdenRow
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
    `Hypostructure.Graph.Strategy.Spine.route8BasinBurden
    { Requires := [K .route8GlobalSqueeze, K .typeAVisibleFirstExcess]
      Produces := [K .route8BasinBurden]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let global := inputs.get (K .route8GlobalSqueeze)
      let excess := inputs.get (K .typeAVisibleFirstExcess)
      let burden : Route8BasinBurden data inputs.current.object :=
        ⟨global.down, excess.down⟩
      .cons (key := K .route8BasinBurden) ⟨burden⟩ .nil)
    0 0

omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def route8LargeBudgetDeficitRow
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
    `Hypostructure.Graph.Strategy.Spine.route8LargeBudgetDeficit
    { Requires := [K .route8BasinBurden, K .largeBudgetResidual]
      Produces := [K .route8LargeBudgetDeficit]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let burden := inputs.get (K .route8BasinBurden)
      let largeBudget := inputs.get (K .largeBudgetResidual)
      .cons (key := K .route8LargeBudgetDeficit)
        ⟨⟨burden.down, largeBudget.down⟩⟩ .nil)
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

/-! ## Node `[117]`: the two-carrier decision on the object-level census

`prop:typeA-route8-carrier-reduction`, at the indexed route-8 entries of the
extracted Type A collection `𝒳_A` (`Graph.Route8Census.entries`: the
`(piece, receiver, silent-excess load)` triples with their selected trace basins
and canonical essential cores).  The manuscript's "some entry has `π_𝒳(ξ) ≤ 2`?"
is decided exhaustively; the yes arm carries the two-carrier entry to nodes
`[118]`--`[124]`, the no arm carries "every entry has more than `δ` private
essential carriers" to the private-carrier census `[119]`--`[122]`, which
`K .route8Census` (deficit and rate) refutes. -/
/-! ## Node `[111]`, the global squeeze as the all-pieces classification

`thm:branch-kill` and `lem:typeA-unified-deficit` sum the canonical decomposition
of the remainder piece by piece: a negative piece with no ambient surplus is a
Type A piece whose deficit is carried by silent-excess entries provided it is
silent-first (no saturated receiver has a completion port carrying `s` visible
returns — node `[93]`'s no arm at that piece), and a negative piece with surplus
is a Type B bridge component (`lem:typeB-bridge-deficit-bound`).  That
classification is a property of the residual and is decided on it: the yes arm
carries the deficit reading `|R| ≤ N_basin + s·|∂R| + F·s·T(n)`
(`Graph.Route8Deficit.deficit_of_classification`); the no arm is a negative piece
that is visible-first Type A (`lem:typeA-visible-entry`) or a Type B piece outside
the bridge residual (`prop:typeB-bridge-reduction`), carried as its own branch. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
noncomputable def route8PieceClassificationDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : @FactKeys (Input BranchState Presentation presentation data)
      _ (factSystem BranchState Presentation presentation data)}
    (previous :
      @ExactLedger (Input BranchState Presentation presentation data)
        _ (factSystem BranchState Presentation presentation data) current known)
    [@Core.Residual.FactKeys.Has
      (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data)
      (K .route8SmallCoreCollapse) known]
    (classifiedFresh : K .route8PiecesClassified ∉ known)
    (unclassifiedFresh : K .route8UnclassifiedPiece ∉ known) :
    @Decision (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data) current known
      (K .route8PiecesClassified) (K .route8UnclassifiedPiece) previous :=
  @Decision.run (Input BranchState Presentation presentation data) _
    (factSystem BranchState Presentation presentation data) current known
    previous (K .route8PiecesClassified) (K .route8UnclassifiedPiece)
    `Hypostructure.Graph.Strategy.Spine.route8PieceClassificationDichotomy
    (by
      classical
      -- Decided on the `[116]` residual; read that literal predecessor fact.
      let _collapse := (@ExactLedger.get
        (Input BranchState Presentation presentation data) _
        (factSystem BranchState Presentation presentation data)
        current known previous (K .route8SmallCoreCollapse)).down
      exact if classified : Graph.Route8Deficit.PieceClassification current.object
          (canonicalWindowPacking data current.object) data.threshold
          data.dischargeScale then
        .inl ⟨classified⟩
      else
        .inr ⟨classified⟩)
    classifiedFresh unclassifiedFresh

/-! Nodes `[111]`--`[113]`, the deficit reading of the census
(`def:typeA-large-budget-deficit` with `lem:typeA-route8-burden` and
`thm:branch-kill` substituted): on the classified residual,
`|R| ≤ N_basin + s·|∂R| + F·s·T(n)`, from the receiver routing of node `[88]`
at every zero-surplus piece, the near-cubic surplus bound, and the piece-by-piece
sum of `Graph.Route8Deficit`. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def route8DeficitRow
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
    `Hypostructure.Graph.Strategy.Spine.route8Deficit
    { Requires := [K .route8PiecesClassified, K .typeAReceiverRouting,
        K .surplusAtOrBelow]
      Produces := [K .route8Deficit]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let classified := (inputs.get (K .route8PiecesClassified)).down
      let routing := (inputs.get (K .typeAReceiverRouting)).down
      let surplus := (inputs.get (K .surplusAtOrBelow)).down
      .cons (key := K .route8Deficit)
        ⟨by
          classical
          have baseline : ∀ vertex : inputs.current.object.Vertex,
              data.threshold ≤ inputs.current.object.degree vertex := fun vertex =>
            le_trans inputs.current.baseline
              (inputs.current.object.minDegree_le_degree vertex)
          have packingSpec := Classical.choose_spec
            (inputs.current.object.exists_windowPacking_card_eq data.windowOrder)
          have valid : inputs.current.object.IsWindowPacking data.windowOrder
              (canonicalWindowPacking data inputs.current.object) := packingSpec.1
          have maximal : ∀ window : Finset inputs.current.object.Vertex,
              inputs.current.object.InducesWindow data.windowOrder window →
              ∃ member ∈ canonicalWindowPacking data inputs.current.object,
                ¬ Disjoint window member := fun window induces =>
            inputs.current.object.exists_mem_not_disjoint_of_card_eq
              data.windowOrder_pos valid packingSpec.2 induces
          exact Graph.Route8Deficit.deficit_of_classification inputs.current.object
            (canonicalWindowPacking data inputs.current.object) data.threshold
            data.dischargeScale data.bridgeMassFactor
            (data.surplusThreshold inputs.current.object.vertexCount)
            data.dischargeScale_pos data.bridgeMassSlack baseline
            (fun piece inside surplusZero vertex member full =>
              (routing (canonicalWindowPacking data inputs.current.object) valid maximal
                piece inside surplusZero).1 vertex member full)
            surplus classified⟩
        .nil)
    0 0

omit [FactSystem (Input BranchState Presentation presentation data)] in
noncomputable def route8CarrierDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : @FactKeys (Input BranchState Presentation presentation data)
      _ (factSystem BranchState Presentation presentation data)}
    (previous :
      @ExactLedger (Input BranchState Presentation presentation data)
        _ (factSystem BranchState Presentation presentation data) current known)
    [@Core.Residual.FactKeys.Has
      (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data)
      (K .route8Census) known]
    (twoFresh : K .route8TwoCarrierEntry ∉ known)
    (noTwoFresh : K .route8NoTwoCarrierEntry ∉ known) :
    @Decision (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data) current known
      (K .route8TwoCarrierEntry) (K .route8NoTwoCarrierEntry) previous :=
  @Decision.run (Input BranchState Presentation presentation data) _
    (factSystem BranchState Presentation presentation data) current known
    previous (K .route8TwoCarrierEntry) (K .route8NoTwoCarrierEntry)
    `Hypostructure.Graph.Strategy.Spine.route8CarrierDichotomy
    (by
      classical
      -- Node `[117]` is decided on the census residual; read that literal
      -- predecessor fact.
      let _census := (@ExactLedger.get
        (Input BranchState Presentation presentation data) _
        (factSystem BranchState Presentation presentation data)
        current known previous (K .route8Census)).down
      exact if two : ∃ index ∈ Graph.Route8Census.entries current.object
            (canonicalWindowPacking data current.object) data.threshold
            data.dischargeScale,
          Graph.Route8Census.TwoCarrierEntry current.object
            (canonicalWindowPacking data current.object) data.threshold
            data.dischargeScale data.LengthOK index then
        .inl ⟨two⟩
      else
        .inr ⟨fun index member twoCarrier => two ⟨index, member, twoCarrier⟩⟩)
    twoFresh noTwoFresh

/-! ## Node `[118]`: the two-carrier entry is a true route-8 entry or target-defect

`thm:large-budget-route8-only`: "If that two-carrier entry is a route-8 entry,
then `prop:typeA-route8-closure-from-nogo` applies … If instead the entry is
target-defect, then `lem:typeA-pressure-is-exit4-peel` makes its pressure token a
canonical exit-`(4)` witness for its routed load."  The split is decided on the
selected two-carrier entry of `K .route8TwoCarrierEntry`: either its load has no
exit-`(4)` witness at its own receiver (`def:typeA-true-route8-residual`) or it
has one. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
noncomputable def route8EntryKindDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : @FactKeys (Input BranchState Presentation presentation data)
      _ (factSystem BranchState Presentation presentation data)}
    (previous :
      @ExactLedger (Input BranchState Presentation presentation data)
        _ (factSystem BranchState Presentation presentation data) current known)
    [@Core.Residual.FactKeys.Has
      (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data)
      (K .route8TwoCarrierEntry) known]
    (trueFresh : K .route8TrueTwoCarrierEntry ∉ known)
    (defectFresh : K .route8TargetDefectTwoCarrierEntry ∉ known) :
    @Decision (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data) current known
      (K .route8TrueTwoCarrierEntry) (K .route8TargetDefectTwoCarrierEntry) previous :=
  @Decision.run (Input BranchState Presentation presentation data) _
    (factSystem BranchState Presentation presentation data) current known
    previous (K .route8TrueTwoCarrierEntry) (K .route8TargetDefectTwoCarrierEntry)
    `Hypostructure.Graph.Strategy.Spine.route8EntryKindDichotomy
    (by
      classical
      let twoCarrier := (@ExactLedger.get
        (Input BranchState Presentation presentation data) _
        (factSystem BranchState Presentation presentation data)
        current known previous (K .route8TwoCarrierEntry)).down
      exact if trueEntry : ∃ index ∈ Graph.Route8Census.entries current.object
            (canonicalWindowPacking data current.object) data.threshold
            data.dischargeScale,
          Graph.Route8Census.TwoCarrierEntry current.object
            (canonicalWindowPacking data current.object) data.threshold
            data.dischargeScale data.LengthOK index ∧
          ¬ ∃ witness : Graph.ExitFour.Witness (Graph.HasCycleWithLength data.LengthOK)
              index.1 data.threshold index.2.1 ∅,
            witness.load = index.2.2 then
        .inl ⟨trueEntry⟩
      else
        .inr ⟨by
          obtain ⟨index, member, two⟩ := twoCarrier
          refine ⟨index, member, two, ?_⟩
          by_contra noWitness
          exact trueEntry ⟨index, member, two, noWitness⟩⟩)
    trueFresh defectFresh

/-! ## Node `[123]`: `thm:large-budget-route8-only`, the pressure descent

The manuscript's deterministic procedure on the object-level census
(`Graph/Route8Pressure`): from the empty peeling, a stage with the stage rate
`(δs+1)|∂R| + δ·slack + δ|P₄| < δ|R|` (`def:typeA-peeling-reduced-ledger`'s
`D̃_A^{P₄} ≥ (¼ − τ)|R| − o(|R|)`) has a two-carrier entry of the peeled ledger
(`lem:typeA-peeling-reduced-reduction`); a target-defect entry — its load carries
an exit-(4) witness at its receiver with the current peeled loads
(`lem:typeA-pressure-is-exit4-peel`) — is peeled and the number of unpeeled entries
drops (`lem:typeA-exit4-finite-descent`, `Λ₄`); the procedure therefore ends at a
stage with a true (route-8) two-carrier entry, sent to node `[124]`, or at a stage
where the stage rate fails.  The row reads the census (`[111]`--`[113]`, `[120]`)
and publishes the procedure's outcome; the decision after it splits the two ends. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def route8PeelingDescentRow
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
    `Hypostructure.Graph.Strategy.Spine.route8PeelingDescent
    { Requires := [K .route8Census]
      Produces := [K .route8PeelingDescent]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let census := (inputs.get (K .route8Census)).down
      .cons (key := K .route8PeelingDescent)
        (show Value BranchState Presentation presentation data
            .route8PeelingDescent inputs.current from
          ⟨Graph.Route8Pressure.descent_of_census inputs.current.object
            (canonicalWindowPacking data inputs.current.object) data.threshold
            data.dischargeScale
            (data.bridgeMassFactor * data.dischargeScale *
              data.surplusThreshold inputs.current.object.vertexCount)
            data.LengthOK (le_trans (by norm_num) data.three_le_threshold) census.1⟩)
        .nil)
    0 0

/-! The end of the procedure: a stage with a true two-carrier entry of the peeled
ledger — transported to the census's true-entry fact `K .route8TrueTwoCarrierEntry`
(`Graph.Route8Pressure.trueEntry_transport`), the entry of node `[124]` — or a
stage where the stage rate fails (`K .route8PeelingSaturated`). -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
noncomputable def route8PeelingOutcomeDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : @FactKeys (Input BranchState Presentation presentation data)
      _ (factSystem BranchState Presentation presentation data)}
    (previous :
      @ExactLedger (Input BranchState Presentation presentation data)
        _ (factSystem BranchState Presentation presentation data) current known)
    [@Core.Residual.FactKeys.Has
      (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data)
      (K .route8PeelingDescent) known]
    (trueFresh : K .route8TrueTwoCarrierEntry ∉ known)
    (saturatedFresh : K .route8PeelingSaturated ∉ known) :
    @Decision (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data) current known
      (K .route8TrueTwoCarrierEntry) (K .route8PeelingSaturated) previous :=
  @Decision.run (Input BranchState Presentation presentation data) _
    (factSystem BranchState Presentation presentation data) current known
    previous (K .route8TrueTwoCarrierEntry) (K .route8PeelingSaturated)
    `Hypostructure.Graph.Strategy.Spine.route8PeelingOutcomeDichotomy
    (by
      classical
      let outcome := (@ExactLedger.get
        (Input BranchState Presentation presentation data) _
        (factSystem BranchState Presentation presentation data)
        current known previous (K .route8PeelingDescent)).down
      exact if trueEntry : ∃ index ∈ Graph.Route8Census.entries current.object
            (canonicalWindowPacking data current.object) data.threshold
            data.dischargeScale,
          Graph.Route8Census.TwoCarrierEntry current.object
            (canonicalWindowPacking data current.object) data.threshold
            data.dischargeScale data.LengthOK index ∧
          ¬ ∃ witness : Graph.ExitFour.Witness (Graph.HasCycleWithLength data.LengthOK)
              index.1 data.threshold index.2.1 ∅,
            witness.load = index.2.2 then
        .inl ⟨trueEntry⟩
      else
        .inr ⟨by
          obtain ⟨final, chain, ends⟩ := outcome
          refine ⟨final, chain, ?_⟩
          rcases ends with ⟨_rate, index, isTrue⟩ | saturated
          · exact absurd ⟨index, Graph.Route8Pressure.trueEntry_transport current.object
              (canonicalWindowPacking data current.object) data.threshold
              data.dischargeScale data.LengthOK final.toFinset isTrue⟩ trueEntry
          · exact saturated⟩)
    trueFresh saturatedFresh

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

omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def largeBudgetRoute8ClosedRow
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
    `Hypostructure.Graph.Strategy.Spine.largeBudgetRoute8Closed
    { Requires := [K .branchKillClosed, K .typeBBridgeSublinear,
        K .route8TerminalResidual, K .route8TerminalNoGo]
      Produces := [K .largeBudgetRoute8Closed]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let _branchKill := inputs.get (K .branchKillClosed)
      let _bridgeSublinear := inputs.get (K .typeBBridgeSublinear)
      let terminal := inputs.get (K .route8TerminalResidual)
      let noGo := inputs.get (K .route8TerminalNoGo)
      .cons (key := K .largeBudgetRoute8Closed)
        ⟨by
          rcases terminal.down with ⟨_pressure, _witnesses, presented,
            terminalSurvives⟩
          rcases noGo.down with ⟨_pressureNoGo, _witnessesNoGo, terminalNoGo⟩
          exact terminalSurvives (terminalNoGo presented)⟩ .nil)
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
omit [FactSystem (Input BranchState Presentation presentation data)] in
noncomputable def typeAExitOneDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : @FactKeys (Input BranchState Presentation presentation data)
      _ (factSystem BranchState Presentation presentation data)}
    (previous :
      @ExactLedger (Input BranchState Presentation presentation data)
        _ (factSystem BranchState Presentation presentation data) current known)
    [@FactKeys.Has (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data)
      (K .typeAVisibleEntry) known]
    (returnFresh : K .typeAExitOneReturn ∉ known)
    (freeFresh : K .typeAExitOneFree ∉ known) :
    @Decision (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data) current known
      (K .typeAExitOneReturn) (K .typeAExitOneFree) previous :=
  @Decision.run (Input BranchState Presentation presentation data) _
    (factSystem BranchState Presentation presentation data) current known
    previous (K .typeAExitOneReturn) (K .typeAExitOneFree)
    `Hypostructure.Graph.Strategy.Spine.typeAExitOneDichotomy
    (by
      classical
      apply Classical.choice
      obtain ⟨packing, valid, maximal, component, present, negative, zero,
        receiver, isReceiver, saturated, packageExists⟩ :=
        (@ExactLedger.get (Input BranchState Presentation presentation data) _
          (factSystem BranchState Presentation presentation data)
          current known previous (K .typeAVisibleEntry)).down
      obtain ⟨package⟩ := packageExists
      by_cases realized :
          ∃ return' : Graph.VisibleEntry.AnchoredReturn current.object receiver
              package.outside,
            Graph.ShiftedCycleLength data.LengthOK return'.path.length
      · exact ⟨.inl ⟨
          ⟨packing, valid, maximal, component, present, negative, zero,
            receiver, isReceiver, saturated, package, realized⟩⟩⟩
      · exact ⟨.inr ⟨
          ⟨packing, valid, maximal, component, present, negative, zero,
            receiver, isReceiver, saturated, package,
            fun return' accepted => realized ⟨return', accepted⟩⟩⟩⟩)
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
omit [FactSystem (Input BranchState Presentation presentation data)] in
noncomputable def typeAExitTwoDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : @FactKeys (Input BranchState Presentation presentation data)
      _ (factSystem BranchState Presentation presentation data)}
    (previous :
      @ExactLedger (Input BranchState Presentation presentation data)
        _ (factSystem BranchState Presentation presentation data) current known)
    [@FactKeys.Has (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data)
      (K .typeAVisibleEntry) known]
    (thetaFresh : K .typeAExitTwoTheta ∉ known)
    (freeFresh : K .typeAExitTwoFree ∉ known) :
    @Decision (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data) current known
      (K .typeAExitTwoTheta) (K .typeAExitTwoFree) previous :=
  @Decision.run (Input BranchState Presentation presentation data) _
    (factSystem BranchState Presentation presentation data) current known
    previous (K .typeAExitTwoTheta) (K .typeAExitTwoFree)
    `Hypostructure.Graph.Strategy.Spine.typeAExitTwoDichotomy
    (by
      classical
      apply Classical.choice
      obtain ⟨packing, valid, maximal, component, present, negative, zero,
        receiver, isReceiver, saturated, packageExists⟩ :=
        (@ExactLedger.get (Input BranchState Presentation presentation data) _
          (factSystem BranchState Presentation presentation data)
          current known previous (K .typeAVisibleEntry)).down
      obtain ⟨package⟩ := packageExists
      let piece := current.object.pieceSupport
        (current.object.remainderSupport packing) component
      by_cases realized : Graph.VisibleEntry.ExitTwoThrough current.object piece
          data.LengthOK receiver package.outside
      · exact ⟨.inl ⟨
          ⟨packing, valid, maximal, component, present, negative, zero,
            receiver, isReceiver, saturated, package, realized⟩⟩⟩
      · exact ⟨.inr ⟨
          ⟨packing, valid, maximal, component, present, negative, zero,
            receiver, isReceiver, saturated, package, realized⟩⟩⟩)
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
omit [FactSystem (Input BranchState Presentation presentation data)] in
noncomputable def typeAExitThreeDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : @FactKeys (Input BranchState Presentation presentation data)
      _ (factSystem BranchState Presentation presentation data)}
    (previous :
      @ExactLedger (Input BranchState Presentation presentation data)
        _ (factSystem BranchState Presentation presentation data) current known)
    [@FactKeys.Has (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data)
      (K .typeAVisibleEntry) known]
    (collisionFresh : K .typeAExitThreeCollision ∉ known)
    (freeFresh : K .typeAExitThreeFree ∉ known) :
    @Decision (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data) current known
      (K .typeAExitThreeCollision) (K .typeAExitThreeFree) previous :=
  @Decision.run (Input BranchState Presentation presentation data) _
    (factSystem BranchState Presentation presentation data) current known
    previous (K .typeAExitThreeCollision) (K .typeAExitThreeFree)
    `Hypostructure.Graph.Strategy.Spine.typeAExitThreeDichotomy
    (by
      classical
      apply Classical.choice
      obtain ⟨packing, valid, maximal, component, present, negative, zero,
        receiver, isReceiver, saturated, packageExists⟩ :=
        (@ExactLedger.get (Input BranchState Presentation presentation data) _
          (factSystem BranchState Presentation presentation data)
          current known previous (K .typeAVisibleEntry)).down
      obtain ⟨package⟩ := packageExists
      by_cases realized : Graph.WindowLabelCollision.LabelCollision
          current.object data.windowOrder data.LengthOK packing
      · exact ⟨.inl ⟨
          ⟨packing, valid, maximal, component, present, negative, zero,
            receiver, isReceiver, saturated, package, realized⟩⟩⟩
      · exact ⟨.inr ⟨
          ⟨packing, valid, maximal, component, present, negative, zero,
            receiver, isReceiver, saturated, package, realized⟩⟩⟩)
    collisionFresh freeFresh

/-! ## Nodes `[99]`/`[94]` → `[101]`: the shared saturated exit entry

`lem:typeA-exit4-residual-routing`: *"let `w` be a saturated Type A receiver
with a peeling set `P₄(w)`; if `L₄(w) ≥ 4q(w)`, then the unpeeled routed loads
at `w` realize one of exits (1)--(8)"*.  Figure 8 draws one segment
`[101]`--`[107]` with two entries — node `[99]`'s no arm
(`lem:typeA-unpeeled-visible-routing` after exits `(1)`--`(3)` are denied) and
node `[94]` (`lem:typeA-unpeeled-silent-routing`) — and this hypothesis is what
both commit: the selected saturated receiver at the empty peeling set
(`P₄(w) = ∅`, `L₄(w) = L(w)`, `saturatedAfter_empty`), which is
`def:typeA-exit4-peeling`'s witnessed peeling set trivially.  Each entry row
reads only its own lane's predecessor fact by exact key. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def typeAVisibleExitEntryRow :
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
    `Hypostructure.Graph.Strategy.Spine.typeAVisibleExitEntry
    { Requires := [K .typeAExitThreeFree]
      Produces := [K .typeASaturatedExitEntry]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .typeASaturatedExitEntry)
        (show Value BranchState Presentation presentation data
            .typeASaturatedExitEntry inputs.current from ⟨by
          classical
          obtain ⟨packing, valid, maximal, component, present, negative, zero,
            receiver, isReceiver, saturated, _package, _labelFree⟩ :=
            (inputs.get (K .typeAExitThreeFree)).down
          let piece := inputs.current.object.pieceSupport
            (inputs.current.object.remainderSupport packing) component
          exact ⟨packing, valid, maximal, component, present, negative, zero,
            receiver, isReceiver, ∅, Finset.empty_subset _,
            (Graph.ExitFour.saturatedAfter_empty piece data.threshold
              data.dischargeScale receiver).mpr saturated,
            Graph.ExitFour.peeledByWitnesses_empty _ piece data.threshold receiver⟩⟩)
        .nil)
    0 0

omit [FactSystem (Input BranchState Presentation presentation data)] in
/-- The silent entry of the shared exit segment: node `[94]`
(`lem:typeA-unpeeled-silent-routing`) commits the same saturated exit entry at
the empty peeling set. -/
@[reducible] noncomputable def typeASilentExitEntryRow :
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
    `Hypostructure.Graph.Strategy.Spine.typeASilentExitEntry
    { Requires := [K .typeAVisibleFirstExcess]
      Produces := [K .typeASaturatedExitEntry]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .typeASaturatedExitEntry)
        (show Value BranchState Presentation presentation data
            .typeASaturatedExitEntry inputs.current from ⟨by
          classical
          obtain ⟨packing, valid, maximal, component, present, negative, zero,
            receiver, isReceiver, saturated, _silent, _count⟩ :=
            (inputs.get (K .typeAVisibleFirstExcess)).down
          let piece := inputs.current.object.pieceSupport
            (inputs.current.object.remainderSupport packing) component
          exact ⟨packing, valid, maximal, component, present, negative, zero,
            receiver, isReceiver, ∅, Finset.empty_subset _,
            (Graph.ExitFour.saturatedAfter_empty piece data.threshold
              data.dischargeScale receiver).mpr saturated,
            Graph.ExitFour.peeledByWitnesses_empty _ piece data.threshold receiver⟩⟩)
        .nil)
    0 0

/-! ## `lem:typeA-exit4-finite-descent`, the descent principle on the ledger

`lem:typeA-saturated-handoff`, finite descent part, read at the exact selected
receiver and peeling state committed by the exit entry: whatever the retained
and terminal predicates are, the exit-`(4)` peels terminate at a terminal
retained state or at an unsaturated one.  Node `[102]`'s retest below runs the
same descent for the exit segment; node `[123]`'s large-budget pressure descent
reads this fact for the target-defect entries.  The terminal predicates are not
chosen here. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def typeAExitFourFiniteDescentRow :
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
    `Hypostructure.Graph.Strategy.Spine.typeAExitFourFiniteDescent
    { Requires := [K .typeASaturatedExitEntry]
      Produces := [K .typeAExitFourFiniteDescent]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .typeAExitFourFiniteDescent)
        (show Value BranchState Presentation presentation data
            .typeAExitFourFiniteDescent inputs.current from ⟨by
          classical
          obtain ⟨packing, valid, maximal, component, present, negative, zero,
            receiver, isReceiver, startPeeled, startInside, startSaturated,
            _startWitnessed⟩ :=
            (inputs.get (K .typeASaturatedExitEntry)).down
          let piece := inputs.current.object.pieceSupport
            (inputs.current.object.remainderSupport packing) component
          refine ⟨packing, valid, maximal, component, present, negative, zero,
            receiver, isReceiver, startPeeled, startInside, startSaturated,
            ?_⟩
          intro Retained Terminal startRetained step
          exact Graph.ExitFour.terminal_or_unsaturated_from piece
            data.threshold data.dischargeScale receiver startInside
            startRetained step⟩)
        .nil)
    0 0

/-! ## Node `[101]`: exit `(4)`, the target-defective peeling witness

`def:typeA-saturated-exits` (4) and `def:typeA-exit4-family`: at the selected
saturated receiver and its current peeling set, does a generated
target-defective quotient of the receiver family support one of the unpeeled
routed loads under discussion?  `lem:typeA-exit4-residual-routing` names the
loads: in the visible case (a completion port carries the registered number of
unpeeled visible returns) the selected visible loads of the canonical package,
in the silent case the canonical residual excess set `E₄(w)`; the two cases are
exhaustive at a saturated receiver of exact baseline degree
(`visibleFourUnpeeled_or_silentUnpeeledExcess`, `lem:typeA-silent-excess-count`).
The yes arm is charged at node `[102]`; the no arm is the hypothesis exit `(5)`
is asked under. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
noncomputable def typeAExitFourDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : @FactKeys (Input BranchState Presentation presentation data)
      _ (factSystem BranchState Presentation presentation data)}
    (previous :
      @ExactLedger (Input BranchState Presentation presentation data)
        _ (factSystem BranchState Presentation presentation data) current known)
    [@FactKeys.Has (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data)
      (K .typeASaturatedExitEntry) known]
    (exitFresh : K .typeASaturatedHandoffExitFour ∉ known)
    (freeFresh : K .typeASaturatedHandoffExitFourFree ∉ known) :
    @Decision (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data) current known
      (K .typeASaturatedHandoffExitFour) (K .typeASaturatedHandoffExitFourFree)
      previous :=
  @Decision.run (Input BranchState Presentation presentation data) _
    (factSystem BranchState Presentation presentation data) current known
    previous (K .typeASaturatedHandoffExitFour) (K .typeASaturatedHandoffExitFourFree)
    `Hypostructure.Graph.Strategy.Spine.typeAExitFourDichotomy
    (by
      classical
      apply Classical.choice
      obtain ⟨packing, valid, maximal, component, present, negative, zero,
        receiver, isReceiver, peeled, peeledSubset, saturated, witnessed⟩ :=
        (@ExactLedger.get (Input BranchState Presentation presentation data) _
          (factSystem BranchState Presentation presentation data)
          current known previous (K .typeASaturatedExitEntry)).down
      let piece := current.object.pieceSupport
        (current.object.remainderSupport packing) component
      have exactDegree : ∀ vertex ∈ piece,
          current.object.degree vertex = data.threshold := by
        intro vertex member
        have lower : data.threshold ≤ current.object.degree vertex :=
          le_trans current.baseline (current.object.minDegree_le_degree vertex)
        have summand : current.object.degree vertex - data.threshold = 0 :=
          Nat.eq_zero_of_le_zero
            (zero ▸ Finset.single_le_sum
              (f := fun other => current.object.degree other - data.threshold)
              (fun _ _ => Nat.zero_le _) member)
        omega
      rcases Graph.ExitFour.visibleFourUnpeeled_or_silentUnpeeledExcess piece
          data.threshold data.dischargeScale receiver peeled
          (exactDegree receiver isReceiver.1) isReceiver saturated with
        visible | silent
      · obtain ⟨package⟩ := Graph.ExitFour.visibleFourUnpeeledPackage piece
          data.threshold data.dischargeScale receiver peeled visible
        by_cases occurs :
            ∃ witness : Graph.ExitFour.Witness
                (Graph.HasCycleWithLength data.LengthOK) piece data.threshold
                receiver peeled,
              ∃ load ∈ Graph.ExitFour.selectedVisibleUnpeeledLoads piece
                  data.threshold data.dischargeScale receiver package.outside
                  peeled,
                witness.load = load
        · exact ⟨.inl ⟨⟨packing, valid, maximal, component, present, negative,
            zero, receiver, isReceiver, peeled, peeledSubset, saturated, witnessed,
            Or.inl ⟨package, occurs⟩⟩⟩⟩
        · exact ⟨.inr ⟨⟨packing, valid, maximal, component, present, negative,
            zero, receiver, isReceiver, peeled, peeledSubset, saturated,
            Or.inl ⟨package, occurs⟩⟩⟩⟩
      · by_cases occurs :
            ∃ witness : Graph.ExitFour.Witness
                (Graph.HasCycleWithLength data.LengthOK) piece data.threshold
                receiver peeled,
              witness.load ∈ Graph.ExitFour.unpeeledExcess piece data.threshold
                data.dischargeScale receiver peeled
        · exact ⟨.inl ⟨⟨packing, valid, maximal, component, present, negative,
            zero, receiver, isReceiver, peeled, peeledSubset, saturated, witnessed,
            Or.inr ⟨silent, occurs⟩⟩⟩⟩
        · exact ⟨.inr ⟨⟨packing, valid, maximal, component, present, negative,
            zero, receiver, isReceiver, peeled, peeledSubset, saturated,
            Or.inr ⟨silent, occurs⟩⟩⟩⟩)
    exitFresh freeFresh

/-! ## Node `[102]`, `lem:typeA-exit4-discharge`: the peel

Node `[101]`'s yes arm charged one exit-`(4)` witness.  The row inserts that
witness's unpeeled routed load into `P₄(w)`: the enlarged set is still a
witnessed peeling set inside `ℒ(w)` and the residual load `L₄(w)` has dropped
by exactly one — the integral form of the manuscript's exact quarter-charge
update. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def typeAExitFourPeelingStepRow :
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
    `Hypostructure.Graph.Strategy.Spine.typeAExitFourPeelingStep
    { Requires := [K .typeASaturatedHandoffExitFour]
      Produces := [K .typeAExitFourPeeled]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .typeAExitFourPeeled)
        (show Value BranchState Presentation presentation data
            .typeAExitFourPeeled inputs.current from ⟨by
          classical
          obtain ⟨packing, valid, maximal, component, present, negative, zero,
            receiver, isReceiver, peeled, peeledSubset, saturated, witnessed,
            source⟩ :=
            (inputs.get (K .typeASaturatedHandoffExitFour)).down
          let piece := inputs.current.object.pieceSupport
            (inputs.current.object.remainderSupport packing) component
          obtain ⟨witness, unpeeled⟩ :
              ∃ witness : Graph.ExitFour.Witness
                  (Graph.HasCycleWithLength data.LengthOK) piece data.threshold
                  receiver peeled,
                witness.load ∈ Graph.ExitFour.unpeeledLoads piece data.threshold
                  receiver peeled := by
            rcases source with visible | silent
            · obtain ⟨_package, witness, _load, _selected, _witnessEq⟩ := visible
              exact ⟨witness, witness.unpeeled⟩
            · obtain ⟨_silent, witness, _supported⟩ := silent
              exact ⟨witness, witness.unpeeled⟩
          exact ⟨packing, valid, maximal, component, present, negative, zero,
            receiver, isReceiver, peeled, peeledSubset, saturated, witnessed,
            witness, unpeeled,
            Graph.ExitFour.Witness.nextPeeled_subset_routedLoads witness
              peeledSubset,
            Graph.ExitFour.Witness.residualLoad_nextPeeled witness⟩⟩)
        .nil)
    0 0

/-! ## Node `[102]` → `[89]`: "recompute `L₄`" — the finite exit-`(4)` descent

Figure 8 sends the peeled receiver back to node `[89]` with its residual load
`L₄`.  `lem:typeA-exit4-finite-descent` / `lem:typeA-saturated-handoff`: each
peel strictly decreases `L₄(w)` (`lem:typeA-exit4-discharge`), so the loop
`[89] → [93]/[94] → [101] → [102] → [89]` terminates, either at a peeling
state where the receiver is still saturated but no exit-`(4)` witness of the
applicable kind remains — the hypothesis under which exits `(5)`--`(8)` are
asked — or at a peeling state where the receiver is unsaturated, where
`lem:typeA-exit4-peeling-charge` gives it nonnegative remaining charge and the
peeled loads stand in the target-defect ledger.  The descent
(`Graph.ExitFour.terminal_or_unsaturated_from`) is run at the peeling state
node `[102]` committed; every intermediate step is one more exit-`(4)` witness
at the corresponding state, so the terminal peeling set is witnessed. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
noncomputable def typeAExitFourRetestDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : @FactKeys (Input BranchState Presentation presentation data)
      _ (factSystem BranchState Presentation presentation data)}
    (previous :
      @ExactLedger (Input BranchState Presentation presentation data)
        _ (factSystem BranchState Presentation presentation data) current known)
    [@FactKeys.Has (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data)
      (K .typeAExitFourPeeled) known]
    (freeFresh : K .typeASaturatedHandoffExitFourFree ∉ known)
    (dischargedFresh : K .typeAExitFourReceiverDischarged ∉ known) :
    @Decision (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data) current known
      (K .typeASaturatedHandoffExitFourFree) (K .typeAExitFourReceiverDischarged)
      previous :=
  @Decision.run (Input BranchState Presentation presentation data) _
    (factSystem BranchState Presentation presentation data) current known
    previous (K .typeASaturatedHandoffExitFourFree) (K .typeAExitFourReceiverDischarged)
    `Hypostructure.Graph.Strategy.Spine.typeAExitFourRetestDichotomy
    (by
      classical
      apply Classical.choice
      obtain ⟨packing, valid, maximal, component, present, negative, zero,
        receiver, isReceiver, peeled, peeledSubset, _saturated, witnessed, witness,
        _unpeeled, nextSubset, _drop⟩ :=
        (@ExactLedger.get (Input BranchState Presentation presentation data) _
          (factSystem BranchState Presentation presentation data)
          current known previous (K .typeAExitFourPeeled)).down
      let piece := current.object.pieceSupport
        (current.object.remainderSupport packing) component
      have exactDegree : ∀ vertex ∈ piece,
          current.object.degree vertex = data.threshold := by
        intro vertex member
        have lower : data.threshold ≤ current.object.degree vertex :=
          le_trans current.baseline (current.object.minDegree_le_degree vertex)
        have summand : current.object.degree vertex - data.threshold = 0 :=
          Nat.eq_zero_of_le_zero
            (zero ▸ Finset.single_le_sum
              (f := fun other => current.object.degree other - data.threshold)
              (fun _ _ => Nat.zero_le _) member)
        omega
      -- The descent from the peeled state.
      have descent := Graph.ExitFour.terminal_or_unsaturated_from piece
        data.threshold data.dischargeScale receiver
        (Retained := Graph.ExitFour.PeeledByWitnesses
          (Graph.HasCycleWithLength data.LengthOK) piece data.threshold receiver)
        (Terminal := fun state =>
          Graph.ExitFour.SaturatedAfter piece data.threshold data.dischargeScale
              receiver state ∧
            ((∃ package : Graph.ExitFour.VisibleFourUnpeeledPackage piece
                data.threshold data.dischargeScale receiver state,
              ¬ ∃ witness : Graph.ExitFour.Witness
                  (Graph.HasCycleWithLength data.LengthOK) piece
                  data.threshold receiver state,
                ∃ load ∈ Graph.ExitFour.selectedVisibleUnpeeledLoads
                    piece data.threshold data.dischargeScale receiver
                    package.outside state,
                  witness.load = load) ∨
              (Graph.ExitFour.SilentUnpeeledExcessAt piece
                  data.threshold data.dischargeScale receiver state ∧
                ¬ ∃ witness : Graph.ExitFour.Witness
                    (Graph.HasCycleWithLength data.LengthOK) piece
                    data.threshold receiver state,
                  witness.load ∈ Graph.ExitFour.unpeeledExcess piece
                    data.threshold data.dischargeScale receiver state)))
        nextSubset
        (Graph.ExitFour.peeledByWitnesses_nextPeeled witnessed witness)
        (by
          intro state stateInside stateWitnessed stateSaturated
          rcases Graph.ExitFour.visibleFourUnpeeled_or_silentUnpeeledExcess piece
              data.threshold data.dischargeScale receiver state
              (exactDegree receiver isReceiver.1) isReceiver stateSaturated with
            visible | silent
          · obtain ⟨package⟩ := Graph.ExitFour.visibleFourUnpeeledPackage piece
              data.threshold data.dischargeScale receiver state visible
            by_cases occurs :
                ∃ witness : Graph.ExitFour.Witness
                    (Graph.HasCycleWithLength data.LengthOK) piece data.threshold
                    receiver state,
                  ∃ load ∈ Graph.ExitFour.selectedVisibleUnpeeledLoads piece
                      data.threshold data.dischargeScale receiver package.outside
                      state,
                    witness.load = load
            · obtain ⟨next, _load, _selected, _equal⟩ := occurs
              exact Or.inr ⟨next.load, next.routed, next.fresh,
                Graph.ExitFour.peeledByWitnesses_nextPeeled stateWitnessed next⟩
            · exact Or.inl ⟨stateSaturated, Or.inl ⟨package, occurs⟩⟩
          · by_cases occurs :
                ∃ witness : Graph.ExitFour.Witness
                    (Graph.HasCycleWithLength data.LengthOK) piece data.threshold
                    receiver state,
                  witness.load ∈ Graph.ExitFour.unpeeledExcess piece
                    data.threshold data.dischargeScale receiver state
            · obtain ⟨next, _supported⟩ := occurs
              exact Or.inr ⟨next.load, next.routed, next.fresh,
                Graph.ExitFour.peeledByWitnesses_nextPeeled stateWitnessed next⟩
            · exact Or.inl ⟨stateSaturated, Or.inr ⟨silent, occurs⟩⟩)
      rcases descent with
        ⟨final, finalInside, _finalWitnessed, finalSaturated, finalNoWitness⟩ |
        ⟨final, finalInside, finalWitnessed, finalUnsaturated⟩
      · exact ⟨.inl ⟨⟨packing, valid, maximal, component, present, negative,
          zero, receiver, isReceiver, final, finalInside, finalSaturated,
          finalNoWitness⟩⟩⟩
      · exact ⟨.inr ⟨⟨packing, valid, maximal, component, present, negative,
          zero, receiver, isReceiver, final, finalInside, finalWitnessed,
          finalUnsaturated,
          (Graph.ExitFour.not_saturatedAfter_iff piece data.threshold
            data.dischargeScale receiver final).mp finalUnsaturated⟩⟩⟩)
    freeFresh dischargedFresh

/-! ## Node `[103]`: exit `(5)`, target-complete response compression

`def:typeA-saturated-exits` (5): at the selected saturated-handoff state after
exit `(4)` is absent, is there a target-complete compression of a proper
support?  The yes arm is `[104]`, forbidden by `cor:uncompressible` (the
framework's `Incompatible` closure against `K .uncompressible`); the no arm is
the hypothesis exit `(6)` is asked under. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
noncomputable def typeAExitFiveDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : @FactKeys (Input BranchState Presentation presentation data)
      _ (factSystem BranchState Presentation presentation data)}
    (previous :
      @ExactLedger (Input BranchState Presentation presentation data)
        _ (factSystem BranchState Presentation presentation data) current known)
    [@FactKeys.Has (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data)
      (K .typeASaturatedHandoffExitFourFree) known]
    (exitFresh : K .typeAExitFive ∉ known)
    (freeFresh : K .typeAExitFiveFree ∉ known) :
    @Decision (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data) current known
      (K .typeAExitFive) (K .typeAExitFiveFree) previous :=
  @Decision.run (Input BranchState Presentation presentation data) _
    (factSystem BranchState Presentation presentation data) current known
    previous (K .typeAExitFive) (K .typeAExitFiveFree)
    `Hypostructure.Graph.Strategy.Spine.typeAExitFiveDichotomy
    (by
      classical
      apply Classical.choice
      obtain ⟨packing, valid, maximal, component, present, negative, zero,
        receiver, isReceiver, peeled, peeledSubset, saturated, noExitFour⟩ :=
        (@ExactLedger.get (Input BranchState Presentation presentation data) _
          (factSystem BranchState Presentation presentation data)
          current known previous (K .typeASaturatedHandoffExitFourFree)).down
      by_cases compression :
          ∃ support : Finset current.object.Vertex,
            Graph.Strategy.InterfaceReplacement.CompressibleSupport
              (Graph.MinimumDegreeAtLeast data.threshold)
              (Graph.HasCycleWithLength data.LengthOK) current.object support
      · exact ⟨.inl ⟨⟨packing, valid, maximal, component, present, negative, zero,
          receiver, isReceiver, peeled, peeledSubset, saturated, noExitFour,
          compression⟩⟩⟩
      · exact ⟨.inr ⟨⟨packing, valid, maximal, component, present, negative, zero,
          receiver, isReceiver, peeled, peeledSubset, saturated, noExitFour,
          compression⟩⟩⟩)
    exitFresh freeFresh

/-! ## Nodes `[105]`--`[106]`: exit `(6)`, delocalization

`def:typeA-saturated-exits` (6): does the selected saturated-handoff state,
after exits `(4)` and `(5)` have failed, carry a declared response equality that
becomes target-complete only after adjoining a larger connected support?  Node
`[106]` then localizes it: a proper enlarging support gives the
proper-smearing replacement (`lem:proper-smearing`, forbidden by
`K .replacementExclusion`), the whole graph gives the strictly smaller closed
representative of `lem:no-silent-global-smearing` (forbidden by the selection's
minimality). -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
noncomputable def typeAExitSixDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : @FactKeys (Input BranchState Presentation presentation data)
      _ (factSystem BranchState Presentation presentation data)}
    (previous :
      @ExactLedger (Input BranchState Presentation presentation data)
        _ (factSystem BranchState Presentation presentation data) current known)
    [@FactKeys.Has (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data)
      (K .typeAExitFiveFree) known]
    (exitFresh : K .typeAExitSix ∉ known)
    (freeFresh : K .typeAExitSixFree ∉ known) :
    @Decision (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data) current known
      (K .typeAExitSix) (K .typeAExitSixFree) previous :=
  @Decision.run (Input BranchState Presentation presentation data) _
    (factSystem BranchState Presentation presentation data) current known
    previous (K .typeAExitSix) (K .typeAExitSixFree)
    `Hypostructure.Graph.Strategy.Spine.typeAExitSixDichotomy
    (by
      classical
      apply Classical.choice
      obtain ⟨packing, valid, maximal, component, present, negative, zero,
        receiver, isReceiver, peeled, peeledSubset, saturated, noExitFour,
        noCompression⟩ :=
        (@ExactLedger.get (Input BranchState Presentation presentation data) _
          (factSystem BranchState Presentation presentation data)
          current known previous (K .typeAExitFiveFree)).down
      let piece := current.object.pieceSupport
        (current.object.remainderSupport packing) component
      by_cases delocalizes : ExitSixDelocalizes data current.object piece
      · exact ⟨.inl ⟨⟨packing, valid, maximal, component, present, negative, zero,
          receiver, isReceiver, peeled, peeledSubset, saturated, noExitFour,
          noCompression, delocalizes⟩⟩⟩
      · exact ⟨.inr ⟨⟨packing, valid, maximal, component, present, negative, zero,
          receiver, isReceiver, peeled, peeledSubset, saturated, noExitFour,
          noCompression, delocalizes⟩⟩⟩)
    exitFresh freeFresh

omit [FactSystem (Input BranchState Presentation presentation data)] in
/-- Node `[106]`: the scope of the committed exit-`(6)` delocalization —
`Delocalization.localize` at the presented entry: proper (a replacement of the
enlarging support) or global (a strictly smaller closed representative). -/
noncomputable def typeAExitSixScopeDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : @FactKeys (Input BranchState Presentation presentation data)
      _ (factSystem BranchState Presentation presentation data)}
    (previous :
      @ExactLedger (Input BranchState Presentation presentation data)
        _ (factSystem BranchState Presentation presentation data) current known)
    [@FactKeys.Has (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data)
      (K .typeAExitSix) known]
    (properFresh : K .typeAExitSixProper ∉ known)
    (globalFresh : K .typeAExitSixGlobal ∉ known) :
    @Decision (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data) current known
      (K .typeAExitSixProper) (K .typeAExitSixGlobal) previous :=
  @Decision.run (Input BranchState Presentation presentation data) _
    (factSystem BranchState Presentation presentation data) current known
    previous (K .typeAExitSixProper) (K .typeAExitSixGlobal)
    `Hypostructure.Graph.Strategy.Spine.typeAExitSixScopeDichotomy
    (by
      classical
      apply Classical.choice
      obtain ⟨_packing, _valid, _maximal, _component, _present, _negative,
        _zero, _receiver, _isReceiver, _peeled, _peeledSubset, _saturated,
        _noExitFour, _noCompression, _presented, _supportEq, delocalizes⟩ :=
        (@ExactLedger.get (Input BranchState Presentation presentation data) _
          (factSystem BranchState Presentation presentation data)
          current known previous (K .typeAExitSix)).down
      obtain ⟨delocalization⟩ := delocalizes
      rcases delocalization.localize with proper | global
      · exact ⟨.inl ⟨⟨_, proper⟩⟩⟩
      · exact ⟨.inr ⟨global⟩⟩)
    properFresh globalFresh

/-! ## Node `[107]`: exit `(7)`, the decorated handoff fan

`def:typeA-saturated-exits` (7): is a high-degree decorated handoff fan
envelope produced at the selected residual after exits `(4)`--`(6)` have
failed?  The yes arm is reclassified at node `[108]` and leaves the Type A
charge calculation for Type B (`lem:typeA-exits-discharged`); the no arm is
node `[109]`, the route-8 residual of Part IX. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
noncomputable def typeAExitSevenDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : @FactKeys (Input BranchState Presentation presentation data)
      _ (factSystem BranchState Presentation presentation data)}
    (previous :
      @ExactLedger (Input BranchState Presentation presentation data)
        _ (factSystem BranchState Presentation presentation data) current known)
    [@FactKeys.Has (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data)
      (K .typeAExitSixFree) known]
    (producedFresh : K .typeAExitSevenProduced ∉ known)
    (freeFresh : K .typeAExitSevenFree ∉ known) :
    @Decision (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data) current known
      (K .typeAExitSevenProduced) (K .typeAExitSevenFree) previous :=
  @Decision.run (Input BranchState Presentation presentation data) _
    (factSystem BranchState Presentation presentation data) current known
    previous (K .typeAExitSevenProduced) (K .typeAExitSevenFree)
    `Hypostructure.Graph.Strategy.Spine.typeAExitSevenDichotomy
    (by
      classical
      apply Classical.choice
      obtain ⟨packing, valid, maximal, component, present, negative, zero,
        receiver, isReceiver, peeled, peeledSubset, saturated, noExitFour,
        noCompression, noDelocalization⟩ :=
        (@ExactLedger.get (Input BranchState Presentation presentation data) _
          (factSystem BranchState Presentation presentation data)
          current known previous (K .typeAExitSixFree)).down
      let piece := current.object.pieceSupport
        (current.object.remainderSupport packing) component
      by_cases produced : HandoffProduced data current.object packing piece
      · exact ⟨.inl ⟨⟨packing, valid, maximal, component, present, negative, zero,
          receiver, isReceiver, peeled, peeledSubset, saturated, noExitFour,
          noCompression, noDelocalization, produced⟩⟩⟩
      · exact ⟨.inr ⟨⟨packing, valid, maximal, component, present, negative, zero,
          receiver, isReceiver, peeled, peeledSubset, saturated, noExitFour,
          noCompression, noDelocalization, produced⟩⟩⟩)
    producedFresh freeFresh
end Hypostructure.Graph.Strategy.Spine
