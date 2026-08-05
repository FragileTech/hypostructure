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
variable {threshold : Nat} {LengthOK : Nat → Prop}

/-- The residual domain of a minimum-degree cycle spine. -/
abbrev Input (BranchState : Graph.FiniteObject.{u} → Type v)
    (Presentation : Type) (presentation : Presentation) (threshold : Nat) :=
  Core.Strategy.ProblemInput
    (problem BranchState Presentation presentation threshold)

variable [FactSystem (Input BranchState Presentation presentation threshold)]

/-- **The selected context, as the ledger records it.**

Nodes `[11]` onwards call framework theorems that are stated against a
`MinimalCounterexampleContext`.  This rebuilds that context from the residual
and the selection *fact* — its two components are exactly the context's
`avoids` and its minimality kernel — so a later row consumes the committed
fact rather than re-selecting, re-deriving, or re-quantifying over the ambient
graph.  Nothing is proved here; this is the reading of one ledger entry. -/
def contextOfSelection
    (input : Input BranchState Presentation presentation threshold)
    (avoids : ¬ Graph.HasCycleWithLength LengthOK input.object)
    (minimal : ∀ smaller : Graph.FiniteObject.{u},
      (progress BranchState Presentation presentation threshold).Smaller
        smaller input.object →
      Graph.MinimumDegreeAtLeast threshold smaller →
      Graph.HasCycleWithLength LengthOK smaller) :
    Core.MinimalCounterexampleContext
      (problem BranchState Presentation presentation threshold)
      (Graph.HasCycleWithLength LengthOK)
      (progress BranchState Presentation presentation threshold) where
  G := input.object
  baseline := input.baseline
  state := input.branchState
  avoids := avoids
  minimal := minimal

/-- The manifest shape shared by every one-in/one-out spine row. -/
abbrev rowManifest
    (required produced :
      FactKey (Input BranchState Presentation presentation threshold))
    (distinct : required ≠ produced) :
    FactManifest (Input BranchState Presentation presentation threshold) where
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
noncomputable def returnAvoidanceRow
    (selection returnAvoidance :
      FactKey (Input BranchState Presentation presentation threshold))
    (distinct : selection ≠ returnAvoidance)
    (avoidsOf : (input : Input BranchState Presentation presentation threshold) →
      selection.At input → ¬ Graph.HasCycleWithLength LengthOK input.object)
    (encode : (input : Input BranchState Presentation presentation threshold) →
      (∀ dart : input.object.graph.Dart,
        Disjoint (Graph.returnLengthSet input.object dart)
          (Graph.shiftedAcceptedSet LengthOK)) →
      returnAvoidance.At input) :
    AtomicStrategy (Input BranchState Presentation presentation threshold) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.returnAvoidance
    (rowManifest selection returnAvoidance distinct)
    (fun inputs =>
      .cons (key := returnAvoidance)
        (encode inputs.current
          ((Graph.not_hasCycleWithLength_iff_returnLengthSets_disjoint LengthOK
              inputs.current.object).mp
            (avoidsOf inputs.current (inputs.get selection))))
        .nil)

/-! ## Node `[8]`: no proper subgraph satisfies the baseline

`lem:no-proper-core`.  A proper subgraph is strictly smaller in the registered
order, so minimality forces it to have an accepted cycle; but every cycle of a
proper subgraph is a cycle of the ambient graph
(`Graph.cycleProperSubgraphTargetMonotone`), which the selected object does not
have.  So no proper subgraph satisfies the baseline. -/
noncomputable def noProperBaselineRow
    (selection noProperBaseline :
      FactKey (Input BranchState Presentation presentation threshold))
    (distinct : selection ≠ noProperBaseline)
    (avoidsOf : (input : Input BranchState Presentation presentation threshold) →
      selection.At input → ¬ Graph.HasCycleWithLength LengthOK input.object)
    (minimalOf : (input : Input BranchState Presentation presentation threshold) →
      selection.At input →
      ∀ smaller : Graph.FiniteObject.{u},
        smaller.LexicographicallySmaller input.object →
        Graph.MinimumDegreeAtLeast threshold smaller →
        Graph.HasCycleWithLength LengthOK smaller)
    (encode : (input : Input BranchState Presentation presentation threshold) →
      (∀ subgraph : Graph.ProperSubgraph input.object,
        ¬ Graph.MinimumDegreeAtLeast threshold subgraph.value) →
      noProperBaseline.At input) :
    AtomicStrategy (Input BranchState Presentation presentation threshold) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.noProperBaseline
    (rowManifest selection noProperBaseline distinct)
    (fun inputs =>
      let fact := inputs.get selection
      .cons (key := noProperBaseline)
        (encode inputs.current fun subgraph baseline =>
          avoidsOf inputs.current fact
            ((Graph.cycleProperSubgraphTargetMonotone LengthOK).map subgraph
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
      FactKey (Input BranchState Presentation presentation threshold))
    (tightFresh : tight ≠ required) (slackFresh : slack ≠ required)
    (distinct : tight ≠ slack) :
    FactManifest (Input BranchState Presentation presentation threshold) where
  Requires := [required]
  Produces := [tight, slack]
  requiresUnique := by simp
  producesUnique := by simp [distinct]
  producesNonempty := by simp

/-- **Nodes `[9]`--`[10]`.** -/
noncomputable def deletionCriticalityRow
    (noProperBaseline tightEndpoint slackIndependent :
      FactKey (Input BranchState Presentation presentation threshold))
    (tightFresh : tightEndpoint ≠ noProperBaseline)
    (slackFresh : slackIndependent ≠ noProperBaseline)
    (distinct : tightEndpoint ≠ slackIndependent)
    (excludes : (input : Input BranchState Presentation presentation threshold) →
      noProperBaseline.At input →
      ∀ subgraph : Graph.ProperSubgraph input.object,
        ¬ Graph.MinimumDegreeAtLeast threshold subgraph.value)
    (encodeTight :
      (input : Input BranchState Presentation presentation threshold) →
      (∀ dart : input.object.graph.Dart,
        input.object.degree dart.fst = threshold ∨
          input.object.degree dart.snd = threshold) →
      tightEndpoint.At input)
    (encodeSlack :
      (input : Input BranchState Presentation presentation threshold) →
      (∀ left right : input.object.Vertex,
        threshold < input.object.degree left →
        threshold < input.object.degree right →
        ¬ input.object.graph.Adj left right) →
      slackIndependent.At input) :
    AtomicStrategy (Input BranchState Presentation presentation threshold) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.deletionCriticality
    (criticalityManifest noProperBaseline tightEndpoint slackIndependent
      tightFresh slackFresh distinct)
    (fun inputs =>
      let object := inputs.current.object
      let profile := Graph.minimumDegreeDeletionCriticalityProfile threshold
      let noProper := excludes inputs.current (inputs.get noProperBaseline)
      -- Node `[9]`: an edge with two slack endpoints would survive deletion.
      let tight : ∀ dart : object.graph.Dart,
          object.degree dart.fst = threshold ∨
            object.degree dart.snd = threshold := by
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

end Hypostructure.Graph.Strategy.Spine
