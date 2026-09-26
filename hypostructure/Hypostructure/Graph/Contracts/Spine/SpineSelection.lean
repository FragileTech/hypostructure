import Hypostructure.Graph.Statements.Spine

/-!
# Contracts: the selection's first consequences `[5]`--`[14]`

Proof-agnostic contract lemmas for the facts read directly off the selected
object: return avoidance, no proper baseline subgraph, deletion criticality,
the cycle-rank bound, and interface-replacement exclusion.  Each lemma is
stated over a `Graph.FiniteObject` with the registered `Parameters` as a
parameter and every hypothesis explicit; its conclusion is exactly the
statement of the fact it proves.  This module imports no strategy, row, or
vocabulary module.
-/

namespace Hypostructure.Graph.Contracts.Spine

open Hypostructure
open Hypostructure.Graph.Strategy.Spine

universe u v

/-- **Node `[6]`, no arm.**  If no oriented edge carries a Mersenne return, then
every return-length set is disjoint from the shifted accepted set. -/
theorem returnAvoidance_of_not_mersenneReturn (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (noReturn : ¬ MersenneReturnStatement data object) :
    ReturnAvoidanceStatement data object := fun dart => by
  by_contra meets
  exact noReturn ⟨dart, meets⟩

/-- **Node `[7]`, `lem:return-equivalence`.**  A target-avoiding object carries
no Mersenne return: a Mersenne return is an accepted cycle. -/
theorem not_mersenneReturn_of_avoids (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object) :
    ¬ MersenneReturnStatement data object := by
  rintro ⟨dart, meets⟩
  exact meets
    ((Graph.not_hasCycleWithLength_iff_returnLengthSets_disjoint data.LengthOK
      object).mp avoids dart)

/-- **Node `[8]`, `lem:no-proper-core`.**  A proper subgraph is strictly smaller,
so minimality gives it an accepted cycle, which is a cycle of the selected
object; hence no proper subgraph meets the baseline, and the object is
connected. -/
theorem noProperBaseline_of_selection
    {BranchState : Graph.FiniteObject.{u} → Type v}
    {Presentation : Type} {presentation : Presentation}
    (data : Parameters) (object : Graph.FiniteObject.{u})
    (baseline : Graph.MinimumDegreeAtLeast data.threshold object)
    (three_le_threshold : 3 ≤ data.threshold)
    (selection : SelectionStatement BranchState Presentation presentation data object) :
    NoProperBaselineStatement data object :=
  let noProper : ∀ subgraph : Graph.ProperSubgraph object,
      ¬ Graph.MinimumDegreeAtLeast data.threshold subgraph.value :=
    fun subgraph subgraphBaseline =>
      selection.1
        ((Graph.cycleProperSubgraphTargetMonotone data.LengthOK).map subgraph
          (selection.2 subgraph.value subgraph.decreases subgraphBaseline))
  ⟨noProper,
    object.connected_of_noProperBaseline data.threshold
      (lt_of_lt_of_le (by omega) three_le_threshold) baseline noProper⟩

/-- **Node `[9]`, `lem:deletion-critical`.**  An edge with both endpoints
strictly above the threshold could be deleted keeping the baseline, producing a
proper baseline subgraph. -/
theorem tightEndpoint_of_noProperBaseline (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (baseline : Graph.MinimumDegreeAtLeast data.threshold object)
    (noProperBaseline : NoProperBaselineStatement data object) :
    TightEndpointStatement data object := by
  intro dart
  by_contra noncritical
  exact noProperBaseline.1
    (Graph.ProperSubgraph.deleteEdge object (object.edgeOfDart dart))
    ((Graph.minimumDegreeDeletionCriticalityProfile data.threshold).baseline_of_not_critical
      baseline dart noncritical)

/-- **Node `[10]`.**  Two adjacent vertices strictly above the threshold would
form an edge with no tight endpoint. -/
theorem slackIndependent_of_tightEndpoint (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (tight : TightEndpointStatement data object) :
    SlackIndependentStatement data object :=
  fun left right leftSlack rightSlack adjacent =>
    match tight ⟨(left, right), adjacent⟩ with
    | .inl atThreshold => Nat.ne_of_lt' leftSlack atThreshold
    | .inr atThreshold => Nat.ne_of_lt' rightSlack atThreshold

/-- **`lem:cycle-rank`.**  From the handshake `3n ≤ 2m` at a baseline of at
least three, `2β(G) ≥ n + 2`. -/
theorem cycleRankConstraint_of_baseline (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (baseline : Graph.MinimumDegreeAtLeast data.threshold object)
    (three_le_threshold : 3 ≤ data.threshold) :
    CycleRankConstraintStatement object := by
  have lower : ∀ vertex : object.Vertex, data.threshold ≤ object.degree vertex :=
    fun vertex => baseline.trans (object.minDegree_le_degree vertex)
  have thresholdHandshake :
      data.threshold * object.vertexCount ≤ 2 * object.edgeCount :=
    Graph.baselineDegree_mul_vertexCount_le_two_mul_edgeCount
      object data.threshold lower
  have handshake : 3 * object.vertexCount ≤ 2 * object.edgeCount :=
    (Nat.mul_le_mul_right object.vertexCount three_le_threshold).trans
      thresholdHandshake
  change object.vertexCount + 2 ≤
    2 * (object.edgeCount + 1 - object.vertexCount)
  have rankNontruncated : object.vertexCount ≤ object.edgeCount + 1 := by
    omega
  rw [Nat.mul_sub_left_distrib]
  exact Nat.le_sub_of_add_le (by omega)

/-- **Node `[13]`, `lem:replacement`.**  A target-complete compression of a
proper atom would give a strictly smaller baseline object whose obstruction
profile is contained in the original's; minimality gives that object the
target, the shared outside context carries it back, and the reconstruction is
isomorphic to the selected object, which avoids the target. -/
theorem replacementExclusion_of_selection
    {BranchState : Graph.FiniteObject.{u} → Type v}
    {Presentation : Type} {presentation : Presentation}
    (data : Parameters) (object : Graph.FiniteObject.{u})
    (baseline : Graph.MinimumDegreeAtLeast data.threshold object)
    (state : BranchState object)
    (selection : SelectionStatement BranchState Presentation presentation data object) :
    ReplacementExclusionStatement data object := by
  let context :
      Core.MinimalCounterexampleContext
        (Strategy.Spine.problem BranchState Presentation presentation data)
        (Graph.HasCycleWithLength data.LengthOK)
        (Strategy.Spine.progress BranchState Presentation presentation data) :=
    { G := object
      baseline := baseline
      state := state
      avoids := selection.1
      minimal := selection.2.sizeMinimal }
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
  intro support replacementSupport
  rcases replacementSupport with
    ⟨connected, proper, replacement, signatureEq, replacementBaseline, smaller,
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
      baseline := replacementBaseline
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
      (profile.assembly.reconstruct context.G site)).mp sourceTarget)

end Hypostructure.Graph.Contracts.Spine
