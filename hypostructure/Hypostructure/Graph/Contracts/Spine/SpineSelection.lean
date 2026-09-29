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

/-- **Node `[13]`, `lem:replacement`**, stated about G.  A replacement `X'`
of a proper support `Z` makes `G' = glue X' (G − Z)` a strictly smaller
baseline object, so the selection's minimality gives `G'` a power-of-two
cycle, which the replacement excludes. -/
theorem replacementExclusion_of_selection
    {BranchState : Graph.FiniteObject.{u} → Type v}
    {Presentation : Type} {presentation : Presentation}
    (data : Parameters) (object : Graph.FiniteObject.{u})
    (selection : SelectionStatement BranchState Presentation presentation data object) :
    ReplacementExclusionStatement data object :=
  Graph.Strategy.InterfaceReplacement.not_replacementSupport_of_minimal
    (fun H smaller baseline => selection.2 H smaller baseline)

/-- **Node `[11]`, `lem:degree-profile-fibres`** (tex 6088), at the pieces
constructed from G.  The paper's proof: "condition (a) in the definition of a
target-complete quotient requires the quotient to preserve the boundary degree
profile ... an identification of `X₁` with `X₂` would identify two different
boundary-degree profiles, so it violates condition (a)".  Every admissible
quotient of G's declared coordinates carries condition (a) as its `fibrewise`
clause (`def:admissible-rank-quotient`, which requires target-completeness). -/
theorem degreeProfileFibres_holds (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    DegreeProfileFibresStatement data object :=
  fun _region quotient left right different identified =>
    different (quotient.fibrewise left right identified)

/-- **Node `[12]`, `lem:context-universality`** (tex 6106), stated about G,
reading node `[11]` and the selection.  Two constructed pieces an admissible
quotient of G's declared coordinates identifies lie in one boundary-degree
fibre (node `[11]`, contrapositive) and have the same response in G's own rest
`G − Z` (condition (b) of the admissible quotient,
`DeclaredQuotient.contextUniversal`).  No reading of G at any support closes a
power-of-two cycle in `G − Z`: such a gluing is a subgraph of G, which avoids
the target. -/
theorem targetCompleteContextUniversality_of_degreeProfileFibres
    {BranchState : Graph.FiniteObject.{u} → Type v}
    {Presentation : Type} {presentation : Presentation}
    (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (fibres : DegreeProfileFibresStatement data object)
    (selection : SelectionStatement BranchState Presentation presentation data object) :
    TargetCompleteContextUniversalityStatement data object := by
  refine ⟨fun region quotient left right identified => ⟨?_, ?_⟩,
    fun support reading => Graph.ActualContext.not_target_actualGlue selection.1
      support reading⟩
  · by_contra different
    exact fibres region quotient left right different identified
  · exact quotient.contextUniversal left right identified

end Hypostructure.Graph.Contracts.Spine
