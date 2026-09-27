import Hypostructure.Graph.Contracts.TypeB.Support

/-!
# Contracts: the B2 post-ledger core

`lem:typeB-postledger-core-hygiene` and B2(d) of `def:typeB-bridge-statements`
on one disjoint ledger of a canonical remainder piece, proved once for every
consumer.
-/

namespace Hypostructure.Graph.Contracts.TypeB

open Hypostructure
open Hypostructure.Graph.Strategy.Spine

universe u

variable {data : Parameters} {object : Graph.FiniteObject.{u}}

/-- On a target-avoiding, uncompressible, remainder-normalized object, every
remaining component of a B2 disjoint ledger on a canonical piece of G's fixed
packing `P₀` carries the post-ledger Type A hygiene, and the exit-`(7)` productions
of any remaining components form the grouped decorated envelope. -/
theorem disjointLedgerCoreClosure
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (baseline : ∀ vertex : object.Vertex, data.threshold ≤ object.degree vertex)
    (uncompressible : UncompressibleStatement data object)
    (normalized : RemainderNormalizedStatement data object)
    {piece : Graph.TypeBRefinedSupport.CanonicalPiece object
      (canonicalWindowPacking data object)}
    {centres : Finset object.Vertex}
    (ledger : Graph.TypeBRefinedSupport.DisjointLedger object data.threshold
      data.dischargeScale (canonicalWindowPacking data object) piece.vertices centres) :
    PostLedgerComponents data object ledger ∧
      GroupedEnvelopeCoverage data object ledger := by
  classical
  have noBaselineSubsupport : ∀ subset : Finset object.Vertex,
      subset ⊆ object.remainderSupport (canonicalWindowPacking data object) →
        ¬ Graph.MinimumDegreeAtLeast data.threshold (object.induce subset) :=
    fun subset inside => (normalized subset inside).2
  have pieceFree : Graph.InducedPathFree (object.induce piece.vertices)
      data.windowOrder :=
    Graph.FiniteObject.inducedPathFree_induce_of_forall object
      (fun subset inside =>
        (normalized subset
          (inside.trans piece.vertices_subset_remainder)).1)
  have emptyInternal : Graph.TypeAB.EmptyInternalThreeCore
      data.typeABPresentation object piece.vertices :=
    Graph.TypeBPostLedgerCore.emptyInternalThreeCore_of_noBaselineSubsupport
      (threshold := data.threshold) rfl
      (fun subset inside =>
        noBaselineSubsupport subset
          (inside.trans piece.vertices_subset_remainder))
  have targetSafe : Graph.TypeAB.ContextuallyDyadicSafe
      data.typeABPresentation object := by
    simpa [Graph.TypeAB.ContextuallyDyadicSafe,
      Parameters.typeABPresentation] using avoids
  have hereditary : Graph.TypeAB.HereditarilyTargetUncompressible
      data.typeABPresentation object piece.vertices :=
    Graph.TypeAB.hereditarilyTargetUncompressible_of_emptyInternalThreeCore
      emptyInternal
  have components : PostLedgerComponents data object ledger :=
    fun component member =>
      Graph.TypeBPostLedgerCore.postLedgerCoreHygiene
        data.typeABPresentation ledger component member rfl
        noBaselineSubsupport pieceFree targetSafe hereditary baseline
  refine ⟨components, ?_⟩
  intro selectedComponents subset production
  have windowFree : ∀ component, component ∈ selectedComponents →
      handoffWindowFree data object
        (Graph.SupportComponents.Connected.vertices object
          ledger.remainingCore component) := by
    intro component member
    have componentData := components component (subset component member)
    constructor
    · intro window windowSubset induces
      exact (normalized window
        (windowSubset.trans componentData.containedInRemainder)).1 induces
    · intro internal internalSubset
      exact (normalized internal
        (internalSubset.trans componentData.containedInRemainder)).2
  refine ⟨Graph.TypeBMaximalCompletion.groupedOfComponentExitSeven
    ledger selectedComponents production avoids windowFree
      (handoffUncompressible_of_uncompressible uncompressible),
    ?_, ?_⟩
  · intro component
    exact Graph.TypeBMaximalCompletion.Grouped.envelope_core
      ledger selectedComponents production avoids windowFree
      (handoffUncompressible_of_uncompressible uncompressible)
      component
  · intro centre
    exact Graph.TypeBMaximalCompletion.Grouped.mem_centres_iff
      ledger selectedComponents production avoids windowFree
      (handoffUncompressible_of_uncompressible uncompressible)
      centre

end Hypostructure.Graph.Contracts.TypeB
