import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.ColdIncrementArithmetic
import Hypostructure.Graph.ColdGermFamily
import Hypostructure.Graph.Strategy.ColdCorridorRows.Basic

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-! ## Node `[165]`, `lem:refined-minimality-swap`: the canonical exchange

The no-arm of `[163]` enters the canonical-replacement case.  This row proves
the manuscript's exchange uniformly: for every neutral configuration, if its
canonical representative `E` is different from the corridor piece `Q`, gluing
`E` into the retained outside context preserves the baseline, target
avoidance, vertex count, and edge count, and replaces `Q` by a strict
predecessor in the fixed canonical piece order.  The refined-minimality
contradiction belongs to node `[166]`.
-/
@[reducible] noncomputable def canonicalReplacementSwapRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.canonicalReplacementSwap
    { Requires := [K .coldCanonicalNeutralConfiguration]
      Produces := [K .coldCanonicalReplacementSwap]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let canonical :=
        (inputs.get (K .coldCanonicalNeutralConfiguration)).down
      .cons (key := K .coldCanonicalReplacementSwap)
        ⟨by
          classical
          change CanonicalNeutralConfigurationStatement data
            inputs.current.object at canonical
          change CanonicalReplacementSwapStatement data inputs.current.object
          obtain ⟨_markedGerm, _markedRepresentative, _markedConfiguration,
            _notRealized⟩ := canonical
          intro germ representative configuration different
          dsimp only
          obtain ⟨_active, representativeReading, equalSize, canonicalPosition,
            sourceAvoids⟩ := configuration
          let baselineInvariant :=
            Graph.minimumDegreeAtLeast_isomorphismInvariant data.threshold
          have reconstruction :
              (Graph.glue germ.piece germ.atom.outside).Isomorphic
                inputs.current.object :=
            ⟨germ.atom.reconstructionIso⟩
          have sourceBaseline :
              Graph.MinimumDegreeAtLeast data.threshold
                (Graph.glue germ.piece germ.atom.outside) :=
            (baselineInvariant.iff_of_iso reconstruction).mpr
              inputs.current.baseline
          have swappedBaseline :
              Graph.MinimumDegreeAtLeast data.threshold
                (Graph.glue representative.toPiece germ.atom.outside) :=
            representativeReading.1.2.2 germ.atom.outside sourceBaseline
          have swappedAvoids :
              ¬ Graph.HasCycleWithLength data.LengthOK
                (Graph.glue representative.toPiece germ.atom.outside) := by
            intro hit
            exact sourceAvoids
              ((representativeReading.1.2.1 germ.atom.outside).mp hit)
          have vertexCountEq :
              (Graph.glue representative.toPiece germ.atom.outside).vertexCount =
                inputs.current.object.vertexCount := by
            calc
              (Graph.glue representative.toPiece
                  germ.atom.outside).vertexCount =
                  (Graph.glue germ.piece germ.atom.outside).vertexCount := by
                    simp only [Graph.glue_vertexCount,
                      Graph.CanonicalPiece.toPiece_internalVertexCount]
                    omega
              _ = inputs.current.object.vertexCount :=
                Graph.FiniteObject.vertexCount_eq_of_isomorphic reconstruction
          have edgeCountEq :
              (Graph.glue representative.toPiece germ.atom.outside).edgeCount =
                inputs.current.object.edgeCount := by
            calc
              (Graph.glue representative.toPiece
                  germ.atom.outside).edgeCount =
                  (Graph.glue germ.piece germ.atom.outside).edgeCount :=
                    representativeReading.2
              _ = inputs.current.object.edgeCount :=
                Graph.FiniteObject.edgeCount_eq_of_isomorphic reconstruction
          obtain ⟨representativePrecedes, refinedDecrease⟩ :=
            canonicalPosition.resolve_left different
          exact ⟨swappedBaseline, swappedAvoids, vertexCountEq, edgeCountEq,
            representativePrecedes, refinedDecrease⟩⟩
        .nil)

/-! ## Node `[166]`: refined minimality forces the trivial replacement -/

@[reducible] noncomputable def canonicalReplacementTrivialRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.canonicalReplacementTrivial
    { Requires := [K .selection, K .coldCanonicalReplacementSwap]
      Produces := [K .coldCanonicalReplacementTrivial]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let selected := (inputs.get (K .selection)).down
      let swap := (inputs.get (K .coldCanonicalReplacementSwap)).down
      .cons (key := K .coldCanonicalReplacementTrivial)
        ⟨by
          classical
          change CanonicalReplacementSwapStatement data inputs.current.object at swap
          change CanonicalReplacementTrivialStatement data inputs.current.object
          intro germ representative configuration
          by_contra different
          let swapped := Graph.glue representative.toPiece germ.atom.outside
          obtain ⟨baseline, avoids, _vertexCount, _edgeCount,
              _precedes, refinedDecrease⟩ :=
            swap germ representative configuration different
          have smaller :
              (refinedProgress BranchState Presentation presentation data).Smaller
                swapped inputs.current.object :=
            (refinedProgress_smaller_iff BranchState Presentation presentation data).2
              refinedDecrease
          exact avoids
            (selected.2.refinedMinimal swapped smaller baseline)⟩
        .nil)

/-! ## `lem:refined-minimality-swap`, the size split of the canonical replacement

On the residual where a neutral germ has a canonical replacement piece
`E ≠ Q[x,y]`, the fixed canonical order compares sizes first: either `E` has
strictly fewer internal vertices — then exchanging `Q` for `E` is a strictly
smaller counterexample and the `[4]` minimality closes (node `[165]`) — or `E`
has the same size, which is the tie-break of node `[166]`. -/
noncomputable def canonicalSwapSizeDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous : ExactLedger
      (Input BranchState Presentation presentation data) current known)
    [FactKeys.Has (K .coldCanonicalNeutralConfiguration) known]
    (smallerFresh : K .coldCanonicalSwapSmaller ∉ known)
    (sameFresh : K .coldCanonicalSwapSameSize ∉ known) :
    Decision (K .coldCanonicalSwapSmaller) (K .coldCanonicalSwapSameSize) previous := by
  classical
  let _proper := (previous.get (K .coldCanonicalNeutralConfiguration)).down
  exact Decision.run previous (K .coldCanonicalSwapSmaller) (K .coldCanonicalSwapSameSize)
    `Hypostructure.Graph.Strategy.Spine.canonicalSwapSizeDichotomy
    (if smaller : ∃ germ : Graph.ColdCorridor.BoundedGerm data.coldSignature
          (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) current.object,
        germ.Neutral ∧
          (germCanonicalRepresentative data germ).size < germ.piece.internalVertexCount then
      .inl ⟨smaller⟩
    else
      .inr ⟨by
        intro germ neutral lt
        exact smaller ⟨germ, neutral, lt⟩⟩)
    smallerFresh sameFresh

end Hypostructure.Graph.Strategy.Spine
