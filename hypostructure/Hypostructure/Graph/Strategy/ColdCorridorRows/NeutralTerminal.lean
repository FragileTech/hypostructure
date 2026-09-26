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

/-! ## Node `[163]`, `lem:neutral-germ-symmetry`: the symmetry split

A neutral equal-length terminal germ carries no target information; it is a
symmetry.  The manuscript's question is whether its second representative is
graph-realized as a genuine second strand.  The yes-arm is the two-strand route
`[167]`; the no-arm is the canonical-replacement route `[165]`--`[166]`.
Canonical order is deliberately absent from this decision.  Both arms retain
the exact marked configuration read from the incoming `ExactLedger`. -/
@[reducible] noncomputable def neutralEqualLengthTerminalRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.neutralEqualLengthTerminal
    { Requires := [K .coldGermFamilyPositive, K .denseColdCorridorsTerminal,
        K .selection]
      Produces := [K .coldNeutralEqualLengthTerminal]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let positive := (inputs.get (K .coldGermFamilyPositive)).down
      let terminal := (inputs.get (K .denseColdCorridorsTerminal)).down
      let selected := (inputs.get (K .selection)).down
      .cons (key := K .coldNeutralEqualLengthTerminal)
        ⟨by
          classical
          let object := inputs.current.object
          letI : FinEnum object.Vertex := object.vertices
          change ColdGermFamilyPositiveStatement data.toParameters object at positive
          rcases positive with
            ⟨routing, incidence, candidates, disjointFamily, corridorLoss,
              familyWitness, positiveCard⟩
          obtain ⟨epsilon, epsilonMem⟩ := Finset.card_pos.mp positiveCard
          let germ := incidence epsilon
          have active : ActiveColdGermStatement data.toParameters object germ := by
            refine ⟨routing, incidence, candidates, disjointFamily, corridorLoss,
              familyWitness, ?_⟩
            exact ⟨epsilon, epsilonMem, rfl⟩
          let baselineInvariant :=
            Graph.minimumDegreeAtLeast_isomorphismInvariant data.threshold
          let targetInvariant :=
            (Graph.cycleTargetInterface data.LengthOK).isomorphismInvariant
          let Reading : Graph.CanonicalPiece germ.atom.interface → Prop :=
            fun candidate =>
              Graph.CanonicalPiece.CutStateReading
                  (Graph.MinimumDegreeAtLeast data.threshold)
                  (Graph.HasCycleWithLength data.LengthOK)
                  germ.piece candidate ∧
                (Graph.glue candidate.toPiece germ.atom.outside).edgeCount =
                  (Graph.glue germ.piece germ.atom.outside).edgeCount
          have sourceCutState :
              Graph.CanonicalPiece.CutStateReading
                (Graph.MinimumDegreeAtLeast data.threshold)
                (Graph.HasCycleWithLength data.LengthOK)
                germ.piece germ.piece.toCanonical :=
            Graph.CanonicalPiece.cutStateReading_toCanonical
              baselineInvariant targetInvariant germ.piece
          have sourceEdgeCount :
              (Graph.glue germ.piece.toCanonical.toPiece germ.atom.outside).edgeCount =
                (Graph.glue germ.piece germ.atom.outside).edgeCount :=
            Graph.FiniteObject.edgeCount_eq_of_isomorphic
              (germ.piece.toCanonical_glue_isomorphic germ.atom.outside)
          have sourceReading : Reading germ.piece.toCanonical :=
            ⟨sourceCutState, sourceEdgeCount⟩
          have realizable : ∃ candidate, Reading candidate :=
            ⟨germ.piece.toCanonical, sourceReading⟩
          let canonical :=
            Graph.CanonicalPiece.canonicalRepresentative Reading realizable
          have canonicalReading : Reading canonical :=
            Graph.CanonicalPiece.canonicalRepresentative_reading Reading realizable
          have canonicalSizeLe :
              canonical.size ≤ germ.piece.internalVertexCount := by
            calc
              canonical.size ≤ germ.piece.toCanonical.size :=
                Graph.CanonicalPiece.canonicalRepresentative_size_le
                  Reading realizable sourceReading
              _ = germ.piece.internalVertexCount := rfl
          have sourceAvoids :
              ¬ Graph.HasCycleWithLength data.LengthOK
                  (Graph.glue germ.piece germ.atom.outside) := by
            intro hit
            exact selected.1
              ((targetInvariant.iff_of_iso
                ⟨germ.atom.reconstructionIso⟩).mp hit)
          have sourceBaseline :
              Graph.MinimumDegreeAtLeast data.threshold
                (Graph.glue germ.piece germ.atom.outside) :=
            (baselineInvariant.iff_of_iso
              ⟨germ.atom.reconstructionIso⟩).mpr
                inputs.current.baseline
          have canonicalNotShorter :
              ¬ canonical.size < germ.piece.internalVertexCount := by
            intro shorter
            have cutState := canonicalReading.1
            have swappedBaseline :
                Graph.MinimumDegreeAtLeast data.threshold
                  (Graph.glue canonical.toPiece germ.atom.outside) :=
              cutState.2.2 germ.atom.outside sourceBaseline
            have swappedAvoids :
                ¬ Graph.HasCycleWithLength data.LengthOK
                    (Graph.glue canonical.toPiece germ.atom.outside) := by
              intro hit
              exact sourceAvoids ((cutState.2.1 germ.atom.outside).mp hit)
            have swappedSmaller :
                Graph.FiniteObject.LexicographicallySmaller
                  (Graph.glue canonical.toPiece germ.atom.outside) object := by
              refine (Graph.FiniteObject.lexicographicallySmaller_congr_right
                ⟨germ.atom.reconstructionIso⟩).mp ?_
              apply Graph.FiniteObject.lexicographicallySmaller_of_vertexCount_lt
              have sourcePieceCount :
                  germ.atom.piece.internalVertexCount =
                    germ.piece.internalVertexCount := rfl
              simp only [Graph.glue_vertexCount,
                Graph.CanonicalPiece.toPiece_internalVertexCount]
              rw [sourcePieceCount]
              omega
            exact swappedAvoids
              (selected.2 (Graph.glue canonical.toPiece germ.atom.outside)
                swappedSmaller swappedBaseline)
          have canonicalEqualLength :
              canonical.size = germ.piece.internalVertexCount :=
            Nat.le_antisymm canonicalSizeLe
              (Nat.le_of_not_gt canonicalNotShorter)
          let representative :=
            if RefinedLexicographicallySmaller
                (Graph.glue canonical.toPiece germ.atom.outside) object then
              canonical
            else
              germ.piece.toCanonical
          have representativeReading : Reading representative := by
            dsimp only [representative]
            split
            · exact canonicalReading
            · exact sourceReading
          have equalLength :
              representative.size = germ.piece.internalVertexCount := by
            dsimp only [representative]
            split
            · exact canonicalEqualLength
            · rfl
          have canonicalPosition :
              representative = germ.piece.toCanonical ∨
                (Graph.CanonicalPiece.Precedes representative
                    germ.piece.toCanonical ∧
                  RefinedLexicographicallySmaller
                    (Graph.glue representative.toPiece germ.atom.outside)
                    object) := by
            classical
            dsimp only [representative]
            split <;> rename_i decrease
            · by_cases same : canonical = germ.piece.toCanonical
              · exact Or.inl same
              · exact Or.inr ⟨
                  Graph.CanonicalPiece.canonicalRepresentative_precedes
                    Reading realizable sourceReading (Ne.symm same),
                  decrease⟩
            · exact Or.inl rfl
          refine ⟨terminal, germ, representative, ?_⟩
          change ActiveColdGermStatement data.toParameters object germ ∧
            (Graph.CanonicalPiece.CutStateReading
                (Graph.MinimumDegreeAtLeast data.threshold)
                (Graph.HasCycleWithLength data.LengthOK)
                germ.piece representative ∧
              (Graph.glue representative.toPiece germ.atom.outside).edgeCount =
                (Graph.glue germ.piece germ.atom.outside).edgeCount) ∧
            representative.size = germ.piece.internalVertexCount ∧
            (representative = germ.piece.toCanonical ∨
              (Graph.CanonicalPiece.Precedes representative
                  germ.piece.toCanonical ∧
                RefinedLexicographicallySmaller
                  (Graph.glue representative.toPiece germ.atom.outside)
                  object)) ∧
            ¬ Graph.HasCycleWithLength data.LengthOK
                (Graph.glue germ.piece germ.atom.outside)
          exact ⟨active, representativeReading, equalLength,
            canonicalPosition, sourceAvoids⟩
        ⟩
        .nil)

noncomputable def neutralGermSymmetryDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous : ExactLedger
      (Input BranchState Presentation presentation data) current known)
    [FactKeys.Has (K .coldNeutralEqualLengthTerminal) known]
    (canonicalFresh : K .coldCanonicalNeutralConfiguration ∉ known)
    (genuineFresh : K .coldGenuineSecondStrand ∉ known) :
    Decision (K .coldCanonicalNeutralConfiguration)
      (K .coldGenuineSecondStrand) previous := by
  classical
  let neutral := (previous.get (K .coldNeutralEqualLengthTerminal)).down
  let germ := Classical.choose neutral.2
  let representative := Classical.choose (Classical.choose_spec neutral.2)
  let configuration := Classical.choose_spec
    (Classical.choose_spec neutral.2)
  exact Decision.run previous (K .coldCanonicalNeutralConfiguration)
    (K .coldGenuineSecondStrand)
    `Hypostructure.Graph.Strategy.Spine.neutralGermSymmetryDichotomy
    (if realized : ∃ config : Graph.TwoStrand.Configuration,
        GenuineSecondStrandConfiguration data.toParameters current.object germ representative config then
      let config := Classical.choose realized
      .inr ⟨germ, representative, config, configuration,
        Classical.choose_spec realized⟩
    else
      .inl ⟨germ, representative, configuration, realized⟩)
    canonicalFresh genuineFresh

end Hypostructure.Graph.Strategy.Spine
