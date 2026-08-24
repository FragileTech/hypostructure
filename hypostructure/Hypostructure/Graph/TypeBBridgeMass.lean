import Hypostructure.Graph.TypeBEnvelopeCharge
import Hypostructure.Graph.VisibleReceiverEntry

/-!
# The Type B bridge mass by centre deletion

`lem:typeB-bridge-with-route8-core`, exactly as the manuscript assembles it:
the centre region is paid by the per-centre allowance, and the remaining
region — the piece with its high centres deleted — is discharged by the
silence-free staged count of `lem:typeA-silent-excess-count`, whose unpaid
excess loads are the extracted census entries the unified ledger carries
(`D_A(𝒜_X)`).  Receiver routing on the deleted region is total by
`lem:typeA-receiver-loads`' engine (`exists_traceTo_of_no_baseline_subsupport`)
from the committed remainder normalization; nothing is assumed.

The slack `1 + s·δ + 2s ≤ F·s` is arithmetic of the presentation, of the same
registered family as `bridgeMassSlack` (`27k ≥ 85`); at the registered
`δ = 3, s = 4, F = 8` it reads `21 ≤ 32`.
-/

namespace Hypostructure.Graph.TypeBBridgeMass

open Hypostructure
open Hypostructure.Graph

universe u

noncomputable section

local instance (priority := low) {α : Type u} : DecidableEq α :=
  Classical.decEq α

variable (object : FiniteObject.{u})

/-- **The bridge-mass bound with extracted entries.** -/
theorem bridge_mass_of_centre_deletion
    (piece : Finset object.Vertex) (threshold scale factor : Nat)
    (scalePos : 1 ≤ scale)
    (baseline : ∀ vertex : object.Vertex, threshold ≤ object.degree vertex)
    (routed : ∀ vertex ∈
        piece \ TypeBRefinedSupport.centres object threshold piece,
      object.internalDegree
          (piece \ TypeBRefinedSupport.centres object threshold piece)
          vertex = threshold →
      ∃ receiver : object.Vertex,
        object.traceReceiver?
            (piece \ TypeBRefinedSupport.centres object threshold piece)
            threshold vertex = some receiver ∧
          object.IsReceiver
            (piece \ TypeBRefinedSupport.centres object threshold piece)
            threshold receiver)
    (slack : 1 + scale * threshold + 2 * scale ≤ factor * scale) :
    piece.card + scale * object.ambientSurplus piece threshold ≤
      scale * object.positiveDeficiency piece threshold +
        factor * scale * object.ambientSurplus piece threshold +
        ∑ receiver ∈ object.receivers
            (piece \ TypeBRefinedSupport.centres object threshold piece)
            threshold,
          (VisibleEntry.excessBasinReduced object
            (piece \ TypeBRefinedSupport.centres object threshold piece)
            threshold scale receiver ∅).card := by
  classical
  set support' := piece \ TypeBRefinedSupport.centres object threshold piece
    with support'Def
  -- every centre carries at least one surplus unit
  have centresLe : (TypeBRefinedSupport.centres object threshold piece).card ≤
      object.ambientSurplus piece threshold := by
    rw [← TypeBEnvelopeCharge.sum_centres_surplus object threshold piece]
    calc (TypeBRefinedSupport.centres object threshold piece).card
        = ∑ _centre ∈ TypeBRefinedSupport.centres object threshold piece, 1 :=
          (Finset.card_eq_sum_ones _)
      _ ≤ ∑ centre ∈ TypeBRefinedSupport.centres object threshold piece,
            (object.degree centre - threshold) := by
          refine Finset.sum_le_sum fun centre member => ?_
          have high := (TypeBRefinedSupport.mem_centres.mp member).2
          rw [Graph.IsHighCentre] at high
          omega
  -- the deleted region is degree-capped
  have capped : ∀ vertex ∈ support', 
      object.internalDegree support' vertex ≤ threshold := by
    intro vertex member
    obtain ⟨inPiece, notCentre⟩ := Finset.mem_sdiff.mp member
    have notHigh : ¬ Graph.IsHighCentre object threshold vertex := fun high =>
      notCentre (TypeBRefinedSupport.mem_centres.mpr ⟨inPiece, high⟩)
    rw [Graph.IsHighCentre] at notHigh
    exact le_trans (object.internalDegree_le_degree support' vertex) (by omega)
  -- the silence-free staged count on the deleted region, with the committed
  -- `[88]` routing (`K .typeAReceiverRouting` at the deleted region, which is
  -- a surplus-zero sub-support of the remainder) read off the ledger
  have counted := VisibleEntry.card_le_sum_excessBasinReduced_add_positiveDeficiency
    object support' threshold scale scalePos capped routed (fun _ => (∅ : Finset object.Vertex))
  simp only [Finset.empty_inter, Finset.card_empty, Finset.sum_const_zero,
    Nat.add_zero] at counted
  -- deficiency transfer through the deleted centres
  have transfer := object.positiveDeficiency_sdiff_le piece
    (TypeBRefinedSupport.centres object threshold piece) threshold
  have centreDegrees : (∑ vertex ∈
      TypeBRefinedSupport.centres object threshold piece,
      object.internalDegree piece vertex) ≤
      threshold * (TypeBRefinedSupport.centres object threshold piece).card +
        object.ambientSurplus piece threshold := by
    calc (∑ vertex ∈ TypeBRefinedSupport.centres object threshold piece,
          object.internalDegree piece vertex)
        ≤ ∑ vertex ∈ TypeBRefinedSupport.centres object threshold piece,
            (threshold + (object.degree vertex - threshold)) := by
          refine Finset.sum_le_sum fun vertex _ => ?_
          have le := object.internalDegree_le_degree piece vertex
          have base := baseline vertex
          omega
      _ = threshold * (TypeBRefinedSupport.centres object threshold
            piece).card + object.ambientSurplus piece threshold := by
          rw [Finset.sum_add_distrib,
            TypeBEnvelopeCharge.sum_centres_surplus object threshold piece,
            Finset.sum_const, smul_eq_mul, mul_comm]
  -- piece size splits along the deletion
  have cardSplit :
      support'.card + (TypeBRefinedSupport.centres object threshold
        piece).card = piece.card := by
    rw [support'Def]
    exact Finset.card_sdiff_add_card_eq_card (Finset.filter_subset _ _)
  -- assemble with the registered slack
  have slackMul := Nat.mul_le_mul_right
    (object.ambientSurplus piece threshold) slack
  have scaleTransfer := Nat.mul_le_mul_left scale transfer
  have scaleCentre := Nat.mul_le_mul_left scale centreDegrees
  have scaleCentreCard := Nat.mul_le_mul_left (1 + scale * threshold)
    centresLe
  nlinarith [counted, scaleTransfer, scaleCentre, cardSplit, slackMul,
    scaleCentreCard, centresLe]

end

end Hypostructure.Graph.TypeBBridgeMass
