import Hypostructure.Graph.Strategy.SpineVocabulary

/-! Independently compiled spine row declarations. -/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

variable [FactSystem (Input BranchState Presentation presentation data)]

/-! ## `lem:open-port-suppression-safe`

The preceding definition identifies the paper's four suppressibility clauses
with the canonical compatible-family construction.  This row reads that exact
definition fact and applies the proved simultaneous degree balance: shoulder
losses are compensated by their new chords, while the only uncompensated
losses are the centre loads bounded by clause (d). -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def openPortSuppressionSafeRow :
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
    `Hypostructure.Graph.Strategy.Spine.openPortSuppressionSafe
    { Requires := [K .openPortSuppression]
      Produces := [K .openPortSuppressionSafe]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .openPortSuppressionSafe) ⟨by
        change OpenPortSuppressionSafeStatement data inputs.current.object
        classical
        intro family highCentres paperCapacity vertex
        have suppressionDefinition :=
          (inputs.get (K .openPortSuppression)).down family highCentres
        rcases suppressionDefinition with
          ⟨_neighbors, _supports, _centres, _chords, _missing,
            capacityIff, _deleted, _adjacency⟩
        have capacity : family.CenterCapacity data.threshold :=
          capacityIff.mpr paperCapacity
        have oldLower :
            data.threshold ≤ inputs.current.object.degree vertex.1 :=
          inputs.current.baseline.trans
            (inputs.current.object.minDegree_le_degree vertex.1)
        have loadBound := capacity vertex.1 vertex.2
        have balance := family.degree_add_centerLoad vertex
        have thresholdLower :
            data.threshold ≤ family.suppressed.degree vertex := by
          omega
        exact data.three_le_threshold.trans thresholdLower⟩
        .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
