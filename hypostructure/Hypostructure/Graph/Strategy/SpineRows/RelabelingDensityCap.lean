import Hypostructure.Graph.Strategy.SpineRows.Basic

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

/- Exact finite invariant-state cap for relabellings fixing the packed window
support pointwise.  All class, state, invariance, and stabilizer data are bound
inside the published proposition. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def relabelingDensityCapRow :
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
    `Hypostructure.Graph.Strategy.Spine.relabelingDensityCap
    (sourceFreeManifest (K .relabelingDensityCap))
    (fun inputs =>
      .cons (key := K .relabelingDensityCap)
        (show Value BranchState Presentation presentation data
            .relabelingDensityCap inputs.current from
          ⟨fun packing _valid labels => by
            dsimp only
            intro State stateDecidable skeletons state stabilizerBound
              closed invariant bounded
            classical
            letI : DecidableEq State := stateDecidable
            have cap :=
              Core.FiniteRelabelingOrbit.card_image_mul_card_group_le_card_mul_stabilizerBound
                skeletons state stabilizerBound closed invariant bounded
            rw [Graph.LabelledRelabeling.card_fixedSupportPermutations] at cap
            have complementCard :
                inputs.current.object.vertexCount -
                    ((inputs.current.object.windowSupport packing).map
                      labels.toEmbedding).card =
                  (Finset.univ \ ((inputs.current.object.windowSupport packing).map
                    labels.toEmbedding)).card := by
              rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ,
                Finset.card_map]
              simp only [Fintype.card_fin]
            rw [complementCard] at cap
            exact cap⟩)
        .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
