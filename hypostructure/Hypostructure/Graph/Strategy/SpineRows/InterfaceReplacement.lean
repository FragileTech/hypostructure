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

end Hypostructure.Graph.Strategy.Spine
