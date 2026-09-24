import Hypostructure.Graph.Strategy.SpineVocabulary

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure.Core.Residual Hypostructure.Core.Strategy

universe u v

/-- The signature test in `def:typeA-window-attachment-shadow` is exactly
the failure of the singleton window-label safety relation. -/
@[reducible] noncomputable def windowShadowSignatureRow
    {BranchState : Graph.FiniteObject.{u} → Type v}
    {Presentation : Type} {presentation : Presentation} {data : Data.{u}} :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.windowShadowSignature
    { Requires := []
      Produces := [K .windowShadowSignature]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .windowShadowSignature)
        (show Value BranchState Presentation presentation data
            .windowShadowSignature inputs.current from ⟨by
          classical
          intro support window s a b
          have distance : Nat.dist a.1 b.1 < data.windowOrder := by
            rcases Nat.le_total a.1 b.1 with hab | hba
            · rw [Nat.dist_eq_sub_of_le hab]
              omega
            · rw [Nat.dist_eq_sub_of_le_right hba]
              omega
          rw [Graph.WindowAttachmentShadow.mem_shadow]
          simp [b.isLt, distance, Graph.WindowCurvature.Safe,
            Graph.WindowCurvature.ForbiddenGap,
            Graph.WindowCurvature.closingLength,
            data.lengthOK_iff_powerOfTwo]⟩)
        .nil)

end Hypostructure.Graph.Strategy.Spine
