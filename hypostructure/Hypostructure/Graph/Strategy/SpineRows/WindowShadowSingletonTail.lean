import Hypostructure.Graph.Strategy.SpineVocabulary

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure.Core.Residual Hypostructure.Core.Strategy

universe u v

/-- The tail of `lem:typeA-singleton-shadow-table`. At window order thirteen
the cutoff is eighteen, as in the manuscript. The proof separates two
distinct dyadic lengths in the actual attachment interval; it does not assume
the separation as an additional input. -/
@[reducible] noncomputable def windowShadowSingletonTailRow
    {BranchState : Graph.FiniteObject.{u} → Type v}
    {Presentation : Type} {presentation : Presentation} {data : Data.{u}} :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.windowShadowSingletonTail
    { Requires := []
      Produces := [K .windowShadowSingletonTail]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .windowShadowSingletonTail)
        (show Value BranchState Presentation presentation data
            .windowShadowSingletonTail inputs.current from ⟨by
          intro support window s tail
          apply Graph.WindowAttachmentShadow.card_forbiddenDistances_le_one
          intro d₁ bound₁ d₂ bound₂ accepted₁ accepted₂
          obtain ⟨q₁, _lower₁, length₁⟩ :=
            (Core.DyadicLength.powerOfTwoLength_iff _).mp
              ((data.lengthOK_iff_powerOfTwo _).mp accepted₁)
          obtain ⟨q₂, _lower₂, length₂⟩ :=
            (Core.DyadicLength.powerOfTwoLength_iff _).mp
              ((data.lengthOK_iff_powerOfTwo _).mp accepted₂)
          rcases lt_trichotomy q₁ q₂ with before | same | after
          · have gap : 2 ^ q₁ * 2 ≤ 2 ^ q₂ := by
              rw [← pow_succ]
              exact Nat.pow_le_pow_right (by decide) before
            omega
          · rw [same] at length₁
            omega
          · have gap : 2 ^ q₂ * 2 ≤ 2 ^ q₁ := by
              rw [← pow_succ]
              exact Nat.pow_le_pow_right (by decide) after
            omega⟩)
        .nil)

end Hypostructure.Graph.Strategy.Spine
