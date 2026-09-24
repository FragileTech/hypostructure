import Hypostructure.Graph.Strategy.SpineVocabulary

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure.Core.Residual Hypostructure.Core.Strategy

universe u v

/-- Consume the recorded-hit cycle certificate against the same selected
graph's avoidance fact. No path or target fact comes from another branch. -/
@[reducible] noncomputable def windowShadowHitExcludedRow
    {BranchState : Graph.FiniteObject.{u} → Type v}
    {Presentation : Type} {presentation : Presentation} {data : Data.{u}} :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.windowShadowHitExcluded
    { Requires := [K .selection, K .windowShadowHitCycle]
      Produces := [K .windowShadowHitExcluded]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .windowShadowHitExcluded)
        (show Value BranchState Presentation presentation data
            .windowShadowHitExcluded inputs.current from ⟨by
          intro window x y a b corridor path avoids attachA attachB distinct hit
          obtain ⟨cycle, isCycle, _length, accepted⟩ :=
            (inputs.get (K .windowShadowHitCycle)).down
              window x y a b corridor path avoids attachA attachB distinct hit
          exact (inputs.get (K .selection)).down.1
            ⟨⟨window a, cycle, isCycle, accepted⟩⟩⟩)
        .nil)

end Hypostructure.Graph.Strategy.Spine
