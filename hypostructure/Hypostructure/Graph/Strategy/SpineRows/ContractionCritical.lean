import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.Spine.SpineMinimalClosure

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

/-! ## Contraction criticality (no manuscript label; not a manuscript statement)

Contract one edge whose common neighbours are not cubic.  Avoidance of the
accepted quadrilateral makes that common neighbour unique; hence contraction
preserves the cubic baseline.  Selection minimality supplies an accepted
cycle of the contraction.  Its two incidences at the contracted vertex either
lift on one side, contradicting avoidance, or are mixed and splice into a
power-of-two severed return. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def contractionCriticalRow :
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
    `Hypostructure.Graph.Strategy.Spine.contractionCritical
    { Requires := [K .selection, K .cubicBaseline]
      Produces := [K .contractionCritical]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .contractionCritical)
        ⟨Contracts.Spine.contractionCritical_of_selection data.toParameters
          inputs.current.object inputs.current.baseline
          (inputs.get (K .selection)).down (inputs.get (K .cubicBaseline)).down
          data.lengthOK_iff_powerOfTwo⟩
        .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine
