import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.RouteEight.EntryCensus
import Hypostructure.Graph.Contracts.Spine.SpineSelection

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

/-! ## `lem:typeA-unified-deficit` (node `[123]`)

The unified collection carries the whole large-budget deficit, cleared of
denominators: `|R| ≤ s·D̃_A + s·|∂R| + 2·F·s·T(n)`.  The manuscript proof
verbatim: the canonical pieces split into the unified members (their cleared
deficits are `s·D̃_A`), the nonnegative pieces (no mass), the negative
positive-surplus pieces (paid by `lem:typeB-bridge-deficit-bound` through the
tested flat pair, into the first surplus role), and the negative zero-surplus
handoff pieces (paid by `lem:decorated-envelope-deficit-bound`'s family form
through the tested fan-assignment data, into the second surplus role); the
scaled global deficiency is paid by the boundary supply
(`positiveDeficiency_le_boundaryIncidence`), and the near-cubic cap converts
both surplus roles to the registered threshold. -/
/-! ## The tested quotient-freeness of the unified census

Whether some unified entry's selected basin carries the plain trace-response
quotient is decided by a `Decision`.  The yes arm makes every unified entry
route-8 or alternative-(a) and feeds the entry census; the no arm retains the
literal negation, which the paper declares a standing-invariant contradiction
(`instIncompatibleRoute8QuotientResidualSelection`). -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
noncomputable def route8QuotientDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : @FactKeys (Input BranchState Presentation presentation data) _
      (instFactSystem (BranchState := BranchState)
        (Presentation := Presentation) (presentation := presentation)
        (data := data))}
    (previous :
      @ExactLedger (Input BranchState Presentation presentation data) _
        (instFactSystem (BranchState := BranchState)
          (Presentation := Presentation) (presentation := presentation)
          (data := data)) current known)
    [@FactKeys.Has (Input BranchState Presentation presentation data) _
      (instFactSystem (BranchState := BranchState)
        (Presentation := Presentation) (presentation := presentation)
        (data := data))
      (K .route8UnifiedDeficit) known]
    (freeFresh : K .route8QuotientFree ∉ known)
    (residualFresh : K .route8QuotientResidual ∉ known) :
    @Decision (Input BranchState Presentation presentation data) _
      (instFactSystem (BranchState := BranchState)
        (Presentation := Presentation) (presentation := presentation)
        (data := data)) current known
      (K .route8QuotientFree) (K .route8QuotientResidual) previous :=
  letI : FactSystem (Input BranchState Presentation presentation data) :=
    instFactSystem (BranchState := BranchState) (Presentation := Presentation)
      (presentation := presentation) (data := data)
  Decision.run previous (K .route8QuotientFree) (K .route8QuotientResidual)
    `Hypostructure.Graph.Strategy.Spine.route8QuotientDichotomy
    (by
      classical
      -- `lem:typeA-unified-deficit`: the unified census the test is asked of
      -- carries the whole deficit.
      have _deficit := (previous.get (K .route8UnifiedDeficit)).down
      exact if free : Route8QuotientFreeStatement data.toParameters current.object then
        .inl ⟨free⟩
      else
        .inr ⟨free⟩)
    freeFresh residualFresh

end Hypostructure.Graph.Strategy.Spine

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-- **Node `[348]` closed as the paper closes it** (`lem:typeA-unified-carriers`,
tex 15360-15364; the census of `lem:typeA-unified-deficit`, tex 15336-15339):
alternative (b) at a unified entry is exit (5), "a standing-invariant
contradiction (`cor:uncompressible`)".  The standing invariants are `G`'s
selection fact (no accepted cycle, minimality), its baseline, the registered
cubic/dyadic presentation, and the hereditary uncompressibility they give
(`replacementExclusion_of_selection`, `replacementSupportOfCompressibleSupport`).
The paper's step itself is `Contracts.RouteEight.route8QuotientFree_of_uncompressible`,
a recorded paper error. -/
noncomputable instance instIncompatibleRoute8QuotientResidualSelection :
    Incompatible (Input BranchState Presentation presentation data)
      (K .route8QuotientResidual) (K .selection) where
  contradiction := fun input residual selection =>
    residual.down
      (Graph.Contracts.RouteEight.route8QuotientFree_of_uncompressible
        data.toParameters input.object data.threshold_eq_three
        data.lengthOK_iff_powerOfTwo input.baseline selection.down.1
        selection.down.2
        (fun support compressible =>
          Contracts.Spine.replacementExclusion_of_selection data.toParameters
            input.object input.baseline input.branchState selection.down support
            (Graph.Strategy.InterfaceReplacement.replacementSupportOfCompressibleSupport
              _ _ _ support compressible)))

end Hypostructure.Graph.Strategy.Spine
