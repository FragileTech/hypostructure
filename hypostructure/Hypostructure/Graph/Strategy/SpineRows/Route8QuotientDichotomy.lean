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
literal negation. -/
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
      exact if free : Route8QuotientFreeStatement data current.object then
        .inl ⟨free⟩
      else
        .inr ⟨free⟩)
    freeFresh residualFresh

end Hypostructure.Graph.Strategy.Spine
