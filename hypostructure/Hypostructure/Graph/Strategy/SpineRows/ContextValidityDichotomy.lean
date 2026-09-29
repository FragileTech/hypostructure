import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.Spine.BranchD

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

/-! ## Node `[36]`: the context-validity test

The literal post-`[35]` ledger retains node `[21]`'s fact, whose one
inclusion-minimal determination certificate is `branchCertificate? data G`.
Node `[36]` reads that fact and asks the paper's exact question of that
certificate, and of no other, stated about G: does its determination remain
valid in every context of G, i.e. do the readings of G it identifies agree in
G's own rest `G − Z`?  The no arm exhibits an identified pair of readings that
`G − Z` separates; the yes arm records context universality for that same
certificate.  At G the test is decided: the yes arm holds
(`Contracts.Spine.contextUniversal_of_selection`), and the no arm is empty —
its terminal `[37]` closes against node `[12]` (Lean improvement: `[36]`'s
defect arm is empty at G).  Boundary-fibre preservation is already part of the
admissible quotient and is not a second test here. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
noncomputable def contextValidityDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : @FactKeys (Input BranchState Presentation presentation data)
      _ (factSystem BranchState Presentation presentation data)}
    (previous :
      @ExactLedger (Input BranchState Presentation presentation data)
        _ (factSystem BranchState Presentation presentation data) current known)
    [@Core.Residual.FactKeys.Has
      (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data)
      (K .branchDependence) known]
    (defectFresh : K .contextDefect ∉ known)
    (universalFresh : K .contextUniversal ∉ known) :
    @Decision (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data) current known
      (K .contextDefect) (K .contextUniversal) previous :=
  @Decision.run (Input BranchState Presentation presentation data) _
    (factSystem BranchState Presentation presentation data) current known
    previous (K .contextDefect) (K .contextUniversal)
    `Hypostructure.Graph.Strategy.Spine.contextValidityDichotomy
    (by
      classical
      let dependence := (@ExactLedger.get
        (Input BranchState Presentation presentation data) _
        (factSystem BranchState Presentation presentation data)
        current known previous (K .branchDependence)).down
      exact if universal :
          ContextUniversalStatement data.toParameters current.object then
        .inr ⟨universal⟩
      else
        .inl ⟨(Contracts.Spine.contextDefect_or_contextUniversal data.toParameters
          current.object dependence).resolve_right universal⟩)
    defectFresh universalFresh

end Hypostructure.Graph.Strategy.Spine
