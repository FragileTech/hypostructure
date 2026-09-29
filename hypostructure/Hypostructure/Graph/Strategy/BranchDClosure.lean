import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.Spine.BranchD

/-!
# Branch D terminals: nodes `[37]`, `[39]`, `[42]`, `[46]`

Part III of the proof-dependency diagram closes every rank-drop branch in a
round node.  Each terminal is a framework closure (`closeIncompatible`) over
the literal ledger of its arm, against the upstream fact the manuscript cites:

* `[37]` against node `[12]` `K .targetCompleteContextUniversality`
  (`lem:context-universality`; `lem:full-rank`, tex 9388), stated about G: the
  readings of G the certificate identifies agree in G's own rest `G − Z`, so
  the defect arm of `[36]` is empty at G (Lean improvement).
* `[39]` against node `[13]` `K .replacementExclusion` (`lem:replacement`,
  tex 9226 `cor:uncompressible`): the strictly smaller proper representative
  supplied by `def:admissible-rank-quotient` at a proper support is a
  replacement of that support (G's boundary profile, the baseline and no
  power-of-two cycle in `glue X' (G − Z)`).
* `[42]` against node `[13]` (`lem:proper-smearing`): the support `Z ⊊ G` is
  proper, and its target-complete rank reduction is again such a replacement.
* `[46]` against `K .selection` (`lem:no-silent-global-smearing`): the strictly
  smaller admissible closed representative is a baseline graph with no
  power-of-two cycle, against the selection's minimality.
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-- **The terminal `[37]` closes against node `[12]`.**  The certificate's
admissible quotient is a quotient of G's declared coordinates, so node `[12]`
makes every two readings it identifies agree in G's own rest `G − Z`;
`K .contextDefect`'s separated pair contradicts that. -/
noncomputable instance instIncompatibleContextUniversalityDefect :
    Incompatible (Input BranchState Presentation presentation data)
      (K .targetCompleteContextUniversality) (K .contextDefect) where
  contradiction := fun residual universality defect =>
    Contracts.Spine.contextDefect_false_of_contextUniversality data.toParameters
      residual.object universality.down defect.down

/-- **The terminal `[39]` closes against node `[13]`.**  The
`K .atomCompression` fact contains the proper-support replacement derived at
`[38]`; `lem:replacement` (`K .replacementExclusion`) excludes it on G. -/
noncomputable instance instIncompatibleAtomCompression :
    Incompatible (Input BranchState Presentation presentation data)
      (K .replacementExclusion) (K .atomCompression) where
  contradiction := fun residual exclusion compression =>
    Contracts.Spine.atomCompression_replacementExclusion_false data.toParameters
      residual.object exclusion.down compression.down

/-- **The terminal `[42]` closes against node `[13]`.**  The proper support
`Z ⊊ G` carries a target-complete rank reduction, hence a replacement
(`lem:proper-smearing`), excluded by `K .replacementExclusion`. -/
noncomputable instance instIncompatibleProperDelocalization :
    Incompatible (Input BranchState Presentation presentation data)
      (K .replacementExclusion) (K .properDelocalization) where
  contradiction := fun residual exclusion smearing =>
    Contracts.Spine.properDelocalization_replacementExclusion_false
      data.toParameters residual.object exclusion.down smearing.down

/-- **The terminal `[46]` closes against the selected object.**  The global
barrier stores the surviving conclusion of `lem:no-silent-global-smearing`: a
strictly smaller admissible closed representative with no power-of-two cycle.
Selection minimality puts a power-of-two cycle in it. -/
noncomputable instance instIncompatibleGlobalBarrier :
    Incompatible (Input BranchState Presentation presentation data)
      (K .selection) (K .globalBarrier) where
  contradiction := fun residual selected barrier =>
    Contracts.Spine.globalBarrier_selection_false BranchState Presentation
      presentation data.toParameters residual.object selected.down barrier.down

end Hypostructure.Graph.Strategy.Spine
