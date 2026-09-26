import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.Spine.BranchD

/-!
# Branch D terminals: nodes `[37]`, `[39]`, `[42]`, `[46]`

Part III of the proof-dependency diagram closes every rank-drop branch in a
round node.  Each terminal is a framework closure over the literal ledger of
its arm: `closeImpossible` at `[37]` (one fact is uninhabited) and
`closeIncompatible` against `K .selection` at `[39]`, `[42]`, `[46]` (the
committed fact contradicts the selected minimal counterexample).  The four
registrations below are the manuscript's refutations, and nothing else:

* `[37]` (`lem:context-universality`): the selected admissible quotient is
  context-universal, so no outside context distinguishes an identified pair.
* `[39]` (`cor:uncompressible`): the strictly smaller proper representative
  supplied by `def:admissible-rank-quotient` at a proper support is a
  replacement of that support, forbidden at a minimal counterexample.
* `[42]` (`lem:proper-smearing`): the enlarged connected support `Z ⊊ G` is a
  proper support, and its target-complete rank reduction is again such a
  replacement.
* `[46]` (`lem:no-silent-global-smearing`): after target-completeness,
  whole-graph support, and rank reduction have excluded the other alternatives,
  the strictly smaller admissible closed representative contradicts the
  selection's minimality together with its target avoidance.
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-- **The terminal `[37]` is uninhabited.**  The certificate's admissible
quotient is context-universal on its identified pairs, contradicting the
concrete outside-context defect recorded by `K .contextDefect`. -/
noncomputable instance instImpossibleContextDefect :
    Impossible (Input BranchState Presentation presentation data)
      (K .contextDefect) where
  contradiction := fun residual value =>
    Contracts.Spine.contextDefect_false data.toParameters residual.object value.down

/-- **The terminal `[39]` closes against the selected object.**  The
`K .atomCompression` fact contains the proper-support replacement derived at
`[38]`; `lem:replacement` (`not_replacementSupport`) forbids it at the selected
minimal counterexample. -/
noncomputable instance instIncompatibleAtomCompression :
    Incompatible (Input BranchState Presentation presentation data)
      (K .selection) (K .atomCompression) where
  contradiction := fun residual selected compression =>
    Contracts.Spine.atomCompression_selection_false BranchState Presentation
      presentation data.toParameters residual.object residual.branchState
      residual.baseline selected.down compression.down

/-- **The terminal `[42]` closes against the selected object.**  The proper
enlarged support `Z ⊊ G` carries a target-complete rank reduction, hence a
replacement (`lem:proper-smearing`), forbidden by `cor:uncompressible`. -/
noncomputable instance instIncompatibleProperDelocalization :
    Incompatible (Input BranchState Presentation presentation data)
      (K .selection) (K .properDelocalization) where
  contradiction := fun residual selected smearing =>
    Contracts.Spine.properDelocalization_selection_false BranchState Presentation
      presentation data.toParameters residual.object residual.branchState
      residual.baseline selected.down smearing.down

/-- **The terminal `[46]` closes against the selected object.**  The global
barrier stores the surviving conclusion of `lem:no-silent-global-smearing`: a
strictly smaller admissible closed representative.  Selection minimality puts
the target in that representative, target transfer puts it in the selected
object, and selection avoidance gives the contradiction. -/
noncomputable instance instIncompatibleGlobalBarrier :
    Incompatible (Input BranchState Presentation presentation data)
      (K .selection) (K .globalBarrier) where
  contradiction := fun residual selected barrier =>
    Contracts.Spine.globalBarrier_selection_false BranchState Presentation
      presentation data.toParameters residual.object selected.down barrier.down

end Hypostructure.Graph.Strategy.Spine
