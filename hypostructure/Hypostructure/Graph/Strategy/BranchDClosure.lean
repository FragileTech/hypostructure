import Hypostructure.Graph.Strategy.SpineRows

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
  contradiction := fun _residual value => by
    obtain ⟨_packing, _valid, _packingCard, _test, _determiners, quotient,
      _supportData, _certificate, _minimal, left, right, identified,
      outside, distinguishes⟩ := value.down
    exact distinguishes
      (quotient.contextUniversal left right identified outside)

/-- **The terminal `[39]` closes against the selected object.**  The
`K .atomCompression` fact contains the proper-support replacement derived at
`[38]`; `lem:replacement` (`not_replacementSupport`) forbids it at the selected
minimal counterexample. -/
noncomputable instance instIncompatibleAtomCompression :
    Incompatible (Input BranchState Presentation presentation data)
      (K .selection) (K .atomCompression) where
  contradiction := fun residual selected compression => by
    obtain ⟨_packing, _valid, quotient, _certificate, _complete, _inside,
      replacement⟩ := compression.down
    exact Graph.Strategy.InterfaceReplacement.not_replacementSupport
      (Graph.MinimumDegreeAtLeast data.threshold) BranchState
      (Graph.minimumDegreeAtLeast_isomorphismInvariant data.threshold)
      Presentation presentation
      (Core.Target.ofPredicate _ (Graph.HasCycleWithLength data.LengthOK))
      ((Graph.cycleTargetInterface data.LengthOK).coreInvariantWithPresentation
        (Graph.MinimumDegreeAtLeast data.threshold) BranchState
        Presentation presentation
        (Graph.minimumDegreeAtLeast_isomorphismInvariant data.threshold))
      { G := residual.object, baseline := residual.baseline,
        state := residual.branchState, avoids := selected.down.1,
        minimal := selected.down.2 }
      quotient.support replacement

/-- **The terminal `[42]` closes against the selected object.**  The proper
enlarged support `Z ⊊ G` carries a target-complete rank reduction, hence a
replacement (`lem:proper-smearing`), forbidden by `cor:uncompressible`. -/
noncomputable instance instIncompatibleProperDelocalization :
    Incompatible (Input BranchState Presentation presentation data)
      (K .selection) (K .properDelocalization) where
  contradiction := fun residual selected smearing => by
    obtain ⟨_packing, _valid, quotient, _certificate, _complete, _outside,
      _vertex, _vertexOutside, replacement⟩ := smearing.down
    exact Graph.Strategy.InterfaceReplacement.not_replacementSupport
      (Graph.MinimumDegreeAtLeast data.threshold) BranchState
      (Graph.minimumDegreeAtLeast_isomorphismInvariant data.threshold)
      Presentation presentation
      (Core.Target.ofPredicate _ (Graph.HasCycleWithLength data.LengthOK))
      ((Graph.cycleTargetInterface data.LengthOK).coreInvariantWithPresentation
        (Graph.MinimumDegreeAtLeast data.threshold) BranchState
        Presentation presentation
        (Graph.minimumDegreeAtLeast_isomorphismInvariant data.threshold))
      { G := residual.object, baseline := residual.baseline,
        state := residual.branchState, avoids := selected.down.1,
        minimal := selected.down.2 }
      quotient.support replacement

/-- **The terminal `[46]` closes against the selected object.**  The global
barrier stores the surviving conclusion of `lem:no-silent-global-smearing`: a
strictly smaller admissible closed representative.  Selection minimality puts
the target in that representative, target transfer puts it in the selected
object, and selection avoidance gives the contradiction. -/
noncomputable instance instIncompatibleGlobalBarrier :
    Incompatible (Input BranchState Presentation presentation data)
      (K .selection) (K .globalBarrier) where
  contradiction := fun residual selected barrier => by
    obtain ⟨representative, smaller, representativeBaseline, transfer⟩ :=
      barrier.down
    exact selected.down.1
      (transfer (selected.down.2 representative smaller representativeBaseline))

end Hypostructure.Graph.Strategy.Spine
