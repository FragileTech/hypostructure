import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.ColdIncrementArithmetic
import Hypostructure.Graph.ColdGermFamily
import Hypostructure.Graph.Strategy.ColdCorridorRows.Basic
import Hypostructure.Graph.Contracts.Spine.ColdGermRouting

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-! ## Node `[163]`, `lem:neutral-germ-symmetry`: the symmetry split

A neutral equal-length terminal germ carries no target information; it is a
symmetry.  The manuscript's question is whether its second representative is
graph-realized as a genuine second strand.  The yes-arm is the two-strand route
`[167]`; the no-arm is the canonical-replacement route `[165]`--`[166]`.
Canonical order is deliberately absent from this decision.  Both arms retain
the exact marked configuration read from the incoming `ExactLedger`. -/
@[reducible] noncomputable def neutralEqualLengthTerminalRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.neutralEqualLengthTerminal
    { Requires := [K .coldGermFamilyPositive, K .denseColdCorridorsTerminal,
        K .selection]
      Produces := [K .coldNeutralEqualLengthTerminal]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .coldNeutralEqualLengthTerminal)
        ⟨Contracts.Spine.neutralEqualLengthTerminal_of_positive data.toParameters
          inputs.current.object inputs.current.baseline
          (inputs.get (K .selection)).down
          (inputs.get (K .coldGermFamilyPositive)).down
          (inputs.get (K .denseColdCorridorsTerminal)).down⟩
        .nil)

noncomputable def neutralGermSymmetryDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous : ExactLedger
      (Input BranchState Presentation presentation data) current known)
    [FactKeys.Has (K .coldNeutralEqualLengthTerminal) known]
    (canonicalFresh : K .coldCanonicalNeutralConfiguration ∉ known)
    (genuineFresh : K .coldGenuineSecondStrand ∉ known) :
    Decision (K .coldCanonicalNeutralConfiguration)
      (K .coldGenuineSecondStrand) previous := by
  classical
  let neutral := (previous.get (K .coldNeutralEqualLengthTerminal)).down
  let germ := Classical.choose neutral.2
  let representative := Classical.choose (Classical.choose_spec neutral.2)
  let configuration := Classical.choose_spec
    (Classical.choose_spec neutral.2)
  exact Decision.run previous (K .coldCanonicalNeutralConfiguration)
    (K .coldGenuineSecondStrand)
    `Hypostructure.Graph.Strategy.Spine.neutralGermSymmetryDichotomy
    (if realized : ∃ config : Graph.TwoStrand.Configuration,
        GenuineSecondStrandConfiguration data.toParameters current.object germ representative config then
      let config := Classical.choose realized
      .inr ⟨germ, representative, config, configuration,
        Classical.choose_spec realized⟩
    else
      .inl ⟨germ, representative, configuration, realized⟩)
    canonicalFresh genuineFresh

end Hypostructure.Graph.Strategy.Spine
