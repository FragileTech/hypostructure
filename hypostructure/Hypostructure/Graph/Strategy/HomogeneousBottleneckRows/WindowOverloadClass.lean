import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.NamedSurplusExits
import Hypostructure.Graph.SparsePressureLedger
import Hypostructure.Graph.GluedCrossingCycle
import Hypostructure.Graph.Strategy.HomogeneousBottleneckRows.Basic

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-- Classify the concrete overload witness already carried by the incoming
ledger according to whether its token lies in the window-incidence class. -/
noncomputable def windowOverloadClassDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous : ExactLedger (Input BranchState Presentation presentation data)
      current known)
    [FactKeys.Has (K .sparsePressureOverload) known]
    (windowFresh : K .windowClassOverload ∉ known)
    (outsideFresh : K .windowClassAbsent ∉ known) :
    Decision (K .windowClassOverload) (K .windowClassAbsent) previous :=
  Decision.run previous (K .windowClassOverload) (K .windowClassAbsent)
    `Hypostructure.Graph.Strategy.Spine.windowOverloadClassDichotomy
    (Classical.choice (show Nonempty
        ((K .windowClassOverload).At current ⊕
          (K .windowClassAbsent).At current) from by
      obtain ⟨active, declared, activationEq, certified, token, role, tokenMem,
        _selected, rest⟩ := (previous.get (K .sparsePressureOverload)).down
      let ledger := certified.ledger
      cases classified : ledger.presented.tokenClass token with
      | windowIncidence =>
          exact ⟨.inl ⟨active, declared, activationEq, certified, token, role,
            tokenMem, classified, rest⟩⟩
      | remainderSurplus =>
          exact ⟨.inr ⟨active, declared, activationEq, certified, token, role,
            tokenMem, by simpa [ledger, classified], rest⟩⟩
      | primitiveCarrier =>
          exact ⟨.inr ⟨active, declared, activationEq, certified, token, role,
            tokenMem, by simpa [ledger, classified], rest⟩⟩))
    windowFresh outsideFresh

end Hypostructure.Graph.Strategy.Spine
