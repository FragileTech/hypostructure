import Hypostructure.Core.Strategy.Official.Strategies.Common
import Hypostructure.Core.Strategy.Official.Strategies.ResponseClassification
import Hypostructure.Core.Strategy.Official.Strategies.ClosedCodeExhaustion

/-!
# Canonical CT7 → CT16 → CT8 composition: finite replacement classification

Replaces the detached `FiniteReplacementClassification` feature executor.
Core classifies context neutrality/distinction through CT7
(ResponseClassification), checks code equality through CT16
(ClosedCodeExhaustion), and certifies removal through CT8
(ClosedCodeExhaustion).  The composition retains the complete accumulated
ledger and exposes only the exhaustive terminals: universal replacement
closure, separating context, or removal residual.
-/

namespace Hypostructure.Core.Strategy.Official.Strategies.FiniteReplacementClassification

/-- Complete accumulated ledger across CT7, CT16, and CT8. -/
structure Terminal where
  contextSlot : FunctionTableSlot
  codeSlot : FunctionTableSlot
  removalSlot : FunctionTableSlot
  ct7 : ResponseClassification.Terminal contextSlot
  ct16 : ClosedCodeExhaustion.Terminal codeSlot
  ct8 : ClosedCodeExhaustion.Terminal removalSlot
  totalWork : Nat
  totalWork_eq : totalWork =
    ct7.work.bound + ct16.work.bound + ct8.work.bound

def execute
    (contextSlot : FunctionTableSlot)
    (codeSlot : FunctionTableSlot)
    (removalSlot : FunctionTableSlot) : Terminal :=
  let ct7 := ResponseClassification.execute contextSlot
  let ct16 := ClosedCodeExhaustion.execute codeSlot
  let ct8 := ClosedCodeExhaustion.execute removalSlot
  { contextSlot := contextSlot
    codeSlot := codeSlot
    removalSlot := removalSlot
    ct7 := ct7
    ct16 := ct16
    ct8 := ct8
    totalWork := ct7.work.bound + ct16.work.bound + ct8.work.bound
    totalWork_eq := rfl }

end Hypostructure.Core.Strategy.Official.Strategies.FiniteReplacementClassification
