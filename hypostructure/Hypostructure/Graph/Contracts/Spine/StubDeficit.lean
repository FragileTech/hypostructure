import Hypostructure.Graph.Statements.StubDeficit

/-!
# Contracts: the stub-deficit identity and the cycle spectrum of `R₀`

One contract per statement of `Statements/StubDeficit.lean`.  Hypotheses are
facts the `[54]` ledger carries: the selection (G avoids the target).
-/

namespace Hypostructure.Graph.Contracts.Spine

open Hypostructure
open Hypostructure.Graph.Strategy.Spine

universe u

variable {data : Parameters} {object : Graph.FiniteObject.{u}}

theorem stubDeficitIdentity_holds : StubDeficitIdentityStatement data object := by
  intro baseline
  have degree : ∀ vertex : object.Vertex, data.threshold ≤ object.degree vertex :=
    fun vertex => baseline.trans (object.minDegree_le_degree vertex)
  refine ⟨object.boundaryIncidence_add_internalExcess _ _ degree,
    object.two_mul_internalEdgeCount_add_boundaryIncidence _ _ degree,
    object.card_deficitUnits _ _, ?_, object.stubAssignment_injOn _ _⟩
  exact fun unit mem => object.stubAssignment_isSome _ _ degree unit mem

theorem remainderCycleSpectrum_holds
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object) :
    RemainderCycleSpectrumStatement data object :=
  fun support _ cycle => avoids (object.hasCycleWithLength_of_induce support cycle)

end Hypostructure.Graph.Contracts.Spine
