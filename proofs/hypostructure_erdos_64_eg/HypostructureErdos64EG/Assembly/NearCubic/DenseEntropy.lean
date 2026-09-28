import Hypostructure.Graph.Strategy.EntropyClosure
import HypostructureErdos64EG.Assembly.Basic

/-!
# Assembly: NearCubic / DenseEntropy

Node `[53]` on the dense-packing residual with `τ(θ) < 1/4`
(`prop:entropy-high-theta`, `lem:dense-deficiency-routing`).  On the no-edge
`[159]` of `[158]` the exact package overflows the labelled skeleton count,
`B < 2^{b_𝒫·p}`, and `[160]`'s first yes-arm gives `|R| > s·stubs·p`.  On the
high-entropy arm the `[52]` demand then overflows the skeleton budget, so the
entropy cap of `[53]` is active
(`Contracts.Spine.entropyCapActive_of_denseUnrealized`).  The contract lemma
takes the registered table rate, the scale count and the presentation slack
`d ≤ s·stubs` (`10 ≤ 4·15`) as hypotheses; this adapter discharges them at the
registered presentation and reads the three graph facts from the ledger.
-/

namespace HypostructureErdos64EG

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u

/-- The registered presentation's entropy slack: the `[50]` denominator `10`
is at most `s·stubs = 4·15`. -/
theorem spineData_entropySlack :
    (spineData.{u}).toParameters.entropyDenominator ≤
      (spineData.{u}).toParameters.dischargeScale *
        coldExternalStubCount (spineData.{u}).toParameters := by
  have t : (spineData.{u}).toParameters.threshold = 3 := rfl
  have s : (spineData.{u}).toParameters.dischargeScale = 4 := rfl
  have o : (spineData.{u}).toParameters.windowOrder = 13 := rfl
  have d : (spineData.{u}).toParameters.entropyDenominator = 10 := rfl
  unfold coldExternalStubCount
  rw [t, s, o, d]
  norm_num

/-- **Node `[53]` on the `[159]`/`[160]`-yes dense residual, high-entropy
arm**: the entropy cap is active.  Its sole output `K .entropyCapActive`
contradicts `[53]`'s bound arm `K .entropyCapBound`
(`instIncompatibleEntropyCapBoundActive`). -/
@[reducible] noncomputable def denseEntropyCapActiveRow :
    AtomicStrategy EGInput.{u} :=
  factOnly `HypostructureErdos64EG.denseEntropyCapActive
    { Requires := [K .denseDeficiencyBelow, K .windowPackageUnrealized,
        K .entropyPackageDemand]
      Produces := [K .entropyCapActive]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .entropyCapActive)
        ⟨Graph.Contracts.Spine.entropyCapActive_of_denseUnrealized
          (spineData.{u}).toParameters inputs.current.object
          (spineData.{u}).windowRate_eq_barrier
          ((spineData.{u}).separatedScaleCount_le _)
          (spineData.{u}).entropyDenominator_pos
          spineData_entropySlack
          (inputs.get (K .denseDeficiencyBelow)).down
          (inputs.get (K .windowPackageUnrealized)).down
          (inputs.get (K .entropyPackageDemand)).down⟩
        .nil)

end HypostructureErdos64EG
