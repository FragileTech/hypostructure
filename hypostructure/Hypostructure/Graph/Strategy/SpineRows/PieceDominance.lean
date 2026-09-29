import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.Spine.PieceDominance

/-!
# CT3: dominance irreducibility of G's pieces (keys 9975–9980)

Lean improvement (CT3, external-type compression).  A gadget on the cut
boundary of a support `Z` of G that is dominated by `G[Z]` (its linkage systems
are realized in `G[Z]` with the same terminal pairing and length vector, and it
has no power-of-two cycle of its own) glues into `G − Z` without a power-of-two
cycle; node `[13]` (`lem:replacement`) then forbids it when it is strictly
smaller, keeps the boundary-degree profile and the baseline.

* `pieceDominanceRow` publishes, from G's target avoidance (`K .selection`) and
  node `[13]` (`K .replacementExclusion`), the irreducibility of every proper
  connected support (`K .pieceDominanceIrreducible`), its terminal-pair form
  (`K .twoExitNewLength`) and, with the baseline (`K .minDegreeBaseline`), the
  two-exit size monotonicity through the copy of one two-exit support onto
  another (`K .twoExitSizeMonotone`).
* `canonicalPieceDominanceRow` instantiates the three at the canonical pieces of
  `R` (`K .canonicalPieceDominance`, `K .canonicalTwoExitNewLength`,
  `K .canonicalTwoExitSizeMonotone`), using node
  `[15]`'s maximal packing (`K .maximalPacking`) for properness.
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure.Core.Residual Hypostructure.Core.Strategy

universe u v

/-- **CT3 at G** (`PieceDominanceIrreducibleStatement`,
`TwoExitNewLengthStatement`). -/
@[reducible] noncomputable def pieceDominanceRow
    {BranchState : Graph.FiniteObject.{u} → Type v}
    {Presentation : Type} {presentation : Presentation} {data : Data.{u}} :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.pieceDominance
    { Requires := [K .selection, K .replacementExclusion, K .minDegreeBaseline]
      Produces := [K .pieceDominanceIrreducible, K .twoExitNewLength,
        K .twoExitSizeMonotone]
      requiresUnique := by key_fresh
      producesUnique := by key_fresh
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .pieceDominanceIrreducible)
        ⟨Graph.Contracts.Spine.pieceDominanceIrreducible data.toParameters
          inputs.current.object
          (inputs.get (K .selection)).down.1
          (inputs.get (K .replacementExclusion)).down⟩
      (.cons (key := K .twoExitNewLength)
        ⟨Graph.Contracts.Spine.twoExitNewLength data.toParameters
          inputs.current.object
          (inputs.get (K .selection)).down.1
          (inputs.get (K .replacementExclusion)).down⟩
      (.cons (key := K .twoExitSizeMonotone)
        ⟨Graph.Contracts.Spine.twoExitSizeMonotone data.toParameters
          inputs.current.object
          (inputs.get (K .selection)).down.1
          (inputs.get (K .minDegreeBaseline)).down
          (inputs.get (K .replacementExclusion)).down⟩
      .nil)))
    0 0

/-- **CT3 at the canonical pieces of `R`** (`CanonicalPieceDominanceStatement`,
`CanonicalTwoExitNewLengthStatement`). -/
@[reducible] noncomputable def canonicalPieceDominanceRow
    {BranchState : Graph.FiniteObject.{u} → Type v}
    {Presentation : Type} {presentation : Presentation} {data : Data.{u}} :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.canonicalPieceDominance
    { Requires := [K .pieceDominanceIrreducible, K .twoExitNewLength,
        K .twoExitSizeMonotone, K .maximalPacking]
      Produces := [K .canonicalPieceDominance, K .canonicalTwoExitNewLength,
        K .canonicalTwoExitSizeMonotone]
      requiresUnique := by key_fresh
      producesUnique := by key_fresh
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .canonicalPieceDominance)
        ⟨Graph.Contracts.Spine.canonicalPieceDominance data.toParameters
          inputs.current.object
          (inputs.get (K .pieceDominanceIrreducible)).down
          (inputs.get (K .maximalPacking)).down⟩
      (.cons (key := K .canonicalTwoExitNewLength)
        ⟨Graph.Contracts.Spine.canonicalTwoExitNewLength data.toParameters
          inputs.current.object
          (inputs.get (K .twoExitNewLength)).down
          (inputs.get (K .maximalPacking)).down⟩
      (.cons (key := K .canonicalTwoExitSizeMonotone)
        ⟨Graph.Contracts.Spine.canonicalTwoExitSizeMonotone data.toParameters
          inputs.current.object
          (inputs.get (K .twoExitSizeMonotone)).down
          (inputs.get (K .maximalPacking)).down⟩
      .nil)))
    0 0

end Hypostructure.Graph.Strategy.Spine
